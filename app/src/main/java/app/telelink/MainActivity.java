package app.telelink;

import android.app.Activity;
import android.app.AlertDialog;
import android.app.DownloadManager;
import android.app.PendingIntent;
import android.content.Intent;
import android.content.SharedPreferences;
import android.content.pm.PackageInstaller;
import android.content.pm.PackageManager;
import android.graphics.Bitmap;
import android.graphics.Canvas;
import android.graphics.Rect;
import android.media.MediaMetadataRetriever;
import android.content.res.ColorStateList;
import android.graphics.Color;
import android.graphics.drawable.Drawable;
import android.graphics.drawable.GradientDrawable;
import android.graphics.drawable.RippleDrawable;
import android.net.Uri;
import android.os.Build;
import android.os.Bundle;
import android.os.Environment;
import android.os.Handler;
import android.os.Looper;
import android.os.Message;
import android.text.InputType;
import android.text.TextUtils;
import android.util.Base64;
import android.view.Gravity;
import android.view.KeyEvent;
import android.view.PixelCopy;
import android.view.View;
import android.view.ViewGroup;
import android.view.inputmethod.EditorInfo;
import android.view.inputmethod.InputMethodManager;
import android.webkit.CookieManager;
import android.webkit.WebChromeClient;
import android.webkit.WebResourceRequest;
import android.webkit.WebResourceResponse;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;
import android.widget.Button;
import android.widget.EditText;
import android.widget.LinearLayout;
import android.widget.ProgressBar;
import android.widget.TextView;
import android.widget.Toast;

import androidx.webkit.WebSettingsCompat;
import androidx.webkit.WebViewCompat;
import androidx.webkit.WebViewFeature;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.HttpURLConnection;
import java.net.URL;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.json.JSONArray;
import org.json.JSONObject;

public class MainActivity extends Activity {

    private WebView web;
    private EditText urlBar;
    private ProgressBar progress;
    private Button btnVideos;
    private Button btnLock;
    private Button btnSend;
    private volatile int sendSeq;

    /** Lo último que se mandó a la tele: hace falta para saltar y para recordar por dónde ibas. */
    private static final class Session {
        Dlna.Device target;
        String id, base, how, title, pageKey, src;
        Map<String, String> headers;
        volatile boolean framing;
        volatile int offset; // segundo en el que empieza el flujo actual (solo modo compatible)
    }

    private volatile Session session; // cada envío nuevo (o un "Parar") cancela la vigilancia del anterior

    private final List<String> videos = new ArrayList<>();
    private final ExecutorService io = Executors.newSingleThreadExecutor();
    private final Handler ui = new Handler(Looper.getMainLooper());

    private Dlna.Device tv;
    private volatile String lockedDomain; // null = candado quitado
    private volatile String pageTitle = "Vídeo";
    private final Map<String, Map<String, String>> videoHeaders = new ConcurrentHashMap<>();
    private final Map<String, Bridge.Info> infos = new ConcurrentHashMap<>();
    private final Set<String> measuring = ConcurrentHashMap.newKeySet();
    private final ExecutorService probes = Executors.newFixedThreadPool(3);
    private volatile String currentPage = "";
    private String userAgent = "";
    private static final int AUTO = 0, COMPAT = 1, DIRECT = 2, PRELOAD = 3, LOW = 4;
    private static final String RELEASE = "https://github.com/Cimentacion/Telelink/releases/download/latest/";
    private static final String INSTALL = "app.telelink.INSTALL";
    /** Tamaño máximo de un archivo directo que se puede guardar en el móvil (5000 MB). */
    private static final long MAX_SAVE = 5000L * 1024 * 1024;
    private boolean resumed;
    private float[] lastBox; // dónde estaba el vídeo dentro de la página en la última captura
    private String lastBoxUrl = "";
    private boolean autoLockPending; // activar el candado en cuanto cargue la página pedida

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        buildUi();
        setupWeb();
        loadSavedTv();
        Bridge.wipe(new File(getCacheDir(), "preload"));
        if (!handleIntent(getIntent())) {
            showHome();
        }
        checkUpdate();
    }

    // ---------- Actualización automática ----------

    private static HttpURLConnection get(String url) throws IOException {
        HttpURLConnection c = (HttpURLConnection) new URL(url).openConnection();
        c.setConnectTimeout(10000);
        c.setReadTimeout(20000);
        c.setInstanceFollowRedirects(true);
        c.setUseCaches(false);
        return c;
    }

    /** Al abrir la app mira si hay una compilación más nueva en GitHub. */
    private void checkUpdate() {
        new Thread(() -> {
            try {
                int mine = getPackageManager().getPackageInfo(getPackageName(), 0).versionCode;
                HttpURLConnection c = get(RELEASE + "version.txt");
                if (c.getResponseCode() != 200) return;
                byte[] buf = new byte[32];
                InputStream in = c.getInputStream();
                int n = in.read(buf);
                in.close();
                if (n <= 0) return;
                final int remote = Integer.parseInt(new String(buf, 0, n, "UTF-8").trim());
                if (remote <= mine) return;
                ui.post(() -> {
                    if (isFinishing()) return;
                    new AlertDialog.Builder(MainActivity.this)
                            .setTitle("Hay una versión nueva")
                            .setMessage("Tienes la " + mine + " y está disponible la " + remote + ".")
                            .setPositiveButton("Actualizar", (d, w) -> downloadUpdate())
                            .setNegativeButton("Ahora no", null)
                            .show();
                });
            } catch (Exception ignored) {
                // Sin conexión o sin versión publicada: se vuelve a mirar la próxima vez.
            }
        }, "telelink-update").start();
    }

    private void downloadUpdate() {
        toast("Descargando la actualización…");
        new Thread(() -> {
            try {
                HttpURLConnection c = get(RELEASE + "TeleLink.apk");
                if (c.getResponseCode() != 200) throw new IOException("HTTP " + c.getResponseCode());
                PackageInstaller installer = getPackageManager().getPackageInstaller();
                PackageInstaller.SessionParams params =
                        new PackageInstaller.SessionParams(PackageInstaller.SessionParams.MODE_FULL_INSTALL);
                int id = installer.createSession(params);
                PackageInstaller.Session session = installer.openSession(id);
                try {
                    OutputStream out = session.openWrite("telelink.apk", 0, -1);
                    InputStream in = c.getInputStream();
                    byte[] buf = new byte[65536];
                    int r;
                    while ((r = in.read(buf)) > 0) out.write(buf, 0, r);
                    session.fsync(out);
                    out.close();
                    in.close();

                    Intent back = new Intent(MainActivity.this, MainActivity.class).setAction(INSTALL);
                    int flags = PendingIntent.FLAG_UPDATE_CURRENT
                            | (Build.VERSION.SDK_INT >= 31 ? PendingIntent.FLAG_MUTABLE : 0);
                    PendingIntent pi = PendingIntent.getActivity(MainActivity.this, 2, back, flags);
                    session.commit(pi.getIntentSender());
                } finally {
                    session.close();
                }
            } catch (final Exception e) {
                ui.post(() -> toast("No se pudo actualizar: " + e.getMessage()));
            }
        }, "telelink-download").start();
    }

    /** Android devuelve aquí el resultado de la instalación; lo normal es que pida confirmación. */
    private void onInstallResult(Intent intent) {
        int status = intent.getIntExtra(PackageInstaller.EXTRA_STATUS, PackageInstaller.STATUS_FAILURE);
        if (status == PackageInstaller.STATUS_PENDING_USER_ACTION) {
            Intent confirm = intent.getParcelableExtra(Intent.EXTRA_INTENT);
            if (confirm != null) {
                try {
                    startActivity(confirm);
                } catch (Exception e) {
                    toast("No se pudo abrir el instalador");
                }
            }
        } else if (status != PackageInstaller.STATUS_SUCCESS) {
            String msg = intent.getStringExtra(PackageInstaller.EXTRA_STATUS_MESSAGE);
            toast("Actualización cancelada" + (msg == null ? "" : ": " + msg));
        }
    }

    @Override
    protected void onNewIntent(Intent intent) {
        super.onNewIntent(intent);
        setIntent(intent);
        handleIntent(intent);
    }

    // ---------- Interfaz ----------

    // Paleta
    private static final int BG = 0xFF0F1218, SURFACE = 0xFF171C26, RAISED = 0xFF242B39,
            ACCENT = 0xFF3DDC97, ACCENT_DIM = 0xFF1D3A30, TEXT = 0xFFE6E9EF, MUTED = 0xFF8B93A3,
            ON_ACCENT = 0xFF0B1410;

    private int dp(int v) {
        return (int) (v * getResources().getDisplayMetrics().density + 0.5f);
    }

    /** Fondo redondeado con efecto al pulsar. */
    private Drawable pill(int color, int radiusDp) {
        GradientDrawable g = new GradientDrawable();
        g.setColor(color);
        g.setCornerRadius(dp(radiusDp));
        return new RippleDrawable(ColorStateList.valueOf(0x33FFFFFF), g, null);
    }

    private LinearLayout.LayoutParams cell(int width, int height, float weight, int marginDp) {
        LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(width, height, weight);
        int m = dp(marginDp);
        lp.setMargins(m, m, m, m);
        return lp;
    }

    private Button bar(String text) {
        Button b = new Button(this);
        b.setText(text);
        b.setAllCaps(false);
        b.setTextSize(14);
        b.setTextColor(TEXT);
        b.setSingleLine(true);
        b.setEllipsize(TextUtils.TruncateAt.END);
        b.setMinWidth(0);
        b.setMinimumWidth(0);
        b.setMinHeight(0);
        b.setMinimumHeight(0);
        b.setPadding(dp(6), 0, dp(6), 0);
        b.setStateListAnimator(null);
        b.setBackground(pill(RAISED, 12));
        return b;
    }

    private void buildUi() {
        getWindow().setStatusBarColor(SURFACE);
        getWindow().setNavigationBarColor(SURFACE);

        LinearLayout root = new LinearLayout(this);
        root.setOrientation(LinearLayout.VERTICAL);
        root.setBackgroundColor(BG);

        // Barra de dirección
        LinearLayout top = new LinearLayout(this);
        top.setOrientation(LinearLayout.HORIZONTAL);
        top.setGravity(Gravity.CENTER_VERTICAL);
        top.setBackgroundColor(SURFACE);
        top.setPadding(dp(8), dp(6), dp(8), dp(6));

        urlBar = new EditText(this);
        urlBar.setSingleLine(true);
        urlBar.setHint("Busca o escribe una web");
        urlBar.setHintTextColor(MUTED);
        urlBar.setTextColor(TEXT);
        urlBar.setTextSize(15);
        urlBar.setSelectAllOnFocus(true);
        urlBar.setBackground(pill(RAISED, 22));
        urlBar.setPadding(dp(16), 0, dp(16), 0);
        urlBar.setInputType(InputType.TYPE_CLASS_TEXT | InputType.TYPE_TEXT_VARIATION_URI);
        urlBar.setImeOptions(EditorInfo.IME_ACTION_GO);
        urlBar.setOnEditorActionListener((v, actionId, event) -> {
            boolean enter = event != null && event.getKeyCode() == KeyEvent.KEYCODE_ENTER
                    && event.getAction() == KeyEvent.ACTION_DOWN;
            if (actionId == EditorInfo.IME_ACTION_GO || enter) {
                go(urlBar.getText().toString());
                return true;
            }
            return false;
        });
        top.addView(urlBar, new LinearLayout.LayoutParams(0, dp(44), 1));

        Button goBtn = bar("Ir");
        goBtn.setTextColor(ON_ACCENT);
        goBtn.setBackground(pill(ACCENT, 22));
        goBtn.setOnClickListener(v -> go(urlBar.getText().toString()));
        LinearLayout.LayoutParams goLp = new LinearLayout.LayoutParams(dp(56), dp(44));
        goLp.setMargins(dp(8), 0, 0, 0);
        top.addView(goBtn, goLp);
        root.addView(top);

        progress = new ProgressBar(this, null, android.R.attr.progressBarStyleHorizontal);
        progress.setMax(100);
        progress.setProgressTintList(ColorStateList.valueOf(ACCENT));
        progress.setProgressBackgroundTintList(ColorStateList.valueOf(SURFACE));
        progress.setVisibility(View.INVISIBLE);
        root.addView(progress, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(3)));

        web = new WebView(this);
        web.setBackgroundColor(BG);
        root.addView(web, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1));

        // Botón grande de enviar: solo aparece cuando hay un vídeo detectado
        LinearLayout sendWrap = new LinearLayout(this);
        sendWrap.setBackgroundColor(SURFACE);
        btnSend = new Button(this);
        btnSend.setAllCaps(false);
        btnSend.setTextSize(16);
        btnSend.setTextColor(ON_ACCENT);
        btnSend.setSingleLine(true);
        btnSend.setEllipsize(TextUtils.TruncateAt.END);
        btnSend.setStateListAnimator(null);
        btnSend.setBackground(pill(ACCENT, 14));
        btnSend.setVisibility(View.GONE);
        btnSend.setOnClickListener(v -> quickSend());
        LinearLayout.LayoutParams sendLp =
                new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(52));
        sendLp.setMargins(dp(8), dp(8), dp(8), dp(2));
        sendWrap.addView(btnSend, sendLp);
        root.addView(sendWrap);

        // Barra inferior
        LinearLayout bottom = new LinearLayout(this);
        bottom.setOrientation(LinearLayout.HORIZONTAL);
        bottom.setBackgroundColor(SURFACE);
        bottom.setPadding(dp(5), dp(3), dp(5), dp(5));

        Button back = bar("◀");
        back.setOnClickListener(v -> {
            back();
        });
        bottom.addView(back, cell(0, dp(46), 1, 3));

        Button menu = bar("☰");
        menu.setTextSize(17);
        menu.setOnClickListener(v -> showMenu());
        bottom.addView(menu, cell(0, dp(46), 1, 3));

        btnLock = bar("🔓");
        btnLock.setOnClickListener(v -> toggleLock());
        bottom.addView(btnLock, cell(0, dp(46), 1, 3));

        btnVideos = bar("Vídeos · 0");
        btnVideos.setOnClickListener(v -> showVideos());
        bottom.addView(btnVideos, cell(0, dp(46), 2.2f, 3));

        Button remote = bar("Mando");
        remote.setOnClickListener(v -> showRemote());
        bottom.addView(remote, cell(0, dp(46), 1.8f, 3));

        root.addView(bottom);
        setContentView(root);
    }

    // ---------- Portada ----------

    private static String esc(String t) {
        return t == null ? "" : t.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
                .replace("\"", "&quot;");
    }

    /** Nombre corto para las listas: "Naruto 1" en vez del título entero de la web. */
    private static String nice(String title, String url) {
        try {
            Uri u = Uri.parse(url);
            String site = baseDomain(u.getHost());
            int dot = site.indexOf('.');
            String n = Names.nice(title, dot > 0 ? site.substring(0, dot) : site, u.getLastPathSegment());
            return n == null || n.isEmpty() ? (title == null || title.isEmpty() ? url : title) : n;
        } catch (Exception e) {
            return title == null || title.isEmpty() ? url : title;
        }
    }

    private void cards(StringBuilder h, String heading, String key, int max, boolean grid) {
        JSONArray a = loadList(key);
        if (a.length() == 0) return;
        SharedPreferences resume = getSharedPreferences("resume", MODE_PRIVATE);
        h.append("<h3>").append(heading);
        if (grid) h.append("<a href='telelink://clear'>Borrar</a>");
        h.append("</h3>");
        if (grid) h.append("<div class='grid'>");
        for (int i = 0; i < a.length() && i < max; i++) {
            JSONObject o = a.optJSONObject(i);
            if (o == null) continue;
            String u = o.optString("u");
            String host = Uri.parse(u).getHost();
            int pos = resume.getInt(u, 0);
            String name = esc(nice(o.optString("t"), u));
            String sub = esc(host == null ? u : host) + (pos >= 60 ? " · vas por " + clock(pos) : "");
            if (!grid) {
                h.append("<a class='c' href=\"").append(esc(u)).append("\"><b>").append(name)
                        .append("</b><span>").append(sub).append("</span></a>");
                continue;
            }
            String img = thumbData(u, pos >= 60);
            h.append("<div class='g'><a class='o' href=\"").append(esc(u)).append("\">")
                    .append(img == null ? "<i></i>" : "<img src='" + img + "'>")
                    .append("<b>").append(name).append("</b><span>").append(sub).append("</span></a>")
                    .append("<a class='x' href=\"telelink://remove?u=").append(Uri.encode(u)).append("\">×</a></div>");
        }
        if (grid) h.append("</div>");
    }

    /**
     * Busca vídeos de ok.ru. Se hace con el buscador (limitado a ok.ru) porque la búsqueda propia
     * de ok.ru no admite que se le pase el texto en la dirección.
     */
    private void searchOkru(String q) {
        String t = q == null ? "" : q.trim();
        if (t.isEmpty()) {
            toast("Escribe qué quieres buscar");
            return;
        }
        go("https://duckduckgo.com/?q=" + Uri.encode(t + " site:ok.ru inurl:video"));
    }

    private void askOkru() {
        final EditText in = new EditText(this);
        in.setHint("Naruto 1, una peli…");
        in.setSingleLine(true);
        new AlertDialog.Builder(this)
                .setTitle("Buscar vídeos en ok.ru")
                .setView(in)
                .setPositiveButton("Buscar", (d, w) -> searchOkru(in.getText().toString()))
                .setNegativeButton("Cancelar", null)
                .show();
    }

    /** Botones de la portada: borrar todos los recientes o quitar uno. */
    private void homeAction(Uri u) {
        if ("clear".equals(u.getHost())) {
            new AlertDialog.Builder(this)
                    .setTitle("¿Borrar los recientes?")
                    .setPositiveButton("Borrar", (d, w) -> {
                        storeList("history", new JSONArray());
                        showHome();
                    })
                    .setNegativeButton("Cancelar", null)
                    .show();
        } else if ("okru".equals(u.getHost())) {
            searchOkru(u.getQueryParameter("q"));
        } else if ("remove".equals(u.getHost())) {
            String target = u.getQueryParameter("u");
            JSONArray a = loadList("history");
            int i = target == null ? -1 : indexOf(a, target);
            if (i < 0) return;
            a.remove(i);
            storeList("history", a);
            showHome();
        }
    }

    /** Portada con los pasos básicos, tus favoritos y lo último que abriste. */
    private void showHome() {
        grabNow();
        StringBuilder h = new StringBuilder();
        h.append("<html><head><meta name='viewport' content='width=device-width,initial-scale=1'><style>")
                .append("body{background:#0f1218;color:#e6e9ef;font-family:sans-serif;margin:0;padding:22px 18px 40px}")
                .append("h1{color:#3ddc97;font-size:26px;margin:6px 0 2px}p.s{color:#8b93a3;margin:0 0 18px}")
                .append("ol{padding-left:20px;line-height:1.55;color:#c9ced8;margin:0 0 8px}")
                .append("h3{color:#8b93a3;font-size:13px;text-transform:uppercase;letter-spacing:.08em;margin:26px 0 8px}")
                .append("a.c{display:block;background:#171c26;border-radius:12px;padding:12px 14px;margin:0 0 8px;")
                .append("text-decoration:none;color:#e6e9ef}a.c b{display:block;font-weight:600;white-space:nowrap;")
                .append("overflow:hidden;text-overflow:ellipsis}a.c span{color:#8b93a3;font-size:13px}")
                .append("form.s{display:flex;gap:8px;margin:18px 0 0}form.s input{flex:1;min-width:0;background:#171c26;")
                .append("border:0;border-radius:12px;padding:13px 14px;color:#e6e9ef;font-size:16px;outline:none}")
                .append("form.s button{background:#3ddc97;color:#0f1218;border:0;border-radius:12px;padding:0 18px;")
                .append("font-size:15px;font-weight:600}")
                .append("h3 a{float:right;color:#3ddc97;text-decoration:none;text-transform:none;letter-spacing:0;")
                .append("font-weight:normal;padding:0 2px}")
                .append(".grid{display:grid;grid-template-columns:1fr 1fr;gap:10px}")
                .append(".g{position:relative;background:#171c26;border-radius:12px;overflow:hidden}")
                .append(".g a.o{display:block;text-decoration:none;color:#e6e9ef}")
                .append(".g img,.g i{display:block;width:100%;aspect-ratio:16/9;object-fit:cover;background:#0b0e13}")
                .append(".g b,.g span{display:block;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}")
                .append(".g b{font-weight:600;font-size:14px;padding:8px 10px 0}")
                .append(".g span{color:#8b93a3;font-size:12px;padding:2px 10px 9px}")
                .append(".g a.x{position:absolute;top:6px;right:6px;width:28px;height:28px;line-height:28px;")
                .append("text-align:center;border-radius:14px;background:rgba(0,0,0,.6);color:#fff;")
                .append("text-decoration:none;font-size:17px}")
                .append("</style></head><body><h1>TeleLink</h1><p class='s'>Del móvil a la tele, sin anuncios.</p>")
                .append("<ol><li>Abre una web y dale al play.</li>")
                .append("<li>Pulsa el botón verde <b>Enviar a la tele</b>.</li>")
                .append("<li>Controla la peli desde <b>Mando</b>.</li></ol>")
                .append("<form class='s' action='telelink://okru' method='get'>")
                .append("<input name='q' placeholder='Buscar vídeos en ok.ru' autocomplete='off'>")
                .append("<button>Buscar</button></form>");
        cards(h, "Favoritos", "favorites", 12, false);
        cards(h, "Recientes", "history", 6, true);
        h.append("</body></html>");
        currentPage = "";
        urlBar.setText("");
        web.loadDataWithBaseURL(null, h.toString(), "text/html", "utf-8", null);
    }

    private void toast(String s) {
        Toast.makeText(this, s, Toast.LENGTH_SHORT).show();
    }

    private void refreshVideos() {
        btnVideos.setText("Vídeos · " + videos.size());
        btnVideos.setTextColor(videos.isEmpty() ? MUTED : ACCENT);
        btnSend.setVisibility(videos.isEmpty() ? View.GONE : View.VISIBLE);
        if (videos.isEmpty() || !sending) sendLabel();
    }

    private volatile boolean sending;

    private void sendLabel() {
        btnSend.setText(tv == null ? "▶  Enviar a la tele" : "▶  Enviar a " + tv.name);
    }

    /** Texto de progreso en el botón grande (se puede llamar desde cualquier hilo). */
    private void status(final String text) {
        ui.post(() -> btnSend.setText(text));
    }

    // ---------- Medir los vídeos detectados ----------

    private void measure(final String url) {
        if (infos.containsKey(url) || !measuring.add(url)) return;
        final Map<String, String> h = headersFor(url);
        probes.execute(() -> {
            try {
                infos.put(url, Bridge.measure(url, h));
            } finally {
                measuring.remove(url);
            }
        });
    }

    /** Ejecuta "then" cuando todos los vídeos de la lista están medidos (o tras unos segundos). */
    private void withInfos(final Runnable then) {
        final List<String> snap = new ArrayList<>(videos);
        boolean ready = true;
        for (String v : snap) {
            if (!infos.containsKey(v)) {
                ready = false;
                measure(v);
            }
        }
        if (ready) {
            then.run();
            return;
        }
        new Thread(() -> {
            long end = System.currentTimeMillis() + 7000;
            while (System.currentTimeMillis() < end) {
                boolean all = true;
                for (String v : snap) if (!infos.containsKey(v)) all = false;
                if (all) break;
                try {
                    Thread.sleep(150);
                } catch (InterruptedException e) {
                    break;
                }
            }
            ui.post(then);
        }, "telelink-measure").start();
    }

    /** Peso comparable: segundos de duración; los archivos se convierten a segundos aproximados. */
    private long score(String url) {
        Bridge.Info i = infos.get(url);
        if (i == null || i.code >= 400) return 0;
        if (i.hls) return Math.max(0, i.secs);
        return i.bytes > 0 ? i.bytes / 200000 : 0;
    }

    /** Los vídeos ordenados del más largo/pesado al más pequeño. */
    private List<String> ranked() {
        List<String> list = new ArrayList<>(videos);
        java.util.Collections.sort(list, (x, y) -> Long.compare(score(y), score(x)));
        return list;
    }

    /** El vídeo de verdad suele ser el más largo o pesado; los anuncios falsos son cortos. */
    private String bestVideo() {
        List<String> list = ranked();
        if (list.isEmpty()) return null;
        if (score(list.get(0)) > 0) return list.get(0);
        // Sin medidas: la lista HLS principal si la hay; si no, el último archivo.
        String firstHls = null, lastFile = null;
        for (String v : videos) {
            String p = Uri.parse(v).getPath();
            p = p == null ? "" : p.toLowerCase(Locale.US);
            if (p.endsWith(".m3u8")) {
                if (p.contains("master")) return v;
                if (firstHls == null) firstHls = v;
            } else {
                lastFile = v;
            }
        }
        return firstHls != null ? firstHls : lastFile;
    }

    private void quickSend() {
        if (videos.isEmpty()) {
            toast("Dale primero al play en la página");
            return;
        }
        if (sending) return;
        btnSend.setText("Eligiendo el vídeo…");
        withInfos(() -> {
            String url = bestVideo();
            if (url == null) {
                sendLabel();
                toast("Dale primero al play en la página");
                return;
            }
            send(url, AUTO);
        });
    }

    // ---------- Navegador ----------

    private void setupWeb() {
        WebSettings s = web.getSettings();
        s.setJavaScriptEnabled(true);
        s.setDomStorageEnabled(true);
        s.setDatabaseEnabled(true);
        s.setLoadWithOverviewMode(true);
        s.setUseWideViewPort(true);
        s.setBuiltInZoomControls(true);
        s.setDisplayZoomControls(false);
        s.setMediaPlaybackRequiresUserGesture(true);
        s.setMixedContentMode(WebSettings.MIXED_CONTENT_COMPATIBILITY_MODE);
        // Con ventanas múltiples activadas, los window.open pasan por onCreateWindow y ahí se bloquean.
        s.setSupportMultipleWindows(true);
        s.setJavaScriptCanOpenWindowsAutomatically(false);
        CookieManager.getInstance().setAcceptThirdPartyCookies(web, true);
        // Quita la marca de WebView del User-Agent: hay reproductores que se niegan si la ven.
        userAgent = s.getUserAgentString().replace("; wv", "").replaceAll("Version/\\d+\\.\\d+ ", "");
        s.setUserAgentString(userAgent);
        // Sin esto cada petición lleva "X-Requested-With: app.telelink" y hay webs que por eso
        // rechazan los formularios (el captcha se pasa, pero te devuelven a la misma página).
        try {
            if (WebViewFeature.isFeatureSupported(WebViewFeature.REQUESTED_WITH_HEADER_ALLOW_LIST)) {
                WebSettingsCompat.setRequestedWithHeaderOriginAllowList(s, Collections.<String>emptySet());
            }
        } catch (Throwable ignored) {
        }

        try {
            if (WebViewFeature.isFeatureSupported(WebViewFeature.DOCUMENT_START_SCRIPT)) {
                WebViewCompat.addDocumentStartJavaScript(web, COMPAT_JS, Collections.singleton("*"));
            }
        } catch (Throwable ignored) {
        }

        web.setWebChromeClient(new WebChromeClient() {
            @Override
            public void onProgressChanged(WebView view, int p) {
                progress.setProgress(p);
                progress.setVisibility(p < 100 ? View.VISIBLE : View.INVISIBLE);
            }

            @Override
            public void onReceivedTitle(WebView view, String title) {
                if (title != null && !title.isEmpty()) pageTitle = title;
            }

            @Override
            public boolean onCreateWindow(WebView view, boolean isDialog, boolean isUserGesture, Message msg) {
                if (!isUserGesture || msg == null || !(msg.obj instanceof WebView.WebViewTransport)) return false;
                // El pop-up se "abre" en una ventana que no se ve y que no carga nada: la página cree
                // que su anuncio ha salido (si no, hay webs que no dejan seguir) y tú no lo ves.
                try {
                    final WebView ghost = new WebView(MainActivity.this);
                    ghost.setWebViewClient(new WebViewClient() {
                        @Override
                        public boolean shouldOverrideUrlLoading(WebView v, WebResourceRequest r) {
                            return true;
                        }

                        @Override
                        public WebResourceResponse shouldInterceptRequest(WebView v, WebResourceRequest r) {
                            return new WebResourceResponse("text/plain", "utf-8",
                                    new ByteArrayInputStream(new byte[0]));
                        }
                    });
                    ((WebView.WebViewTransport) msg.obj).setWebView(ghost);
                    msg.sendToTarget();
                    ui.postDelayed(() -> {
                        try {
                            ghost.destroy();
                        } catch (Exception ignored) {
                        }
                    }, 4000);
                    return true;
                } catch (Exception e) {
                    return false;
                }
            }
        });

        web.setWebViewClient(new WebViewClient() {
            @Override
            public WebResourceResponse shouldInterceptRequest(WebView view, WebResourceRequest request) {
                Uri u = request.getUrl();
                if (!adsAllowed && AdBlock.isAd(u.getHost())) {
                    return new WebResourceResponse("text/plain", "utf-8",
                            new ByteArrayInputStream(new byte[0]));
                }
                if (isVideo(u) || isMediaRequest(request)) {
                    Map<String, String> h = request.getRequestHeaders();
                    videoHeaders.put(u.toString(), h == null ? new HashMap<>() : new HashMap<>(h));
                    addVideo(u.toString());
                }
                return null;
            }

            @Override
            public boolean shouldOverrideUrlLoading(WebView view, WebResourceRequest request) {
                Uri u = request.getUrl();
                String scheme = u.getScheme() == null ? "" : u.getScheme().toLowerCase(Locale.US);
                if (scheme.equals("telelink")) {
                    if (currentPage.isEmpty()) homeAction(u); // solo valen desde la portada
                    return true;
                }
                if (!scheme.equals("http") && !scheme.equals("https")) return true; // intent://, market://...
                if (AdBlock.isAd(u.getHost()) && (!adsAllowed || request.isForMainFrame())) return true;
                if (request.isForMainFrame() && currentPage.isEmpty()) {
                    go(u.toString());
                    return true;
                }
                if (request.isForMainFrame() && isClip(u)) {
                    offerSave(u.toString());
                    return true;
                }
                String lock = lockedDomain;
                if (lock != null && request.isForMainFrame() && !lock.equals(baseDomain(u.getHost()))) {
                    toast("Bloqueado salto a " + u.getHost());
                    return true;
                }
                return false;
            }

            @Override
            public void onPageStarted(WebView view, String url, Bitmap favicon) {
                if (url != null && url.startsWith("http")) {
                    urlBar.setText(url);
                    currentPage = url;
                    captchaZoomed = "";
                    adsAllowed = getSharedPreferences("noblock", MODE_PRIVATE)
                            .getBoolean(baseDomain(Uri.parse(url).getHost()), false);
                    view.evaluateJavascript(COMPAT_JS, null);
                } else if (url != null && !currentPage.isEmpty() && !autoLockPending) {
                    // Se ha vuelto a la portada por otro camino: vuelve a contar como portada.
                    currentPage = "";
                    urlBar.setText("");
                }
            }

            @Override
            public void onPageFinished(WebView view, String url) {
                if (url != null && url.startsWith("http")) {
                    addHistory(view.getTitle(), url);
                    view.evaluateJavascript(COMPAT_JS, null); // por si el móvil no admite inyectar al inicio
                    ui.postDelayed(() -> snap(), 2500);
                    ui.postDelayed(() -> findVideos(), 2000);
                    ui.postDelayed(() -> findVideos(), 6000);
                    final String at = url;
                    ui.postDelayed(() -> zoomCaptcha(at), 1200);
                    ui.postDelayed(() -> zoomCaptcha(at), 4000);
                }
                if (!autoLockPending || url == null || !url.startsWith("http")) return;
                autoLockPending = false;
                String host = Uri.parse(url).getHost();
                if (host == null || isSearchEngine(host)) return;
                // Candado automático: a partir de aquí la página no puede llevarte a otra web.
                setLock(baseDomain(host));
            }
        });
    }

    /** Busca un captcha en la página; devuelve cuánto hay que ampliar para que se pueda tocar. */
    private static final String CAPTCHA_JS = "(function(){try{var e=document.querySelector("
            + "'iframe[src*=\\'recaptcha\\'],iframe[src*=\\'hcaptcha\\'],iframe[src*=\\'turnstile\\'],"
            + ".g-recaptcha,.h-captcha,.cf-turnstile');if(!e)return 0;var r=e.getBoundingClientRect();"
            + "if(r.width<50)return 0;window.__tlCaptcha=e;"
            + "var w=window.visualViewport?window.visualViewport.width:window.innerWidth;"
            + "return 0.75*w/r.width;}catch(x){return 0;}})()";
    private String captchaZoomed = "";
    /**
     * El navegador incrustado de Android no trae la API de notificaciones web que sí tiene Chrome.
     * Hay webs que la consultan al pasar el captcha y, al no encontrarla, dan el formulario por malo.
     * Se rellena el hueco con lo mismo que responde un Chrome recién instalado ("sin decidir").
     */
    private static final String COMPAT_JS = "(function(){try{if(!('Notification' in window)){"
            + "var N=function(){};N.permission='default';"
            + "N.requestPermission=function(c){if(c)c('default');return Promise.resolve('default');};"
            + "window.Notification=N;}"
            + "if(!navigator.permissions){Object.defineProperty(navigator,'permissions',{value:{"
            + "query:function(){return Promise.resolve({state:'prompt',onchange:null});}.bind(null)}});}"
            + "}catch(e){}})();";
    private volatile boolean adsAllowed; // el usuario ha quitado el bloqueo de anuncios en esta web

    /**
     * Las webs con diseño de ordenador salen en miniatura y el captcha no hay quien lo toque:
     * se amplía la página hasta dejarlo a un tamaño cómodo y se centra. Resolverlo sigue siendo cosa tuya.
     */
    private void zoomCaptcha(final String url) {
        if (url == null || !url.equals(currentPage) || url.equals(captchaZoomed)) return;
        try {
            web.evaluateJavascript(CAPTCHA_JS, v -> {
                float f;
                try {
                    f = Float.parseFloat(v);
                } catch (Exception e) {
                    return;
                }
                if (!url.equals(currentPage) || url.equals(captchaZoomed)) return;
                if (f <= 0) return;
                captchaZoomed = url;
                if (f < 1.3f) return; // ya se ve a buen tamaño
                web.zoomBy(Math.min(f, 5f));
                ui.postDelayed(() -> web.evaluateJavascript("(function(){try{window.__tlCaptcha.scrollIntoView("
                        + "{block:'center',inline:'center'});}catch(x){}})()", null), 350);
                toast("Captcha ampliado: resuélvelo y pulsa continuar");
            });
        } catch (Exception ignored) {
        }
    }

    private void go(String text) {
        String t = text == null ? "" : text.trim();
        if (t.isEmpty()) return;
        String url;
        if (t.startsWith("http://") || t.startsWith("https://")) {
            url = t;
        } else if (t.contains(".") && !t.contains(" ")) {
            url = "https://" + t;
        } else {
            url = "https://duckduckgo.com/?q=" + Uri.encode(t);
        }
        grabNow();
        // Navegación pedida por el usuario: el candado se quita para no bloquearla.
        setLock(null);
        currentPage = url; // desde ya deja de contar como portada (evita reabrir en cada redirección)
        autoLockPending = true;
        videos.clear();
        videoHeaders.clear();
        refreshVideos();
        hideKeyboard();
        web.loadUrl(url);
    }

    private boolean handleIntent(Intent intent) {
        if (intent == null) return false;
        if (INSTALL.equals(intent.getAction())) {
            onInstallResult(intent);
            return false;
        }
        String url = null;
        if (Intent.ACTION_VIEW.equals(intent.getAction()) && intent.getData() != null) {
            url = intent.getData().toString();
        } else if (Intent.ACTION_SEND.equals(intent.getAction())) {
            String text = intent.getStringExtra(Intent.EXTRA_TEXT);
            if (text != null) {
                Matcher m = Pattern.compile("https?://\\S+").matcher(text);
                if (m.find()) url = m.group();
            }
        }
        if (url == null) return false;
        go(url);
        return true;
    }

    private void hideKeyboard() {
        InputMethodManager imm = (InputMethodManager) getSystemService(INPUT_METHOD_SERVICE);
        if (imm != null) imm.hideSoftInputFromWindow(urlBar.getWindowToken(), 0);
        urlBar.clearFocus();
    }

    private static boolean isSearchEngine(String host) {
        String d = baseDomain(host);
        return d.startsWith("duckduckgo.") || d.startsWith("google.") || d.startsWith("bing.");
    }

    private void toggleLock() {
        autoLockPending = false;
        if (lockedDomain != null) {
            setLock(null);
            toast("Candado quitado");
            return;
        }
        String url = web.getUrl();
        String host = url == null ? null : Uri.parse(url).getHost();
        if (host == null) {
            toast("Abre primero una web");
            return;
        }
        setLock(baseDomain(host));
        toast("Solo se permite navegar dentro de " + lockedDomain);
    }

    private void setLock(String domain) {
        lockedDomain = domain;
        btnLock.setText(domain == null ? "🔓" : "🔒");
        btnLock.setBackground(pill(domain == null ? RAISED : ACCENT_DIM, 12));
    }

    /** Aproximación: las dos últimas partes del host (o tres si es tipo .co.uk / .com.es). */
    private static String baseDomain(String host) {
        if (host == null) return "";
        String[] p = host.toLowerCase(Locale.US).split("\\.");
        if (p.length <= 2) return host.toLowerCase(Locale.US);
        String second = p[p.length - 2];
        boolean compound = p[p.length - 1].length() == 2
                && (second.equals("co") || second.equals("com") || second.equals("org") || second.equals("net"));
        int n = compound ? 3 : 2;
        StringBuilder sb = new StringBuilder();
        for (int i = p.length - n; i < p.length; i++) {
            if (sb.length() > 0) sb.append('.');
            sb.append(p[i]);
        }
        return sb.toString();
    }

    // ---------- Vídeos detectados ----------

    private static boolean isVideo(Uri u) {
        String p = u.getPath();
        if (p == null) return false;
        p = p.toLowerCase(Locale.US);
        return p.endsWith(".m3u8") || p.endsWith(".mp4") || p.endsWith(".webm")
                || p.endsWith(".mkv") || p.endsWith(".mov");
    }

    /**
     * Vídeos cuya dirección no acaba en .mp4 (ok.ru y otras): se reconocen porque el reproductor
     * los pide "a trozos" (cabecera Range), cosa que no se hace con imágenes ni scripts.
     */
    private static boolean isMediaRequest(WebResourceRequest r) {
        try {
            if (r.isForMainFrame() || !"GET".equalsIgnoreCase(r.getMethod())) return false;
            Map<String, String> h = r.getRequestHeaders();
            if (h == null) return false;
            String range = null;
            for (Map.Entry<String, String> e : h.entrySet()) {
                if ("range".equalsIgnoreCase(e.getKey())) range = e.getValue();
            }
            if (range == null || !range.startsWith("bytes=")) return false;
            String p = r.getUrl().getPath();
            p = p == null ? "" : p.toLowerCase(Locale.US);
            int dot = p.lastIndexOf('.');
            String ext = dot >= 0 && dot > p.lastIndexOf('/') ? p.substring(dot + 1) : "";
            switch (ext) {
                case "js": case "css": case "png": case "jpg": case "jpeg": case "gif": case "webp":
                case "svg": case "ico": case "woff": case "woff2": case "ttf": case "json": case "html":
                case "htm": case "pdf": case "mp3": case "m4a": case "ogg": case "wav": case "vtt":
                case "srt": case "ts": case "m4s":
                    return false;
                default:
                    return true;
            }
        } catch (Exception e) {
            return false;
        }
    }

    /**
     * Busca vídeos en la propia página: el <video> que esté puesto y, en ok.ru, la lista de
     * calidades que la página trae guardada. Devuelve sus direcciones.
     */
    private static final String FIND_JS = "(function(){var out=[];function add(u){try{if(u){"
            + "u=new URL(u,location.href).href;if(/^https?:/.test(u)&&out.indexOf(u)<0)out.push(u);}}catch(e){}}"
            + "try{document.querySelectorAll('video,video source').forEach(function(v){"
            + "add(v.currentSrc);add(v.getAttribute('src'));});}catch(e){}"
            + "try{document.querySelectorAll('[data-options]').forEach(function(e){try{"
            + "var o=JSON.parse(e.getAttribute('data-options'));var m=o.flashvars&&o.flashvars.metadata;"
            + "if(typeof m==='string')m=JSON.parse(m);if(m){(m.videos||[]).forEach(function(v){add(v.url);});"
            + "add(m.hlsManifestUrl);}}catch(x){}});}catch(e){}"
            + "try{document.querySelectorAll('[data-video]').forEach(function(e){try{"
            + "add(JSON.parse(e.getAttribute('data-video')).videoSrc);}catch(x){}});}catch(e){}"
            + "return JSON.stringify(out.slice(0,12));})()";

    private void findVideos() {
        final String url = currentPage;
        if (!url.startsWith("http")) return;
        try {
            web.evaluateJavascript(FIND_JS, v -> {
                if (!url.equals(currentPage) || v == null) return;
                try {
                    JSONArray found = new JSONArray(new JSONArray("[" + v + "]").getString(0));
                    for (int i = 0; i < found.length(); i++) {
                        String u = found.optString(i);
                        if (u.startsWith("http")) addVideo(u);
                    }
                } catch (Exception ignored) {
                }
            });
        } catch (Exception ignored) {
        }
    }

    private void addVideo(final String url) {
        ui.post(() -> {
            if (!videos.contains(url)) {
                videos.add(url);
                refreshVideos();
                measure(url);
            }
        });
    }

    private static String size(long bytes) {
        if (bytes >= 1024L * 1024 * 1024) {
            return String.format(Locale.US, "%.1f GB", bytes / (1024.0 * 1024 * 1024)).replace('.', ',');
        }
        return Math.max(1, bytes / (1024 * 1024)) + " MB";
    }

    private String label(String url, boolean top) {
        Uri u = Uri.parse(url);
        String name = u.getLastPathSegment();
        if (name == null) name = url;
        if (name.length() > 34) name = "…" + name.substring(name.length() - 34);
        Bridge.Info i = infos.get(url);
        String what;
        if (i == null) what = "sin medir";
        else if (i.code >= 400) what = "no disponible";
        else if (i.hls) what = i.secs > 0 ? "dura " + clock(i.secs) : "duración desconocida";
        else what = i.bytes > 0 ? size(i.bytes) : "tamaño desconocido";
        String type = name.toLowerCase(Locale.US).endsWith(".m3u8") ? "HLS" : "Archivo";
        return (top ? "★ " : "") + type + " · " + what + "\n" + name + " · " + u.getHost();
    }

    private void showVideos() {
        if (videos.isEmpty()) {
            new AlertDialog.Builder(this)
                    .setTitle("Aún no hay vídeos")
                    .setMessage("Dale al play en la página y espera un par de segundos. "
                            + "Cuando el contador suba, vuelve aquí.")
                    .setPositiveButton("Vale", null)
                    .show();
            return;
        }
        btnVideos.setText("Midiendo…");
        withInfos(() -> {
            refreshVideos();
            showVideoList(false);
        });
    }

    /** Relleno: no disponible, o mucho más pequeño que el vídeo principal (anuncios, blank.mp4...). */
    private boolean isFiller(String url, long top) {
        Bridge.Info i = infos.get(url);
        if (i == null) return false;      // sin medir: no se puede juzgar, se muestra
        if (i.code >= 400) return true;
        long sc = score(url);
        return top > 0 && sc > 0 && sc * 10 < top;
    }

    private void showVideoList(final boolean all) {
        final List<String> rankedAll = ranked();
        if (rankedAll.isEmpty()) return;
        final long top = score(rankedAll.get(0));
        final List<String> snapshot = new ArrayList<>();
        for (String v : rankedAll) {
            if (all || !isFiller(v, top)) snapshot.add(v);
        }
        if (snapshot.isEmpty()) snapshot.addAll(rankedAll);
        final int hidden = rankedAll.size() - snapshot.size();

        String[] items = new String[snapshot.size()];
        for (int i = 0; i < items.length; i++) items[i] = label(snapshot.get(i), top > 0 && i == 0);
        AlertDialog.Builder b = new AlertDialog.Builder(this)
                .setTitle("Mandar a la tele")
                .setItems(items, (d, which) -> chooseMode(snapshot.get(which)))
                .setNeutralButton("Vaciar lista", (d, w) -> {
                    videos.clear();
                    infos.clear();
                    refreshVideos();
                })
                .setNegativeButton("Cancelar", null);
        if (hidden > 0) {
            b.setPositiveButton("Ver " + hidden + " de relleno", (d, w) -> showVideoList(true));
        }
        b.show();
    }

    // ---------- Tele ----------

    private void loadSavedTv() {
        SharedPreferences p = getSharedPreferences("tv", MODE_PRIVATE);
        String av = p.getString("av", null);
        if (av == null) return;
        tv = new Dlna.Device();
        tv.name = p.getString("name", "Tele");
        tv.avControl = av;
        tv.rcControl = p.getString("rc", null);
    }

    private void saveTv() {
        getSharedPreferences("tv", MODE_PRIVATE).edit()
                .putString("name", tv.name)
                .putString("av", tv.avControl)
                .putString("rc", tv.rcControl)
                .apply();
    }

    private void pickTv(final Runnable then) {
        if (!Dlna.hasWifi(this)) {
            new AlertDialog.Builder(this)
                    .setTitle("El móvil no está en la wifi")
                    .setMessage("Ahora mismo vas por datos móviles. Conecta el móvil a la misma wifi "
                            + "que la tele y vuelve a intentarlo.")
                    .setPositiveButton("Reintentar", (d, w) -> pickTv(then))
                    .setNegativeButton("Cancelar", null)
                    .show();
            return;
        }
        final AlertDialog wait = new AlertDialog.Builder(this)
                .setMessage("Buscando teles en la wifi…")
                .setCancelable(false)
                .show();
        io.execute(() -> {
            final List<Dlna.Device> found = Dlna.discover(MainActivity.this, 4000);
            ui.post(() -> {
                wait.dismiss();
                if (found.isEmpty()) {
                    new AlertDialog.Builder(MainActivity.this)
                            .setTitle("No encuentro ninguna tele")
                            .setMessage("Comprueba que la tele está encendida y en la misma wifi que el móvil. "
                                    + "Si lo está, escribe su IP (en la tele, Ajustes > General > Red > "
                                    + "Estado de red).")
                            .setPositiveButton("Reintentar", (d, w) -> pickTv(then))
                            .setNeutralButton("Escribir la IP", (d, w) -> askTvIp(then))
                            .setNegativeButton("Cancelar", null)
                            .show();
                    return;
                }
                chooseTv(found, then);
            });
        });
    }

    private void askTvIp(final Runnable then) {
        final EditText field = new EditText(this);
        field.setInputType(InputType.TYPE_CLASS_PHONE);
        field.setHint("192.168.1.40");
        field.setSingleLine(true);
        new AlertDialog.Builder(this)
                .setTitle("IP de la tele")
                .setView(field)
                .setPositiveButton("Buscar", (d, w) -> {
                    final String ip = field.getText().toString().trim();
                    final AlertDialog wait = new AlertDialog.Builder(MainActivity.this)
                            .setMessage("Buscando la tele en " + ip + "…")
                            .setCancelable(false)
                            .show();
                    io.execute(() -> {
                        final List<Dlna.Device> found = Dlna.atIp(MainActivity.this, ip);
                        ui.post(() -> {
                            wait.dismiss();
                            if (found.isEmpty()) {
                                new AlertDialog.Builder(MainActivity.this)
                                        .setTitle("No hay ninguna tele en " + ip)
                                        .setMessage("Revisa la IP y que la tele esté encendida.")
                                        .setPositiveButton("Otra IP", (d2, w2) -> askTvIp(then))
                                        .setNegativeButton("Cancelar", null)
                                        .show();
                                return;
                            }
                            chooseTv(found, then);
                        });
                    });
                })
                .setNegativeButton("Cancelar", null)
                .show();
    }

    private void chooseTv(final List<Dlna.Device> found, final Runnable then) {
        String[] names = new String[found.size()];
        for (int i = 0; i < names.length; i++) names[i] = found.get(i).name;
        new AlertDialog.Builder(this)
                .setTitle("Elige la tele")
                .setItems(names, (d, which) -> {
                    tv = found.get(which);
                    saveTv();
                    if (!sending) sendLabel();
                    if (then != null) then.run();
                })
                .setNegativeButton("Cancelar", null)
                .show();
    }

    private void chooseMode(final String url) {
        String[] modes = {
                "Automático (recomendado)",
                "Modo compatible\nSi la tele da error o se queda en negro",
                "Directo\nSin pasar por el móvil",
                "Precargar en el móvil\nPara webs lentas o teles que tardan en abrir. Solo archivos directos (mp4)",
                "Compatible con menos calidad\nPara wifi floja. Solo si el vídeo trae varias calidades"
        };
        new AlertDialog.Builder(this)
                .setTitle("Cómo enviarlo")
                .setItems(modes, (d, which) -> send(url, which))
                .setNegativeButton("Cancelar", null)
                .show();
    }

    /** Cabeceras con las que el navegador pidió el vídeo; el puente las repite ante la web. */
    private Map<String, String> headersFor(String url) {
        Map<String, String> h = new HashMap<>();
        Map<String, String> seen = videoHeaders.get(url);
        if (seen != null) h.putAll(seen);
        boolean referer = false, agent = false;
        for (String k : h.keySet()) {
            if (k.equalsIgnoreCase("Referer")) referer = true;
            if (k.equalsIgnoreCase("User-Agent")) agent = true;
        }
        if (!referer && currentPage.startsWith("http")) h.put("Referer", currentPage);
        if (!agent && !userAgent.isEmpty()) h.put("User-Agent", userAgent);
        return h;
    }

    private void startBridgeService() {
        if (Build.VERSION.SDK_INT >= 33
                && checkSelfPermission("android.permission.POST_NOTIFICATIONS") != PackageManager.PERMISSION_GRANTED) {
            requestPermissions(new String[]{"android.permission.POST_NOTIFICATIONS"}, 1);
        }
        Intent i = new Intent(this, BridgeService.class);
        try {
            if (Build.VERSION.SDK_INT >= 26) startForegroundService(i);
            else startService(i);
        } catch (Exception ignored) {
        }
    }

    private void stopBridgeService() {
        try {
            startService(new Intent(this, BridgeService.class).setAction(BridgeService.STOP));
        } catch (Exception ignored) {
            Bridge.stop();
        }
    }

    private String siteKey() {
        try {
            String host = Uri.parse(currentPage).getHost();
            return host == null ? "" : "mode_" + baseDomain(host);
        } catch (Exception e) {
            return "";
        }
    }

    /**
     * Vigila la tele unos segundos tras enviar. true = está reproduciendo; false = se ha quedado
     * parada o en negro. Si la tele no informa de su estado, se da por bueno.
     */
    private boolean watch(Dlna.Device target, int my) {
        int playing = 0, dead = 0, unknown = 0;
        for (int i = 0; i < 10; i++) {
            try {
                Thread.sleep(2000);
            } catch (InterruptedException e) {
                return true;
            }
            if (my != sendSeq) return true;
            String st;
            int pos = 0;
            try {
                st = Dlna.state(this, target);
                try {
                    pos = Dlna.position(this, target);
                } catch (IOException ignored) {
                }
            } catch (IOException e) {
                unknown++;
                continue;
            }
            if (st.equals("PLAYING") || st.equals("PAUSED_PLAYBACK")) {
                playing++;
                dead = 0;
                if (pos > 0 || playing >= 3) return true;
            } else if (st.equals("STOPPED") || st.equals("NO_MEDIA_PRESENT")) {
                playing = 0;
                if (i >= 1 && ++dead >= 2) return false;
            } else {
                playing = 0;
            }
        }
        return unknown >= 8;
    }

    private static String clock(int secs) {
        int h = secs / 3600, m = (secs / 60) % 60, sec = secs % 60;
        return h > 0 ? String.format(Locale.US, "%d:%02d:%02d", h, m, sec)
                : String.format(Locale.US, "%d:%02d", m, sec);
    }

    /** Envía; si de esta página hay un punto guardado, pregunta si seguir desde ahí. */
    private void send(final String url, final int mode) {
        if (tv == null) {
            pickTv(() -> send(url, mode));
            return;
        }
        final int saved = getSharedPreferences("resume", MODE_PRIVATE).getInt(currentPage, 0);
        if (saved < 60) {
            send(url, mode, 0);
            return;
        }
        new AlertDialog.Builder(this)
                .setTitle("Ya habías empezado este vídeo")
                .setPositiveButton("Seguir desde " + clock(saved), (d, w) -> send(url, mode, saved))
                .setNegativeButton("Desde el principio", (d, w) -> send(url, mode, 0))
                .show();
    }

    private void send(final String url, final int mode, final int startAt) {
        if (tv == null) {
            pickTv(() -> send(url, mode, startAt));
            return;
        }
        final Dlna.Device target = tv;
        final String title = pageTitle;
        final String pageKey = currentPage;
        final Map<String, String> headers = headersFor(url);
        final String site = siteKey();
        final SharedPreferences modes = getSharedPreferences("modes", MODE_PRIVATE);
        final int my = ++sendSeq;
        if (mode != DIRECT) startBridgeService();
        sending = true;
        status("Enviando a " + target.name + "…");

        new Thread(() -> {
            try {
                final Session ses = new Session();
                ses.target = target;
                ses.title = title;
                ses.pageKey = pageKey;
                ses.src = url;
                ses.headers = headers;
                if (mode == DIRECT) {
                    Dlna.play(MainActivity.this, target, url, title, null);
                    ses.how = "directo";
                } else {
                    String ip = Dlna.wifiIp(MainActivity.this);
                    if (ip == null) throw new IOException("El móvil no está en la wifi.");
                    int port = Bridge.start();
                    Bridge.cancelPreloads(); // una precarga anterior ya no hace falta
                    String id = mode == LOW ? Bridge.registerLow(url, headers) : Bridge.register(url, headers);
                    Bridge.Probe p;
                    try {
                        p = Bridge.probe(id);
                    } catch (java.net.SocketTimeoutException slow) {
                        throw new IOException("La web del vídeo no responde (tiempo de espera agotado). "
                                + "Recarga la página, dale al play otra vez y vuelve a enviarlo.");
                    }
                    if (p.code >= 400) {
                        throw new IOException("La web no entrega este vídeo (HTTP " + p.code + "). "
                                + "Recarga la página, dale al play otra vez y vuelve a enviarlo.");
                    }
                    String base = "http://" + ip + ":" + port;
                    ses.id = id;
                    ses.base = base;
                    if (mode == PRELOAD) {
                        if (p.hls) {
                            throw new IOException("Este vídeo es un streaming por trozos y no se puede precargar. "
                                    + "Usa Automático o Modo compatible.");
                        }
                        Bridge.Cache cache = Bridge.preload(id, new File(getCacheDir(), "preload"));
                        // Colchón antes de avisar a la tele: el 5 % del vídeo, entre 24 y 80 MB.
                        long mega = 1024L * 1024;
                        long need = Math.min(cache.total, Math.min(80 * mega, Math.max(24 * mega, cache.total / 20)));
                        while (cache.have < need) {
                            if (my != sendSeq) {
                                Bridge.cancelPreloads();
                                return;
                            }
                            if (cache.failed) throw new IOException("La precarga se ha cortado: " + cache.error);
                            status("Precargando… " + (cache.have / mega) + " de " + (need / mega) + " MB");
                            Thread.sleep(700);
                        }
                        status("Enviando a " + target.name + "…");
                        Dlna.play(MainActivity.this, target, base + "/c/" + id + "/video.mp4", title, cache.type);
                        ses.how = "precarga";
                    } else if (!p.hls) {
                        if (mode == LOW) {
                            throw new IOException("Este vídeo es un archivo con una sola calidad y no se puede "
                                    + "bajar. Prueba «Precargar en el móvil».");
                        }
                        String mime = p.type != null && p.type.startsWith("video/") ? p.type : "video/mp4";
                        Dlna.play(MainActivity.this, target, base + "/p/" + id + "/video.mp4", title, mime);
                        ses.how = "puente";
                    } else {
                        // Si con esta web ya hizo falta el modo compatible, se va directo a él.
                        if (mode == LOW && Bridge.variants(id) <= 1) {
                            ui.post(() -> toast("Este vídeo solo trae una calidad: se envía tal cual"));
                        }
                        boolean compatFirst = mode == COMPAT || mode == LOW
                                || (mode == AUTO && modes.getInt(site, AUTO) == COMPAT);
                        boolean ok = false;
                        if (!compatFirst) {
                            try {
                                Dlna.play(MainActivity.this, target, base + "/p/" + id + "/index.m3u8", title,
                                        "application/vnd.apple.mpegurl");
                                status("Comprobando que la tele reproduce…");
                                ok = watch(target, my);
                            } catch (IOException rejected) {
                                ok = false;
                            }
                            if (my != sendSeq) return;
                        }
                        if (ok) {
                            ses.how = "puente";
                            if (!site.isEmpty()) modes.edit().putInt(site, AUTO).apply();
                        } else {
                            if (!compatFirst) status("No arranca. Probando modo compatible…");
                            Dlna.play(MainActivity.this, target,
                                    base + "/ts/" + id + "/" + startAt + "/stream.ts", title, "video/mpeg");
                            if (compatFirst) status("Comprobando que la tele reproduce…");
                            ok = watch(target, my);
                            if (my != sendSeq) return;
                            if (!ok) {
                                String err = Bridge.lastError;
                                throw new IOException("La tele no ha llegado a reproducir el vídeo."
                                        + (err == null || err.isEmpty() ? "" : "\n\n" + err));
                            }
                            ses.how = "compatible";
                            ses.offset = startAt;
                            if (!site.isEmpty()) modes.edit().putInt(site, COMPAT).apply();
                        }
                    }
                }
                // En los modos en que la tele sabe saltar, se coloca en el punto guardado.
                if (startAt > 0 && !"compatible".equals(ses.how)) {
                    try {
                        Thread.sleep(1500);
                        Dlna.seekTo(MainActivity.this, target, startAt);
                    } catch (Exception ignored) {
                    }
                }
                if (my != sendSeq) return;
                session = ses;
                track(ses, my);
                ui.post(() -> {
                    if (my != sendSeq) return;
                    sending = false;
                    sendLabel();
                    toast("Reproduciendo en " + target.name + " (" + ses.how + ")");
                });
            } catch (final Exception e) {
                ui.post(() -> {
                    if (my != sendSeq) return;
                    sending = false;
                    sendLabel();
                    new AlertDialog.Builder(MainActivity.this)
                            .setTitle("No se ha podido enviar")
                            .setMessage(String.valueOf(e.getMessage()))
                            .setPositiveButton("Probar otro modo", (d, w) -> chooseMode(url))
                            .setNeutralButton("Buscar tele", (d, w) -> pickTv(() -> send(url, mode, startAt)))
                            .setNegativeButton("Cerrar", null)
                            .show();
                });
            }
        }, "telelink-send").start();
    }

    /** Mientras se reproduce, guarda cada 15 s por dónde va para poder retomarlo otro día. */
    private void track(final Session ses, final int my) {
        new Thread(() -> {
            final SharedPreferences resume = getSharedPreferences("resume", MODE_PRIVATE);
            int stopped = 0, saves = 0;
            while (my == sendSeq && stopped < 4) {
                try {
                    Thread.sleep(15000);
                } catch (InterruptedException e) {
                    return;
                }
                if (my != sendSeq) return;
                try {
                    String st = Dlna.state(MainActivity.this, ses.target);
                    if (st.equals("PLAYING") || st.equals("PAUSED_PLAYBACK")) {
                        stopped = 0;
                        int pos = Dlna.position(MainActivity.this, ses.target) + ses.offset;
                        if (pos >= 60 && ses.pageKey != null && ses.pageKey.startsWith("http")) {
                            resume.edit().putInt(ses.pageKey, pos).apply();
                            if (saves++ % 4 == 0) frameThumb(ses, pos); // un fotograma por minuto
                        }
                    } else if (st.equals("STOPPED") || st.equals("NO_MEDIA_PRESENT")) {
                        stopped++;
                    }
                } catch (IOException ignored) {
                }
            }
        }, "telelink-track").start();
    }

    /** Salto relativo. En modo compatible la tele no sabe saltar: se reinicia el flujo en el punto nuevo. */
    private String jump(Dlna.Device d, int delta) throws Exception {
        Session ses = session;
        if (ses != null && "compatible".equals(ses.how) && ses.target == d) {
            int now = ses.offset + Dlna.position(this, d);
            int to = Math.max(0, now + delta);
            Dlna.play(this, d, ses.base + "/ts/" + ses.id + "/" + to + "/stream.ts", ses.title, "video/mpeg");
            ses.offset = to;
            return "Saltando a " + clock(to);
        }
        Dlna.seekBy(this, d, delta);
        return null;
    }

    // ---------- Guardar clips cortos ----------

    private static boolean isClip(Uri u) {
        String p = u.getPath();
        if (p == null) return false;
        p = p.toLowerCase(Locale.US);
        return p.endsWith(".mp4") || p.endsWith(".webm") || p.endsWith(".gif");
    }

    private void offerSave(final String url) {
        new AlertDialog.Builder(this)
                .setTitle("Enlace a un clip")
                .setItems(new String[]{"Guardar en el móvil", "Abrir aquí"}, (d, which) -> {
                    if (which == 0) saveClip(url);
                    else web.loadUrl(url);
                })
                .setNegativeButton("Cancelar", null)
                .show();
    }

    /** Guarda en Descargas/TeleLink un archivo de vídeo directo, si no pasa del tamaño máximo. */
    private void saveClip(final String url) {
        if (Build.VERSION.SDK_INT < 29
                && checkSelfPermission("android.permission.WRITE_EXTERNAL_STORAGE") != PackageManager.PERMISSION_GRANTED) {
            requestPermissions(new String[]{"android.permission.WRITE_EXTERNAL_STORAGE"}, 3);
            toast("Acepta el permiso y vuelve a pulsar Guardar");
            return;
        }
        final String page = currentPage;
        final String title = pageTitle;
        toast("Comprobando el clip…");
        new Thread(() -> {
            try {
                String cookie = null;
                try {
                    cookie = CookieManager.getInstance().getCookie(url);
                } catch (Exception ignored) {
                }
                HttpURLConnection c = get(url);
                c.setRequestProperty("Range", "bytes=0-0");
                if (!userAgent.isEmpty()) c.setRequestProperty("User-Agent", userAgent);
                if (page.startsWith("http")) c.setRequestProperty("Referer", page);
                if (cookie != null && !cookie.isEmpty()) c.setRequestProperty("Cookie", cookie);
                int code = c.getResponseCode();
                String type = c.getContentType();
                long size = -1;
                String range = c.getHeaderField("Content-Range");
                if (range != null && range.contains("/")) {
                    try {
                        size = Long.parseLong(range.substring(range.lastIndexOf('/') + 1).trim());
                    } catch (NumberFormatException ignored) {
                    }
                } else if (code == 200) {
                    size = c.getContentLengthLong();
                }
                c.disconnect();

                if (code >= 400) throw new IOException("La web no entrega el archivo (HTTP " + code + ").");
                if (type != null && type.toLowerCase(Locale.US).contains("mpegurl")) {
                    throw new IOException("Esto es un streaming, no un archivo. Solo se guardan clips en archivo directo.");
                }
                if (size <= 0) throw new IOException("No se puede comprobar el tamaño del archivo.");
                if (size > MAX_SAVE) {
                    throw new IOException("Ocupa " + (size / (1024 * 1024)) + " MB. El máximo para guardar es de "
                            + (MAX_SAVE / (1024 * 1024)) + " MB.");
                }

                String last = Uri.parse(url).getLastPathSegment();
                if (last == null || last.isEmpty()) last = "clip.mp4";
                String prefix = title == null ? "" : title.replaceAll("[^\\p{L}\\p{N} _-]", "").trim();
                if (prefix.length() > 40) prefix = prefix.substring(0, 40).trim();
                final String name = (prefix.isEmpty() ? "" : prefix + " - ") + last.replaceAll("[\\\\/:*?\"<>|]", "_");

                DownloadManager.Request r = new DownloadManager.Request(Uri.parse(url));
                if (!userAgent.isEmpty()) r.addRequestHeader("User-Agent", userAgent);
                if (page.startsWith("http")) r.addRequestHeader("Referer", page);
                if (cookie != null && !cookie.isEmpty()) r.addRequestHeader("Cookie", cookie);
                r.setTitle(name);
                r.setNotificationVisibility(DownloadManager.Request.VISIBILITY_VISIBLE_NOTIFY_COMPLETED);
                r.setDestinationInExternalPublicDir(Environment.DIRECTORY_DOWNLOADS, "TeleLink/" + name);
                ((DownloadManager) getSystemService(DOWNLOAD_SERVICE)).enqueue(r);
                final long mb = Math.max(1, size / (1024 * 1024));
                ui.post(() -> toast("Guardando en Descargas/TeleLink (" + mb + " MB)"));
            } catch (final Exception e) {
                ui.post(() -> new AlertDialog.Builder(MainActivity.this)
                        .setTitle("No se ha guardado")
                        .setMessage(String.valueOf(e.getMessage()))
                        .setPositiveButton("Vale", null)
                        .show());
            }
        }, "telelink-save").start();
    }

    /** Botón del menú: guarda el clip directo que esté sonando en la página. */
    private void saveCurrentClip() {
        String pick = null;
        for (String v : videos) {
            if (isClip(Uri.parse(v))) pick = v;
        }
        if (pick == null) {
            toast("No hay ningún clip en archivo directo en esta página");
            return;
        }
        saveClip(pick);
    }

    // ---------- Miniaturas: captura de por dónde ibas ----------

    /** Devuelve, en fracciones de la pantalla de la web, el hueco del vídeo o reproductor más grande. */
    private static final String BOX_JS = "(function(){try{var W=window.innerWidth,H=window.innerHeight,b='',m=0,"
            + "e=document.querySelectorAll('video,iframe');for(var i=0;i<e.length;i++){"
            + "var r=e[i].getBoundingClientRect(),x=Math.max(0,r.left),y=Math.max(0,r.top),"
            + "w=Math.min(W,r.right)-x,h=Math.min(H,r.bottom)-y;if(w<W*0.4||h<H*0.1)continue;"
            + "if(w*h>m){m=w*h;b=[x/W,y/H,w/W,h/H].join(',');}}return b;}catch(x){return '';}})()";

    private final Runnable snapTick = new Runnable() {
        @Override
        public void run() {
            snap();
            if (resumed) findVideos();
            ui.postDelayed(this, 10000);
        }
    };

    private static String thumbKey(String url) {
        try {
            byte[] d = MessageDigest.getInstance("MD5").digest(url.getBytes("UTF-8"));
            StringBuilder sb = new StringBuilder();
            for (byte x : d) sb.append(String.format(Locale.US, "%02x", x));
            return sb.toString();
        } catch (Exception e) {
            return "x";
        }
    }

    /** frame = fotograma sacado del propio vídeo; si no, captura de la página. */
    private File thumbFile(String url, boolean frame) {
        return new File(new File(getFilesDir(), "thumbs"), thumbKey(url) + (frame ? ".f.jpg" : ".jpg"));
    }

    /** La miniatura lista para incrustar en la portada, o null si esa página no tiene. */
    private String thumbData(String url, boolean started) {
        File f = thumbFile(url, true);
        if (!started || !f.isFile()) f = thumbFile(url, false);
        if (!f.isFile() || f.length() > 300000) return null;
        try (FileInputStream in = new FileInputStream(f)) {
            ByteArrayOutputStream out = new ByteArrayOutputStream();
            byte[] buf = new byte[8192];
            int n;
            while ((n = in.read(buf)) > 0) out.write(buf, 0, n);
            return "data:image/jpeg;base64," + Base64.encodeToString(out.toByteArray(), Base64.NO_WRAP);
        } catch (Exception e) {
            return null;
        }
    }

    private void storeThumb(final File f, final Bitmap bmp) {
        probes.execute(() -> {
            try {
                File dir = f.getParentFile();
                if (dir != null) dir.mkdirs();
                File tmp = new File(f.getPath() + ".tmp");
                try (FileOutputStream o = new FileOutputStream(tmp)) {
                    bmp.compress(Bitmap.CompressFormat.JPEG, 72, o);
                }
                if (!tmp.renameTo(f)) tmp.delete();
            } catch (Exception ignored) {
            } finally {
                bmp.recycle();
            }
        });
    }

    /** Borra las miniaturas de páginas que ya no están ni en recientes ni en favoritos. */
    private void pruneThumbs() {
        final JSONArray hist = loadList("history"), favs = loadList("favorites");
        probes.execute(() -> {
            try {
                File[] files = new File(getFilesDir(), "thumbs").listFiles();
                if (files == null || files.length == 0) return;
                Set<String> keep = new HashSet<>();
                for (JSONArray a : new JSONArray[]{hist, favs}) {
                    for (int i = 0; i < a.length(); i++) {
                        JSONObject o = a.optJSONObject(i);
                        if (o != null) keep.add(thumbKey(o.optString("u")));
                    }
                }
                for (File f : files) {
                    String n = f.getName();
                    int dot = n.indexOf('.');
                    if (!keep.contains(dot > 0 ? n.substring(0, dot) : n)) f.delete();
                }
            } catch (Exception ignored) {
            }
        });
    }

    /** Captura periódica: busca dónde está el vídeo en la página y guarda esa zona. */
    private void snap() {
        final String url = currentPage;
        if (!resumed || !url.startsWith("http") || progress.getVisibility() == View.VISIBLE) return;
        try {
            web.evaluateJavascript(BOX_JS, v -> {
                if (!url.equals(currentPage)) return;
                float[] box = null;
                try {
                    String[] p = v == null ? new String[0] : v.replace("\"", "").split(",");
                    if (p.length == 4) {
                        box = new float[4];
                        for (int i = 0; i < 4; i++) box[i] = Float.parseFloat(p[i]);
                    }
                } catch (Exception e) {
                    box = null;
                }
                lastBox = box;
                lastBoxUrl = url;
                grab(url, box);
            });
        } catch (Exception ignored) {
        }
    }

    /** Captura inmediata, justo antes de salir de la página. */
    private void grabNow() {
        final String url = currentPage;
        if (!resumed || !url.startsWith("http") || progress.getVisibility() == View.VISIBLE) return;
        grab(url, url.equals(lastBoxUrl) ? lastBox : null);
    }

    private void grab(final String url, float[] box) {
        try {
            int w = web.getWidth(), h = web.getHeight();
            if (w <= 0 || h <= 0) return;
            float x = 0, y = 0, bw = w, bh = h;
            if (box != null) {
                x = box[0] * w;
                y = box[1] * h;
                bw = box[2] * w;
                bh = box[3] * h;
            }
            // Recorte a 16:9: centrado si es el reproductor, desde arriba si es la página entera.
            float tall = bw * 9f / 16f;
            if (bh > tall) {
                if (box != null) y += (bh - tall) / 2f;
                bh = tall;
            } else {
                float wide = bh * 16f / 9f;
                x += (bw - wide) / 2f;
                bw = wide;
            }
            if (bw < 32 || bh < 18) return;
            final Bitmap bmp = Bitmap.createBitmap(320, 180, Bitmap.Config.ARGB_8888);
            final File out = thumbFile(url, false);
            if (Build.VERSION.SDK_INT >= 26) {
                int[] at = new int[2];
                web.getLocationInWindow(at);
                Rect r = new Rect(at[0] + (int) x, at[1] + (int) y, at[0] + (int) (x + bw), at[1] + (int) (y + bh));
                PixelCopy.request(getWindow(), r, bmp, res -> {
                    if (res == PixelCopy.SUCCESS) storeThumb(out, bmp);
                    else bmp.recycle();
                }, ui);
            } else {
                Canvas c = new Canvas(bmp);
                float sc = 320f / bw;
                c.scale(sc, sc);
                c.translate(-x - web.getScrollX(), -y - web.getScrollY());
                web.draw(c);
                storeThumb(out, bmp);
            }
        } catch (Throwable ignored) {
        }
    }

    /** Saca del propio vídeo el fotograma del segundo por el que va la tele. */
    private void frameThumb(final Session ses, final int pos) {
        if (ses.src == null || ses.pageKey == null || ses.framing) return;
        ses.framing = true;
        final File out = thumbFile(ses.pageKey, true);
        new Thread(() -> {
            MediaMetadataRetriever r = new MediaMetadataRetriever();
            try {
                Map<String, String> h = new HashMap<>();
                if (ses.headers != null) {
                    for (Map.Entry<String, String> e : ses.headers.entrySet()) {
                        String k = e.getKey();
                        if (k.equalsIgnoreCase("Referer") || k.equalsIgnoreCase("User-Agent")
                                || k.equalsIgnoreCase("Cookie") || k.equalsIgnoreCase("Origin")) {
                            h.put(k, e.getValue());
                        }
                    }
                }
                r.setDataSource(ses.src, h);
                Bitmap full = r.getFrameAtTime(pos * 1000000L, MediaMetadataRetriever.OPTION_CLOSEST_SYNC);
                if (full == null || full.getWidth() < 16 || full.getHeight() < 9) return;
                Bitmap bmp = Bitmap.createBitmap(320, 180, Bitmap.Config.ARGB_8888);
                float sc = Math.max(320f / full.getWidth(), 180f / full.getHeight());
                Canvas c = new Canvas(bmp);
                c.translate((320 - full.getWidth() * sc) / 2f, (180 - full.getHeight() * sc) / 2f);
                c.scale(sc, sc);
                c.drawBitmap(full, 0, 0, new android.graphics.Paint(android.graphics.Paint.FILTER_BITMAP_FLAG));
                full.recycle();
                storeThumb(out, bmp);
            } catch (Throwable ignored) {
            } finally {
                try {
                    r.release();
                } catch (Throwable ignored) {
                }
                ses.framing = false;
            }
        }, "telelink-frame").start();
    }

    // ---------- Menú, favoritos e historial ----------

    private JSONArray loadList(String key) {
        try {
            return new JSONArray(getSharedPreferences("lists", MODE_PRIVATE).getString(key, "[]"));
        } catch (Exception e) {
            return new JSONArray();
        }
    }

    private void storeList(String key, JSONArray a) {
        getSharedPreferences("lists", MODE_PRIVATE).edit().putString(key, a.toString()).apply();
        pruneThumbs();
    }

    private int indexOf(JSONArray a, String url) {
        for (int i = 0; i < a.length(); i++) {
            JSONObject o = a.optJSONObject(i);
            if (o != null && url.equals(o.optString("u"))) return i;
        }
        return -1;
    }

    /** Pone la página la primera de la lista (sin repetirla) y recorta a un máximo. */
    private void putFirst(String key, String title, String url, int max) {
        try {
            JSONArray old = loadList(key), out = new JSONArray();
            JSONObject e = new JSONObject();
            e.put("t", title == null || title.isEmpty() ? url : title);
            e.put("u", url);
            out.put(e);
            for (int i = 0; i < old.length() && out.length() < max; i++) {
                JSONObject o = old.optJSONObject(i);
                if (o != null && !url.equals(o.optString("u"))) out.put(o);
            }
            storeList(key, out);
        } catch (Exception ignored) {
        }
    }

    private void addHistory(String title, String url) {
        putFirst("history", title, url, 60);
    }

    private void showMenu() {
        final String url = web.getUrl();
        final boolean page = url != null && url.startsWith("http");
        final boolean fav = page && indexOf(loadList("favorites"), url) >= 0;
        String[] items = {
                "Inicio",
                "Recargar",
                fav ? "★ Quitar de favoritos" : "☆ Añadir a favoritos",
                "Favoritos",
                "Historial",
                "Guardar clip de esta página",
                adsAllowed ? "Volver a bloquear anuncios en esta web" : "Quitar bloqueo de anuncios en esta web",
                "Duplicar pantalla en la tele (opcional)",
                "Buscar vídeos en ok.ru"
        };
        new AlertDialog.Builder(this)
                .setItems(items, (d, which) -> {
                    if (which == 0) {
                        setLock(null);
                        videos.clear();
                        videoHeaders.clear();
                        refreshVideos();
                        showHome();
                    } else if (which == 1) {
                        web.reload();
                    } else if (which == 2) {
                        if (!page) {
                            toast("Abre primero una web");
                        } else if (fav) {
                            JSONArray a = loadList("favorites");
                            int i = indexOf(a, url);
                            if (i >= 0) a.remove(i);
                            storeList("favorites", a);
                            toast("Quitado de favoritos");
                        } else {
                            putFirst("favorites", web.getTitle(), url, 200);
                            toast("Guardado en favoritos");
                        }
                    } else if (which == 3) {
                        showList("favorites", "Favoritos", false);
                    } else if (which == 4) {
                        showList("history", "Historial", false);
                    } else if (which == 5) {
                        saveCurrentClip();
                    } else if (which == 7) {
                        mirror();
                    } else if (which == 8) {
                        askOkru();
                    } else if (!page) {
                        toast("Abre primero una web");
                    } else {
                        String domain = baseDomain(Uri.parse(url).getHost());
                        boolean off = !adsAllowed;
                        getSharedPreferences("noblock", MODE_PRIVATE).edit().putBoolean(domain, off).apply();
                        adsAllowed = off;
                        toast(off ? "Anuncios permitidos en " + domain : "Anuncios bloqueados en " + domain);
                        web.reload();
                    }
                })
                .show();
    }

    /**
     * Alternativa cuando el envío normal no va: abre el ajuste de Android para duplicar la pantalla
     * del móvil en la tele (Miracast / Smart View). No pasa por la wifi del router.
     */
    private void mirror() {
        String[] actions = {"android.settings.CAST_SETTINGS", "android.settings.WIRELESS_SETTINGS",
                "android.settings.SETTINGS"};
        for (String a : actions) {
            try {
                startActivity(new Intent(a));
                toast("Elige tu tele en la lista. El móvil tiene que quedarse con la pantalla encendida.");
                return;
            } catch (Exception ignored) {
            }
        }
        toast("Este móvil no tiene ajuste para duplicar pantalla");
    }

    /** Lista de páginas guardadas. En modo borrar, tocar una la quita en vez de abrirla. */
    private void showList(final String key, final String title, final boolean deleting) {
        final JSONArray a = loadList(key);
        if (a.length() == 0) {
            toast(title + ": no hay nada todavía");
            return;
        }
        final SharedPreferences resume = getSharedPreferences("resume", MODE_PRIVATE);
        String[] items = new String[a.length()];
        for (int i = 0; i < items.length; i++) {
            JSONObject o = a.optJSONObject(i);
            String u = o == null ? "" : o.optString("u");
            String t = o == null ? "" : nice(o.optString("t"), u);
            int pos = resume.getInt(u, 0);
            String host = Uri.parse(u).getHost();
            items[i] = t + "\n" + (host == null ? u : host) + (pos >= 60 ? "  ·  vas por " + clock(pos) : "");
        }
        AlertDialog.Builder b = new AlertDialog.Builder(this)
                .setTitle(deleting ? title + ": toca para quitar" : title)
                .setItems(items, (d, which) -> {
                    JSONObject o = a.optJSONObject(which);
                    if (o == null) return;
                    if (deleting) {
                        a.remove(which);
                        storeList(key, a);
                        if (a.length() > 0) showList(key, title, true);
                    } else {
                        go(o.optString("u"));
                    }
                })
                .setNegativeButton("Cerrar", null);
        if (deleting) {
            b.setNeutralButton("Borrar todo", (d, w) -> storeList(key, new JSONArray()));
        } else {
            b.setNeutralButton("Quitar…", (d, w) -> showList(key, title, true));
        }
        b.show();
    }

    private interface TvAction {
        String run(Dlna.Device d) throws Exception;
    }

    private void control(final TvAction action) {
        if (tv == null) {
            pickTv(null);
            return;
        }
        final Dlna.Device target = tv;
        io.execute(() -> {
            try {
                final String msg = action.run(target);
                if (msg != null) ui.post(() -> toast(msg));
            } catch (final Exception e) {
                ui.post(() -> toast(String.valueOf(e.getMessage())));
            }
        });
    }

    private void showRemote() {
        LinearLayout box = new LinearLayout(this);
        box.setOrientation(LinearLayout.VERTICAL);
        box.setPadding(dp(16), dp(8), dp(16), dp(8));

        LinearLayout r1 = new LinearLayout(this);
        LinearLayout r2 = new LinearLayout(this);
        LinearLayout r3 = new LinearLayout(this);

        addRemote(r1, "−30 s", d -> jump(d, -30));
        addRemote(r1, "Pausa", d -> { Dlna.pause(this, d); return null; });
        addRemote(r1, "Play", d -> { Dlna.resume(this, d); return null; });
        addRemote(r1, "+30 s", d -> jump(d, 30));

        addRemote(r2, "Vol −", d -> "Volumen " + Dlna.volumeBy(this, d, -3));
        addRemote(r2, "Vol +", d -> "Volumen " + Dlna.volumeBy(this, d, 3));
        addRemote(r2, "−5 min", d -> jump(d, -300));
        addRemote(r2, "+5 min", d -> jump(d, 300));

        addRemote(r3, "Parar", d -> {
            sendSeq++;
            ui.post(() -> {
                sending = false;
                sendLabel();
                stopBridgeService();
            });
            Dlna.stop(this, d);
            return "Parado";
        });

        // Diagnóstico: si la tele no pide nada al móvil, el contador se queda en 0.
        TextView diag = new TextView(this);
        diag.setPadding(dp(4), dp(10), dp(4), 0);
        diag.setTextSize(12);
        diag.setTextColor(MUTED);
        String err = Bridge.lastError;
        diag.setText("Peticiones de la tele al móvil: " + Bridge.hits.get()
                + (err == null || err.isEmpty() ? "" : "\nÚltimo error: " + err));

        box.addView(r1);
        box.addView(r2);
        box.addView(r3);
        box.addView(diag);

        new AlertDialog.Builder(this)
                .setTitle(tv == null ? "Mando (sin tele)" : "Mando · " + tv.name)
                .setView(box)
                .setNeutralButton("Cambiar de tele", (d, w) -> pickTv(null))
                .setPositiveButton("Cerrar", null)
                .show();
    }

    private void addRemote(LinearLayout row, String text, final TvAction action) {
        Button b = bar(text);
        b.setOnClickListener(v -> control(action));
        row.addView(b, cell(0, dp(54), 1, 4));
    }

    // ---------- Ciclo de vida ----------

    @Override
    public void onBackPressed() {
        if (!back()) super.onBackPressed();
    }

    /**
     * Atrás. Si la página anterior es la portada, se vuelve a pintar entera en vez de sacar la copia
     * vieja del historial: así sus botones (buscar, borrar, tarjetas) vuelven a funcionar y los
     * recientes salen al día. false = ya no hay adónde volver.
     */
    private boolean back() {
        grabNow();
        if (!web.canGoBack()) return false;
        try {
            android.webkit.WebBackForwardList h = web.copyBackForwardList();
            android.webkit.WebHistoryItem prev = h.getItemAtIndex(h.getCurrentIndex() - 1);
            String u = prev == null ? null : prev.getUrl();
            if (u == null || !u.startsWith("http")) {
                setLock(null);
                videos.clear();
                videoHeaders.clear();
                refreshVideos();
                showHome();
                web.clearHistory();
                ui.postDelayed(() -> web.clearHistory(), 600); // la portada tarda un instante en cargar
                return true;
            }
        } catch (Exception ignored) {
        }
        web.goBack();
        return true;
    }

    @Override
    protected void onPause() {
        super.onPause();
        grabNow();
        resumed = false;
        ui.removeCallbacks(snapTick);
        web.onPause();
    }

    @Override
    protected void onResume() {
        super.onResume();
        web.onResume();
        resumed = true;
        ui.removeCallbacks(snapTick);
        ui.postDelayed(snapTick, 10000);
    }

    @Override
    protected void onDestroy() {
        io.shutdownNow();
        web.destroy();
        super.onDestroy();
    }
}
