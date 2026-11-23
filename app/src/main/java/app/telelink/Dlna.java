package app.telelink;

import android.content.Context;
import android.net.ConnectivityManager;
import android.net.LinkAddress;
import android.net.LinkProperties;
import android.net.Network;
import android.net.NetworkCapabilities;
import android.net.wifi.WifiManager;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.DatagramPacket;
import java.net.DatagramSocket;
import java.net.HttpURLConnection;
import java.net.Inet4Address;
import java.net.InetAddress;
import java.net.InetSocketAddress;
import java.net.Socket;
import java.net.SocketTimeoutException;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Set;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/** Cliente DLNA/UPnP mínimo: busca teles en la wifi y les manda un vídeo por URL. */
final class Dlna {

    static final String AVT = "urn:schemas-upnp-org:service:AVTransport:1";
    static final String RC = "urn:schemas-upnp-org:service:RenderingControl:1";

    static final class Device {
        String name;
        String avControl;
        String rcControl;
    }

    private Dlna() {}

    // ---------- Red ----------

    /** Devuelve la red wifi para no salir por datos móviles (la tele solo está en la wifi). */
    private static Network wifi(Context ctx) {
        try {
            ConnectivityManager cm =
                    (ConnectivityManager) ctx.getSystemService(Context.CONNECTIVITY_SERVICE);
            for (Network n : cm.getAllNetworks()) {
                NetworkCapabilities c = cm.getNetworkCapabilities(n);
                if (c != null && c.hasTransport(NetworkCapabilities.TRANSPORT_WIFI)) return n;
            }
        } catch (Exception ignored) {
        }
        return null;
    }

    static boolean hasWifi(Context ctx) {
        return wifi(ctx) != null;
    }

    /** IP del móvil en la wifi, que es la que la tele usará para llegar al puente. */
    static String wifiIp(Context ctx) {
        try {
            Network n = wifi(ctx);
            if (n == null) return null;
            ConnectivityManager cm =
                    (ConnectivityManager) ctx.getSystemService(Context.CONNECTIVITY_SERVICE);
            LinkProperties lp = cm.getLinkProperties(n);
            if (lp == null) return null;
            for (LinkAddress a : lp.getLinkAddresses()) {
                if (a.getAddress() instanceof Inet4Address) return a.getAddress().getHostAddress();
            }
        } catch (Exception ignored) {
        }
        return null;
    }

    private static HttpURLConnection open(Context ctx, String url) throws IOException {
        Network n = wifi(ctx);
        URL u = new URL(url);
        HttpURLConnection c = (HttpURLConnection) (n != null ? n.openConnection(u) : u.openConnection());
        c.setConnectTimeout(5000);
        c.setReadTimeout(8000);
        return c;
    }

    private static String readAll(InputStream in) throws IOException {
        if (in == null) return "";
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        byte[] buf = new byte[8192];
        int r;
        while ((r = in.read(buf)) > 0) out.write(buf, 0, r);
        in.close();
        return new String(out.toByteArray(), StandardCharsets.UTF_8);
    }

    // ---------- Descubrimiento (SSDP) ----------

    private static final String SSDP_GROUP = "239.255.255.250";

    /** Puerto fijo donde las teles Samsung con Tizen publican su receptor DLNA. */
    private static final int SAMSUNG_DMR_PORT = 9197;

    /**
     * Busca teles en la wifi. Primero con el aviso general (multicast); si el router no lo
     * deja pasar, pregunta directamente a cada dirección de la red.
     */
    static List<Device> discover(Context ctx, int timeoutMs) {
        List<InetAddress> group = new ArrayList<>();
        try {
            group.add(InetAddress.getByName(SSDP_GROUP));
        } catch (IOException ignored) {
        }
        List<Device> found = describeAll(ctx, search(ctx, group, timeoutMs));
        if (!found.isEmpty()) return found;

        List<InetAddress> hosts = neighbours(ctx);
        if (hosts.isEmpty()) return found;

        // Las dos búsquedas directas van a la vez para acortar la espera.
        final Set<String> unicast = Collections.synchronizedSet(new LinkedHashSet<>());
        Thread t = new Thread(() -> unicast.addAll(search(ctx, hosts, 2500)), "telelink-ssdp");
        t.start();
        Set<String> locations = probeSamsung(ctx, hosts);
        try {
            t.join(5000);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
        synchronized (unicast) {
            locations.addAll(unicast);
        }
        return describeAll(ctx, locations);
    }

    /** Busca una tele en una IP concreta que escribe el usuario. */
    static List<Device> atIp(Context ctx, String ip) {
        List<Device> none = new ArrayList<>();
        if (ip == null || !ip.trim().matches("\\d{1,3}(\\.\\d{1,3}){3}")) return none;
        InetAddress host;
        try {
            host = InetAddress.getByName(ip.trim());
        } catch (IOException e) {
            return none;
        }
        List<InetAddress> one = new ArrayList<>();
        one.add(host);
        Set<String> locations = search(ctx, one, 2500);
        locations.add("http://" + host.getHostAddress() + ":" + SAMSUNG_DMR_PORT + "/dmr");
        return describeAll(ctx, locations);
    }

    /** Envía M-SEARCH (SSDP) a cada destino y devuelve las direcciones de descripción recibidas. */
    private static Set<String> search(Context ctx, List<InetAddress> targets, int timeoutMs) {
        Set<String> locations = new LinkedHashSet<>();
        if (targets.isEmpty()) return locations;

        WifiManager wm = (WifiManager) ctx.getApplicationContext().getSystemService(Context.WIFI_SERVICE);
        WifiManager.MulticastLock lock = null;
        DatagramSocket sock = null;
        try {
            if (wm != null) {
                lock = wm.createMulticastLock("telelink");
                lock.acquire();
            }
            sock = new DatagramSocket();
            Network n = wifi(ctx);
            if (n != null) {
                try {
                    n.bindSocket(sock);
                } catch (Exception ignored) {
                }
            }
            sock.setSoTimeout(600);

            String[] types = {"urn:schemas-upnp-org:device:MediaRenderer:1", AVT};
            for (int round = 0; round < 2; round++) {
                for (InetAddress to : targets) {
                    for (String st : types) {
                        String msg = "M-SEARCH * HTTP/1.1\r\n"
                                + "HOST: " + to.getHostAddress() + ":1900\r\n"
                                + "MAN: \"ssdp:discover\"\r\n"
                                + "MX: 2\r\n"
                                + "ST: " + st + "\r\n\r\n";
                        byte[] data = msg.getBytes(StandardCharsets.US_ASCII);
                        try {
                            sock.send(new DatagramPacket(data, data.length, to, 1900));
                        } catch (IOException ignored) {
                            // Una dirección inalcanzable no debe cortar el envío a las demás.
                        }
                    }
                }
            }

            Pattern loc = Pattern.compile("(?im)^location:\\s*(\\S+)");
            long end = System.currentTimeMillis() + timeoutMs;
            byte[] buf = new byte[4096];
            while (System.currentTimeMillis() < end) {
                try {
                    DatagramPacket p = new DatagramPacket(buf, buf.length);
                    sock.receive(p);
                    String resp = new String(p.getData(), 0, p.getLength(), StandardCharsets.US_ASCII);
                    Matcher m = loc.matcher(resp);
                    if (m.find()) locations.add(m.group(1));
                } catch (SocketTimeoutException ignored) {
                }
            }
        } catch (Exception ignored) {
        } finally {
            if (sock != null) sock.close();
            if (lock != null && lock.isHeld()) lock.release();
        }
        return locations;
    }

    /** Las demás direcciones del mismo bloque /24 que el móvil en la wifi. */
    private static List<InetAddress> neighbours(Context ctx) {
        List<InetAddress> hosts = new ArrayList<>();
        String ip = wifiIp(ctx);
        if (ip == null) return hosts;
        String[] parts = ip.split("\\.");
        if (parts.length != 4) return hosts;
        String prefix = parts[0] + "." + parts[1] + "." + parts[2] + ".";
        for (int i = 1; i <= 254; i++) {
            String h = prefix + i;
            if (h.equals(ip)) continue;
            try {
                hosts.add(InetAddress.getByName(h));
            } catch (IOException ignored) {
            }
        }
        return hosts;
    }

    /** Prueba en paralelo el puerto DLNA de las Samsung en cada dirección. */
    private static Set<String> probeSamsung(Context ctx, List<InetAddress> hosts) {
        final Set<String> locations = Collections.synchronizedSet(new LinkedHashSet<>());
        final Network n = wifi(ctx);
        ExecutorService pool = Executors.newFixedThreadPool(32);
        for (final InetAddress h : hosts) {
            pool.execute(() -> {
                Socket s = null;
                try {
                    s = n != null ? n.getSocketFactory().createSocket() : new Socket();
                    s.connect(new InetSocketAddress(h, SAMSUNG_DMR_PORT), 500);
                    locations.add("http://" + h.getHostAddress() + ":" + SAMSUNG_DMR_PORT + "/dmr");
                } catch (IOException ignored) {
                } finally {
                    if (s != null) {
                        try {
                            s.close();
                        } catch (IOException ignored) {
                        }
                    }
                }
            });
        }
        pool.shutdown();
        try {
            if (!pool.awaitTermination(15, TimeUnit.SECONDS)) pool.shutdownNow();
        } catch (InterruptedException e) {
            pool.shutdownNow();
            Thread.currentThread().interrupt();
        }
        return new LinkedHashSet<>(locations);
    }

    private static List<Device> describeAll(Context ctx, Set<String> locations) {
        List<Device> found = new ArrayList<>();
        for (String location : locations) {
            try {
                Device d = describe(ctx, location);
                if (d != null) {
                    boolean dup = false;
                    for (Device o : found) if (o.avControl.equals(d.avControl)) dup = true;
                    if (!dup) found.add(d);
                }
            } catch (Exception ignored) {
            }
        }
        return found;
    }

    private static Device describe(Context ctx, String location) throws IOException {
        HttpURLConnection c = open(ctx, location);
        String xml = readAll(c.getInputStream());

        String base = tag(xml, "URLBase");
        if (base == null || base.isEmpty()) base = location;

        Device d = new Device();
        d.name = unescape(tag(xml, "friendlyName"));
        if (d.name == null || d.name.isEmpty()) d.name = new URL(location).getHost();

        Matcher m = Pattern.compile("(?s)<service>(.*?)</service>").matcher(xml);
        while (m.find()) {
            String s = m.group(1);
            String type = tag(s, "serviceType");
            String ctl = tag(s, "controlURL");
            if (type == null || ctl == null) continue;
            String abs = new URL(new URL(base), ctl.trim()).toString();
            if (type.contains(":AVTransport:")) d.avControl = abs;
            else if (type.contains(":RenderingControl:")) d.rcControl = abs;
        }
        return d.avControl != null ? d : null;
    }

    // ---------- SOAP ----------

    private static String soap(Context ctx, String control, String service, String action, String args)
            throws IOException {
        return soap(ctx, control, service, action, args, 8000);
    }

    private static String soap(Context ctx, String control, String service, String action, String args,
                               int readMs) throws IOException {
        String body = "<?xml version=\"1.0\" encoding=\"utf-8\"?>"
                + "<s:Envelope xmlns:s=\"http://schemas.xmlsoap.org/soap/envelope/\" "
                + "s:encodingStyle=\"http://schemas.xmlsoap.org/soap/encoding/\"><s:Body>"
                + "<u:" + action + " xmlns:u=\"" + service + "\">" + args + "</u:" + action + ">"
                + "</s:Body></s:Envelope>";
        byte[] data = body.getBytes(StandardCharsets.UTF_8);

        HttpURLConnection c = open(ctx, control);
        c.setReadTimeout(readMs);
        c.setRequestMethod("POST");
        c.setDoOutput(true);
        c.setRequestProperty("Content-Type", "text/xml; charset=\"utf-8\"");
        c.setRequestProperty("SOAPAction", "\"" + service + "#" + action + "\"");
        c.setRequestProperty("Connection", "close");
        c.setFixedLengthStreamingMode(data.length);
        OutputStream os = c.getOutputStream();
        os.write(data);
        os.close();

        int code = c.getResponseCode();
        if (code >= 400) {
            String err = readAll(c.getErrorStream());
            String desc = tag(err, "errorDescription");
            String num = tag(err, "errorCode");
            throw new IOException(action + " falló (HTTP " + code
                    + (num != null ? ", UPnP " + num : "")
                    + (desc != null ? ": " + desc : "") + ")");
        }
        return readAll(c.getInputStream());
    }

    // ---------- Acciones ----------

    static void play(Context ctx, Device d, String url, String title, String mime) throws IOException {
        try {
            soap(ctx, d.avControl, AVT, "Stop", "<InstanceID>0</InstanceID>");
        } catch (IOException ignored) {
        }

        if (mime == null) mime = mimeFor(url);
        String didl = "<DIDL-Lite xmlns=\"urn:schemas-upnp-org:metadata-1-0/DIDL-Lite/\" "
                + "xmlns:dc=\"http://purl.org/dc/elements/1.1/\" "
                + "xmlns:upnp=\"urn:schemas-upnp-org:metadata-1-0/upnp/\">"
                + "<item id=\"0\" parentID=\"-1\" restricted=\"1\">"
                + "<dc:title>" + escape(title) + "</dc:title>"
                + "<upnp:class>object.item.videoItem</upnp:class>"
                + "<res protocolInfo=\"http-get:*:" + mime + ":*\">" + escape(url) + "</res>"
                + "</item></DIDL-Lite>";

        String head = "<InstanceID>0</InstanceID><CurrentURI>" + escape(url) + "</CurrentURI>";
        // Hay teles (LG webOS) que no contestan a esta orden hasta haber abierto el vídeo, y eso
        // puede tardar. Si se les repite la orden mientras tanto responden "701: Transition not
        // available", así que: se espera mucho más, y ante un 701 se aguarda en vez de insistir.
        boolean meta = true, set = false;
        IOException last = null;
        for (int attempt = 0; attempt < 5 && !set; attempt++) {
            try {
                soap(ctx, d.avControl, AVT, "SetAVTransportURI", head + "<CurrentURIMetaData>"
                        + (meta ? escape(didl) : "") + "</CurrentURIMetaData>", 30000);
                set = true;
            } catch (SocketTimeoutException slow) {
                last = new IOException("La tele no ha contestado a tiempo. Comprueba que está encendida "
                        + "y en la misma wifi que el móvil, y vuelve a enviarlo.");
                set = settled(ctx, d, 20000);
                if (!set) break;
            } catch (IOException e) {
                last = e;
                String m = String.valueOf(e.getMessage());
                if (m.contains("UPnP 701") || m.contains("UPnP 705")) {
                    // Ocupada con la orden anterior: se le da tiempo a terminar.
                    last = new IOException("La tele está ocupada con el envío anterior. "
                            + "Espera unos segundos y vuelve a enviarlo.\n\n" + m);
                    settled(ctx, d, 8000);
                    try {
                        soap(ctx, d.avControl, AVT, "Stop", "<InstanceID>0</InstanceID>");
                    } catch (IOException ignored) {
                    }
                    pause(1500);
                } else if (m.contains("UPnP 716")) {
                    // La tele ha ido a por el vídeo y no se lo han dado: reintentar no sirve.
                    throw new IOException("La tele no ha conseguido abrir el vídeo. Si lo has enviado en "
                            + "«Directo», esta web no deja que la tele lo pida por su cuenta: usa Automático "
                            + "o «Precargar en el móvil».\n\n" + m);
                } else if (meta) {
                    meta = false; // algunas teles rechazan los metadatos: se prueba sin ellos
                } else {
                    break;
                }
            }
        }
        if (!set) throw last;

        for (int attempt = 0; ; attempt++) {
            try {
                soap(ctx, d.avControl, AVT, "Play", "<InstanceID>0</InstanceID><Speed>1</Speed>", 30000);
                return;
            } catch (SocketTimeoutException slow) {
                return; // la orden ha llegado; si de verdad no arranca, lo detecta la vigilancia posterior
            } catch (IOException e) {
                if (attempt >= 3 || !String.valueOf(e.getMessage()).contains("UPnP 701")) throw e;
                pause(2000);
            }
        }
    }

    private static void pause(int ms) throws IOException {
        try {
            Thread.sleep(ms);
        } catch (InterruptedException e) {
            throw new IOException("Envío cancelado");
        }
    }

    /** Espera a que la tele deje de estar "en transición". false si no contesta o no termina. */
    private static boolean settled(Context ctx, Device d, int maxMs) throws IOException {
        long end = System.currentTimeMillis() + maxMs;
        while (System.currentTimeMillis() < end) {
            pause(1500);
            try {
                String st = state(ctx, d);
                if (!st.isEmpty() && !st.equals("TRANSITIONING")) return true;
            } catch (IOException ignored) {
            }
        }
        return false;
    }

    /** Estado de la tele: PLAYING, PAUSED_PLAYBACK, TRANSITIONING, STOPPED, NO_MEDIA_PRESENT... */
    static String state(Context ctx, Device d) throws IOException {
        String r = soap(ctx, d.avControl, AVT, "GetTransportInfo", "<InstanceID>0</InstanceID>");
        String st = tag(r, "CurrentTransportState");
        return st == null ? "" : st.trim();
    }

    /** Segundo por el que va la reproducción. */
    static int position(Context ctx, Device d) throws IOException {
        String r = soap(ctx, d.avControl, AVT, "GetPositionInfo", "<InstanceID>0</InstanceID>");
        return parseTime(tag(r, "RelTime"));
    }

    static void resume(Context ctx, Device d) throws IOException {
        soap(ctx, d.avControl, AVT, "Play", "<InstanceID>0</InstanceID><Speed>1</Speed>");
    }

    static void pause(Context ctx, Device d) throws IOException {
        soap(ctx, d.avControl, AVT, "Pause", "<InstanceID>0</InstanceID>");
    }

    static void stop(Context ctx, Device d) throws IOException {
        soap(ctx, d.avControl, AVT, "Stop", "<InstanceID>0</InstanceID>");
    }

    static void seekTo(Context ctx, Device d, int target) throws IOException {
        int t = Math.max(0, target);
        String s = String.format(Locale.US, "%02d:%02d:%02d", t / 3600, (t / 60) % 60, t % 60);
        soap(ctx, d.avControl, AVT, "Seek",
                "<InstanceID>0</InstanceID><Unit>REL_TIME</Unit><Target>" + s + "</Target>");
    }

    static void seekBy(Context ctx, Device d, int seconds) throws IOException {
        String info = soap(ctx, d.avControl, AVT, "GetPositionInfo", "<InstanceID>0</InstanceID>");
        int now = parseTime(tag(info, "RelTime"));
        int target = Math.max(0, now + seconds);
        String t = String.format(Locale.US, "%02d:%02d:%02d", target / 3600, (target / 60) % 60, target % 60);
        soap(ctx, d.avControl, AVT, "Seek",
                "<InstanceID>0</InstanceID><Unit>REL_TIME</Unit><Target>" + t + "</Target>");
    }

    static int volumeBy(Context ctx, Device d, int delta) throws IOException {
        if (d.rcControl == null) throw new IOException("Esta tele no deja controlar el volumen");
        String r = soap(ctx, d.rcControl, RC, "GetVolume",
                "<InstanceID>0</InstanceID><Channel>Master</Channel>");
        int v = 0;
        try {
            v = Integer.parseInt(tag(r, "CurrentVolume").trim());
        } catch (Exception ignored) {
        }
        v = Math.max(0, Math.min(100, v + delta));
        soap(ctx, d.rcControl, RC, "SetVolume",
                "<InstanceID>0</InstanceID><Channel>Master</Channel><DesiredVolume>" + v + "</DesiredVolume>");
        return v;
    }

    // ---------- Utilidades ----------

    static String mimeFor(String url) {
        String u = url.toLowerCase(Locale.US);
        int q = u.indexOf('?');
        if (q >= 0) u = u.substring(0, q);
        if (u.endsWith(".m3u8")) return "application/vnd.apple.mpegurl";
        if (u.endsWith(".webm")) return "video/webm";
        if (u.endsWith(".mkv")) return "video/x-matroska";
        if (u.endsWith(".mov")) return "video/quicktime";
        return "video/mp4";
    }

    private static int parseTime(String t) {
        if (t == null) return 0;
        try {
            String[] p = t.trim().split(":");
            if (p.length != 3) return 0;
            return Integer.parseInt(p[0]) * 3600 + Integer.parseInt(p[1]) * 60
                    + (int) Double.parseDouble(p[2]);
        } catch (Exception e) {
            return 0;
        }
    }

    private static String tag(String xml, String name) {
        if (xml == null) return null;
        Matcher m = Pattern.compile("(?s)<(?:\\w+:)?" + name + "(?:\\s[^>]*)?>(.*?)</(?:\\w+:)?" + name + ">")
                .matcher(xml);
        return m.find() ? m.group(1).trim() : null;
    }

    private static String escape(String s) {
        if (s == null) return "";
        return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
                .replace("\"", "&quot;").replace("'", "&apos;");
    }

    private static String unescape(String s) {
        if (s == null) return null;
        return s.replace("&lt;", "<").replace("&gt;", ">").replace("&quot;", "\"")
                .replace("&apos;", "'").replace("&amp;", "&");
    }
}
