package message;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.net.URI;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;
import java.util.Objects;
import java.util.concurrent.ConcurrentHashMap;

/** SourceOracle
 * - RealFS: disk-backed with in-memory overlays for tentative edits.
 * - Debug: map-backed, never touches disk.
 *
 * Contract:
 *  - load(uri): return source for uri (overlay wins if present).
 *  - putOverlay/removeOverlay: set or clear an in-memory shadow for a uri.
 *  - exists(uri): true if overlay present, else whether disk has it (RealFS) or map has it (Debug).
 *  - No caching of disk content: every load() without overlay re-reads from disk.
 */
public interface SourceOracle {
  CharSequence load(URI uri);
  boolean exists(URI uri);
  void putOverlay(URI uri, String text);
  void removeOverlay(URI uri);
  boolean hasOverlay(URI uri);
  static URI defaultDbgUri(int index){
    return Path.of("___DBG___/in_memory"+index+".fear").toAbsolutePath().normalize().toUri();
  }
  default String loadString(URI uri){ return load(uri).toString(); }

  /** Utility: best-effort normalization for file: URIs, pass-through otherwise. */
  static URI normalize(URI uri){
    Objects.requireNonNull(uri);
    try{ if(isFile(uri)){ return Path.of(uri).toAbsolutePath().normalize().toUri(); } }
    catch(Exception ignore){}
    return uri.normalize();
  }
  static boolean isFile(URI k){ return "file".equalsIgnoreCase(k.getScheme()); }
  static SourceOracle realFS(){ return new RealFS(Charset.defaultCharset()); }
  static SourceOracle realFS(Charset cs){ return new RealFS(cs); }

  final class RealFS implements SourceOracle{
    private final Charset cs;
    private final ConcurrentHashMap<URI,String> overlays= new ConcurrentHashMap<>();
    RealFS(Charset cs){ this.cs= Objects.requireNonNull(cs); }
    @Override public CharSequence load(URI uri){
      URI k= normalize(uri);
      String over= overlays.get(k);
      if(over != null){ return over; }
      try{
        if(!isFile(k)){ throw new IllegalArgumentException("RealFS only supports file: URIs, got "+k); }
        return Files.readString(Path.of(k), cs);
      }catch(IOException e){ throw new UncheckedIOException(e); }
    }
    @Override public boolean exists(URI uri){
      URI k = normalize(uri);
      if(overlays.containsKey(k)){ return true; }
      if(!isFile(k)){ return false; }
      return Files.exists(Path.of(k));
    }
    @Override public void putOverlay(URI uri, String text){
      overlays.put(normalize(uri), Objects.requireNonNull(text));
    }
    @Override public void removeOverlay(URI uri){
      overlays.remove(normalize(uri));
    }
    @Override public boolean hasOverlay(URI uri){
      return overlays.containsKey(normalize(uri));
    }
  }

  static Debug.Builder debugBuilder(){ return new Debug.Builder(); }

  final class Debug implements SourceOracle{
    private final ConcurrentHashMap<URI,String> map;

    private Debug(Map<URI,String> seed){ this.map= new ConcurrentHashMap<>(seed); }

    @Override public CharSequence load(URI uri){
      URI k= normalize(uri);
      String s= map.get(k);
      if (s == null){ throw new IllegalArgumentException("No debug content for "+k); }
      return s;
    }
    @Override public boolean exists(URI uri){ return map.containsKey(normalize(uri)); }
    @Override public void putOverlay(URI uri, String text){ map.put(normalize(uri), Objects.requireNonNull(text)); }
    @Override public void removeOverlay(URI uri){ map.remove(normalize(uri)); }
    @Override public boolean hasOverlay(URI uri){ return map.containsKey(normalize(uri)); }

    public static final class Builder{
      private final ConcurrentHashMap<URI,String> seed= new ConcurrentHashMap<>();
      public Builder putURI(URI uri, String content){ seed.put(normalize(uri), Objects.requireNonNull(content)); return this; }
      public Builder put(String pathLike, String content){
        URI u = Path.of(pathLike).toAbsolutePath().normalize().toUri();
        return putURI(u, content);
      }
      public Debug build(){ return new Debug(Map.copyOf(seed)); }
      public Builder put(int index,String content){ return putURI(defaultDbgUri(index), content); }
    }
  }
}