package inference;

import java.util.HashMap;
import java.util.List;
import java.util.stream.IntStream;

public final class Gamma {
 public final static class GammaSignature {
    long hash;
    public GammaSignature clear(){ hash = 0; return this;}
    @Override public boolean equals(Object o){ return true; }
    @Override public int hashCode(){ return 0; }
  }
  private static final int maxBindings= 4096;
  private static final int maxDepth= 256;
  private static final int indexThreshold= 12;

  private final String[] xs= new String[maxBindings];
  private final IT[]     ts= new IT[maxBindings];
  private final int[] declDepth= new int[maxBindings];
  private int size= 0;

  private final int[]  marks= new int[maxDepth];
  private final long[] envHash= new long[maxDepth];
  private int depth= 0;

  private HashMap<String,Integer> idx= new HashMap<>(indexThreshold * 10);
  public Gamma(){ marks[0]= 0; envHash[0]= 0L; depth= 1; }
  public void newScope(){
    marks[depth]= size;
    envHash[depth]= envHash[depth - 1];
    depth++;
  }
  public void popScope(){
    assert depth > 1 : "cannot pop root";
    int newSize= marks[depth - 1];
    for(int i= size - 1; i >= newSize; i--){ idx.remove(xs[i]); xs[i] = null; ts[i] = null; }
    size = newSize;
    depth--;
  }
  public IT get(String x){ return ts[indexOf(x)]; } // offensive: throws on -1

  public void declare(String x, IT t){
    if("_".equals(x)){ return; }
    assert indexOf(x) < 0 : "duplicate: " + x;
    assert size < maxBindings;
    xs[size] = x;
    ts[size] = t;
    declDepth[size] = depth - 1;
    idx.put(x, size);
    envHash[depth - 1] ^= contrib(x, t);
    size++;
  }
  public void update(String x, IT t){
    int i= indexOf(x);
    if(ts[i].equals(t)){ return; }
    long cold= contrib(xs[i], ts[i]);
    long cnew= contrib(xs[i], t);
    int d= declDepth[i];
    for(int s= d; s < depth; s++){ envHash[s] ^= cold ^ cnew; }
    ts[i] = t;
  }
  public boolean represents(GammaSignature sig){
    //return false;
    return sig.hash == envHash[depth - 1];
  }
  public void sign(GammaSignature sig){ sig.hash = envHash[depth - 1]; }
  public long snapshot(){ return envHash[depth - 1]; }
  public boolean changed(long shot){ return shot != envHash[depth - 1]; }
  private int indexOf(String x){
    assert x != null;
    if (size > indexThreshold){
      Integer i= idx.get(x);
      return i != null ? i : -1;
    }
    for (int i= size - 1; i >= 0; i--){ if (xs[i].equals(x)){ return i; } }
    return -1;
  }
  private static long contrib(String x, IT t){
    int hx= x.hashCode();
    int ht= t.hashCode();
    long packed = ((hx & 0xffffffffL) << 32) | (ht & 0xffffffffL);
    return fmix64(packed ^ 0x9e3779b97f4a7c15L);
  }
  private static long fmix64(long x){
    x ^= x >>> 33;
    x *= 0xff51afd7ed558ccdL;
    x ^= x >>> 33;
    x *= 0xc4ceb9fe1a85ec53L;
    x ^= x >>> 33;
    return x;
  }

  @Override public String toString(){
    StringBuilder sb = new StringBuilder();
    for(int s = 0; s < depth; s++){
      int start = marks[s];
      int end   = (s + 1 < depth) ? marks[s + 1] : size;
      sb.append('[');
      for(int i = start; i < end; i++){
        if(i > start) sb.append(',');
        sb.append(xs[i]).append("->").append(ts[i]);
      }
      sb.append(']');
    }
    return sb.toString();
  }

  public static Gamma of(List<String> xs2, List<IT> ts2, String self, IT t){
    Gamma res= new Gamma();
    assert xs2.size() == ts2.size();
    IntStream.range(0, xs2.size())
      .filter(i -> !xs2.get(i).equals("_"))
      .forEach(i -> res.declare(xs2.get(i), ts2.get(i)));
    if(!self.equals("_")) res.declare(self, t);
    return res;
  }
}
