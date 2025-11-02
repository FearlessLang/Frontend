package inferenceGrammar;

import java.util.HashMap;
import java.util.List;
import java.util.stream.IntStream;

import fullWellFormedness.TypeRename;

public final class Gamma {
  private static final int maxBindings= 4096;
  private static final int maxDepth=     256;
  private static final int indexThreshold = 12;
  private HashMap<String,Integer> idx = new HashMap<>(indexThreshold * 10);
  boolean indexActive(){ return size > indexThreshold; }
  private final String[] xs= new String[maxBindings];
  private final IT[]      ts= new IT[maxBindings];
  private final int[] declDepth= new int[maxBindings];
  private int size= 0;

  private final int[]  marks=  new int[maxDepth];
  private final long[] visVer= new long[maxDepth];
  private int depth= 0;
  Gamma() { marks[0] = 0; visVer[0] = 0L; depth = 1; }

  public void newScope(){
    marks[depth]  =  size;
    visVer[depth] = visVer[depth - 1];
    depth++;
  }
  public void popScope() {
    assert depth > 1 : "cannot pop root";
    int newSize = marks[depth - 1];
    for (int i= size - 1; i >= newSize; i--){ idx.remove(xs[i]); xs[i] = null; ts[i] = null; }//removing this line still requires on demand maps clean up.
    size = newSize;
    depth--;
  }  
  
  public IT get(String x){ return ts[indexOf(x)]; }//purposely fail with indexOf -1 == offensive programming

  public void declare(String x, IT t){
    assert indexOf(x) < 0 : "duplicate: " + x;
    assert size < maxBindings;
    //var old= xs[size]; if (old != null){ idx.remove(old); }//if we instead do not clean the map
    xs[size] = x;
    ts[size] = t;
    declDepth[size] = depth - 1;
    idx.put(x, size);
    stampVisibleFrom(declDepth[size]);
    size++;
  } 
  
  public void update(String x, IT t){
    int i= indexOf(x);
    ts[i]= t;
    stampVisibleFrom(declDepth[i]);
  }
  public long visibleVersion(){ return visVer[depth - 1]; }
  
  private int indexOf(String x){
    assert x != null;
    if (indexActive()){
      Integer i= idx.get(x);
      //return i != null && i < size ? i.intValue() : -1; //if we instead do not clean the map
      return i != null ? i.intValue() : -1;
    }
    for (int i= size - 1; i >= 0; i--) { if (xs[i].equals(x)){ return i; } }
    return -1;
  }
  
  private long versionClock= 0L;
  private void stampVisibleFrom(int d) {
    long next= ++versionClock;
    for (int i= d; i < depth; i++){ visVer[i] = next; }
  }
  @Override public String toString() {
    StringBuilder sb = new StringBuilder();
    for (int s = 0; s < depth; s++) {
      int start = marks[s];
      int end   = (s + 1 < depth) ? marks[s + 1] : size;
      sb.append('[');
      for (int i = start; i < end; i++) {
        if (i > start) sb.append(',');
        sb.append(xs[i]).append("->").append(ts[i]);
      }
      sb.append(']');
    }
    return sb.toString();
  }
  public static Gamma of(List<String> xs2, List<T> ts2){
    Gamma res= new Gamma();
    assert xs2.size() == ts2.size();
    IntStream.range(0, xs2.size())
      .filter(i->!xs2.get(i).equals("_"))
      .forEach(i->
      res.declare(xs2.get(i),TypeRename.tToIT(ts2.get(i))));
    return res;
  }
}