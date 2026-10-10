package inference;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.List;
import java.util.Optional;
import java.util.stream.IntStream;

import core.B;
import core.RC;
import offensiveUtils.NeverAsKey;
import utils.Range;
import utils.Streams;

public final class Gamma{
  /** Never as Map/Set key (nondiscriminating equals/hashCode). Build-time checker rejects it. */
  @NeverAsKey
  public static final class GammaSignature{
    long hash;
    final HashMap<Monotonicity.Slot,ArrayList<Object>> monotonicity= new HashMap<>();
    //public GammaSignature clear(){ hash = 0; return this;}//more performance
    public GammaSignature clear(){ return new GammaSignature(); }//more safe
    @Override public boolean equals(Object o){ return o instanceof GammaSignature; }
    @Override public int hashCode(){ return 0; }
  }
  private static final int initialBindings= 4096;
  private static final int initialDepth= 256;
  private static final int indexThreshold= 12;

  private String[] xs= new String[initialBindings];
  private IT[]     ts= new IT[initialBindings];
  private int[] declDepth= new int[initialBindings];
  private int size= 0;

  private int[]  marks= new int[initialDepth];
  private long[] envHash= new long[initialDepth];
  private RC[]  rcs= new RC[initialDepth];
  @SuppressWarnings("unchecked")
  private List<B>[] bss= (List<B>[])new List<?>[initialDepth];
  private E.Literal[] owners= new E.Literal[initialDepth];
  private int depth= 0;

  private final HashMap<String,Integer> idx= new HashMap<>(indexThreshold * 10);
  public Gamma(){ marks[0]= 0; envHash[0]= 0L; depth= 1; }
  public void newScope(RC rc, List<B> bs, E.Literal owner){
    if (depth == marks.length){ growScopes(); }
    marks[depth]= size;
    envHash[depth]= envHash[depth - 1];
    rcs[depth]= rc;
    bss[depth]= bs;
    owners[depth]= owner;
    depth++;
  }
  private void growScopes(){
    var n= 2 * depth;
    marks= Arrays.copyOf(marks, n);
    envHash= Arrays.copyOf(envHash, n);
    rcs= Arrays.copyOf(rcs, n);
    bss= Arrays.copyOf(bss, n);
    owners= Arrays.copyOf(owners, n);
  }
  private void growBindings(){
    var n= 2 * size;
    xs= Arrays.copyOf(xs, n);
    ts= Arrays.copyOf(ts, n);
    declDepth= Arrays.copyOf(declDepth, n);
  }
  public void popScope(){
    assert depth > 1;
    var newSize= marks[depth - 1];
    for (var i= size - 1; i >= newSize; i--){ idx.remove(xs[i]); xs[i]= null; ts[i]= null; }
    size= newSize;
    depth--;
  }
  public IT getWithRC(String x){
    //Can this be done? need to locate the dept of x.
    //Then, if there is imm over (not under) x turn the IT to imm and return theIt.withRC(imm)
    // if there is read over (not under) x and theIt.explicitRC().equals(Optional.of(RC.mut), turn the IT to read and return theIt.withRC(read)
    var i= indexOf(x);         // offensive: -1 would crash later
    var t= ts[i];              // the stored (true) type
    for (var s= declDepth[i] + 1; s < depth; s++){ t= adapt(t, rcs[s], bss[s]); }
    return t;
  }
  public Optional<E.Literal> notFunnelledInto(String x){
    var i= indexOf(x);
    var xs= ts[i].ftv().toList();
    return IntStream.range(declDepth[i] + 1, depth).filter(s->!B.xs(bss[s]).containsAll(xs)).mapToObj(s->owners[s]).findFirst();
  }
  private static IT adapt(IT t, RC rc, List<B> bs){ return switch (t){
    case IT.X(var x, _) -> adaptX(t, B.get(bs, x).rcs(), rc);
    case IT.ReadImmX(IT.X(var x, _)) -> adaptX(t, B.get(bs, x).rcs(), rc);
    default -> adaptRC(t, rc);
  };}
  private static IT adaptX(IT t, EnumSet<RC> xRcs, RC rc){
    if (rc == RC.imm || EnumSet.of(RC.iso, RC.imm).containsAll(xRcs)){ return t.withRC(RC.imm); }
    if (xRcs.stream().anyMatch(RC::isH)){ return t; }
    if (rc == RC.read){ return t.readImm(); }
    return xRcs.contains(RC.iso) ? t.readImm() : t;
  }
  private static IT adaptRC(IT t, RC rc){
    var trc= t.explicitRC();
    if (rc == RC.imm || trc.equals(Optional.of(RC.iso))){ return t.withRC(RC.imm); }
    if (rc == RC.mut){ return t; }
    if (trc.equals(Optional.of(RC.mutH))){ return t.withRC(RC.readH); }
    return trc.equals(Optional.of(RC.mut)) ? t.withRC(RC.read) : t;
  }
  public IT get(String x){ return ts[indexOf(x)]; }
  public Optional<IT> getOpt(String x){ var i= indexOf(x); return i == -1 ? Optional.empty() : Optional.of(ts[i]); }

  public void declare(String x, IT t){
    if (x.equals("_")){ return; }
    assert indexOf(x) == -1;
    if (size == xs.length){ growBindings(); }
    xs[size]= x;
    ts[size]= t;
    declDepth[size]= depth - 1;
    idx.put(x, size);
    envHash[depth - 1] ^= contrib(x, t);
    size++;
  }
  public void update(String x, IT t){
    var i= indexOf(x);
    if (ts[i].equals(t)){ return; }
    var cold= contrib(xs[i], ts[i]);
    var cnew= contrib(xs[i], t);
    var d= declDepth[i];
    for (int s : Range.of(d,depth)){ envHash[s] ^= cold ^ cnew; }
    ts[i]= t;
  }
  public boolean represents(GammaSignature sig){
    return sig.hash == envHash[depth - 1];
  }
  public void sign(GammaSignature sig){ sig.hash= envHash[depth - 1]; }
  public long snapshot(){ return envHash[depth - 1]; }
  public boolean changed(long shot){ return shot != envHash[depth - 1]; }
  private int indexOf(String x){
    assert x != null;
    if (size > indexThreshold){ return idx.getOrDefault(x,-1); }
    for (var i= size - 1; i >= 0; i--){ if (xs[i].equals(x)){ return i; } }
    return -1;
  }
  private static long contrib(String x, IT t){
    var hx= x.hashCode();
    var ht= t.hashCode();
    var packed= ((hx & 0xffffffffL) << 32) | (ht & 0xffffffffL);
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
    var sb= new StringBuilder();
    for (int s : Range.of(0,depth)){
      var start= marks[s];
      var end= (s + 1 < depth) ? marks[s + 1] : size;
      sb.append('[');
      for (int i : Range.of(start,end)){
        if (i > start){ sb.append(','); }
        sb.append(xs[i]).append("->").append(ts[i]);
      }
      sb.append(']');
    }
    return sb.toString();
  }

  public static Gamma of(List<String> xs2, List<IT> ts2, String self, IT t){
    var res= new Gamma();
    Streams.zip(xs2, ts2).forEach(res::declare);
    res.declare(self, t);
    return res;
  }
}
