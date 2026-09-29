package instantiationSweep;

import static org.junit.jupiter.api.Assertions.fail;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.UnaryOperator;
import java.util.stream.IntStream;

import org.junit.jupiter.api.Test;

import core.FearlessException;
import main.FrontendLogicMain;
import testUtils.DbgBlock;
import utils.Join;

public class InstantiationSweepTest extends testUtils.FearlessTestBase{
  static final List<String> rcs= List.of("iso","imm","mut","read","mutH","readH");
  static final List<String> forms= List.of("_","read/imm _","iso _","imm _","mut _","read _","mutH _","readH _");
  static final List<String> mRcs= List.of("imm","read","mut");
  static final String allRcs= String.join(",",rcs);
  static final List<core.E.Literal> base= DbgBlock.all();
  static final Map<String,Boolean> concrete= new ConcurrentHashMap<>();
  record Found(String title, AtomicLong n, List<String> sample){
    Found(String title){ this(title,new AtomicLong(),Collections.synchronizedList(new ArrayList<>())); }
    void add(String s){ n.incrementAndGet(); if (sample.size() < 20){ sample.add(s); } }
    public String toString(){ return title+": "+n+"\n"+Join.of(sample.stream().sorted(),"","\n","\n",""); }
  }
  static final Found unsound= new Found("Generic accepted, some instantiation rejected");
  static final Found incomplete= new Found("Generic rejected, every instantiation accepted");
  static final Found crashes= new Found("Crashes");
  static final AtomicLong done= new AtomicLong();

  record Case(List<String> bound, boolean classGen, String rm, String rk, Optional<String> p, String r, String ta, String tr){
    String program(String zDecl, UnaryOperator<String> ty, String targ){
      var ps= p.map(pi->"a: "+pi.replace("_","Y")).orElse("");
      var k= classGen
        ? "K[Y:"+allRcs+"]:{ "+rm+" .m("+ps+"): "+r.replace("_","Y")+" }\n"
        : "K:{ "+rm+" .m[Y:"+allRcs+"]("+ps+"): "+r.replace("_","Y")+" }\n";
      var kt= classGen ? rk+" K["+targ+"]" : rk+" K";
      var call= classGen ? "k.m(" : "k.m["+targ+"](";
      var as= p.isPresent() ? ", a: "+ty.apply(ta) : "";
      return "Foo:{}\n"+k+"C:{ .c"+zDecl+"(k: "+kt+as+"): "+ty.apply(tr)+" -> "+call+(p.isPresent() ? "a" : "")+") }\n";
    }
    String generic(List<String> b){ return program("[Z:"+String.join(",",b)+"]", f->f.replace("_","Z"), "Z"); }
    String instance(String rc){ return program("", f->inst(f,rc), rc+" Foo"); }
  }
  static String inst(String form, String rc){
    if (form.equals("_")){ return rc+" Foo"; }
    if (!form.equals("read/imm _")){ return form.replace("_","Foo"); }
    return (rc.equals("iso") || rc.equals("imm") ? "imm" : "read")+" Foo";
  }
  static boolean ok(String src){
    var o= oraclePkg(List.of(src));
    try{ new FrontendLogicMain().of("p",Map.of(),o.allFiles(),otherFrom(base)); return true; }
    catch(FearlessException _){ return false; }
    catch(RuntimeException | AssertionError e){ crashes.add(e+"\n"+src); return false; }
  }
  static Optional<Case> decode(long i){
    var tr= forms.get((int)(i % 8)); i /= 8;
    var ta= forms.get((int)(i % 8)); i /= 8;
    var r= forms.get((int)(i % 8)); i /= 8;
    var pi= (int)(i % 9); i /= 9;
    var rk= rcs.get((int)(i % 6)); i /= 6;
    var rm= mRcs.get((int)(i % 3)); i /= 3;
    var classGen= i % 2 == 0; i /= 2;
    var mask= (int)i + 1;
    if (pi == 8 && !ta.equals("_")){ return Optional.empty(); }
    var bound= IntStream.range(0,6).filter(j->(mask & (1 << j)) != 0).mapToObj(rcs::get).toList();
    return Optional.of(new Case(bound,classGen,rm,rk,pi == 8 ? Optional.empty() : Optional.of(forms.get(pi)),r,ta,tr));
  }
  static void check(Case c){
    var n= done.incrementAndGet();
    if (n % 500_000 == 0){ System.out.println("checked "+n+" unsound "+unsound.n()+" incomplete "+incomplete.n()+" crashes "+crashes.n()); }
    var g= ok(c.generic(c.bound()));
    var insts= c.bound().stream().allMatch(rc->concrete.computeIfAbsent(c.instance(rc),InstantiationSweepTest::ok));
    if (g && !insts){ unsound.add(c.generic(c.bound())); return; }
    if (!g && insts){ incomplete.add(c.generic(c.bound())); }
  }
  @Test void genericTypingMatchesAllInstantiations(){
    var total= 63L*2*3*6*9*8*8*8;
    IntStream.range(0,(int)total).parallel().mapToObj(InstantiationSweepTest::decode).flatMap(Optional::stream).forEach(InstantiationSweepTest::check);
    if (unsound.n().get() + incomplete.n().get() + crashes.n().get() == 0){ return; }
    fail(""+unsound+incomplete+crashes);
  }
}
