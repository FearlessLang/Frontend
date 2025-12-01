package typeSystem;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.IntStream;

import core.T;
import typeSystem.TypeSystem.MType;

public record ArgMatrix(List<MType> cs,
    List<List<Integer>> okByArg,//forall arg1..argn, the List of cs indexes where the arg expression is typed
    List<List<TResult>> resByArg){
  public record TResult(String reqName,T best,String reason){ boolean success(){return reason.isEmpty(); } }
  int aCount(){ return okByArg.size(); }
  int cCount(){ return cs.size(); }
  List<Integer> okForArg(int argi){ return okByArg.get(argi); }
  TResult res(int argi,int ci){ return resByArg.get(argi).get(ci); }
  public MType candidate(int ci){ return cs.get(ci); }
  public List<Integer> candidatesOkForAllArgs(){
    if(okByArg.isEmpty()){ return IntStream.range(0,cs.size()).boxed().toList(); }
    var acc= new ArrayList<>(okByArg.getFirst());
    for(int i= 1; i < okByArg.size(); i++){ acc.retainAll(okByArg.get(i)); }
    return acc;
  }
}