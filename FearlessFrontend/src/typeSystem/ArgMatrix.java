package typeSystem;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.IntStream;
import typeSystem.TypeSystem.MType;
import message.Reason;

public record ArgMatrix(List<MType> cs,
    ArrayList<List<Integer>> okByArg,//forall arg1..argn, the List of cs indexes where the arg expression is typed
    ArrayList<List<Reason>> resByArg){
  public MType candidate(int ci){ return cs.get(ci); }
  public List<Integer> candidatesOkForAllArgs(){
    return IntStream.range(0,cs.size()).boxed().filter(ci->okByArg.stream().allMatch(ok->ok.contains(ci))).toList();
  }
}