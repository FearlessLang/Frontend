package fuzz;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Random;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.junit.jupiter.api.Test;

public final class FuzzTest{
  static final int generated= 6000;
  static final int generatedDepth= 7;
  static final int mutants= 40000;
  static final int mutantDepth= 5;
  static final int batch= 500;
  @Test void mutatedTestPrograms(){
    var fuzz= new Fuzz("mutatedTestPrograms");
    var mutations= new Mutations(Seeds.all);
    var programs= new ArrayList<String>();
    for (var s : Seeds.all){
      programs.add(s);
      var rnd= new Random(s.hashCode());
      for (int i= 0; i < Mutations.perSeed; i += 1){ programs.add(mutations.mutate(s, rnd)); }
    }
    fuzz.check(programs);
    fuzz.assertNothingFound();
  }
  @Test void underAnnotatedTestPrograms(){
    var fuzz= new Fuzz("underAnnotatedTestPrograms");
    fuzz.check(Seeds.annotated.stream().flatMap(Mutations::underAnnotations).toList());
    fuzz.assertNothingFound();
  }
  @Test void generatedPrograms(){
    var fuzz= new Fuzz("generatedPrograms");
    var first= IntStream.range(0, generated).mapToObj(i -> new Gen(new Random(i), generatedDepth).of(Ast.Program.class)).toList();
    var parents= new ArrayDeque<>(fuzz.accepted(first));
    var rnd= new Random(0);
    for (int done= 0; done < mutants; done += batch){
      var mutated= new ArrayList<Ast.Program>();
      for (int i= 0; i < batch; i += 1){
        var p= parents.poll();
        parents.add(p);
        var n= Trees.positions(p);
        if (n > 0){ mutated.add(Trees.replace(p, rnd.nextInt(n), (_, t) -> new Gen(rnd, mutantDepth).value(t))); }
      }
      parents.addAll(fuzz.accepted(mutated));
    }
    fuzz.assertNothingFound();
  }
  @Test void writingTheInferredTypesKeepsTheCore(){
    var fuzz= new Fuzz("writingTheInferredTypesKeepsTheCore");
    var underAnnotated= Seeds.annotated.stream().flatMap(Mutations::underAnnotations);
    Stream.concat(Seeds.all.stream(), underAnnotated).distinct().forEach(s -> InferredTypes.check(fuzz, s));
    fuzz.assertNothingFound();
  }
}
