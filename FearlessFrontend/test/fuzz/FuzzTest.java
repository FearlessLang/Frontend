package fuzz;

import java.util.ArrayDeque;
import java.util.Random;
import java.util.stream.Stream;

import org.junit.jupiter.api.Test;

public final class FuzzTest{
  static final int generated= 3000;
  static final int generatedDepth= 7;
  static final int mutants= 10000;
  static final int mutantDepth= 5;
  @Test void mutatedTestPrograms(){
    var fuzz= new Fuzz("mutatedTestPrograms");
    var mutations= new Mutations(Seeds.all);
    for (var s : Seeds.all){
      fuzz.check(s);
      var rnd= new Random(s.hashCode());
      for (int i= 0; i < Mutations.perSeed; i += 1){ fuzz.check(mutations.mutate(s, rnd)); }
    }
    fuzz.assertNothingFound();
  }
  @Test void underAnnotatedTestPrograms(){
    var fuzz= new Fuzz("underAnnotatedTestPrograms");
    Seeds.annotated.stream().flatMap(Mutations::underAnnotations).forEach(fuzz::check);
    fuzz.assertNothingFound();
  }
  @Test void generatedPrograms(){
    var fuzz= new Fuzz("generatedPrograms");
    var accepted= new ArrayDeque<Ast.Program>();
    for (int i= 0; i < generated; i += 1){
      var p= new Gen(new Random(i), generatedDepth).of(Ast.Program.class);
      if (fuzz.check(p)){ accepted.add(p); }
    }
    var rnd= new Random(0);
    for (int i= 0; i < mutants; i += 1){
      var p= accepted.poll();
      accepted.add(p);
      var n= Trees.positions(p);
      if (n == 0){ continue; }
      var mutant= Trees.replace(p, rnd.nextInt(n), (_, t) -> new Gen(rnd, mutantDepth).value(t));
      if (fuzz.check(mutant)){ accepted.add(mutant); }
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
