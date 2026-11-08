package fuzz;

import java.util.ArrayDeque;
import java.util.Random;
import java.util.stream.Stream;

import org.junit.jupiter.api.Test;

public final class FuzzTest{
  @Test void mutatedTestProgramsNeverCrash(){
    var fuzz= new Fuzz("mutatedTestProgramsNeverCrash");
    var mutations= new Mutations(Seeds.all);
    for (var s : Seeds.all){
      fuzz.check(s);
      var rnd= new Random(s.hashCode());
      for (int i= 0; i < Mutations.perSeed; i += 1){ fuzz.check(mutations.mutate(s, rnd)); }
    }
    fuzz.assertNothingFound();
  }
  @Test void underAnnotatedTestProgramsNeverCrash(){
    var fuzz= new Fuzz("underAnnotatedTestProgramsNeverCrash");
    Seeds.annotated.stream().flatMap(Mutations::underAnnotations).forEach(fuzz::check);
    fuzz.assertNothingFound();
  }
  @Test void generatedProgramsAgree(){
    var fuzz= new Fuzz("generatedProgramsAgree");
    var accepted= new ArrayDeque<Ast.Program>();
    for (int i= 0; i < 3000; i += 1){
      var p= new Gen(new Random(i), 7).of(Ast.Program.class);
      if (fuzz.check(Source.of(p))){ accepted.add(p); }
    }
    var rnd= new Random(0);
    for (int i= 0; i < 10000; i += 1){
      var p= accepted.poll();
      accepted.add(p);
      var n= Trees.positions(p);
      if (n == 0){ continue; }
      var mutant= Trees.replace(p, rnd.nextInt(n), (_, t) -> new Gen(rnd, 5).value(t));
      if (fuzz.check(Source.of(mutant))){ accepted.add(mutant); }
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
