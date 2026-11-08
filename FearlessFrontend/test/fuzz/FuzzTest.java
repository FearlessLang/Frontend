package fuzz;

import java.util.Random;
import java.util.stream.Stream;

import org.junit.jupiter.api.Test;

public final class FuzzTest{
  @Test void mutatedTestProgramsNeverCrash(){
    var fuzz= new Fuzz();
    var mutations= new Mutations(Seeds.all);
    for (var s : Seeds.all){
      fuzz.check(s);
      var rnd= new Random(s.hashCode());
      for (int i= 0; i < Mutations.perSeed; i += 1){ fuzz.check(mutations.mutate(s, rnd)); }
    }
    fuzz.assertNothingFound();
  }
  @Test void underAnnotatedTestProgramsNeverCrash(){
    var fuzz= new Fuzz();
    Seeds.annotated.stream().flatMap(Mutations::underAnnotations).forEach(fuzz::check);
    fuzz.assertNothingFound();
  }
  @Test void writingTheInferredTypesKeepsTheCore(){
    var fuzz= new Fuzz();
    var underAnnotated= Seeds.annotated.stream().flatMap(Mutations::underAnnotations);
    Stream.concat(Seeds.all.stream(), underAnnotated).distinct().forEach(s -> InferredTypes.check(fuzz, s));
    fuzz.assertNothingFound();
  }
}
