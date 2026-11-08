package fuzz;

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
    for (int i= 0; i < 3000; i += 1){ fuzz.check(Source.of(new Gen(new Random(i), 7).of(Ast.Program.class))); }
    fuzz.assertNothingFound();
  }
  @Test void writingTheInferredTypesKeepsTheCore(){
    var fuzz= new Fuzz("writingTheInferredTypesKeepsTheCore");
    var underAnnotated= Seeds.annotated.stream().flatMap(Mutations::underAnnotations);
    Stream.concat(Seeds.all.stream(), underAnnotated).distinct().forEach(s -> InferredTypes.check(fuzz, s));
    fuzz.assertNothingFound();
  }
}
