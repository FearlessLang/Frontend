The package fuzz compiles many programs with the full frontend and, with the argument compact, also with the compact frontend.
From Coordinator/Build/src, TestFuzz.java runs only this package, and TestFuzz.java compact also runs the compact frontend.

A 'finding' is a program where:
- a frontend throws an exception other than its rejection (FearlessException for the full frontend, Frontend.Fail for the compact frontend), or
- with the argument compact, the two frontends disagree:
  A: the full frontend accepts, the compact frontend rejects;
  B: the compact frontend accepts, the full frontend rejects;
  C: both accept, and the cores differ after FearlessTestBase.canon.
A program that both frontends reject is not a finding.
Each test fails with its findings, one for each report key.
The report key of a finding is its kind and its place:
the class, method and line that rejects, the first token where the two cores differ, or the class and method that throws the exception.
The program under a report key is shrunk (see Shrink below).

The tests:
- mutatedTestPrograms: the 'seeds', the string constants of the test classes that look like programs (Seeds),
  each with 9 mutants of 1 to 3 text mutations (Mutations): deleted characters, an inserted token, a copied slice,
  a slice of another seed, a swapped capability, a swapped name.
- underAnnotatedTestPrograms: the seeds with annotations, each with 9 mutants that drop 1 to 4 annotations:
  type arguments of calls, heads of literals, parameter types, return types, capabilities.
- generatedPrograms: 6000 programs generated from the grammar Ast (Gen, printed by Source),
  then 40000 mutants, each replacing one position of an accepted program with a new generated value (Trees).
  The mutants are made in batches of 500; the accepted mutants of a batch are mutated in the next batches.
  An accepted mutant whose core holds a triple of tokens that no earlier accepted program had is mutated three times as often.
  Most mutants differ from an accepted program in one place, so most of them are accepted too.
- LibraryTest.standardLibrary: the package base of the standard library, with the full frontend and, with the argument compact, also with the compact frontend,
  whose cores must be the same declaration by declaration; then every single-package project of the folder integrationTests of the standard library, compiled against that base.
  Each project also has 10 mutants that drop 1 to 4 type arguments of calls or heads of literals in one of its files.
  The scripts give the folder of the standard library to the tests as the property standardLibrary.
- writingTheInferredTypesKeepsTheCore: the programs of the first two tests, with the types the full frontend infers written in the source (InferredTypes).
  The full frontend must accept the written program and print the same core.

The two frontends compile the programs of a test in parallel; the findings, the summary and the shrinking follow the order of the programs, so a report does not depend on the threads.
Every test prints a summary line: the number of programs, how many of them the full frontend accepts,
how many distinct triples of consecutive tokens the cores of the accepted programs hold (a measure of their variety),
and the three most frequent places where the full frontend rejects.

Gen:
A record is built by its canonical constructor, with a generated value for each component.
A sealed interface is built as one of its permitted records, chosen at random in proportion to their @Weight (1 when absent).
Past the maximum depth, Gen chooses only among the leaf records: the records without a component of a sealed type.
@Size bounds the size of a list; @OneOf lists the values of a string, and a repeated value is chosen more often.

Source:
A program is the helpers Id and Box[X], then the declarations A, B, C and D; each can implement the declarations before it,
and one of Box[A], Box[B] and Box of itself.
Methods are named by position, .m, .n, # and .k; parameters are named x0, x1, ... in the order they are printed.
Source also knows base.Bool, base.True, base.False, base.Nat and 5, with the methods .not, .and, .or, & and +, *:
a call on a receiver of one of these types calls one of their methods, and the values base.Void, base.True, base.False and 5 can replace a body.
A parameter reference names a variable in scope, the innermost first.
A method omits its types only when a supertype, or the head of its literal, has a method in the same position;
the method then takes the arity and the capability of that method.
The type name Self stands for the declaration that holds it, also inside Box[Self].
The capabilities readH and mutH are written only in types; a method is written without iso, readH and mutH.
A typed method can have a generic X1, X2, ... (one more for each enclosing generic method); the type name X stands for the innermost one, or for the declaration when there is none.
Inside a literal with a self name, this stands for the self name.
A literal writes its self name only when its methods use it.
Source knows the type of some expressions: this, the parameters with a type, the type names, the calls of a method with a known result, the literals with a head.
When the type of a method body is known and is not a subtype of the result type of the method, or the body is a parameter of unknown type,
Source writes instead a value of the result type: one of the values above, a declaration without abstract methods implementing that type, or a function returning such a value.
A literal with a head also implements the abstract methods of the head that its methods do not implement, when Source can write a value of their result type.
When the type of the receiver of a call is known, the call has the arity of the method, and each argument is written as a method body of the type of its parameter.
A call writes its type argument only when its method is known to have a generic; the helper Id has the generic method #.

Shrink:
A generated program is first shrunk as a tree: at each position, Shrink tries a list without one element,
a subtree of the same type, a leaf, false, the first enum constant, the first string of @OneOf.
Every program is then shrunk as text: Shrink deletes runs of tokens, from half of the tokens down to one token.
A shrinking step is kept when the program keeps the same report key; a shrinking makes at most 2000 attempts.
A program is shrunk only when its report key is new, or when it is shorter than the program kept for that key.
A project of the standard library is shrunk file by file, each file as text, with at most 300 attempts for each file.
