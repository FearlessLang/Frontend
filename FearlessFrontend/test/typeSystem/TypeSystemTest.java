package typeSystem;

import java.util.List;
import org.junit.jupiter.api.Test;

public class TypeSystemTest extends testUtils.FearlessTestBase{
  static void ok(List<String> input){ typeOk(input); }
  static void ok(String head,List<String> input){ typeOk(head, input); }
  static void fail(String expected, List<String> input){ typeFail(expected, input); }
  static void fail(String expected, String head, List<String> input){ typeFail(expected, head, input); }
  static void failExt(String expected, List<String> input){ typeFailExt(expected, input); }
   
@Test void tsMiniOk(){ok(List.of("""
A:{.foo123:A->this.foo123}
"""));}
@Test void tsMiniFail(){fail("""
002| A:{.foo123:A->this.ba}
   |    -----------~~~~^^^^

While inspecting ".foo123" line 2
This call to method ".ba" can not typecheck.
Method ".ba" is not declared on type "A".

Available methods on type "A":
-       .foo123:A

Compressed relevant code with inferred types: (compression indicated by `-`)
this.ba
""",List.of("""
A:{.foo123:A->this.ba}
"""));}
//--------------
//--------------
//--------------
@Test void typeNotWellKinded_genericInstantiationViolatesBounds(){fail("""
004| User:{ imm .m(a:imm A[mut B]):base.Void; }
   | --------------------^^^^^^^^--------------

While inspecting type declaration "User"
The type "A[mut B]" is invalid.
Type argument 1 ("mut B") does not satisfy the bounds
for type parameter "X" in "A[_]".
Here "X" can only use capabilities "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
User:{.m(A[mut B]):-.Void}
""", List.of("""
A[X:imm]:{}
B:{}
User:{ imm .m(a:imm A[mut B]):base.Void; }
"""));}

@Test void typeNotWellKinded_secondTypeArgViolatesBoundsInParamType(){fail("""
005| User:{ imm .m(a:imm A[imm B,mut C]):base.Void; }
   | --------------------^^^^^^^^^^^^^^--------------

While inspecting type declaration "User"
The type "A[B,mut C]" is invalid.
Type argument 2 ("mut C") does not satisfy the bounds
for type parameter "Y" in "A[_,_]".
Here "Y" can only use capabilities "iso" or "read".

Compressed relevant code with inferred types: (compression indicated by `-`)
User:{.m(A[B,mut C]):-.Void}
""", List.of("""
A[X:imm,Y:read,iso]:{}
B:{}
C:{}
User:{ imm .m(a:imm A[imm B,mut C]):base.Void; }
"""));}

@Test void typeNotWellKinded_nestedInnerGenericViolatesBounds(){fail("""
005| User:{ imm .m(a:imm A[B[mut C]]):base.Void; }
   | ----------------------^^^^^^^^---------------

While inspecting type declaration "User"
The type "B[mut C]" is invalid.
Type argument 1 ("mut C") does not satisfy the bounds
for type parameter "Y" in "B[_]".
Here "Y" can only use capabilities "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
User:{.m(A[B[mut C]]):-.Void}
""", List.of("""
A[X:imm]:{}
B[Y:imm]:{}
C:{}
User:{ imm .m(a:imm A[B[mut C]]):base.Void; }
"""));}

@Test void typeNotWellKinded_literalSupertypeViolatesBounds(){fail("""
004| User:A[mut B]{ .foo(b:B):B->b;}
   | -----^^^^^^^^------------------

While inspecting type declaration "User"
The type "A[mut B]" is invalid.
Type argument 1 ("mut B") does not satisfy the bounds
for type parameter "X" in "A[_]".
Here "X" can only use capabilities "imm" or "mutH" or "readH".

Compressed relevant code with inferred types: (compression indicated by `-`)
User:A[mut B]{.foo(b:B):B->b}
""", List.of("""
A[X:imm,readH,mutH]:{}
B:{}
User:A[mut B]{ .foo(b:B):B->b;}
"""));}

@Test void typeNotWellKinded_methodReturnTypeViolatesBounds(){fail("""
004| User:{ imm .m(a:imm B):imm A[mut B]; }
   | ---------------------------^^^^^^^^---

While inspecting type declaration "User"
The type "A[mut B]" is invalid.
Type argument 1 ("mut B") does not satisfy the bounds
for type parameter "X" in "A[_]".
Here "X" can only use capabilities "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
User:{.m(B):A[mut B]}
""", List.of("""
A[X:imm]:{}
B:{}
User:{ imm .m(a:imm B):imm A[mut B]; }
"""));}

@Test void typeNotWellKinded_methodTypeArgViolatesBounds_simple(){fail("""
004| User:{ imm .m(a:imm A,b:imm B):base.Void->a.id[mut B](b); }
   |        -----------------------------------^^^^^^^^^^^^^^

While inspecting method call ".id(_)" > ".m(_,_)" line 4
The call to ".id(_)" is invalid.
Type argument 1 ("mut B") does not satisfy the bounds
for type parameter "X" in "A.id(_)".
Here "X" can only use capabilities "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
a.id[imm,mut B](b)
""", List.of("""
A:{ imm .id[X:imm](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:imm B):base.Void->a.id[mut B](b); }
"""));}

@Test void typeNotWellKinded_methodTypeArgSecondParamViolatesBounds(){fail("""
005| User:{ imm .m(a:imm A,b:imm B,c:imm C):base.Void->a.pair[imm B,mut C](b,c); }
   |        -------------------------------------------^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting method call ".pair(_,_)" > ".m(_,_,_)" line 5
The call to ".pair(_,_)" is invalid.
Type argument 2 ("mut C") does not satisfy the bounds
for type parameter "Y" in "A.pair(_,_)".
Here "Y" can only use capabilities "read".

Compressed relevant code with inferred types: (compression indicated by `-`)
a.pair[imm,B,mut C](b,c)
""", List.of("""
A:{ imm .pair[X:imm,Y:read](x:X,y:Y):base.Void->{} }
B:{}
C:{}
User:{ imm .m(a:imm A,b:imm B,c:imm C):base.Void->a.pair[imm B,mut C](b,c); }
"""));}

@Test void typeNotWellKinded_methodTypeArgNestedViolatesBounds(){fail("""
005| User:{ imm .m(a:imm A,b:imm B[C],c:imm C):base.Void->a.use[B[mut C]](b); }
   |        ----------------------------------------------~~~~~~^^^^^^^^~~~~

While inspecting method call ".use(_)" > ".m(_,_,_)" line 5
The type "B[mut C]" is invalid.
Type argument 1 ("mut C") does not satisfy the bounds
for type parameter "Y" in "B[_]".
Here "Y" can only use capabilities "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
a.use[imm,B[mut C]](b)
""", List.of("""
A:{ imm .use[X:imm](x:X):base.Void->{} }
B[Y:imm]:{}
C:{}
User:{ imm .m(a:imm A,b:imm B[C],c:imm C):base.Void->a.use[B[mut C]](b); }
"""));}

@Test void typeNotWellKinded_literalHeaderUsesTypeParamViolatingBounds(){fail("""
003| User[Y:read]:A[Y]{}
   | -------------^^^^--

While inspecting type declaration "User[_]"
The type "A[Y]" is invalid.
Type argument 1 ("Y") does not satisfy the bounds
for type parameter "X" in "A[_]".
Here "X" can only use capabilities "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
User[Y:read]:A[Y]{}
""", List.of("""
A[X:imm]:{}
User[Y:read]:A[Y]{}
"""));}

@Test void typeNotWellKinded_nestedTwiceInnerMostViolatesBounds(){fail("""
005| User:{ imm .m(x:imm A[B[mut C]]):base.Void; }
   | ----------------------^^^^^^^^---------------

While inspecting type declaration "User"
The type "B[mut C]" is invalid.
Type argument 1 ("mut C") does not satisfy the bounds
for type parameter "Y" in "B[_]".
Here "Y" can only use capabilities "read".

Compressed relevant code with inferred types: (compression indicated by `-`)
User:{.m(A[B[mut C]]):-.Void}
""", List.of("""
A[X:imm]:{}
B[Y:read]:{}
C:{}
User:{ imm .m(x:imm A[B[mut C]]):base.Void; }
"""));}

@Test void typeNotWellKinded_methodTypeArgOnTypeWithMultipleBounds(){fail("""
004| User:{ imm .m(a:imm A,b:imm B):base.Void->a.id[mut B](b); }
   |        -----------------------------------^^^^^^^^^^^^^^

While inspecting method call ".id(_)" > ".m(_,_)" line 4
The call to ".id(_)" is invalid.
Type argument 1 ("mut B") does not satisfy the bounds
for type parameter "X" in "A.id(_)".
Here "X" can only use capabilities "imm" or "read".

Compressed relevant code with inferred types: (compression indicated by `-`)
a.id[imm,mut B](b)
""", List.of("""
A:{ imm .id[X:imm,read](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:imm B):base.Void->a.id[mut B](b); }
"""));}


@Test void typeNotWellKinded_methodTypeArgOnTypeInfer(){fail("""
004| User:{ imm .m(a:imm A,b:imm B):base.Void->a.id(b); }
   |        -----------------------------------^^^^^^^

While inspecting method call ".id(_)" > ".m(_,_)" line 4
The call to ".id(_)" is invalid.
Type argument 1 ("B") does not satisfy the bounds
for type parameter "X" in "A.id(_)".
Here "X" can only use capabilities "mut" or "read".

Compressed relevant code with inferred types: (compression indicated by `-`)
a.id[imm,B](b)
""", List.of("""
A:{ imm .id[X:mut,read](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:imm B):base.Void->a.id(b); }
"""));}
//TODO: this used to print, hinting at some other issue in the compact printer 
//mut User:{.m(A,B):-Void->{a.id[mut B](b)}} ?? why mut here? Why meth sig printed as .m(A,B) with no par names
//but it prints correctly in typeNotWellKinded_literalSupertypeViolatesBounds,.. why??

@Test void typeNotWellKinded_methodTypeArgOnTypeInfer2(){fail("""
004| User:{ imm .m(a:imm A,b:imm B):read B->a.id(b); }
   |        --------------------------------^^^^^^^

While inspecting method call ".id(_)" > ".m(_,_)" line 4
The call to ".id(_)" is invalid.
Type argument 1 ("read B") does not satisfy the bounds
for type parameter "X" in "A.id(_)".
Here "X" can only use capabilities "iso" or "mut".

Compressed relevant code with inferred types: (compression indicated by `-`)
a.id[imm,read B](b)
""", List.of("""
A:{ imm .id[X:mut,iso](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:imm B):read B->a.id(b); }
"""));}

@Test void typeNotWellKinded_methodTypeArgOnTypeInferFromRetType(){ok(List.of("""
A:{ imm .id[X:mut,read](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:imm B):read B->a.id(b); }
"""));}
@Test void typeNotWellKinded_twistToPassInfer(){ok(List.of("""
A:{ imm .id[X:mut,read](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:mut B):read B->a.id(b); }
"""));}


@Test void methodImplementationDeadCode_readLiteralHasMutMethod(){ fail("""
004|   imm .m():read B->read BB:B{
005|     mut .h:base.Void->base.Void{};
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
006|   }

While inspecting object literal "read BB" > ".m" line 4
The method "BB.h" is dead code.
The object literal "BB" is "read", so it will never be seen as "mut".
But it implements method "mut .h", which requires a "mut" receiver.

Compressed relevant code with inferred types: (compression indicated by `-`)
read BB:B{mut .h:-.Void->-.Void{}}
""", List.of("""
B:{ mut .h:base.Void; }
User:{
  imm .m():read B->read BB:B{
    mut .h:base.Void->base.Void{};
  }
}
"""));}
@Test void methodImplementationDeadCode_immLiteralHasMutMethod(){ fail("""
004|   imm .m():imm B->imm BB:B{
005|     mut .h:base.Void->base.Void{};
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
006|   }

While inspecting object literal "BB" > ".m" line 4
The method "BB.h" is dead code.
The object literal "BB" is "imm", so it will never be seen as "mut".
But it implements method "mut .h", which requires a "mut" receiver.

Compressed relevant code with inferred types: (compression indicated by `-`)
BB:B{mut .h:-.Void->-.Void{}}
""", List.of("""
B:{ mut .h:base.Void; }
User:{
  imm .m():imm B->imm BB:B{
    mut .h:base.Void->base.Void{};
  }
}
"""));}

@Test void notAffineIso_usedDirectlyTwice_sameCall(){ fail("""
005| User:{ imm .bad(x:iso B):Unit->Use2#(x,x); }
   |        ------------------------------^^~~

While inspecting ".bad(_)" line 5
Iso parameter "x" violates the single-use rule in method "User.bad(_)" (line 5).
It is used directly 2 times.
Iso parameters can be used directly at most once.
Allowed: capture into object literals as "imm", or use directly once.

Compressed relevant code with inferred types: (compression indicated by `-`)
Use2#(x,x)
""", List.of("""
Unit:{}
B:{}
Use2:{ #(a:iso B,b:iso B):Unit->Unit{} }
User:{ imm .bad(x:iso B):Unit->Use2#(x,x); }
"""));}

@Test void notAffineIso_usedDirectlyAndCaptured_literalArg(){ fail("""
008|   imm .bad(xyz:iso B):Unit->Mix#(xyz, imm KK:K{ imm .k:Unit->UseImm#(xyz); });
   |   -------------------------------^^^^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~----

While inspecting ".bad(_)" line 8
Iso parameter "xyz" violates the single-use rule in method "User.bad(_)" (line 8).
It is used directly and also captured into object literals.
An iso parameter must be either captured, or used directly once (but not both).
Allowed: capture into object literals as "imm", or use directly once.

Compressed relevant code with inferred types: (compression indicated by `-`)
Mix#(xyz,KK:K{.k:Unit->UseImm#(xyz)})
""", List.of("""
Unit:{}
B:{}
UseImm:{ #(b:imm B):Unit->Unit{} }
K:{ imm .k:Unit; }
Mix:{ #(a:iso B,k:imm K):Unit->Unit{} }
User:{
  imm .bad(xyz:iso B):Unit->Mix#(xyz, imm KK:K{ imm .k:Unit->UseImm#(xyz); });
}
"""));}

@Test void notAffineIso_usedDirectlyAndCaptured_twice_twoLiterals(){ fail("""
008|   imm .bad(x:iso B):Unit->Mix2#(x,
   |                                 ^^
009|     imm K1:K{ imm .k:Unit->UseImm#(x); },

While inspecting ".bad(_)" line 8
Iso parameter "x" violates the single-use rule in method "User.bad(_)" (line 8).
It is used directly and also captured into object literals.
An iso parameter must be either captured, or used directly once (but not both).
Allowed: capture into object literals as "imm", or use directly once.

Compressed relevant code with inferred types: (compression indicated by `-`)
Mix2#(x,K1:K{.k:Unit->UseImm#(x)},K2:K{.k:Unit->UseImm#(x)})
""", List.of("""
Unit:{}
B:{}
UseImm:{ #(b:imm B):Unit->Unit{} }
K:{ imm .k:Unit; }
Mix2:{ #(a:iso B,k1:imm K,k2:imm K):Unit->Unit{} }
User:{
  imm .bad(x:iso B):Unit->Mix2#(x,
    imm K1:K{ imm .k:Unit->UseImm#(x); },
    imm K2:K{ imm .k:Unit->UseImm#(x); }
  );
}
"""));}

@Test void methBodyWrongType_xWrongNominal_shortNames(){ fail("""
005|   imm .m(x:imm A):B->x;
   |   -------------------^^

While inspecting parameter "x" > ".m(_)" line 5
The body of method ".m(_)" of type declaration "User" is an expression returning "A".
Parameter "x" has type "A" instead of a subtype of "B".

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
User:{.m(x:A):B->x}
""", List.of("""
A:{}
B:{}
User:{
  imm .m(x:imm A):B->x;
}
"""));}

@Test void methBodyWrongType_xWrongNominal_longNames_indent(){ fail("""
005|   imm .veryLongMethodName(veryVeryLongParamName:imm Alpha):Beta->
006|     veryVeryLongParamName;
   |     ^^^^^^^^^^^^^^^^^^^^^^

While inspecting parameter "veryVeryLongParamName" > ".veryLongMethodName(_)" line 5
The body of method ".veryLongMethodName(_)" of type declaration "User" is an expression returning "Alpha".
Parameter "veryVeryLongParamName" has type "Alpha" instead of a subtype of "Beta".

See inferred typing context below for how type "Beta" was introduced: (compression indicated by `-`)
User:{.veryLongMethodName(veryVeryLongParamName:Alpha):Beta->veryVeryLongParamName}
""", List.of("""
Alpha:{}
Beta:{}
User:{
  imm .veryLongMethodName(veryVeryLongParamName:imm Alpha):Beta->
    veryVeryLongParamName;
}
"""));}

@Test void methBodyWrongType_callWrongType_namedCallee(){ fail("""
006|   imm .m():B->MakeA#({  }    );
   |   ------------^^^^^^^^^^^-----

While inspecting method call "#(_)" > ".m" line 6
The body of method ".m" of type declaration "User" is an expression returning "A".
Method call "MakeA#(_)" has type "A" instead of a subtype of "B".

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
User:{.m:B->MakeA#(-.Void)}
""", List.of("""
A:{}
B:{}
MakeA:{ #(u:base.Void):A->A{} }
User:{
  imm .m():B->MakeA#({  }    );
}
"""));}

@Test void methBodyWrongType_inferredContextShowsInferredGenericInstantiation(){fail("""
008|   imm .m():Car->Apply#(Person,{_->Foo});
   |   -----------------------------~~~^^^^-

While inspecting object literal instance of "Foo" > "#(_)" line 8 > ".m" line 8
Method "#(_)" inside the object literal instance of "F[_,_]" (line 8)
is implemented with an expression returning "Foo".
Object literal is of type "Foo" instead of a subtype of "Car".

See inferred typing context below for how type "Car" was introduced: (compression indicated by `-`)
User:{.m:Car->Apply#(Person,F[Person,Car]{#(Person):Car->Foo})}
""", List.of("""
Person:{}
Car:{}
Foo:{}
F[A:imm,B:imm]:{ #(a:imm A):B; }
Apply:{ #(p:imm Person, f:imm F[Person,Car]):Car->f#(p); }
User:{
  imm .m():Car->Apply#(Person,{_->Foo});
}
"""));} 
@Test void methBodyWrongType_callWrongType_nestedCall(){ fail("""
007|   imm .m():B->Wrap#(Mk#({}));
   |   ------------^^^^^^^^^^^^--

While inspecting method call "#(_)" > ".m" line 7
The body of method ".m" of type declaration "User" is an expression returning "A".
Method call "Wrap#(_)" has type "A" instead of a subtype of "B".

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
User:{.m:B->Wrap#(Mk#(-.Void))}
""", List.of("""
A:{}
B:{}
Mk:{ #(u:base.Void):A->A{} }
Wrap:{ #(a:A):A->a }
User:{
  imm .m():B->Wrap#(Mk#({}));
}
"""));}

@Test void methBodyWrongType_literalWrongType_namedLiteral(){ fail("""
005|   imm .m():B->imm AA:A{};
   |   ----------------^^^^^^

While inspecting object literal "AA" > ".m" line 5
The body of method ".m" of type declaration "User" is an expression returning "AA".
Object literal is of type "AA" instead of a subtype of "B".

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
User:{.m:B->AA:A{}}
""", List.of("""
A:{}
B:{}
User:{
  imm .m():B->imm AA:A{};
}
"""));}
@Test void methBodyWrongType_xWeakenedCapability_dueToCapture(){fail("""
005|   read .m(loooooong:mut A):mut A->
006|     read Get{ loooooong };
   |               ^^^^^^^^^

While inspecting parameter "loooooong" > ".get" line 6 > ".m(_)" line 5
Method ".get" inside the object literal instance of "read Get" (line 6)
is implemented with an expression returning "read A".
Parameter "loooooong" has type "read A" instead of a subtype of "mut A".
Note: the declared type "mut A" would instead be a valid subtype.
Capture adaptation trace:
"mut A" --setToRead(line 6)--> "read A".

See inferred typing context below for how type "mut A" was introduced: (compression indicated by `-`)
User:{read .m(loooooong:mut A):mut A->read Get{read .get:mut A->loooooong}}
""", List.of("""
A:{}
Get:{ read .get: mut A; }
User:{
  read .m(loooooong:mut A):mut A->
    read Get{ loooooong };
}
"""));}
@Test void methBodyWrongType_xWeakenedCapability_dueToCapture2(){fail("""
005|   read .m(loooooong:mut A):read Get->
006|     read Get{ loooooong };
   |               ^^^^^^^^^

While inspecting parameter "loooooong" > ".get" line 6 > ".m(_)" line 5
Method ".get" inside the object literal instance of "read Get" (line 6)
is implemented with an expression returning "read A".
Parameter "loooooong" has type "read A" instead of a subtype of "iso A".
Note: the declared type "mut A" also does not satisfy the requirement.
Capture adaptation trace:
"mut A" --setToRead(line 6)--> "read A".

See inferred typing context below for how type "iso A" was introduced: (compression indicated by `-`)
User:{read .m(loooooong:mut A):read Get->read Get{read .get:iso A->loooooong}}
""", List.of("""
A:{}
Get:{ read .get: iso A; }
User:{
  read .m(loooooong:mut A):read Get->
    read Get{ loooooong };
}
"""));}
@Test void regressionBadError(){fail("""
005|   read .m(loooooong:mut A):mut A->
006|     read Get{ loooooong };
   |               ^^^^^^^^^

While inspecting parameter "loooooong" > ".get" line 6 > ".m(_)" line 5
Method ".get" inside the object literal instance of "read Get" (line 6)
is implemented with an expression returning "read A".
Parameter "loooooong" has type "read A" instead of a subtype of "iso A".
Note: the declared type "mut A" also does not satisfy the requirement.
Capture adaptation trace:
"mut A" --setToRead(line 6)--> "read A".

See inferred typing context below for how type "iso A" was introduced: (compression indicated by `-`)
User:{read .m(loooooong:mut A):mut A->read Get{read .get:iso A->loooooong}}
""", List.of("""
A:{}
Get:{ read .get: iso A; }
User:{
  read .m(loooooong:mut A):mut A->
    read Get{ loooooong };
}
"""));}

@Test void methBodyWrongType_xWeakenedCapability_dueToCapture_chain(){fail("""
006|   read .m(loooooong:mut A):mut A->
007|     read Wrap{ mut Get{ loooooong } };
   |                ---------^^^^^^^^^--

While inspecting parameter "loooooong" > ".get" line 7 > ".wrap" line 7 > ".m(_)" line 6
Method ".get" inside the object literal instance of "mut Get" (line 7)
is implemented with an expression returning "A".
Parameter "loooooong" has type "imm A" instead of a subtype of "iso A".
Note: the declared type "mut A" also does not satisfy the requirement.
Capture adaptation trace:
"mut A" --setToRead(line 7)--> "read A" --strengthenToImm(line 7)--> "A".

See inferred typing context below for how type "iso A" was introduced: (compression indicated by `-`)
User:{read .m(loooooong:mut A):mut A->read Wrap{read .wrap:Get->mut Get{.get:iso A->loooooong}}}
""", List.of("""
A:{}
Get:{ imm .get: iso A; }
Wrap:{ read .wrap: imm Get; }
User:{
  read .m(loooooong:mut A):mut A->
    read Wrap{ mut Get{ loooooong } };
}
"""));
}

@Test void drop(){fail("""
008|   read .m(loooooong:mut A):mut A->Do2[mut A]#(
009|     Capture#({#():base.Void->Ignore#(loooooong)}),
   |               -----------------------^^^^^^^^^^
010|     loooooong
011|   );

While inspecting parameter "loooooong" > "#" line 9 > ".m(_)" line 8
parameter "loooooong" has type "mut A".
parameter "loooooong" can observe mutation; thus it can not be captured in the "imm" object literal instance of "G" (line 9).
Hint: capture an immutable copy instead, or move this use outside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
loooooong
""", List.of("""
A:{}
G:{ #(): base.Void; }
Ignore:{ #(x: read A): base.Void->{}; }
Capture:{#(g: G): base.Void->{}; }
Do2[X:imm,mut,read]: { #(v:base.Void, x:X):X->x; }
User:{
  read .m(loooooong:mut A):mut A->Do2[mut A]#(
    Capture#({#():base.Void->Ignore#(loooooong)}),
    loooooong
  );
}
"""));}

@Test void drop_hygienicMutH(){fail("""
008|   read .m(loooooong:mutH A):mutH A->Do2H[mutH A]#(
009|     Capture#({#():base.Void->Ignore#(loooooong)}),
   |               -----------------------^^^^^^^^^^
010|     loooooong
011|   );

While inspecting parameter "loooooong" > "#" line 9 > ".m(_)" line 8
parameter "loooooong" has type "mutH A".
The type of parameter "loooooong" is hygienic (readH or mutH)
and thus it can not be captured in the object literal instance of "G" (line 9).

Compressed relevant code with inferred types: (compression indicated by `-`)
loooooong
""", List.of("""
A:{}
G:{ #(): base.Void; }
Ignore:{ #(x: mutH A): base.Void->{}; }
Capture:{ #(g: G): base.Void->{}; }
Do2H[X:imm,mut,read,readH,mutH]: { #(v:base.Void, x:X):X->x; }
User:{
  read .m(loooooong:mutH A):mutH A->Do2H[mutH A]#(
    Capture#({#():base.Void->Ignore#(loooooong)}),
    loooooong
  );
}
""")); }

@Test void drop_hygienicMutH2(){fail("""
006|   read .m(loooooong:mutH A):imm G->
007|     {#():base.Void->IgnoreH#(loooooong)};
   |      ------------------------^^^^^^^^^^

While inspecting parameter "loooooong" > "#" line 7 > ".m(_)" line 6
parameter "loooooong" has type "mutH A".
The type of parameter "loooooong" is hygienic (readH or mutH)
and thus it can not be captured in the object literal instance of "G" (line 7).

Compressed relevant code with inferred types: (compression indicated by `-`)
loooooong
""", List.of("""
A:{}
G:{ #(): base.Void; }
IgnoreH:{ #(x: mutH A): base.Void->{}; }
User:{
  read .m(loooooong:mutH A):imm G->
    {#():base.Void->IgnoreH#(loooooong)};
}
""")); }
@Test void shouldPassViaInference(){ok(List.of("""
Bar:{}
Beer[X:imm,mut,read]:{ read .bar: Bar; }
Foo:{ read .m: Bar; }
User:{
  read .m[X:imm,mut,read](webeer:Beer[X]):read Foo->
    read Foo{ webeer.bar() };
}
""")); }

@Test void drop_ftv_notPropagatedIntoExplicitFoo(){fail("""
005|     read .m[X:imm,mut,read](beer:Beer[X]):read Foo->
006|       read Foo:{ read .m:Bar -> beer.bar() };
   |                  ---------------^^^^^-----

While inspecting parameter "beer" > ".m" line 6 > ".m(_)" line 5
parameter "beer" has type "Beer[X]".
parameter "beer" uses type parameters that are not propagated
into object literal "read Foo" (line 6) and thus it can not be captured.
Hint: change "Foo" by adding the missing type parameters: "Foo[...,...]"

Compressed relevant code with inferred types: (compression indicated by `-`)
beer
""", List.of("""
  Bar:{}
  Beer[X:imm,mut,read]:{ read .bar: Bar; }
  User:{
    read .m[X:imm,mut,read](beer:Beer[X]):read Foo->
      read Foo:{ read .m:Bar -> beer.bar() };
  }
""")); }

@Test void drop_hygienicsAllowedByTypeParam(){fail("""
003|   read .m[X:imm,mut,read,readH,mutH](beer:X):G[X]->
004|     G[X:imm,mut,read,readH,mutH]:{ read .get: X->beer; }
   |                                    --------------^^^^^

While inspecting parameter "beer" > ".get" line 4 > ".m(_)" line 3
parameter "beer" has type "X".
The type of parameter "beer" can be instantiated with hygienics (readH or mutH)
and thus it can not be captured in the object literal "G[_]" (line 4).

Compressed relevant code with inferred types: (compression indicated by `-`)
beer
""", List.of("""
User:{
  read .m[X:imm,mut,read,readH,mutH](beer:X):G[X]->
    G[X:imm,mut,read,readH,mutH]:{ read .get: X->beer; }
}
""")); }

@Test void receiverIsTypeParam(){fail("""
003|   .m[X:**](x:X):X->x.foo;
   |   -----------------~^^^^^

While inspecting ".m(_)" line 3
This call to method ".foo" can not typecheck.
The receiver is of type "X". This is a type parameter.
Type parameters cannot be receivers of method calls.

See inferred typing context below for how type "X" was introduced: (compression indicated by `-`)
User:{.m[X:**](x:X):X->x.foo}
""", List.of("""
User:{
  .m[X:**](x:X):X->x.foo;
}
""")); }
//-----------
@Test void methodOverrideSignatureMismatchGenericBounds(){ failExt("""
In file: [###]/in_memory0.fear

004| Current:Parent2{ imm .id[X:imm,read](x:imm X):base.Void; }
   |                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Current"
Invalid method implementation for "Current.id(_)".
The local declaration uses different capability bounds than the supertypes for type parameter 1 of ".id(_)".
Local: "X:imm,read".
From supertypes: "-:imm".
The parameter name may differ; only the position matters.
Change the local bounds to match the supertypes, or adjust the supertypes.
Error 9 WellFormedness
""", List.of("""
P:{}
Parent2:{ imm .id[X:imm](x:imm X):base.Void; }
Current:Parent2{ imm .id[X:imm,read](x:imm X):base.Void; }
"""));}

@Test void methodOverrideSignatureMismatchGenericBoundsArity(){ failExt("""
In file: [###]/in_memory0.fear

004| Sub:Sup{ imm .f[X:imm,Y:imm](x:imm X):base.Void; }
   |          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Sub"
Invalid method implementation for "Sub.f(_)".
The method ".f(_)" declares 2 type parameter(s), but supertypes declare 1.
Local declaration: "[X:imm, Y:imm]".
From supertypes: "[-:imm]".
Change the local number of type parameters to 1, or adjust the supertypes.
Error 9 WellFormedness
""", List.of("""
P:{}
Sup:{ imm .f[X:imm](x:imm X):base.Void; }
Sub:Sup{ imm .f[X:imm,Y:imm](x:imm X):base.Void; }
"""));}

@Test void methodOverrideSignatureMismatchContravariance(){ fail("""
004| Current:Parent{ imm .g(x:imm P):base.Void; }
   | ----------------^^^^^^^^^^^^^^^^^^^^^^^^^---

While inspecting type declaration "Current"
Invalid method signature overriding for "Current.g(_)".
The method ".g(_)" accepts parameter 1 of type "P".
But "Parent.g(_)" requires "read P", which is not a subtype of "P".
It is instead a supertype: you are strenghtening the parameter instead of weakening it.

Compressed relevant code with inferred types: (compression indicated by `-`)
Current:Parent{.g(P):-.Void}
""", List.of("""
P:{}
Parent:{ imm .g(x:read P):base.Void; }
Current:Parent{ imm .g(x:imm P):base.Void; }
"""));}

@Test void methodOverrideSignatureMismatchCovariance(){ fail("""
004| Sub:Sup{ imm .h():read P; }
   | ---------^^^^^^^^^^^^^^^---

While inspecting type declaration "Sub"
Invalid method signature overriding for "Sub.h".
The method ".h" returns type "read P".
But "Sup.h" returns type "P", which is not a supertype of "read P".
It is instead a subtype: you are weakening the result instead of strenghtening it.

Compressed relevant code with inferred types: (compression indicated by `-`)
Sub:Sup{.h:read P}
""", List.of("""
P:{}
Sup:{ imm .h():imm P; }
Sub:Sup{ imm .h():read P; }
""")); }

@Test void callableMethodStillAbstract_missingRequiredMethod_anonLiteral(){ fail("""
007|   imm .m():Sup->Sup{ imm .h:base.Void->base.Void{} }
   |   --------------^^^^--------------------------------

While inspecting object literal instance of "Sup" > ".m" line 7
This object literal is missing a required method.
Missing: "imm .k".
Required by: "Sup".
Hint: add an implementation for ".k" inside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
Sup{.h:-.Void->-.Void{}}
""", List.of("""
Sup:{
  imm .h:base.Void;
  imm .k:base.Void;
}
User:{
  imm .m():Sup->Sup{ imm .h:base.Void->base.Void{} }
}
"""));}

@Test void callableMethodStillAbstract_missingRequiredMethod_namedLiteral(){ fail("""
007|   imm .m():Sup->Bad:Sup{ imm .h:base.Void->base.Void{} }
   |   --------------^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal "Bad" > ".m" line 7
This object literal is missing a required method.
Missing: "imm .k".
Required by: "Sup".
Hint: add an implementation for ".k" inside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
Bad:Sup{.h:-.Void->-.Void{}}
""", List.of("""
Sup:{
  imm .h:base.Void;
  imm .k:base.Void;
}
User:{
  imm .m():Sup->Bad:Sup{ imm .h:base.Void->base.Void{} }
}
"""));}


@Test void methodNotDeclared_noSuchName_typeHasNoMethods(){fail("""
004|   read .m(e:Empty):base.Void->
005|     e.nope();
   |     -^^^^^^

While inspecting ".m(_)" line 4
This call to method ".nope" can not typecheck.
Method ".nope" is not declared on type "Empty".
The type "Empty" does not have any methods.

Compressed relevant code with inferred types: (compression indicated by `-`)
e.nope
""", List.of("""
Empty:{}
User:{
  read .m(e:Empty):base.Void->
    e.nope();
}
""")); }

@Test void methodNotDeclared_noSuchName_didYouMean(){fail("""
008|   read .m(o:Ops):base.Void->
009|     read Runner{ o.sise() };
   |                  ~^^^^^^-

While inspecting ".run" line 9 > ".m(_)" line 8
This call to method ".sise" can not typecheck.
Method ".sise" is not declared on type "Ops".
Did you mean ".size" ?

Available methods on type "Ops":
-  read .sign:base.Void
-  read .size:base.Void

Compressed relevant code with inferred types: (compression indicated by `-`)
o.sise
""", List.of("""
Ops:{
  read .size: base.Void->{};
  read .sign: base.Void->{};
}
Runner:{ read .run: base.Void; }
User:{
  read .m(o:Ops):base.Void->
    read Runner{ o.sise() };
}
""")); }
@Test void methodNotDeclared_noSuchName_listAvailable(){fail("""
008|   read .m(o:Ops):base.Void->
009|     o.xyzzy();
   |     -^^^^^^^

While inspecting ".m(_)" line 8
This call to method ".xyzzy" can not typecheck.
Method ".xyzzy" is not declared on type "Ops".

Available methods on type "Ops":
-  read .alpha:base.Void
-  read .beta:base.Void
-  read .gamma:base.Void

Compressed relevant code with inferred types: (compression indicated by `-`)
o.xyzzy
""", List.of("""
Ops:{
  read .alpha: base.Void->{};
  read .beta: base.Void->{};
  read .gamma: base.Void->{};
}
User:{
  read .m(o:Ops):base.Void->
    o.xyzzy();
}
""")); }

@Test void methodNotDeclared_noSuchName_listAvailable_useVoid(){fail("""
In file: [###]/in_memory0.fear

008|   read .m(o:Ops):base.Void->
009|     o.xyzzy();
   |     -^^^^^^^

While inspecting ".m(_)" line 8
This call to method ".xyzzy" can not typecheck.
Method ".xyzzy" is not declared on type "Ops".

Available methods on type "Ops":
-  read .alpha:Woid
-  read .beta:Woid
-  read .gamma:Woid

Compressed relevant code with inferred types: (compression indicated by `-`)
o.xyzzy
Error 10 TypeError
""","role app000; use base.Void as Woid;", List.of("""
Ops:{
  read .alpha: Woid->{};
  read .beta:  base.Void->{};
  read .gamma: base.Void->{};
}
User:{
  read .m(o:Ops):base.Void->
    o.xyzzy();
}
""")); }


@Test void methodNotDeclared_wrongArity_listsAvailableArities(){fail("""
008|   read .m(m:Mixer, a:A):A->
009|     m.mix(a, a, a);
   |     -^^^^^--------

While inspecting ".m(_,_)" line 8
This call to method ".mix(_,_,_)" can not typecheck.
There is a method ".mix" on type "Mixer",
but with different number of arguments.
This call supplies 3, but available methods take 1 or 2.

Compressed relevant code with inferred types: (compression indicated by `-`)
m.mix(a,a,a)
""", List.of("""
A:{}
Mixer:{
  read .mix(x:A):A->x;
  read .mix(x:A, y:A):A->x;
}
User:{
  read .m(m:Mixer, a:A):A->
    m.mix(a, a, a);
}
""")); }
@Test void methodNotDeclared_wrongReceiverRc_mutNeedsMutButOnlyReadExists(){fail("""
007|   mut .m(z:mut Z, a:A):A->
008|     z.zap[mut](a);
   |     -^^^^^-------

While inspecting ".m(_,_)" line 7
This call to method ".zap(_)" can not typecheck.
".zap(_)" exists on type "Z", but not with the requested capability.
This call requires the existence of a "mut" method.
Available capabilities for this method: "read".

Compressed relevant code with inferred types: (compression indicated by `-`)
z.zap[mut](a)
""", List.of("""
A:{}
Z:{
  read .zap(x:A):A->x;
}
User:{
  mut .m(z:mut Z, a:A):A->
    z.zap[mut](a);
}
""")); }
@Test void methodTArgsArityError_oneLessThanNeeded(){fail("""
008|   read .m(p:Pairer,a:mut A,b:mut B):mut A->
009|     p.pair[mut A](a,b);
   |     -^^^^^^-----------

While inspecting ".m(_,_,_)" line 8
This call to method "Pairer.pair(_,_)" can not typecheck.
Wrong number of type arguments for ".pair(_,_)".
This method expects 2 type arguments, but this call provides 1 type argument.

Compressed relevant code with inferred types: (compression indicated by `-`)
p.pair[read,mut A](a,b)
""", List.of("""
A:{}
B:{}
Pairer:{
  read .pair[X:imm,mut,read,Y:imm,mut,read](x:X,y:Y):X->x;
}
User:{
  read .m(p:Pairer,a:mut A,b:mut B):mut A->
    p.pair[mut A](a,b);
}
"""));}

@Test void methodTArgsArityError_twoMoreThanNeeded(){fail("""
009|   read .m(i:Id,a:mut A):mut A->
010|     i.id[mut A,mut B,mut C](a);
   |     -^^^^---------------------

While inspecting ".m(_,_)" line 9
This call to method "Id.id(_)" can not typecheck.
Wrong number of type arguments for ".id(_)".
This method expects 1 type argument, but this call provides 3 type arguments.

Compressed relevant code with inferred types: (compression indicated by `-`)
i.id[read,mut A,mut B,mut C](a)
""", List.of("""
A:{}
B:{}
C:{}
Id:{
  read .id[X:imm,mut,read](x:X):X->x;
}
User:{
  read .m(i:Id,a:mut A):mut A->
    i.id[mut A,mut B,mut C](a);
}
"""));}

@Test void rcvBlocksCall(){fail("""
005|   read .m(a:A):A->
006|     this.zap(a);
   |     ----^^^^^--

While inspecting ".m(_)" line 5
This call to method "User.zap(_)" can not typecheck.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "mut" or "iso" or "mutH".

Receiver required by each promotion:
- "mut" (As declared)
- "iso" (Strengthen result, Strengthen hygienic result, Allow readH arguments, Allow mutH argument 1)
- "mutH" (Allow mutH receiver)

Compressed relevant code with inferred types: (compression indicated by `-`)
this.zap[mut](a)
""", List.of("""
A:{}
User:{
  mut .zap(x:A):A->x;
  read .m(a:A):A->
    this.zap(a);
}
""")); }
//---------
@Test void hopelessArg_wrongNominal_suppressesPromotionsAndReason(){fail("""
006|   .f(aaaa:mut B):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa));}
   |                                    -------------~~~~^^~~~~~~~~~~~~~-

While inspecting ".foo" line 6 > ".f(_)" line 6
This call to method "Need#(_)" can not typecheck.
Argument 1 has type "read B".
That is not a subtype of "mut A".

Compressed relevant code with inferred types: (compression indicated by `-`)
-#(AsRead#(aaaa))
""",List.of("""
B:{}
Need:{ #(a:mut A):B->B{} }
AsRead:{ #(x:read B):read B->x }
A:{
  .f(aaaa:mut B):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa));}
}
"""));}

@Test void hopelessArg_calls_pArgHasType_baselineConsistent(){fail("""
006|   .f(aaaa:mut A):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa));}
   |                                    -------------~~~~^^~~~~~~~~~~~~~-

While inspecting ".foo" line 6 > ".f(_)" line 6
This call to method "Need#(_)" can not typecheck.
Argument 1 has type "read A".
That is not a subtype of any of "mut A" or "iso A" or "mutH A".
Method call "AsRead#(_)" has type "read A" instead of a subtype of "mut A".

Type required by each promotion:
- "mut A"  (As declared)
- "iso A"  (Strengthen result, Strengthen hygienic result, Allow readH arguments, Allow mutH receiver)
- "mutH A"  (Allow mutH argument 1)

See inferred typing context below for how type "mut A" was introduced: (compression indicated by `-`)
A:{.f(aaaa:mut A):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa))}}
""",List.of("""
B:{}
Need:{ #(a:mut A):B->B{} }
AsRead:{ #(x:read A):read A->x }
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa));}
}
"""));}

@Test void noVar2Fail_viewpointAdaptation_reasonShown(){fail("""
005|   .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(aaaa);}
   |                                    -------------~~~~^^~~~~~

While inspecting ".foo" line 5 > ".f(_)" line 5
This call to method "Skip#(_)" can not typecheck.
Argument 1 has type "read A".
That is not a subtype of any of "mut A" or "iso A" or "mutH A".
Parameter "aaaa" has type "read A" instead of a subtype of "mut A".
Note: the declared type "mut A" would instead be a valid subtype.
Capture adaptation trace:
"mut A" --setToRead(line 5)--> "read A".

Type required by each promotion:
- "mut A"  (As declared)
- "iso A"  (Strengthen result, Strengthen hygienic result, Allow readH arguments, Allow mutH receiver)
- "mutH A"  (Allow mutH argument 1)

Compressed relevant code with inferred types: (compression indicated by `-`)
Skip#[imm,mut A](aaaa)
""",List.of("""
Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(aaaa);}
}
"""));}

@Test void badDeepCall_inferenceNestedGenericCall_explained(){fail("""
006|   .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(Id#(aaaa));}
   |                                    -------------------~~^^~~~~~-

While inspecting ".foo" line 6 > ".f(_)" line 6
This call to method "Id#(_)" can not typecheck.
Argument 1 has type "read A".
That is not a subtype of any of "mut A" or "iso A" or "mutH A".
Parameter "aaaa" has type "read A" instead of a subtype of "mut A".
Note: the declared type "mut A" would instead be a valid subtype.
Capture adaptation trace:
"mut A" --setToRead(line 6)--> "read A".

Type required by each promotion:
- "mut A"  (As declared)
- "iso A"  (Strengthen result, Strengthen hygienic result, Allow readH arguments, Allow mutH receiver)
- "mutH A"  (Allow mutH argument 1)

Compressed relevant code with inferred types: (compression indicated by `-`)
Id#[imm,mut A](aaaa)
""",List.of("""
Skip:{#[X:**](X):B->B}
Id:{#[X:**](x:X):X->x}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(Id#(aaaa));}
}
"""));}

@Test void argFromGenericCall_boundForcesRead_inferenceHintBadBounds(){fail("""
006|   .f(aaaa:mut A):B->
007|     Need#(IdRO#(aaaa));
   |           ^^^^^^^^^^^

While inspecting method call "#(_)" > ".f(_)" line 6
The call to "#(_)" is invalid.
Type argument 1 ("mut A") does not satisfy the bounds
for type parameter "X" in "IdRO#(_)".
Here "X" can only use capabilities "imm" or "read".

Compressed relevant code with inferred types: (compression indicated by `-`)
IdRO#[imm,mut A](aaaa)
""",List.of("""
B:{}
Need:{ #(a:mut A):B->B{} }
IdRO:{ #[X:imm,read](x:X):X->x }
A:{
  .f(aaaa:mut A):B->
    Need#(IdRO#(aaaa));
}
"""));}

@Test void argFromGenericCall_boundForcesRead_inferenceHint(){fail("""
006|   .f(aaaa:mut A):B->
007|     Need#(IdRO#[read A](aaaa));
   |     ----^^-------------------

While inspecting ".f(_)" line 6
This call to method "Need#(_)" can not typecheck.
Argument 1 has type "read A".
That is not a subtype of any of "mut A" or "iso A" or "mutH A".
Method call "IdRO#(_)" has type "read A" instead of a subtype of "mut A".

Type required by each promotion:
- "mut A"  (As declared)
- "iso A"  (Strengthen result, Strengthen hygienic result, Allow readH arguments, Allow mutH receiver)
- "mutH A"  (Allow mutH argument 1)

See inferred typing context below for how type "mut A" was introduced: (compression indicated by `-`)
A:{.f(aaaa:mut A):B->Need#(IdRO#[imm,read A](aaaa))}
""",List.of("""
B:{}
Need:{ #(a:mut A):B->B{} }
IdRO:{ #[X:imm,read](x:X):X->x }
A:{
  .f(aaaa:mut A):B->
    Need#(IdRO#[read A](aaaa));
}
"""));}

@Test void argFromObjectLiteral_defaultImm_hintToAnnotate(){fail("""
006|   .f:B->
007|     Need#(A{});
   |     ----^^--

While inspecting ".f" line 6
This call to method "Need#(_)" can not typecheck.
Argument 1 has type "imm A".
That is not a subtype of any of "mut A" or "iso A" or "mutH A".
Object literal is of type "imm A" instead of a subtype of "mut A".
Hint: write "mut A{...}" if you need a "mut" object literal.

Type required by each promotion:
- "mut A"  (As declared)
- "iso A"  (Strengthen result, Strengthen hygienic result, Allow readH arguments, Allow mutH receiver)
- "mutH A"  (Allow mutH argument 1)

Compressed relevant code with inferred types: (compression indicated by `-`)
Need#(A{})
""",List.of("""
B:{}
Need:{ #(a:mut A):B->B{} }
A:{}
User:{
  .f:B->
    Need#(A{});
}
"""));}

@Test void promotionsDisagree_mergesIdenticalBlocks_readH_mutH(){fail("""
004|   .caller(x:readH A, y:mutH A):A->this.f(x,y);
   |   --------------------------------~~~~^^^~~~~

While inspecting ".caller(_,_)" line 4
This call to method ".f(_,_)" can not typecheck.
Each argument is compatible with at least one promotion, but no single promotion fits all arguments.

Compatible promotions by argument:
- Argument 1 has type "readH A" and is compatible with: Allow readH arguments, Allow mutH argument 1.
- Argument 2 has type "mutH A" and is compatible with: Allow mutH argument 2.

Promotion failures:
- Argument 1 fails:    As declared
  Parameter "x" has type "readH A" instead of a subtype of "read A".
- Argument 1 fails:    Strengthen result, Strengthen hygienic result, Allow mutH receiver, Allow mutH argument 2
  Parameter "x" has type "readH A" instead of a subtype of "imm A".
- Argument 2 fails:    Allow readH arguments, Allow mutH argument 1
  Parameter "y" has type "mutH A" instead of a subtype of "iso A".

Compressed relevant code with inferred types: (compression indicated by `-`)
this.f(x,y)
""",List.of("""
A:{
  .f(a:read A, b:mut A):A->this;
  .caller(x:readH A, y:mutH A):A->this.f(x,y);
}
"""));}

@Test void promotionsDisagree_dontOverMergeAcrossDifferentArgs_mutH_mutH(){fail("""
004|   .caller(x:mutH A, y:mutH A):A->this.f(x,y);
   |   -------------------------------~~~~^^^~~~~

While inspecting ".caller(_,_)" line 4
This call to method ".f(_,_)" can not typecheck.
Each argument is compatible with at least one promotion, but no single promotion fits all arguments.

Compatible promotions by argument:
- Argument 1 has type "mutH A" and is compatible with: Allow mutH argument 1.
- Argument 2 has type "mutH A" and is compatible with: Allow mutH argument 2.

Promotion failures:
- Argument 1 fails:    As declared
  Parameter "x" has type "mutH A" instead of a subtype of "mut A".
- Argument 1 fails:    Strengthen result, Strengthen hygienic result, Allow readH arguments, Allow mutH receiver, Allow mutH argument 2
  Parameter "x" has type "mutH A" instead of a subtype of "iso A".
- Argument 2 fails:    Allow mutH argument 1
  Parameter "y" has type "mutH A" instead of a subtype of "iso A".

Compressed relevant code with inferred types: (compression indicated by `-`)
this.f(x,y)
""",List.of("""
A:{
  .f(a:mut A, b:mut A):A->this;
  .caller(x:mutH A, y:mutH A):A->this.f(x,y);
}
"""));}

@Test void tsOkIndirect(){ok(List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foo123;}
"""));}

@Test void tsOkIndirectFail1(){fail("""
002| A:{.foo123:A->this.foo123; .bar:A->this.foO123; mut .bob(a:A):A}
   |                            --------~~~~^^^^^^^^

While inspecting ".bar" line 2
This call to method ".foO123" can not typecheck.
Method ".foO123" is not declared on type "A".
Did you mean ".foo123" ?

Available methods on type "A":
-       .bar:A
-   mut .bob(A):A
-       .foo123:A

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foO123
""",List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foO123; mut .bob(a:A):A}
"""));}

@Test void tsOkIndirectFail2(){fail("""
002| A:{.foo123:A->this.foo123; .bar:A->this.foo23;}
   |                            --------~~~~^^^^^^^

While inspecting ".bar" line 2
This call to method ".foo23" can not typecheck.
Method ".foo23" is not declared on type "A".
Did you mean ".foo123" ?

Available methods on type "A":
-       .bar:A
-       .foo123:A

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo23
""",List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foo23;}
"""));}

@Test void tsOkIndirectFail3(){fail("""
002| A:{.foo123:A->this.foo123; .bar:A->this.foo1123;}
   |                            --------~~~~^^^^^^^^^

While inspecting ".bar" line 2
This call to method ".foo1123" can not typecheck.
Method ".foo1123" is not declared on type "A".
Did you mean ".foo123" ?

Available methods on type "A":
-       .bar:A
-       .foo123:A

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo1123
""",List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foo1123;}
"""));}

@Test void tsOkIndirectFail4(){fail("""
004|   .bar:A->this.foo123(this);
   |   --------~~~~^^^^^^^^~~~~~

While inspecting ".bar" line 4
This call to method ".foo123(_)" can not typecheck.
There is a method ".foo123" on type "A",
but with different number of arguments.
This call supplies 1, but available methods take 0 or 3.

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo123(this)
""",List.of("""
A:{
  .foo123:A->this.foo123; 
  .bar:A->this.foo123(this);
  .foo123(A,A,A):A->this.foo123;
  }
"""));}

@Test void tsOkIndirectFail4spaces(){fail("""
004|   .bar:A->this.foo123(this      );
   |   --------~~~~^^^^^^^^~~~~-------

While inspecting ".bar" line 4
This call to method ".foo123(_)" can not typecheck.
There is a method ".foo123" on type "A",
but with different number of arguments.
This call supplies 1, but available methods take 0 or 3.

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo123(this)
""",List.of("""
A:{
  .foo123:A->this.foo123; 
  .bar:A->this.foo123(this      );
  .foo123(A,A,A):A->this.foo123;
  }
"""));}
@Test void tsOkIndirectFail5(){fail("""
002| A:{.foo123:A->this.foo123; mut .bar:A->this.foo123;}
   |                            ------------~~~~^^^^^^^^

While inspecting ".bar" line 2
This call to method "A.foo123" can not typecheck.
The receiver (the expression before the method name) has capability "mut".
This call requires a receiver with capability "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo123
""",List.of("""
A:{.foo123:A->this.foo123; mut .bar:A->this.foo123;}
"""));}
@Test void tsOkIndirectFail6a(){fail("""
002| A:{.foo123:A->this.foo123; read .bar:A->this.foo123;}
   |                            -------------~~~~^^^^^^^^

While inspecting ".bar" line 2
This call to method "A.foo123" can not typecheck.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo123
""",List.of("""
A:{.foo123:A->this.foo123; read .bar:A->this.foo123;}
"""));}//With inference we infer [imm] (next case)
@Test void tsOkIndirectFail6b(){fail("""
002| A:{.foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
   |                            -------------~~~~^^^^^^^^~~~~~

While inspecting ".bar" line 2
This call to method "A.foo123" can not typecheck.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo123
""",List.of("""
A:{.foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
"""));}
@Test void tsOkIndirectFail6c(){fail("""
002| A:{.foo123:A->this.foo123; read .bar:A->this.foo123[read];}
   |                            -------------~~~~^^^^^^^^~~~~~~

While inspecting ".bar" line 2
This call to method ".foo123" can not typecheck.
".foo123" exists on type "A", but not with the requested capability.
This call requires the existence of a "read" method.
Available capabilities for this method: "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo123[read]
""",List.of("""
A:{.foo123:A->this.foo123; read .bar:A->this.foo123[read];}
"""));} 

@Test void tsOkIndirectFail7(){fail("""
002| A:{mut .foo123:A->this.foo123; imm .bar:A->this.foo123;}
   |                                ------------~~~~^^^^^^^^

While inspecting ".bar" line 2
This call to method "A.foo123" can not typecheck.
The receiver (the expression before the method name) has capability "imm".
This call requires a receiver with capability "mut" or "iso" or "mutH".

Receiver required by each promotion:
- "mut" (As declared)
- "iso" (Strengthen result, Strengthen hygienic result, Allow readH arguments)
- "mutH" (Allow mutH receiver)

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo123[mut]
""",List.of("""
A:{mut .foo123:A->this.foo123; imm .bar:A->this.foo123;}
"""));}
@Test void tsOkIndirectFail8(){fail("""
002| A:{mut .foo123:A->this.foo123; imm .foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
   |                                                            -------------~~~~^^^^^^^^~~~~~

While inspecting ".bar" line 2
This call to method "A.foo123" can not typecheck.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo123
""",List.of("""
A:{mut .foo123:A->this.foo123; imm .foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
"""));}

@Test void tsOkIndirectInferredAsRead(){ok(List.of("""
A:{mut .foo123:A->this.foo123; read .foo123:A->this.foo123; imm .bar:A->this.foo123;}
"""));}
@Test void tsOkIndirectFail10(){fail("""
007|   read .bar:A->
008|     this.foo123[mut];
   |     ----^^^^^^^^-----

While inspecting ".bar" line 7
This call to method "A.foo123" can not typecheck.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "mut" or "iso" or "mutH".

Receiver required by each promotion:
- "mut" (As declared)
- "iso" (Strengthen result, Strengthen hygienic result, Allow readH arguments)
- "mutH" (Allow mutH receiver)

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo123[mut]
""",List.of("""
A:{
  mut .foo123:A->
    this.foo123;
  imm .foo123:A->
    this.foo123;
  read .bar:A->
    this.foo123[mut];
  }
"""));}
@Test void baseTypeError(){fail("""
002| A:{ .bar(b:B):A->b; }
   |     -------------^^

While inspecting parameter "b" > ".bar(_)" line 2
The body of method ".bar(_)" of type declaration "A" is an expression returning "B".
Parameter "b" has type "B" instead of a subtype of "A".

See inferred typing context below for how type "A" was introduced: (compression indicated by `-`)
A:{.bar(b:B):A->b}
""",List.of("""
A:{ .bar(b:B):A->b; }
B:{ }
"""));}
@Test void uncallableMethodOk(){ok(List.of("""
B:{ mut .bar:B }
A:{ mut .baz(b: B):B->{}; }
"""));}
@Test void uncallableMethodFail(){fail("""
003| A:{ mut .baz(b: B):B->{ .bar->b}; }
   |     ------------------~~^^^^^^^~

While inspecting object literal instance of "B" > ".baz(_)" line 3
The method "B.bar" is dead code.
The object literal instance of "B" is "imm", so it will never be seen as "mut".
But it implements method "mut .bar", which requires a "mut" receiver.

Compressed relevant code with inferred types: (compression indicated by `-`)
B{mut .bar:B->b}
""",List.of("""
B:{ mut .bar:B }
A:{ mut .baz(b: B):B->{ .bar->b}; }
"""));}
@Test void methodReceiverNotRcc(){fail("""
004|   .bar[X:imm,mut,read](x:X):A->x.foo123;
   |   -----------------------------~^^^^^^^^

While inspecting ".bar(_)" line 4
This call to method ".foo123" can not typecheck.
The receiver is of type "X". This is a type parameter.
Type parameters cannot be receivers of method calls.

See inferred typing context below for how type "X" was introduced: (compression indicated by `-`)
A:{.foo123:A->this.foo123;.bar[X:*](x:X):A->x.foo123}
""",List.of("""
A:{
  .foo123:A->this.foo123;
  .bar[X:imm,mut,read](x:X):A->x.foo123;
}
"""));}

@Test void methodTArgsArityError(){fail("""
004|   .bar:A->this.id[A,A](this);
   |   --------~~~~^^^^~~~~~~~~~~

While inspecting ".bar" line 4
This call to method "A.id(_)" can not typecheck.
Wrong number of type arguments for ".id(_)".
This method expects 1 type argument, but this call provides 2 type arguments.

Compressed relevant code with inferred types: (compression indicated by `-`)
this.id[imm,A,A](this)
""",List.of("""
A:{
  .id[X:imm,mut,read](x:X):X->x;
  .bar:A->this.id[A,A](this);
}
"""));}

@Test void methodArgsDisagree(){fail("""
004|   .caller(x:readH A, y:mutH A):A->this.f(x,y);
   |   --------------------------------~~~~^^^~~~~

While inspecting ".caller(_,_)" line 4
This call to method ".f(_,_)" can not typecheck.
Each argument is compatible with at least one promotion, but no single promotion fits all arguments.

Compatible promotions by argument:
- Argument 1 has type "readH A" and is compatible with: Allow readH arguments, Allow mutH argument 1.
- Argument 2 has type "mutH A" and is compatible with: Allow mutH argument 2.

Promotion failures:
- Argument 1 fails:    As declared
  Parameter "x" has type "readH A" instead of a subtype of "read A".
- Argument 1 fails:    Strengthen result, Strengthen hygienic result, Allow mutH receiver, Allow mutH argument 2
  Parameter "x" has type "readH A" instead of a subtype of "imm A".
- Argument 2 fails:    Allow readH arguments, Allow mutH argument 1
  Parameter "y" has type "mutH A" instead of a subtype of "iso A".

Compressed relevant code with inferred types: (compression indicated by `-`)
this.f(x,y)
""",List.of("""
A:{
  .f(a:read A, b:mut A):A->this;
  .caller(x:readH A, y:mutH A):A->this.f(x,y);
}
"""));}

@Test void methodArgsDisagree2(){fail("""
005|   .caller(x:readH A, y:mutH A):A->this.f(x,ID#[mutH A]y);
   |   --------------------------------~~~~^^^~~~~~~~~~~~~~~~

While inspecting ".caller(_,_)" line 5
This call to method ".f(_,_)" can not typecheck.
Each argument is compatible with at least one promotion, but no single promotion fits all arguments.

Compatible promotions by argument:
- Argument 1 has type "readH A" and is compatible with: Allow readH arguments, Allow mutH argument 1.
- Argument 2 has type "mutH A" and is compatible with: Allow mutH argument 2.

Promotion failures:
- Argument 1 fails:    As declared
  Parameter "x" has type "readH A" instead of a subtype of "read A".
- Argument 1 fails:    Strengthen result, Strengthen hygienic result, Allow mutH receiver, Allow mutH argument 2
  Parameter "x" has type "readH A" instead of a subtype of "imm A".
- Argument 2 fails:    Allow readH arguments, Allow mutH argument 1
  Method call "ID#(_)" has type "mutH A" instead of a subtype of "iso A".

Compressed relevant code with inferred types: (compression indicated by `-`)
this.f(x,ID#[imm,mutH A](y))
""",List.of("""
ID:{#[T:**](x:T):T->x}
A:{
  .f(a:read A, b:mut A):A->this;
  .caller(x:readH A, y:mutH A):A->this.f(x,ID#[mutH A]y);
}
"""));}

@Test void noVar1Ok(){ok(List.of("""
Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):B->Skip#(aaaa);
}
"""));}
@Test void noVar1Fail(){fail("""
005|   .f(aaaa:mut A):B->imm BB:B{.foo:B->Skip#(aaaa);}
   |   ---------------------------~~~~~~~~~~~~~~^^^^^--

While inspecting parameter "aaaa" > ".foo" line 5 > ".f(_)" line 5
parameter "aaaa" has type "mut A".
parameter "aaaa" can observe mutation; thus it can not be captured in the "imm" object literal "BB" (line 5).
Hint: capture an immutable copy instead, or move this use outside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
aaaa
""",List.of("""
Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):B->imm BB:B{.foo:B->Skip#(aaaa);}
}
"""));}

@Test void noVar1FailAnon(){fail("""
005|   .f(aaaa:mut A):B->imm B{.foo:B->Skip#(aaaa);}
   |   ------------------------~~~~~~~~~~~~~~^^^^^--

While inspecting parameter "aaaa" > ".foo" line 5 > ".f(_)" line 5
parameter "aaaa" has type "mut A".
parameter "aaaa" can observe mutation; thus it can not be captured in the "imm" object literal instance of "B" (line 5).
Hint: capture an immutable copy instead, or move this use outside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
aaaa
""",List.of("""
Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):B->imm B{.foo:B->Skip#(aaaa);}
}
"""));}


@Test void noVar2Fail(){fail("""
005|   .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(aaaa);}
   |                                    -------------~~~~^^~~~~~

While inspecting ".foo" line 5 > ".f(_)" line 5
This call to method "Skip#(_)" can not typecheck.
Argument 1 has type "read A".
That is not a subtype of any of "mut A" or "iso A" or "mutH A".
Parameter "aaaa" has type "read A" instead of a subtype of "mut A".
Note: the declared type "mut A" would instead be a valid subtype.
Capture adaptation trace:
"mut A" --setToRead(line 5)--> "read A".

Type required by each promotion:
- "mut A"  (As declared)
- "iso A"  (Strengthen result, Strengthen hygienic result, Allow readH arguments, Allow mutH receiver)
- "mutH A"  (Allow mutH argument 1)

Compressed relevant code with inferred types: (compression indicated by `-`)
Skip#[imm,mut A](aaaa)
""",List.of("""
Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(aaaa);}
}
"""));}

@Test void correctDeepCall(){ok(List.of("""
Skip:{#[X:**](X):B->B}
Id:{#[X:**](x:X):X->x}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#[imm,read A](Id#[imm,read A](aaaa));}}
"""));}//TODO: this works with either one of the method targs explicitly listed
@Test void badDeepCall(){fail("""
006|   .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(Id#(aaaa));}}
   |                                    -------------------~~^^~~~~~-

While inspecting ".foo" line 6 > ".f(_)" line 6
This call to method "Id#(_)" can not typecheck.
Argument 1 has type "read A".
That is not a subtype of any of "mut A" or "iso A" or "mutH A".
Parameter "aaaa" has type "read A" instead of a subtype of "mut A".
Note: the declared type "mut A" would instead be a valid subtype.
Capture adaptation trace:
"mut A" --setToRead(line 6)--> "read A".

Type required by each promotion:
- "mut A"  (As declared)
- "iso A"  (Strengthen result, Strengthen hygienic result, Allow readH arguments, Allow mutH receiver)
- "mutH A"  (Allow mutH argument 1)

Compressed relevant code with inferred types: (compression indicated by `-`)
Id#[imm,mut A](aaaa)
""",List.of("""
Skip:{#[X:**](X):B->B}
Id:{#[X:**](x:X):X->x}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(Id#(aaaa));}}
"""));}//This fails because inference infers [mut A] instead of [read A]
//TODO: make the error message show the inference somehow

@Test void hopelessArg_calls_pArgHasType(){fail("""
006|   .f(aaaa:mut A):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa));}
   |                                    -------------~~~~^^~~~~~~~~~~~~~-

While inspecting ".foo" line 6 > ".f(_)" line 6
This call to method "Need#(_)" can not typecheck.
Argument 1 has type "read A".
That is not a subtype of any of "mut A" or "iso A" or "mutH A".
Method call "AsRead#(_)" has type "read A" instead of a subtype of "mut A".

Type required by each promotion:
- "mut A"  (As declared)
- "iso A"  (Strengthen result, Strengthen hygienic result, Allow readH arguments, Allow mutH receiver)
- "mutH A"  (Allow mutH argument 1)

See inferred typing context below for how type "mut A" was introduced: (compression indicated by `-`)
A:{.f(aaaa:mut A):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa))}}
""",List.of("""
B:{}
Need:{ #(a:mut A):B->B{} }
AsRead:{ #(x:read A):read A->x }
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa));}
}
"""));} 

@Test void bestLitName_anonLiteralNoImpl_withMeth(){ok(List.of("""
A:{}
Main:{
  .m:A -> {.foo:A->A }.foo
}
"""));}


@Test void err_bestLitName_anonLiteralNoImpl_missingMethod(){fail("""
004|   .m:A -> { .bar:A->A }.foo
   |   --------~~~~~~~~~~~~~^^^^

While inspecting ".m" line 4
This call to method ".foo" can not typecheck.
Method ".foo" is not declared on "{...}".

Available methods on "{...}":
-       .bar:A

Compressed relevant code with inferred types: (compression indicated by `-`)
{.bar:A->A}.foo
""",List.of("""
A:{}
Main:{
  .m:A -> { .bar:A->A }.foo
  }
"""));}

@Test void err_bestLitName_anonLiteralNoImpl_empty(){fail("""
004|    .m:A -> { }.foo
   |    --------~~~^^^^

While inspecting ".m" line 4
This call to method ".foo" can not typecheck.
Method ".foo" is not declared on "{...}".
The object literal "{...}" does not have any methods.

Compressed relevant code with inferred types: (compression indicated by `-`)
{}.foo
""",List.of("""
A:{}
 Main:{
   .m:A -> { }.foo
  }
"""));}
@Test void err_bestLitName_NamedLiteralNoImpl_empty(){fail("""
004|    .m:A -> B:{ }.foo
   |    --------~~~~~^^^^

While inspecting ".m" line 4
This call to method ".foo" can not typecheck.
Method ".foo" is not declared on type "B".
The type "B" does not have any methods.

Compressed relevant code with inferred types: (compression indicated by `-`)
B:{}.foo
""",List.of("""
A:{}
 Main:{
   .m:A -> B:{ }.foo
  }
"""));}

@Test void passInt(){ok(List.of("""
 Main:{ .m:base.Int -> +42 }
"""));}
@Test void passFloat(){ok(List.of("""
 Main:{ .m:base.Float -> +42.0 }
"""));}
@Test void passNat(){ok(List.of("""
 Main:{ .m:base.Nat -> 42 }
"""));}
@Test void passSStr(){ok(List.of("""
 Main:{ .m:base.Str -> `Hi` }
"""));}
@Test void passUStr(){ok(List.of("""
 Main:{ .m:base.UStr -> "Hi" }
"""));}
@Test void passNum(){ok(List.of("""
 Main:{ .m:base.Num -> +3/4 }
"""));}
@Test void failIntTooBig(){failExt("""
In file: [###]/in_memory0.fear

002|  Main:{ .m:base.Int -> +421381834238972893748972389723 }
   |                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Integer literal is out of range for "base.Int".
"base.Int" must be representable as a 32-bit signed integer.
Valid range: -2147483648 .. 2147483647.
This literal is: "421381834238972893748972389723".
Hint: if you need arbitrary precision numbers, use "base.Num".
Error 9 WellFormedness
""",List.of("""
 Main:{ .m:base.Int -> +421381834238972893748972389723 }
"""));}
@Test void failNatTooBig(){failExt("""
In file: [###]/in_memory0.fear

002|  Main:{ .m:base.Nat -> 421381834238972893748972389723 }
   |                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Natural literal is out of range for "base.Nat".
"base.Nat" must be representable as a 32-bit unsigned integer.
Valid range: 0 .. 4294967295.
This literal is: "421381834238972893748972389723".
Hint: if you need arbitrary precision numbers, use "base.Num".
Error 9 WellFormedness
""",List.of("""
 Main:{ .m:base.Nat -> 421381834238972893748972389723 }
"""));}

@Test void failFloatTooBig(){failExt("""
In file: [###]/___DBG___/in_memory0.fear

002|  Main:{ .m:base.Float -> +1.0e309 }
   |                          ^^^^^^^^

While inspecting the file
Float literal is not exactly representable as "base.Float".
"base.Float" must be representable exactly as a 64-bit IEEE 754 double.
This literal is: +1.0e309.
This literal overflows; the nearest representable value is "+179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.0".
Error 9 WellFormedness
""",List.of("""
 Main:{ .m:base.Float -> +1.0e309 }
"""));}
@Test void failFloatTooSmall(){failExt("""
In file: [###]/in_memory0.fear

002|  Main:{ .m:base.Float -> +1.0e-400 }
   |                          ^^^^^^^^^

While inspecting the file
Float literal is not exactly representable as "base.Float".
"base.Float" must be representable exactly as a 64-bit IEEE 754 double.
This literal is: +1.0e-400.
If rounded, the nearest representable value is "+0.0".
Hint: if you need arbitrary precision numbers, use "base.Num".
Error 9 WellFormedness
""",List.of("""
 Main:{ .m:base.Float -> +1.0e-400 }
"""));}
@Test void failFloatImprecise1(){failExt("""
In file: [###]/in_memory0.fear

002|  Main:{ .m:base.Float -> +0.1 }
   |                          ^^^^

While inspecting the file
Float literal is not exactly representable as "base.Float".
"base.Float" must be representable exactly as a 64-bit IEEE 754 double.
This literal is: +0.1.
If rounded, the nearest representable value is "+0.1000000000000000055511151231257827021181583404541015625".
Hint: if you need arbitrary precision numbers, use "base.Num".
Error 9 WellFormedness
""",List.of("""
 Main:{ .m:base.Float -> +0.1 }
"""));}
@Test void failFloatImprecise2(){failExt("""
In file: [###]/in_memory0.fear

002|  Main:{ .m:base.Float -> +0.2 }
   |                          ^^^^

While inspecting the file
Float literal is not exactly representable as "base.Float".
"base.Float" must be representable exactly as a 64-bit IEEE 754 double.
This literal is: +0.2.
If rounded, the nearest representable value is "+0.200000000000000011102230246251565404236316680908203125".
Hint: if you need arbitrary precision numbers, use "base.Num".
Error 9 WellFormedness
""",List.of("""
 Main:{ .m:base.Float -> +0.2 }
"""));}
@Test void okFloatTooBig(){ok(List.of("""
 Main:{ .m:base.Float -> +179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.0 }
"""));}
@Test void okFloatPrecise1(){ok(List.of("""
 Main:{ .m:base.Float ->  +0.1000000000000000055511151231257827021181583404541015625 }
"""));}
@Test void okFloatPrecise2(){ok(List.of("""
 Main:{ .m:base.Float -> +0.200000000000000011102230246251565404236316680908203125 }
"""));}

@Test void byNameOk1(){ok(List.of("""
 A:{.foo:A->A}
 B:A{}
 Main:{ .m:B -> B }
"""));}
@Test void byNameOk2(){ok(List.of("""
 A:{.foo:A->A}
 B:A{}
 Main:{ .m:B -> B{.bar:A->A} }
"""));}
@Test void byNameFail1(){fail("""
004|  Main:{ .m:B -> B }
   |         --------^

While inspecting object literal instance of "B" > ".m" line 4
This object literal is missing a required method.
Missing: "imm .foo".
Required by: "A".
Hint: add an implementation for ".foo" inside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
B
""",List.of("""
 A:{.foo:A}
 B:A{}
 Main:{ .m:B -> B }
"""));}
@Test void byNameFail2(){fail("""
004|  Main:{ .m:B -> B{.bar:A->A} }
   |         --------^^----------

While inspecting object literal instance of "B" > ".m" line 4
This object literal is missing a required method.
Missing: "imm .foo".
Required by: "B".
Hint: add an implementation for ".foo" inside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
B{.bar:A->A}
""",List.of("""
 A:{.foo:A->A}
 B:A{.foo:A}
 Main:{ .m:B -> B{.bar:A->A} }
"""));}

@Test void byNameOkMut(){ok(List.of("""
 A:{mut .foo:A->A}
 B:A{.foo:A}
 Main:{ .m:B -> B{.bar:A->A} }
"""));}

@Test void toStr(){ok(List.of("""
Str:{}
ToStr:{ read .str: Str }
ToStrBy[T]:{#(read T):read ToStr}
ToStr[E:*]:{ read .str(ToStrBy[imm E]): Str }
Box[EE:*]: ToStr[EE]{
  mut  .get: EE;
  read .get: read/imm EE;
  imm  .get: imm EE;
  .str by-> by#(this.get).str
  }
A:ToStr{ .str->Str}
Top:{ 
  .m00(b:Box[A]):Str -> b.str {::};
  .m01(b:Box[read A]):Str -> b.str {::};
  .m02(b:Box[mut A]):Str -> b.str {::};
  .m03(b:read Box[A]):Str -> b.str {::};
  .m04(b:read Box[read A]):Str -> b.str {::};
  .m05(b:read Box[mut A]):Str -> b.str {::};
  .m06(b:mut Box[A]):Str -> b.str {::};
  .m07(b:mut Box[read A]):Str -> b.str {::};
  .m08(b:mut Box[mut A]):Str -> b.str {::};
  .m09(b:iso Box[A]):Str -> b.str {::};
  .m10(b:iso Box[read A]):Str -> b.str {::};
  .m11(b:iso Box[mut A]):Str -> b.str {::};
  .m12(b:readH Box[A]):Str -> b.str {::};
  .m13(b:readH Box[read A]):Str -> b.str {::};
  .m14(b:readH Box[mut A]):Str -> b.str {::};
  .m15(b:mutH Box[A]):Str -> b.str {::};
  .m16(b:mutH Box[read A]):Str -> b.str {::};
  .m17(b:mutH Box[mut A]):Str -> b.str {::};
  }
"""));}


}