package simplified;

import static org.junit.jupiter.api.Assertions.assertThrows;

import java.util.List;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.opentest4j.AssertionFailedError;

import utils.Err;

final class InferTest{
  static{ Err.setUp(AssertionFailedError.class, Assertions::assertEquals, Assertions::assertTrue); }
  static final String h= """
    Animal:{ name():Animal; } Cat:Animal{ purr():Cat; } Dog:Animal{}
    Box[T]:{ unbox():T; } G[R]:{ get():R; } F[A,R]:{ app(a:A):R; } Two[R]:{ first():R; second():R; }
    H:{
      both[T](a:T,b:T):T; three[T](a:T,b:T,c:T):T;
      box[T](t:T):Box[T]; mk[T]():Box[T]; pair[T](b:Box[T],x:T):T;
      sink[T](g:G[T]):H; app[T](g:G[T],x:T):T; sinkTwo[T](t:Two[T]):H;
      needAnimal(a:Animal):Animal; needCat(c:Cat):Animal; two(a:Animal,b:Animal):Animal;
      use[A,R](f:F[A,R]):H; let[A,R](a:A,f:F[A,R]):R;
    }
    """;
  static void ok(String expected, String src){
    var res= Infer.of(h+src);
    Err.strCmp(expected, res.substring(res.lastIndexOf('\n') + 1));
  }
  static void fail(String expected, String src){ Err.strCmp(expected, assertThrows(Fail.class, () -> Infer.of(h+src)).getMessage()); }

  @Test void variableNotDeclared(){ fail("""
    Variable "x" is not declared
    """, """
    User:{ m(h:H):H->x; }
    """); }
  @Test void typeNameNotDeclared(){ fail("""
    Type name "Foo" is not declared
    """, """
    User:{ m(h:Foo):H->h; }
    """); }
  @Test void typeArgumentsOfATypeNameAreCounted(){ fail("""
    Type "Box" has 0 type arguments, but "Box[T]" is declared with 1
    """, """
    User:{ m(h:Box):H->h; }
    """); }
  @Test void typeParameterAsASupertype(){ fail("""
    Type "User" has the type parameter "X" as a supertype
    """, """
    User[X]:X{}
    """); }
  @Test void methodWithNoBodyHasAWrittenSignature(){ fail("""
    Method "m(h:?):H;" has no body and has "?" in the signature; only a method with a body can have "?" in the signature
    """, """
    User:{ m(h:?):H; }
    """); }
  @Test void methodDeclaredTwice(){ fail("""
    Method "m" is declared twice in the same literal
    """, """
    User:{ m(h:H):H->h; m(a:Animal):H->this.m(this); }
    """); }
  @Test void methodNotDeclared(){ fail("""
    Method "foo" is not declared in type "H"
    """, """
    User:{ m(h:H):H->h.foo(); }
    """); }
  @Test void argumentsOfACallAreCounted(){ fail("""
    Method "both" of type "H" has 2 parameters, but the call "h.both(h)" has 1 arguments
    """, """
    User:{ m(h:H):H->h.both(h); }
    """); }
  @Test void genericArgumentsJoinToTheSupertype(){ ok("User:{m(h:H,a:A,z:Z):A->h.both[A](a,z);}", """
    A:{} Z:A{}
    User:{ m(h:H,a:A,z:Z):A->h.both(a,z); }
    """); }
  @Test void genericArgumentsJoinToTheSupertypeInEitherOrder(){ ok("User:{m(h:H,a:A,z:Z):A->h.both[A](z,a);}", """
    A:{} Z:A{}
    User:{ m(h:H,a:A,z:Z):A->h.both(z,a); }
    """); }
  @Test void genericArgumentsWithNoRequiredTypeJoinToTheSupertype(){ ok("User:{m(h:H,a:A,z:Z):A->h.both[A](z,a).k();}", """
    A:{ k():A; } Z:A{}
    User:{ m(h:H,a:A,z:Z):A->h.both(z,a).k(); }
    """); }
  @Test void requiredTypeDecidesOverTheArguments(){ ok("User:{m(h:H,z:Z):A->h.both[A](z,z);}", """
    A:{} Z:A{}
    User:{ m(h:H,z:Z):A->h.both(z,z); }
    """); }
  @Test void argumentsDecideWithNoRequiredType(){ ok("User:{m(h:H,z:Z):A->h.both[Z](z,z).k();}", """
    A:{ k():A; } Z:A{}
    User:{ m(h:H,z:Z):A->h.both(z,z).k(); }
    """); }
  @Test void threeArgumentsJoinToTheSupertypeInEveryOrder(){
    for (var p : List.of("a,c,d", "a,d,c", "c,a,d", "c,d,a", "d,a,c", "d,c,a")){
      ok("User:{m(h:H,a:Animal,c:Cat,d:Dog):Animal->h.three[Animal]("+p+").name();}", "User:{ m(h:H,a:Animal,c:Cat,d:Dog):Animal->h.three("+p+").name(); }");
    }
  }
  @Test void writtenTypeArgumentIsKept(){ fail("""
    The expression "a" has type "A", and "A" is not a subtype of "Z"
    """, """
    A:{} Z:A{}
    User:{ m(h:H,a:A,z:Z):A->h.both[Z](a,z); }
    """); }
  @Test void siblingsJoinToTheRequiredSupertypeA(){ ok("User:{m(h:H,y:Y,z:Z):A->h.both[A](y,z);}", """
    A:{} B:{} Y:A,B{} Z:A,B{}
    User:{ m(h:H,y:Y,z:Z):A->h.both(y,z); }
    """); }
  @Test void siblingsJoinToTheRequiredSupertypeB(){ ok("User:{m(h:H,y:Y,z:Z):B->h.both[B](y,z);}", """
    A:{} B:{} Y:A,B{} Z:A,B{}
    User:{ m(h:H,y:Y,z:Z):B->h.both(y,z); }
    """); }
  @Test void siblingsWithNoRequiredTypeCannotBeInferred(){ fail("""
    The type argument "T" is inferred from the types "Y", "Z", but no one of those types is a supertype of all the others
    """, """
    A:{ k():A; } B:{} Y:A,B{} Z:A,B{}
    User:{ m(h:H,y:Y,z:Z):A->h.both(y,z).k(); }
    """); }
  @Test void siblingsWithOneCommonSupertypeAndNoWidenToCannotBeInferred(){ fail("""
    The type argument "T" is inferred from the types "Y", "Z", but no one of those types is a supertype of all the others
    """, """
    A:{ k():A; } Y:A{} Z:A{}
    User:{ m(h:H,y:Y,z:Z):A->h.both(y,z).k(); }
    """); }
  @Test void siblingsJoinToTheirWidenTo(){ ok("User:{m(h:H,y:Y,z:Z):Top->h.both[Top](y,z).k();}", """
    Top:{ k():Top; } Y:Top,WidenTo[Top]{} Z:Top,WidenTo[Top]{}
    User:{ m(h:H,y:Y,z:Z):Top->h.both(y,z).k(); }
    """); }
  @Test void unrelatedTypesCannotBeInferred(){ fail("""
    The expression "b" has type "B", and "B" is not a subtype of "A"
    """, """
    A:{} B:{}
    User:{ m(h:H,a:A,b:B):A->h.both(a,b); }
    """); }
  @Test void typesWithDifferentInvariantArgumentsCannotBeInferred(){ fail("""
    The type argument "T" is inferred from the types "Y", "Z", but no one of those types is a supertype of all the others
    """, """
    A:{} B:{} Sup[T]:{ k():T; } Y:Sup[A]{} Z:Sup[B]{}
    User:{ m(h:H,y:Y,z:Z):H->h.both(y,z).k(); }
    """); }
  @Test void typesWithDifferentInvariantArgumentsJoinToACommonSupertypeAbove(){ ok("User:{m(h:H,y:Y,z:Z):Top->h.both[Top](y,z).k();}", """
    A:{} B:{} Top:{ k():Top; } Sup[T]:Top{} Y:Sup[A],WidenTo[Top]{} Z:Sup[B],WidenTo[Top]{}
    User:{ m(h:H,y:Y,z:Z):Top->h.both(y,z).k(); }
    """); }
  @Test void requiredTypeDecidesTypeArgumentOverWidenTo(){ ok("User:{m(h:H,n:North):Box[Family[Dir]]->h.box[Family[Dir]](n);}", """
    Family[T]:WidenTo[T]{} Dir:Family[Dir]{} North:Dir{}
    User:{ m(h:H,n:North):Box[Family[Dir]]->h.box(n); }
    """); }
  @Test void requiredTypeDecidesNestedTypeArguments(){ ok("User:{m(h:H,c:Cat):Box[Box[Animal]]->h.box[Box[Animal]](h.box[Animal](c));}", """
    User:{ m(h:H,c:Cat):Box[Box[Animal]]->h.box(h.box(c)); }
    """); }
  @Test void requiredSupertypeDecidesTypeArgument(){ ok("User:{m(h:Sub[H],c:Cat):Sup[Animal]->h.sub[Animal](c);}", """
    Sup[T]:{} Sub[T]:Sup[T]{ sub[U](u:U):Sub[U]; }
    User:{ m(h:Sub[H],c:Cat):Sup[Animal]->h.sub(c); }
    """); }
  @Test void argumentOfAGenericTypeDecidesTheTypeArgument(){ ok("User:{m(h:H,b:Box[Cat]):Animal->h.pair[Cat](b,b.unbox());}", """
    User:{ m(h:H,b:Box[Cat]):Animal->h.pair(b,b.unbox()); }
    """); }
  @Test void requiredTypeFlowsIntoTheInnerCallA(){ ok("User:{m(h:H,a:Animal,c:Cat):Animal->h.pair[Animal](h.box[Animal](c),a);}", """
    User:{ m(h:H,a:Animal,c:Cat):Animal->h.pair(h.box(c),a); }
    """); }
  @Test void requiredTypeFlowsIntoTheInnerCallB(){ ok("User:{m(h:H,a:Animal,c:Cat):Animal->h.pair[Animal](h.box[Animal](a),c);}", """
    User:{ m(h:H,a:Animal,c:Cat):Animal->h.pair(h.box(a),c); }
    """); }
  @Test void withNoRequiredTypeTheInnerCallDecidesFirstA(){ ok("User:{m(h:H,a:Animal,c:Cat):Animal->h.pair[Animal](h.box[Animal](a),c).name();}", """
    User:{ m(h:H,a:Animal,c:Cat):Animal->h.pair(h.box(a),c).name(); }
    """); }
  @Test void withNoRequiredTypeTheInnerCallDecidesFirstB(){ fail("""
    The expression "a" has type "Animal", and "Animal" is not a subtype of "Cat"
    """, """
    User:{ m(h:H,a:Animal,c:Cat):Animal->h.pair(h.box(c),a).name(); }
    """); }
  @Test void innerCallWithNoArgumentsFollowsTheOuterCall(){ ok("User:{m(h:H,b:Box[Cat]):Cat->h.both[Box[Cat]](h.mk[Cat](),b).unbox().purr();}", """
    User:{ m(h:H,b:Box[Cat]):Cat->h.both(h.mk(),b).unbox().purr(); }
    """); }
  @Test void literalFollowsTheRequiredType(){ ok("User:{m(z:Z):G[A]->_:G[A]{get():A->z;};}", """
    A:{} Z:A{}
    User:{ m(z:Z):G[A]->{get():?->z;}; }
    """); }
  @Test void writtenSignatureOfALiteralIsKept(){ fail("""
    The type argument "R" is required to be both "A" and "Z"
    """, """
    A:{} Z:A{}
    User:{ m(z:Z):G[A]->{get():Z->z;}; }
    """); }
  @Test void extraMethodOfALiteralNeedsAWrittenSignature(){ fail("""
    The signature of the method "extra" of the literal "_:G[A]{get():A->z;extra(x:?):?->x;}" is not inferred
    """, """
    A:{} Z:A{}
    User:{ m(z:Z):G[A]->{get():?->z;extra(x:?):?->x;}; }
    """); }
  @Test void extraMethodOfALiteralWithAWrittenSignature(){ ok("User:{m(z:Z):G[A]->_:G[A]{get():A->z;extra(x:Z):Z->x;};}", """
    A:{} Z:A{}
    User:{ m(z:Z):G[A]->{get():?->z;extra(x:Z):Z->x;}; }
    """); }
  @Test void signatureOfADeclaredLiteralFollowsTheSupertype(){ ok("User:Base{get(x:Cat):Animal->x;}", """
    Base:{ get(x:Cat):Animal; }
    User:Base{ get(x:?):?->x; }
    """); }
  @Test void newMethodOfADeclaredLiteralNeedsAWrittenSignature(){ fail("""
    The signature of the method "get" of the literal "User:{get(x:?):?->x;}" is not inferred
    """, """
    User:{ get(x:?):?->x; }
    """); }
  @Test void methodBodyDecidesTheTypeArgumentOfALiteral(){ ok("User:{m(h:H,c:Cat):H->h.sink[Cat](_:G[Cat]{get():Cat->c;});}", """
    User:{ m(h:H,c:Cat):H->h.sink({get():?->c;}); }
    """); }
  @Test void literalFollowsTheTypeArgumentOfTheRequiredType(){ ok("User:{wrap[T](g:G[T]):Box[T]->this.wrap[T](g);m(h:User,c:Cat):Box[Animal]->h.wrap[Animal](_:G[Animal]{get():Animal->c;});}", """
    User:{ wrap[T](g:G[T]):Box[T]->this.wrap(g); m(h:User,c:Cat):Box[Animal]->h.wrap({get():?->c;}); }
    """); }
  @Test void methodBodiesJoinToTheSupertype(){ ok("User:{m(h:H,a:Animal,c:Cat):H->h.sinkTwo[Animal](_:Two[Animal]{first():Animal->c;second():Animal->a;});}", """
    User:{ m(h:H,a:Animal,c:Cat):H->h.sinkTwo({first():?->c;second():?->a;}); }
    """); }
  @Test void methodBodiesOfUnrelatedTypesCannotBeInferred(){ fail("""
    The type argument "R" is inferred from the types "Cat", "Dog", but no one of those types is a supertype of all the others
    """, """
    User:{ m(h:H,c:Cat,d:Dog):H->h.sinkTwo({first():?->c;second():?->d;}); }
    """); }
  @Test void methodBodiesFollowTheRequiredType(){ ok("User:{m(c:Cat,d:Dog):Two[Animal]->_:Two[Animal]{first():Animal->c;second():Animal->d;};}", """
    User:{ m(c:Cat,d:Dog):Two[Animal]->{first():?->c;second():?->d;}; }
    """); }
  @Test void genericArgumentFromALiteralJoinsToo(){ ok("User:{m(h:H,a:Animal,c:Cat):Animal->h.app[Animal](_:G[Animal]{get():Animal->c;},a);}", """
    User:{ m(h:H,a:Animal,c:Cat):Animal->h.app({get():?->c;},a); }
    """); }
  @Test void withNoRequiredTypeTheLiteralDecidesFirst(){ fail("""
    The expression "a" has type "Animal", and "Animal" is not a subtype of "Cat"
    """, """
    User:{ m(h:H,a:Animal,c:Cat):Animal->h.app({get():?->c;},a).name(); }
    """); }
  @Test void emptyLiteralArgumentDoesNotDecideATypeArgument(){ ok("User:{m(h:K,c:Cat,a:Animal):Animal->h.k[Animal,Animal](c,_:Pair[Animal,Animal]{},a);}", """
    Pair[X,Y]:{} K:{ k[X,Y](a:X,b:Pair[X,Y],c:Y):X; }
    User:{ m(h:K,c:Cat,a:Animal):Animal->h.k(c,{},a); }
    """); }
  @Test void emptyLiteralArgumentFollowsATypeArgumentBelowTheResultType(){ ok("User:{m(h:K,c:Cat):Animal->h.k[Animal](c,_:Box[Animal]{});}", """
    K:{ k[X](a:X,b:Box[X]):X; }
    User:{ m(h:K,c:Cat):Animal->h.k(c,{}); }
    """); }
  @Test void emptyLiteralArgumentFollowsTheOtherArgument(){ ok("User:{m(h:H,a:Animal):Animal->h.both[Animal](_:Animal{},a).name();}", """
    User:{ m(h:H,a:Animal):Animal->h.both({},a).name(); }
    """); }
  @Test void emptyLiteralWithNoTypeArgumentCannotBeInferred(){ fail("""
    The type arguments of the call "h.sink[?](_:G[?]{})" are not inferred
    """, """
    User:{ m(h:H):H->h.sink({}); }
    """); }
  @Test void partlyWrittenSignatureOfALiteral(){ ok("User:{m(h:H):H->h.use[Cat,Cat](_:F[Cat,Cat]{app(x:Cat):Cat->x;});}", """
    User:{ m(h:H):H->h.use({app(x:Cat):?->x;}); }
    """); }
  @Test void literalParameterUsedAsASubtypeThenAsASupertypeIsTheSubtype(){ ok("User:{m(h:H):H->h.use[Cat,Animal](_:F[Cat,Animal]{app(x:Cat):Animal->h.two(h.needCat(x),h.needAnimal(x));});}", """
    User:{ m(h:H):H->h.use({app(x:?):?->h.two(h.needCat(x),h.needAnimal(x));}); }
    """); }
  @Test void literalParameterUsedAsASupertypeThenAsASubtypeIsTheSubtype(){ ok("User:{m(h:H):H->h.use[Cat,Animal](_:F[Cat,Animal]{app(x:Cat):Animal->h.two(h.needAnimal(x),h.needCat(x));});}", """
    User:{ m(h:H):H->h.use({app(x:?):?->h.two(h.needAnimal(x),h.needCat(x));}); }
    """); }
  @Test void literalParameterUsedAsASupertypeThenAsASubtypeCallsAMethodOfTheSubtype(){ ok("User:{m(h:H):H->h.use[Cat,Animal](_:F[Cat,Animal]{app(x:Cat):Animal->h.two(h.needAnimal(x),h.two(h.needCat(x),x.purr()));});}", """
    User:{ m(h:H):H->h.use({app(x:?):?->h.two(h.needAnimal(x),h.two(h.needCat(x),x.purr()));}); }
    """); }
  @Test void literalParameterUsedAsTwoSupertypesThenAsTheirCommonSubtypeIsTheSubtype(){ ok("User:{m(h:H,p:P):H->h.use[Cat2,Animal](_:F[Cat2,Animal]{app(x:Cat2):Animal->h.two(h.needAnimal(x),h.two(p.needPet(x),p.needCat2(x)));});}", """
    Pet:{} Cat2:Animal,Pet{} P:{ needPet(p:Pet):Animal; needCat2(c:Cat2):Animal; }
    User:{ m(h:H,p:P):H->h.use({app(x:?):?->h.two(h.needAnimal(x),h.two(p.needPet(x),p.needCat2(x)));}); }
    """); }
  @Test void literalParameterUsedAsTwoUnrelatedSupertypesCannotBeInferred(){ fail("""
    The type argument "A" is inferred from the types "Animal", "Pet", but no one of those types is a subtype of all the others
    """, """
    Pet:{} Cat2:Animal,Pet{} P:{ needPet(p:Pet):Animal; }
    User:{ m(h:H,p:P):H->h.use({app(x:?):?->h.two(h.needAnimal(x),p.needPet(x));}); }
    """); }
  @Test void literalParameterUsedAsAGenericSupertypeThenAsASubtypeIsTheSubtype(){ ok("User:{m(h:H,p:P):H->h.use[List[Cat],Animal](_:F[List[Cat],Animal]{app(x:List[Cat]):Animal->h.two(p.needSeq(x),p.needList(x));});}", """
    Seq[T]:{} List[T]:Seq[T]{} P:{ needSeq(s:Seq[Cat]):Animal; needList(l:List[Cat]):Animal; }
    User:{ m(h:H,p:P):H->h.use({app(x:?):?->h.two(p.needSeq(x),p.needList(x));}); }
    """); }
  @Test void literalParameterTypeReachesAnotherUseOfTheParameter(){ ok("User:{m(h:H,p:P):H->h.use[Cat,Cat](_:F[Cat,Cat]{app(x:Cat):Cat->p.y[Cat](x,h.needCat(x));});}", """
    P:{ y[T](a:T,v:Animal):T; }
    User:{ m(h:H,p:P):H->h.use({app(x:?):?->p.y(x,h.needCat(x));}); }
    """); }
  @Test void literalParameterTypeReachesAnEarlierUseOfTheParameter(){ ok("User:{m(h:H,p:P):H->h.use[Cat,Cat](_:F[Cat,Cat]{app(x:Cat):Cat->p.y[Cat](h.needCat(x),x);});}", """
    P:{ y[T](v:Animal,a:T):T; }
    User:{ m(h:H,p:P):H->h.use({app(x:?):?->p.y(h.needCat(x),x);}); }
    """); }
  @Test void literalParameterUsedOnlyAsAReceiverCannotBeInferred(){ fail("""
    The type arguments of the call "h.use[?,?](_:F[?,?]{app(x:?):?->x.purr();})" are not inferred
    """, """
    User:{ m(h:H):H->h.use({app(x:?):?->x.purr();}); }
    """); }
  @Test void variableTypeArgumentRequiredAsASubtypeThenAsASupertypeIsTheSubtype(){ ok("User:{m(h:H):Animal->h.let[Box[Cat],Animal](h.mk[Cat](),_:F[Box[Cat],Animal]{app(b:Box[Cat]):Animal->h.two(h.needCat(b.unbox()),h.needAnimal(b.unbox()));});}", """
    User:{ m(h:H):Animal->h.let(h.mk(),{app(b:?):?->h.two(h.needCat(b.unbox()),h.needAnimal(b.unbox()));}); }
    """); }
}
