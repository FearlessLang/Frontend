package fearlessParser;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;

import files.Pos;
import message.FearlessException;
import message.SourceOracle;
import utils.Err;

class TestParse {
  static void ok(String expected,String input){
    expected = expected.replace("\n","").replace(" ","");
    FileFull res= Parse.from(Pos.UNKNOWN.fileName(), input);
    var rres= res.toString().replace("\n","").replace(" ","");
    Err.strCmp(expected,rres);
  }
  static void fail(String expectedErr, String input){
    SourceOracle o= SourceOracle.debugBuilder()
      .put(0, input)
      .build();
    FearlessException err= assertThrows(FearlessException.class,()->Parse.from(SourceOracle.defaultDbgUri(0), input));
    var rres= err.render(o);
    Err.strCmp(expectedErr,rres);
  }  
@Test void mini(){ok("""
FileFull[renames=[], decs=[
  Declaration[name=TName[s=A, arity=0], bs=Optional.empty, cs=[], l=Literal[]]]]
""","""
A:{}
""");}
@Test void decl_generics_plain(){ok("""
FileFull[renames=[], decs=[
Declaration[name=TName[s=Pair, arity=2], bs=Optional[[B[x=X[name=X], bt=RCS[rcs=[]]], B[x=X[name=Y], bt=RCS[rcs=[]]]]], cs=[], l=Literal[]]]]
""","""
Pair[X,Y]:{}
""");}
@Test void decl_generics_with_rcs(){ok("""
FileFull[renames=[], decs=[
Declaration[name=TName[s=Box, arity=1], bs=Optional[[B[x=X[name=X], bt=RCS[rcs=[imm]]]]], cs=[], l=Literal[]]]]
""","""
Box[X:imm]:{}
""");}
@Test void decl_generics_star1(){ok("""
FileFull[renames=[], decs=[
Declaration[name=TName[s=Vec, arity=1], bs=Optional[[B[x=X[name=X], bt=Star[]]]], cs=[], l=Literal[]]]]
""","""
Vec[X: *]:{}
""");}
@Test void decl_generics_star2(){ok("""
FileFull[renames=[], decs=[
Declaration[name=TName[s=Vec, arity=1], bs=Optional[[B[x=X[name=X], bt=Star[]]]], cs=[], l=Literal[]]]]
""","""
Vec[X:*]:{}
""");}
@Test void decl_generics_starstar1(){ok("""
FileFull[renames=[], decs=[
Declaration[name=TName[s=Graph, arity=1], bs=Optional[[B[x=X[name=X], bt=StarStar[]]]], cs=[], l=Literal[]]]]
""","""
Graph[X: **]:{}
""");}
@Test void decl_generics_starstar2(){ok("""
FileFull[renames=[], decs=[
Declaration[name=TName[s=Graph, arity=1], bs=Optional[[B[x=X[name=X], bt=StarStar[]]]], cs=[], l=Literal[]]]]
""","""
Graph[X:**]:{}
""");}
@Test void decl_generics_use(){ok("""
FileFull[renames=[],decs=[Declaration[name=TName[s=Pair,arity=2],
bs=Optional[[B[x=X[name=X],bt=RCS[rcs=[]]],B[x=X[name=Y],bt=RCS[rcs=[]]]]],cs=[],
l=Literal[M[sig=Optional[Sig[rc=Optional.empty,m=Optional[
MName[s=.x,arity=0]],bs=Optional.empty,hasParenthesis=false,parameters=[],t=Optional[X[name=X]]]],
body=Optional.empty],
M[sig=Optional[Sig[rc=Optional.empty,m=Optional[MName[s=.y,arity=0]],bs=Optional.empty,hasParenthesis=false,parameters=[],t=Optional[X[name=Y]]]],
body=Optional.empty]]]]]
""","""
Pair[X,Y]:{ .x:X; .y:Y;}
""");}
@Test void decl_generics_use_repeat(){fail("""
In file: [###]/in_memory0.fear

001| Pair[X,X]:{ .x:X; .y:X;}
   | ^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration > full file
A method signature cannot declare multiple generic type parameters with the same name
Generic type parameter "X" is repeated
Error 2  UnexpectedToken""","""
Pair[X,X]:{ .x:X; .y:X;}
""");}
@Test void meth_generics_use_repeat(){fail("""
In file: [###]/in_memory0.fear

001| Pairs:{.of[X,X]():A->A;}
   | ------~^^^^^^^^^^^^~~~~~

While inspecting method signature > method declaration > type declaration body > type declaration > full file
A method signature cannot declare multiple generic type parameters with the same name
Generic type parameter "X" is repeated
Error 2  UnexpectedToken""","""
Pairs:{.of[X,X]():A->A;}
""");}

@Test void meth_generics_use_repeatHash(){fail("""
In file: [###]/in_memory0.fear

001| Pairs:{#[X,X]():A->A;}
   | ------~^^^^^^^^^^~~~~~

While inspecting method signature > method declaration > type declaration body > type declaration > full file
A method signature cannot declare multiple generic type parameters with the same name
Generic type parameter "X" is repeated
Error 2  UnexpectedToken""","""
Pairs:{#[X,X]():A->A;}
""");}//here we need to fix the tokenizer

@Test void decl_generics_use_repeat_meth(){fail("""
In file: [###]/in_memory0.fear

001| Pair[X,Y]:{ .x:X; .y:Y; .foo[X](x:X):X; }
   | ------------------------~~~~~^~~~~~~~~---

While inspecting generic bounds declaration > method declaration > type declaration body > type declaration > full file
Name "X" already in scope
Error 2  UnexpectedToken
""","""
Pair[X,Y]:{ .x:X; .y:Y; .foo[X](x:X):X; }
""");}

@Test void meth_meth_repeat(){fail("""
In file: [###]/in_memory0.fear

001| A:{.foo[X]:A->B:{.bar[X]:B->B}; }
   | --------------~~~~~~~~^~~~~~~~---

While inspecting generic bounds declaration > method signature > method declaration > type declaration body > method body > method declaration > type declaration body > type declaration > full file
Name "X" already in scope
Error 2  UnexpectedToken
""","""
A:{.foo[X]:A->B:{.bar[X]:B->B}; }
""");}
@Test void type_type_repeat(){fail("""
In file: [###]/in_memory0.fear

001| A[X]:{.foo:AA->B[X]:{.bar:BB->BB}; }
   | ---------------~~^~~~~~~~~~~~~~~~---

While inspecting generic bounds declaration > method body > method declaration > type declaration body > type declaration > full file
Name "X" already in scope
Error 2  UnexpectedToken""","""
A[X]:{.foo:AA->B[X]:{.bar:BB->BB}; }
""");}
@Test void use_this(){ok("""
FileFull[renames=[],decs=[Declaration[name=TName[s=A,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional[Sig[rc=Optional.empty,m=Optional[MName[s=.foo,arity=0]],bs=Optional.empty,hasParenthesis=false,parameters=[],t=Optional[RCC[rc=Optional.empty,c=C[name=TName[s=A,arity=0],ts=Optional.empty]]]]],
body=Optional[this]]]]]]
""","""
A:{.foo:A->this; }
""");}
@Test void use_selfBadBackTick(){fail("""
In file: [###]/in_memory0.fear

001| A:{ 'x .foo:A->A + A; } //ill formed: the first layer has to be 'this or nothing
   |   ^^^^^^^^^^^^^^^^^^^^^------------------------------------------

While inspecting the file
Unclosed "{" group.
Found a matching closer inside a string literal between here and the stopping point.
Did you mean to place the closer outside the string literal?
Otherwise expected one of: "}id", "}".
Error 0  Unclosed
""","""
A:{ 'x .foo:A->A + A; } //ill formed: the first layer has to be 'this or nothing
""");}
@Test void use_self(){fail("""
In file: [###]/in_memory0.fear

001| A:{ `abc .foo:A->A + A; } //ill formed: the first layer has to be `this or nothing
   | ~~~~~^^^~~~~~~~~~~~~~~~~~---------------------------------------------------------

While inspecting type declaration > full file
Self name abc invalid in a top level type.
Top level types self names can only be "`this".
Error 2  UnexpectedToken
""","""
A:{ `abc .foo:A->A + A; } //ill formed: the first layer has to be `this or nothing
""");}

@Test void use_self_inner(){ok("""
FileFull[renames=[],decs=[Declaration[name=TName[s=A,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional[Sig[rc=Optional.empty,m=Optional[MName[s=.foo,arity=0]],bs=Optional.empty,hasParenthesis=false,parameters=[],t=Optional[RCC[rc=Optional.empty,c=C[name=TName[s=A,arity=0],ts=Optional.empty]]]]],
body=Optional[DeclarationLiteralDeclaration[name=TName[s=B,arity=0],bs=Optional.empty,cs=[],
l=Literalx[M[sig=Optional[Sig[rc=Optional.empty,m=Optional[MName[s=.foo,arity=2]],bs=Optional.empty,hasParenthesis=false,parameters=[Parameter[xp=Optional[Name[x=y]],t=Optional.empty],Parameter[xp=Optional[Name[x=a]],t=Optional.empty]],t=Optional.empty]],body=Optional[Call[Call[this]MName[s=+,arity=1]false[x]]MName[s=+,arity=1]false[a]]]]]]]]]]]
""","""
A:{ .foo:A->B:{`x .foo y,a -> this + x + a; } }
""");}

@Test void method_with_parens_and_ret(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=Id, arity=0], bs=Optional.empty, cs=[], l=Literal[
M[sig=Optional[Sig[rc=Optional.empty, m=Optional[MName[s=.id, arity=1]], bs=Optional.empty, hasParenthesis=true, 
parameters=[Parameter[xp=Optional[Name[x=x]],t=Optional[RCC[rc=Optional.empty,c=C[name=TName[s=X,arity=0],ts=Optional.empty]]]]],t=Optional[RCC[rc=Optional.empty,c=C[name=TName[s=X,arity=0],ts=Optional.empty]]]]],
body=Optional[x]]]]]]
""","""
Id:{ .id(x:X):X -> x }
""");}
@Test void method_without_parens_sig_form(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=NoPar,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional[Sig[rc=Optional.empty,m=Optional[MName[s=.one,arity=1]],bs=Optional.empty,hasParenthesis=false,parameters=[
Parameter[xp=Optional[Name[x=x]],t=Optional[RCC[rc=Optional.empty,c=C[name=TName[s=X,arity=0],ts=Optional.empty]]]]],
t=Optional.empty]],body=Optional[x]]]]]]
""","""
NoPar:{ .one x:X -> x }
""");}
@Test void abstract_method_only_sig(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=Abs,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional[Sig[rc=Optional.empty,m=Optional[MName[s=.abs,arity=1]],bs=Optional.empty,hasParenthesis=true,parameters=[
Parameter[xp=Optional[Name[x=x]],t=Optional[RCC[rc=Optional.empty,c=C[name=TName[s=X,arity=0],ts=Optional.empty]]]]],
t=Optional[RCC[rc=Optional.empty,c=C[name=TName[s=X,arity=0],ts=Optional.empty]]]]],
body=Optional.empty]]]]]
""","""
Abs:{ .abs(x:X):X }
""");}
@Test void call_inside_body_simple_dotname(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=Sum,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional[
Sig[rc=Optional.empty,m=Optional[MName[s=.sum,arity=2]],bs=Optional.empty,hasParenthesis=true,parameters=[
Parameter[xp=Optional[Name[x=x]],t=Optional[RCC[rc=Optional.empty,c=C[name=TName[s=X,arity=0],ts=Optional.empty]]]],
Parameter[xp=Optional[Name[x=y]],t=Optional[RCC[rc=Optional.empty,c=C[name=TName[s=X,arity=0],ts=Optional.empty]]]]],
t=Optional[RCC[rc=Optional.empty,c=C[name=TName[s=X,arity=0],ts=Optional.empty]]]]],
body=Optional[Call[x]MName[s=.plus,arity=1]true[y]]]]]]]
""","""
Sum:{ .sum(x:X,y:X):X -> x.plus(y) }
""");}
@Test void round_group_in_body(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=Par,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional[Sig[rc=Optional.empty,m=Optional[MName[s=.paren,arity=1]],bs=Optional.empty,hasParenthesis=true,parameters=[
Parameter[xp=Optional[Name[x=x]],t=Optional[RCC[rc=Optional.empty,c=C[name=TName[s=X,arity=0],ts=Optional.empty]]]]],
t=Optional[RCC[rc=Optional.empty,c=C[name=TName[s=X,arity=0],ts=Optional.empty]]]]],
body=Optional[(x)]]]]]]
""","""
Par:{ .paren(x:X):X -> (x) }
""");}
@Test void typed_literal_in_body_unsigned(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=Lit,arity=0],bs=Optional.empty,cs=[],l=Literal[M[
sig=Optional[Sig[rc=Optional.empty,m=Optional[MName[s=.lit,arity=0]],bs=Optional.empty,hasParenthesis=true,parameters=[],
t=Optional[RCC[rc=Optional.empty,c=C[name=TName[s=+45,arity=0],ts=Optional.empty]]]]],
body=Optional[TypedLiteralRCC[rc=Optional.empty,c=C[name=TName[s=+45,arity=0],ts=Optional.empty]]
Literal[]]]]]]]
""","""
Lit:{ .lit(): +45 -> +45{} }//:+45 would (correctly) trigger BadOpDigit :+
""");}
@Test void typed_literal_in_body_with_rc(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=Lit2,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional[Sig[rc=Optional.empty,m=Optional[MName[s=.lit2,arity=0]],bs=Optional.empty,hasParenthesis=true,parameters=[],
t=Optional[RCC[rc=Optional.empty,c=C[name=TName[s=+45,arity=0],ts=Optional.empty]]]]],
body=Optional[TypedLiteralRCC[rc=Optional[read],c=C[name=TName[s=+45,arity=0],ts=Optional.empty]]
Literal[]]]]]]]
""","""
Lit2:{ .lit2(): +45 -> read +45{} }
""");}
@Test void literal_with_thisname_and_method1(){ok("""
[###]
body=Optional[self]
[###]
""","""
A:{Selfy:{`self .me():Selfy -> self}}
""");}
@Test void literal_with_thisname_and_method2(){ok("""
[###]
body=Optional[self]
[###]
""","""
B:{Selfy:{`self .me:Selfy -> self}}
""");}
@Test void stringInterpol_s(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=A,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional[Sig[rc=Optional.empty,m=Optional[MName[s=.a,arity=0]],bs=Optional.empty,hasParenthesis=false,parameters=[],t=Optional[RCC[rc=Optional.empty,c=C[name=TName[s=Str,arity=0],ts=Optional.empty]]]]],
body=Optional[Inter[true][0,0][abc\\ndef\\n][]]]]]]]
""","""
A:{.a:Str -> 
  |'abc
  |'def
}
""");}
@Test void stringInterpol_s_e(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=A,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional[Sig[rc=Optional.empty,m=Optional[MName[s=.a,arity=0]],bs=Optional.empty,hasParenthesis=false,parameters=[],t=Optional[RCC[rc=Optional.empty,c=C[name=TName[s=Str,arity=0],ts=Optional.empty]]]]],
body=Optional[Inter[true][1,0][ab,c\\ndef\\n]
[Call[TypedLiteralRCC[rc=Optional.empty,c=C[name=TName[s=B,arity=0],ts=Optional.empty]]]
MName[s=.foo,arity=1]true[TypedLiteralRCC[rc=Optional.empty,c=C[name=TName[s=C,arity=0],ts=Optional.empty]]]]]]]]]]
""","""
A:{.a:Str ->
  #|'ab{B.foo(C)}c
  |'def
}
""");}
@Test void calls_1(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=A,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional[Sig[rc=Optional.empty,m=Optional.empty,bs=Optional.empty,hasParenthesis=false,parameters=[
Parameter[xp=Optional[Name[x=x]],t=Optional.empty],
Parameter[xp=Optional[Name[x=y]],t=Optional.empty]],
t=Optional.empty]],
body=Optional[Call[x]MName[s=#,arity=1]false[y]]]]]]]
""","""
A:{x,y ->x#y;}
""");}
@Test void calls_2(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=A,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional[Sig[rc=Optional.empty,m=Optional.empty,bs=Optional.empty,hasParenthesis=false,parameters=[
Parameter[xp=Optional[Name[x=x]],t=Optional.empty],
Parameter[xp=Optional[Name[x=y]],t=Optional.empty]],
t=Optional.empty]],
body=Optional[Call[x]MName[s=#,arity=1]true[y]]]]]]]
""","""
A:{x,y, ->x#(y);}
""");}
@Test void calls_3(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=A,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional[Sig[rc=Optional.empty,m=Optional.empty,bs=Optional.empty,hasParenthesis=false,parameters=[
Parameter[xp=Optional[Name[x=x]],t=Optional.empty],
Parameter[xp=Optional[Name[x=y]],t=Optional.empty]],
t=Optional.empty]],
body=Optional[Call[x]MName[s=++,arity=1]false[y]]]]]]]
""","""
A:{x,y ->x++y}
""");}
@Test void calls_4(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=A,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional[Sig[rc=Optional.empty,m=Optional.empty,bs=Optional.empty,hasParenthesis=false,parameters=[
Parameter[xp=Optional[Name[x=x]],t=Optional.empty],
Parameter[xp=Optional[Name[x=y]],t=Optional.empty]],
t=Optional.empty]],
body=Optional[Call[x]MName[s=.foo,arity=1]false[y]]]]]]]
""","""
A:{x,y ->x .foo y}
""");}

@Test void calls_5(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=A,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional[Sig[rc=Optional.empty,m=Optional.empty,bs=Optional.empty,hasParenthesis=false,parameters=[
Parameter[xp=Optional[Name[x=x]],t=Optional.empty],
Parameter[xp=Optional[Name[x=y]],t=Optional.empty]],
t=Optional.empty]],
body=Optional[Call[::]MName[s=.foo,arity=1]false[y]]]]]]]
""","""
A:{x,y ->::.foo y}
""");}

@Test void eq_1(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=A,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional.empty,body=Optional[
Call[Call[Call[
TypedLiteralRCC[rc=Optional.empty,c=C[name=TName[s=Block,arity=0],ts=Optional.empty]]]
MName[s=#,arity=0]false[]]
MName[s=.let,arity=2]falseName[x=x][Literal[M[sig=Optional.empty,body=Optional[TypedLiteralRCC[rc=Optional.empty,c=C[name=TName[s=5,arity=0],ts=Optional.empty]]]]]]]
MName[s=.return,arity=1]false[Literal[M[sig=Optional.empty,body=Optional[
Call[x]MName[s=*,arity=1]false[TypedLiteralRCC[rc=Optional.empty,c=C[name=TName[s=2,arity=0],ts=Optional.empty]]]]]]]]]]]]]
""","""
A:{Block#.let x= {5} .return {x*2} }
""");}

@Test void calls_square_rc_only(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=A,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional[Sig[rc=Optional.empty,m=Optional.empty,bs=Optional.empty,hasParenthesis=false,parameters=[
Parameter[xp=Optional[Name[x=x]],
t=Optional.empty]],t=Optional.empty]],
body=Optional[Call[x]MName[s=.foo,arity=0]
CallSquare[rc=Optional[read],ts=[]]false[]]]]]]]
""","""
A:{ x -> x.foo[read] }
""");}
@Test void calls_square_rc_only_comma_ok(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=A,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional[Sig[rc=Optional.empty,m=Optional.empty,bs=Optional.empty,hasParenthesis=false,parameters=[
Parameter[xp=Optional[Name[x=x]],
t=Optional.empty]],t=Optional.empty]],
body=Optional[Call[x]MName[s=.foo,arity=0]
CallSquare[rc=Optional[read],ts=[]]false[]]]]]]]
""","""
A:{ x -> x.foo[read,] }
""");}
@Test void calls_square_rc_T(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=A,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional[Sig[rc=Optional.empty,m=Optional.empty,bs=Optional.empty,hasParenthesis=false,parameters=[
Parameter[xp=Optional[Name[x=x]],t=Optional.empty]],
t=Optional.empty]],
body=Optional[Call[x]MName[s=.foo,arity=0]
CallSquare[rc=Optional[read],ts=[RCC[rc=Optional.empty,c=C[name=TName[s=X,arity=0],ts=Optional.empty]]]]false[]]]]]]]
""","""
A:{ x -> x.foo[read,X] }
""");}
@Test void mini_inner_Declaration(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=A,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional[Sig[rc=Optional.empty,m=Optional[
MName[s=.m,arity=0]],bs=Optional.empty,hasParenthesis=false,parameters=[],t=Optional.empty]],
body=Optional[DeclarationLiteralDeclaration[name=TName[s=B,arity=0],bs=Optional.empty,cs=[],l=Literal[]]]]]]]]
""","""
A:{ .m -> B:{} }
""");}

@Test void destructEq(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=A,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional[Sig[rc=Optional.empty,m=Optional[MName[s=.m,arity=0]],bs=Optional.empty,hasParenthesis=false,parameters=[],t=Optional.empty]],
body=Optional[Call[Call[Call[
TypedLiteralRCC[rc=Optional.empty,c=C[name=TName[s=Block,arity=0],ts=Optional.empty]]]
MName[s=#,arity=0]false[]]
MName[s=.let,arity=2]false
Destruct[extract=[[MName[s=.name,arity=0],MName[s=.size,arity=0]],[MName[s=.age,arity=0]]],
id=Optional[Bob]][Literal[]]]
MName[s=.use,arity=2]true[sizeBob,ageBob]]]]]]]
""","""
A:{ .m -> Block#.let {.name.size,.age}Bob = {} .use(sizeBob,ageBob) }
""");}
@Test void eRound1(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=A,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional[Sig[rc=Optional.empty,m=Optional[MName[s=.m,arity=0]],bs=Optional.empty,hasParenthesis=false,parameters=[],t=Optional.empty]],body=Optional[
Call[(Call[Call[
TypedLiteralRCC[rc=Optional.empty,c=C[name=TName[s=Block,arity=0],ts=Optional.empty]]]
MName[s=#,arity=0]false[]]
MName[s=.let,arity=2]falseName[x=x]
[Literal[M[sig=Optional.empty,body=Optional[TypedLiteralRCC[rc=Optional.empty,c=C[name=TName[s=5,arity=0],ts=Optional.empty]]]]]])]
MName[s=.use,arity=1]true
[TypedLiteralRCC[rc=Optional.empty,c=C[name=TName[s=5,arity=0],ts=Optional.empty]]]]]]]]]
""","""
A:{ .m -> (Block#.let x={5}) .use(5) }
""");}

@Test void missingReturnType(){fail("""
In file: [###]/in_memory0.fear

001| A:{ .m(): -> (Block#.let x={5}) .use(x) }
   | ----~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~--

While inspecting method signature > method declaration > type declaration body > type declaration > full file
Missing type name.
Expected "TypeName".
Error 2  UnexpectedToken
""","""
A:{ .m(): -> (Block#.let x={5}) .use(x) }
""");}
@Test void useOutOfScope1(){fail("""
In file: [###]/in_memory0.fear

001| A:{ .m -> (Block#.let x={5}) .use(x) }
   | ----------~~~~~~~~~~~~~~~~~~~~~~~~^~--

While inspecting arguments list > method body > method declaration > type declaration body > type declaration > full file
Name "x" is not in scope
In scope: "this".
Error 2  UnexpectedToken
""","""
A:{ .m -> (Block#.let x={5}) .use(x) }
""");}

@Test void useOutOfScope2(){fail("""
In file: [###]/in_memory0.fear

001| A:{ .m ->
002| ( (Block#.let x={5}) .use(x) )
   | --------------------------^---

While inspecting arguments list > expression in round parenthesis > method body > method declaration > type declaration body > type declaration > full file
Name "x" is not in scope
In scope: "this".
Error 2  UnexpectedToken
""","""
A:{ .m -> 
( (Block#.let x={5}) .use(x) )
 }
""");}

@Test void useOutOfScope3(){fail("""
In file: [###]/in_memory0.fear

001| A:{ .m ->
002| (   (  (Block#.let x={5}) .use(x)       )      )
   | ----~~~~~~~~~~~~~~~~~~~~~~~~~~~^~~~~~~~~~-------

While inspecting arguments list > expression in round parenthesis > expression in round parenthesis > method body > method declaration > type declaration body > type declaration > full file
Name "x" is not in scope
In scope: "this".
Error 2  UnexpectedToken
""","""
A:{ .m -> 
(   (  (Block#.let x={5}) .use(x)       )      )
 }
""");}


@Test void eqNoExprRounds(){fail("""
In file: [###]/in_memory0.fear

001| A:{ .m ->
002| (   (    Block#.let x= .use(x)    )      )
   | ----~~~~~~~~~~~~~~~~~~~^^^^^^^~~~~~-------

While inspecting expression in round parenthesis > expression in round parenthesis > method body > method declaration > type declaration body > type declaration > full file
Missing expression after "=" in the equals sugar.
Use: ".m x = expression" or ".m {a,b} = expression".
Error 2  UnexpectedToken
""","""
A:{ .m -> 
(   (    Block#.let x= .use(x)    )      )
 }
""");}


@Test void doubleComma(){fail("""
In file: [###]/in_memory0.fear

001| A:{ .m(a,,b):C }
   | ----~~~~~^~~~~--

While inspecting method parameters declaration > method declaration > type declaration body > type declaration > full file
Missing type name.
Expected "TypeName".
Error 2  UnexpectedToken
""","""
A:{ .m(a,,b):C }
""");}

@Test void doubleCommaArg(){fail("""
In file: [###]/in_memory0.fear

001| A:{ .m(x:C):C->x.foo(,) }
   | ---------------~~~~~~^~--

While inspecting arguments list > method body > method declaration > type declaration body > type declaration > full file
Missing expression.
Expected one of: "name", "TypeName", "(", "{".
Error 2  UnexpectedToken
""","""
A:{ .m(x:C):C->x.foo(,) }
""");}

@Test void err_illegal_tab_char(){fail("""
In file: [###]/in_memory0.fear

001| A:{      .m(x:C):C->x.foo(,) }
   |     ^^^^

While inspecting the file
Illegal character [TAB 0x09]
Error 2  UnexpectedToken
""","""
A:{ \t .m(x:C):C->x.foo(,) }
""");}

@Test void err_unclosed_curly_in_decl(){fail("""
In file: [###]in_memory0.fear

001| A:{
   |   ^

While inspecting the file
File ended while parsing a "{" group.
This "{" may be unintended.
Otherwise expected one of: "}id", "}".
Error 0  Unclosed
""","""
A:{
""");}

@Test void err_unclosed_curly_long(){fail("""
In file: [###]in_memory0.fear

001| A:{ fdfdds
   |   ^

While inspecting the file
File ended while parsing a "{" group.
This "{" may be unintended.
Otherwise expected one of: "}id", "}".
Error 0  Unclosed
""","""
A:{ fdfdds
dsdds
fssdf
sdf()fg
g

  gg
fff
""");}

@Test void multi_inside_signature_doubleComma(){fail("""
In file: [###]/in_memory0.fear

001| A:{
002| `self
003| .m(a,,b):C -> self
   | ~~~~~^~~~~--------
004| //comment
005| }

While inspecting method parameters declaration > method signature > method declaration > type declaration body > type declaration > full file
Missing type name.
Expected "TypeName".
Error 2  UnexpectedToken
""","""
A:{
`self
.m(a,,b):C -> self
//comment
}
""");}

@Test void ok_comma_single_arg(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=A,arity=0],bs=Optional.empty,cs=[],l=Literal[
M[sig=Optional[Sig[rc=Optional.empty,m=Optional[MName[s=.m,arity=1]],bs=Optional.empty,hasParenthesis=true,parameters=[
Parameter[xp=Optional[Name[x=x]],t=Optional[RCC[rc=Optional.empty,c=C[name=TName[s=C,arity=0],ts=Optional.empty]]]]],
t=Optional[RCC[rc=Optional.empty,c=C[name=TName[s=C,arity=0],ts=Optional.empty]]]]],
body=Optional[Call[Call[Call[Call[TypedLiteralRCC[rc=Optional.empty,c=C[name=TName[s=Block,arity=0],ts=Optional.empty]]]
MName[s=#,arity=0]false[]]
MName[s=.let,arity=2]falseName[x=z][Literal[
M[sig=Optional.empty,body=Optional[TypedLiteralRCC[rc=Optional.empty,c=C[name=TName[s=5,arity=0],ts=Optional.empty]]]]]]]
MName[s=.use,arity=1]true[z]]
MName[s=.use,arity=1]true[z]]]]]]]
""","""
A:{
.m(x:C):C ->
Block#.let z={5}
.use(z,)
.use(z)
}
""");}
@Test void multi_caret_middle_nameNotInScope(){fail("""
In file: [###]/in_memory0.fear

003| Block#.let x={5}
004| .use(x)
005| .use(y)
   |      ^

While inspecting arguments list > method body > method declaration > type declaration body > type declaration > full file
Name "y" is not in scope
In scope: "this", "x".
Error 2  UnexpectedToken
""","""
A:{
.m ->
Block#.let x={5}
.use(x)
.use(y)
}
""");}

@Test void multi_caret_last_nameNotInScope(){ fail("""
In file: [###]/in_memory0.fear

002| .m ->
003| .use(y)
   | ^^^^^^^

While inspecting method body > method declaration > type declaration body > type declaration > full file
Missing expression.
Found instead: ".use".
Expected one of: "name", "TypeName", "(", "{".
Error 2  UnexpectedToken
""","""
A:{
.m ->
.use(y)
}
""");}

@Test void multi_args_missing_expr_multiline(){fail("""
In file: [###]/in_memory0.fear

003| x.foo(
004|  ,)
   |  ^

While inspecting arguments list > method body > method declaration > type declaration body > type declaration > full file
Missing expression.
Expected one of: "name", "TypeName", "(", "{".
Error 2  UnexpectedToken
""","""
A:{
.m(x:C):C ->
x.foo(
 ,)
}
""");}

@Test void multi_firstContentLine_nameNotInScope_body(){fail("""
In file: [###]/in_memory0.fear

001| A:{//comment1
002| .m -> y;//removing this semicol should give a clear missing separator error
   | ------^
003| .n -> {}
004| /*comment2*/}//comment3

While inspecting method body > method declaration > type declaration body > type declaration > full file
Name "y" is not in scope
In scope: "this".
Error 2  UnexpectedToken
""","""
A:{//comment1
.m -> y;//removing this semicol should give a clear missing separator error
.n -> {}
/*comment2*/}//comment3
""");}

@Test void multi_firstContentLine_nameNotInScope_body2(){fail("""
In file: [###]/in_memory0.fear

001| A:{
002| .m -> y;//removing this semicol should give a clear missing separator error
   | ------^
003| .n -> {}
004| }

While inspecting method body > method declaration > type declaration body > type declaration > full file
Name "y" is not in scope
In scope: "this".
Error 2  UnexpectedToken
""","""
A:{
.m -> y;//removing this semicol should give a clear missing separator error
.n -> {}
}
""");}

@Test void multi_firstContentLine_nameNotInScope_body_NoSemi(){fail("""
In file: [###]/in_memory0.fear

002| .m -> y
003| .n -> {}
   |    ^^

While inspecting method declaration > type declaration body > type declaration > full file
There is a missing ";", operator or method name here or before
Error 6  MissingSeparator
""","""
A:{
.m -> y
.n -> {}
}
""");}

@Test void err_unopened_curly_top(){fail("""
In file: [###]in_memory0.fear

001| A: a b c } f e
   | ^^^^^^^^^^

While inspecting the file
Unopened "}".
This "}" may be unintended.
Error 1  Unopened
""","""
A: a b c } f e
""");}
@Test void err_bad_expr(){fail("""
In file: [###]in_memory0.fear

001| A:{ .m -> :+45 }
   | ----~~~~~~^^^^--

While inspecting method declaration > type declaration body > type declaration > full file
Missing expression.
Found instead: ":".
Expected one of: "name", "TypeName", "(", "{".
Error 2  UnexpectedToken
""","""
A:{ .m -> :+45 }
""");}
@Test void err_bad_open_square_with_space(){fail("""
In file: [###]in_memory0.fear

001| A:{ x -> x.foo [read] }
   |                ^

While inspecting the file
Unrecognized text "[".
Here we expect "[" as a generic/RC argument opener and must follow the name with no space.
Write "Foo[Bar]" not "Foo [Bar]".
Write "x.foo[read]" not "x.foo [read]".
Error 2  UnexpectedToken
""","""
A:{ x -> x.foo [read] }
""");}
@Test void err_bad_op_line_pipe_before_quote(){fail("""
In file: [###]in_memory0.fear

001| A:{ .m -> +|'a'
   |           ^^

While inspecting the file
Unrecognized text "+|".
A "|" immediately before a quote starts a line string (e.g. `|"abc"` or `|'abc'`).
Operators can also contain "|", making it ambiguous what, for example, `<--|'foo'` means.
It could be the "<--" operator followed by `|'foo'` but also the "<--|" operator followed by `'foo'`.
Please add spaces to disambiguate:  `<--| 'foo'`   or   `<-- |'foo'`
Error 2  UnexpectedToken
""","""
A:{ .m -> +|'a'
  }
""");}
@Test void err_disallowed_readH_on_closure(){fail("""
In file: [###]in_memory0.fear

001| A:{ .m -> readH +5{} }
   | ----~~~~~~^^^^^~~~~~--

While inspecting method body > method declaration > type declaration body > type declaration > full file
Capability readH used.
Capabilities readH and mutH are not allowed on closures
Use one of read, mut, imm, iso.
Error 2  UnexpectedToken
""","""
A:{ .m -> readH +5{} }
""");}
@Test void err_disallowed_mutH_on_closure(){fail("""
In file: [###]in_memory0.fear

001| A:{ .m -> mutH -5{} }
   | ----~~~~~~^^^^~~~~~--

While inspecting method body > method declaration > type declaration body > type declaration > full file
Capability mutH used.
Capabilities readH and mutH are not allowed on closures
Use one of read, mut, imm, iso.
Error 2  UnexpectedToken
""","""
A:{ .m -> mutH -5{} }
""");}
@Test void err_missing_expr_after_eq_sugar(){fail("""
In file: [###]in_memory0.fear

001| A:{ .m -> Block#.let x= .use(x) }
   | ----------~~~~~~~~~~~~~~^^^^^^^--

While inspecting method body > method declaration > type declaration body > type declaration > full file
Missing expression after "=" in the equals sugar.
Use: ".m x = expression" or ".m {a,b} = expression".
Error 2  UnexpectedToken
""","""
A:{ .m -> Block#.let x= .use(x) }
""");}

@Test void err_name_redeclared_param(){fail("""
In file: [###]in_memory0.fear

001| A:{ .m(x,x) -> x }
   | ----^^^^^^^~~~~~--

While inspecting method signature > method declaration > type declaration body > type declaration > full file
A method signature cannot declare multiple parameters with the same name
Parameter "x" is repeated
Error 2  UnexpectedToken
""","""
A:{ .m(x,x) -> x }
""");}

//@Test void err_generic_not_in_scope_in_sig(){fail("""
//""","""
//A:{ .m(x:X):X -> x }
//""");}//NOPE, that becomes just a type name

@Test void err_type_name_conflicts_with_generic_in_impl(){fail("""
In file: [###]in_memory0.fear

001| A[X]: X {}
   | ------^---

While inspecting super types declaration > type declaration > full file
Name "X" is used as a type name, but  "X" is already a generic type parameter in scope
Error 2  UnexpectedToken
""","""
A[X]: X {}
""");}

@Test void err_bad_generic_bound_operator(){fail("""
In file: [###]/in_memory0.fear

001| A[X:***]:{}
   | --~~^^^----

While inspecting generic bounds declaration > type declaration > full file
Invalid bound for generic X
Only '*' or '**' are allowed here
Write: X:*   meaning mut,read,imm
   or: X:**  meaning everything
Error 2  UnexpectedToken
""","""
A[X:***]:{}
""");}

@Test void err_name_redeclared_param2(){fail("""
In file: [###]/in_memory0.fear

001| A:{ .m(x,x) -> x }
   | ----^^^^^^^~~~~~--

While inspecting method signature > method declaration > type declaration body > type declaration > full file
A method signature cannot declare multiple parameters with the same name
Parameter "x" is repeated
Error 2  UnexpectedToken
""","""
A:{ .m(x,x) -> x }
""");
}

@Test void err_space_before_destruct_id(){fail("""
In file: [###]/in_memory0.fear

001| A:{ .m({.a} Bob:X):X }
   | -------~~~~~^^^~~-----

While inspecting method parameters declaration > method declaration > type declaration body > type declaration > full file
Found spacing between closed curly and destruct id "Bob".
There need to be no space between the closed curly and the destruct id.
Error 2  UnexpectedToken
""","""
A:{ .m({.a} Bob:X):X }
""");
}

@Test void err_illegal_nbsp_char(){fail("""
In file: [###]/in_memory0.fear

001| A:{·.m():X }
   |    ^

While inspecting the file
Illegal character [NBSP 0x00A0]
Error 2  UnexpectedToken
""",
"A:{\u00A0.m():X }");
}

//U+200D first, then NBSP, BOM, RLO
@Test void err_illegal_zwj_char_and_more(){fail("""
In file: [###]/in_memory0.fear

001| A:{\u00B7\u00B7\uFFFD\uFFFD.m():X }
   |    ^

While inspecting the file
Illegal character [ZWJ 0x200D]
Error 2  UnexpectedToken
""",
"A:{\u200D\u00A0\uFEFF\u202E.m():X }");
}

//U+202E first, then NBSP, ZWJ, ZWNJ
@Test void err_illegal_rlo_char_and_more(){fail("""
In file: [###]/in_memory0.fear

001| A:{\uFFFD\u00B7\u00B7\u00B7.m():X }
   |    ^

While inspecting the file
Illegal character [RLO 0x202E]
Error 2  UnexpectedToken
""",
"A:{\u202E\u00A0\u200D\u200C.m():X }");
}

// U+FEFF first, then ZWSP, IDEOGRAPHIC SPACE
@Test void err_illegal_bom_char_and_more(){fail("""
In file: [###]/in_memory0.fear

001| A:{\uFFFD\u00B7\u00B7.m():X }
   |    ^

While inspecting the file
Illegal character [BOM 0xFEFF]
Error 2  UnexpectedToken
""",
"A:{\uFEFF\u200B\u3000.m():X }");
}
// U+3000 first, then ZWSP, RLM, NBSP
@Test void err_illegal_ideographic_space_and_more(){fail("""
In file: [###]/in_memory0.fear

001| A:{\u00B7\u00B7\uFFFD\u00B7.m():X }
   |    ^

While inspecting the file
Illegal character [IDEOGRAPHIC SPACE 0x3000]
Error 2  UnexpectedToken
""",
"A:{\u3000\u200B\u200F\u00A0.m():X }");
}
// 😀 first, then NBSP, ZWJ
@Test void err_illegal_emoji_and_more(){fail("""
In file: [###]/in_memory0.fear

001| A:{\uFFFD\u00B7\u00B7.m():X }
   |    ^

While inspecting the file
Illegal character "\\uD83D\\uDE00"
Error 2  UnexpectedToken
""",
"A:{\uD83D\uDE00\u00A0\u200D.m():X }");
}

@Test void inter_deep_bad_equals_sugar_fail(){ fail("""
In file: [###]/in_memory0.fear

002| .m:Str ->
003| #|'Head { Block#.let x= .use(x) } Tail
   | ----------~~~~~~~~~~~~~~^^^^^^^~~-----

While inspecting string interpolation expression > method body > method declaration > type declaration body > type declaration > full file
Missing expression after "=" in the equals sugar.
Use: ".m x = expression" or ".m {a,b} = expression".
Error 2  UnexpectedToken
""","""
A:{
.m:Str ->
#|'Head { Block#.let x= .use(x) } Tail
}
"""); }


@Test void inter_deep_bad_equals_sugar_fail_twice_a(){ fail("""
In file: [###]/in_memory0.fear

002| .m:Str ->
003| #|'Head { Block#.let x= .use(x) } Tail1 { Block#.let xy= .golden(xy) } Tail2 End
   | ----------~~~~~~~~~~~~~~^^^^^^^~~-----------------------------------------------

While inspecting string interpolation expression > method body > method declaration > type declaration body > type declaration > full file
Missing expression after "=" in the equals sugar.
Use: ".m x = expression" or ".m {a,b} = expression".
Error 2  UnexpectedToken
""","""
A:{
.m:Str ->
#|'Head { Block#.let x= .use(x) } Tail1 { Block#.let xy= .golden(xy) } Tail2 End 
}
"""); }

@Test void inter_deep_bad_equals_sugar_fail_twice_b(){ fail("""
In file: [###]/in_memory0.fear

002| .m(x):Str ->
003| #|'Head { Block#.let    .use(x) } Tail1 { Block#.let xy= .golden(xy) } Tail2 End
   | ------------------------------------------~~~~~~~~~~~~~~~^^^^^^^^^^^~~----------

While inspecting string interpolation expression > method body > method declaration > type declaration body > type declaration > full file
Missing expression after "=" in the equals sugar.
Use: ".m x = expression" or ".m {a,b} = expression".
Error 2  UnexpectedToken
""","""
A:{
.m(x):Str ->
#|'Head { Block#.let    .use(x) } Tail1 { Block#.let xy= .golden(xy) } Tail2 End 
}
"""); }


@Test void inter_deep_bad_equals_sugar_fail_round(){ fail("""
In file: [###]/in_memory0.fear

002| .m:Str ->
003| #|'Head {     ( /*a*/ (Block#.let x= .use(x)) /*bb*/ ) } Tail
   | --------------~~~~~~~~~~~~~~~~~~~~~~~^^^^^^^~~~~~~~~~~-------

While inspecting expression in round parenthesis > expression in round parenthesis > string interpolation expression > method body > method declaration > type declaration body > type declaration > full file
Missing expression after "=" in the equals sugar.
Use: ".m x = expression" or ".m {a,b} = expression".
Error 2  UnexpectedToken
""","""
A:{
.m:Str ->
#|'Head {     ( /*a*/ (Block#.let x= .use(x)) /*bb*/ ) } Tail
}
"""); }

@Test void badClose_noOpen(){ fail("""
In file: [###]in_memory0.fear

002| .m:Str ->
003| #|'Head } ss
   | --^^^^^^^---

While inspecting method body > method declaration > type declaration body > type declaration > full file
Unopened string interpolation placeholder
Error 8  InterpolationNoOpen
""","""
A:{
.m:Str ->
#|'Head } ss
}
"""); }

@Test void inter_deep_bad_equals_sugar_ok(){ fail("""
In file: [###]in_memory0.fear

002| .m:Str ->
003| #|'Head { Block#.let x={5} .use(x) } Tail
   | --------^^^^^^^^^^^^^^^^-----------------

While inspecting method body > method declaration > type declaration body > type declaration > full file
String interpolation placeholder opened inside interpolation expression.
Note: "{" can not be used in single "#" interpolation expressions. Use at least "##".
Error 7  InterpolationNoClose
""","""
A:{
.m:Str ->
#|'Head { Block#.let x={5} .use(x) } Tail
}
"""); }

@Test void inter_deep_ok(){ ok("""
[###]
body=Optional[Inter[true][2]
[Head,Tail\\n]
[Call[Call[Call[TypedLiteralRCC[rc=Optional.empty,c=C[name=TName[s=Block,arity=0],ts=Optional.empty]]]
MName[s=#,arity=0]false[]]MName[s=.let,arity=2]falseName[x=x][Literal[M[sig=Optional.empty,body=Optional[TypedLiteralRCC[rc=Optional.empty,c=C[name=TName[s=5,arity=0],ts=Optional.empty]]]]]]]
MName[s=.use,arity=1]true[x]]]]]]]]
""","""
A:{
.m:Str ->
##|'Head {{ Block#.let x={5} .use(x) }} Tail
}
"""); }

@Test void inter_hash_no_opener_early_close_fail(){ fail("""
In file: [###]in_memory0.fear

002| .m:Str ->
003| #|" foo } bar
   | --^^^^^^^----

While inspecting method body > method declaration > type declaration body > type declaration > full file
Unopened string interpolation placeholder
Error 8  InterpolationNoOpen
""","""
A:{
.m:Str ->
#|" foo } bar
}
"""); }

@Test void inter_hash_early_close_then_opener_fail(){ fail("""
In file: [###]in_memory0.fear

002| .m:Str ->
003| #|' foo } bar {B.foo(C)} end
   | --^^^^^^^-------------------

While inspecting method body > method declaration > type declaration body > type declaration > full file
Unopened string interpolation placeholder
Error 8  InterpolationNoOpen
""","""
A:{
.m:Str ->
#|' foo } bar {B.foo(C)} end
}
"""); }

@Test void inter_hash_h1_ok_simple_expr1(){ ok("""
[###]
body=Optional[Inter[true][1][pre,post\\n]
[Call[TypedLiteralRCC[rc=Optional.empty,c=C[name=TName[s=B,arity=0],
[###]
""","""
A:{
.m:Str ->
#|' pre {B.foo(C)} post
}
"""); }

@Test void inter_hash_h1_ok_simple_expr2(){ ok("""
[###]
body=Optional[Inter[true][1][$pre$,$post$,$dada$\\n]
[Call[TypedLiteralRCC[rc=Optional.empty,c=C[name=TName[s=B,arity=0],
[###]
""","""
A:{
.m:Str ->
#|'$pre${B.foo(C)}$post${B}$dada$
}
"""); }

@Test void inter_hash_h1_ok_round_parens_only(){ ok("""
[###]
""","""
A:{
.m(x:X,y:X):Str ->
#|' pre { x.plus(y) } post
}
"""); }

@Test void inter_hash_outer_curly_leftovers_literal_ok(){ ok("""
[###]
body=Optional[Inter[true][1][a{{,}}b\\n][
Call[TypedLiteralRCC[rc=Optional.empty,c=C[name=TName[s=B,arity=0],
ts=Optional.empty]]]
MName[s=.foo,arity=1]true[TypedLiteralRCC[rc=Optional.empty,c=C[name=TName[s=C,arity=0],ts=Optional.empty]]]]]]]]]]
""","""
A:{
.m:Str ->
#|' a {{{B.foo(C)}}} b
}
"""); }

@Test void inter_hash_after_closer_literal_close_brace_fail(){ fail("""
In file: [###]in_memory0.fear

002| .m:Str ->
003| #|' pre {B.foo(C)} } tail
   | -----------------^^^-----

While inspecting method body > method declaration > type declaration body > type declaration > full file
Unopened string interpolation placeholder
Error 8  InterpolationNoOpen
""","""
A:{
.m:Str ->
#|' pre {B.foo(C)} } tail
}
"""); }

@Test void inter_hash_multi_interpolations_h1_ok_5x(){ ok("""
[###]body=Optional[Inter[true][1]
[aa,b,ccc{,}d{,}ee,z\\n][x1,x2,x3,x4,x5]]]]]]]
""","""
A:{
.m(x1,x2,x3,x4,x5):Str ->
#|' aa{x1} b {x2}ccc{{x3}} d {{x4}} ee{x5} z
}
"""); }

@Test void inter_hash_h2_ok_curly_in_body(){ ok("""
[###]
""","""
A:{
.m:Str ->
##|' Head {{ Block#.let x={5} .use(x) }} Tail
}
"""); }

@Test void inter_hash_h2_adjacent_closers_fail_require_space(){ fail("""
In file: [###]/in_memory0.fear

002| .m:Str ->
003| ##|' pre {{ +5{}}} post
   | ------------~~^--------

While inspecting string interpolation expression > method body > method declaration > type declaration body > type declaration > full file
Interpolation expression ended while parsing a "{" group.
This "{" may be unintended.
Otherwise expected one of: "}id", "}".
Error 0  Unclosed
""","""
A:{
.m:Str ->
##|' pre {{ +5{}}} post
}
"""); }

//ok because spaces
@Test void inter_hash_h2_adjacent_closers_ok_with_space(){ ok("""
[###]
""","""
A:{
.m:Str ->
##|' pre {{ +5{} }} post
}
"""); }

@Test void inter_hash_h2_two_interpolations_back_to_back_ok(){ ok("""
[###]body=Optional[Inter[true][2]
[a,,z\\n]
[Call[###]
""","""
A:{
.m:Str ->
##|' a {{B.foo(C)}}{{B.foo(C)}} z
}
"""); }

@Test void inter_hash_h2_early_shortclose_before_opener(){ ok("""
[###]
""","""
A:{
.m:Str ->
##|' foo } bar {{B.foo(C)}} end
}
"""); }

@Test void inter_hash_h2_after_closer_literal_close_brace(){ ok("""
[###]
""","""
A:{
.m:Str ->
##|' pre {{B.foo(C)}} } tail
}
"""); }

@Test void inter_hash_multi_interpolations_h2_ok_5x(){ ok("""
[###]
""","""
A:{
.m:Str ->
##|' a {{B.foo(C)}} b {{B.foo(C)}} c {{B.foo(C)}} d {{B.foo(C)}} e {{B.foo(C)}} z
}
"""); }

@Test void inter_hash_h3_fail(){ fail("""
In file: [###]/in_memory0.fear

002| .m:Str ->
003| ###|' pre {{{ +5{} }} mid
   | ----^^^^^^^^^------------

While inspecting method body > method declaration > type declaration body > type declaration > full file
Unclosed string interpolation placeholder
Error 7  InterpolationNoClose
""","""
A:{
.m:Str ->
###|' pre {{{ +5{} }} mid
}
"""); }
@Test void inter_hash_h3_pass(){ ok("""
[###]
""","""
A:{
.m:Str ->
###|' pre {{{ +5{} }}} mid
}
"""); }

@Test void inter_hash_h3_outer_leftovers_literal_ok(){ ok("""
[###]
[aa {,} bb\\n]
[###]
""","""
A:{
.m:Str ->
###|' aa {{{{B.foo(C)}}}} bb
}
"""); }

@Test void inter_hash_h4_simple_ok(){ ok("""
[###]
[head,tail\\n]
[###]
""","""
A:{
.m:Str ->
####|' head {{{{B.foo(C)}}}} tail
}
"""); }

@Test void doubleclose_h4(){ fail("""
In file: [###]/in_memory0.fear

002| .m:Str ->
003| ####|' {{{{B.foo(C)}}}} ddd }}}} end
   | ----------------------^^^^^^^^^^----

While inspecting method body > method declaration > type declaration body > type declaration > full file
Unopened string interpolation placeholder
Error 8  InterpolationNoOpen
""","""
A:{
.m:Str ->
####|' {{{{B.foo(C)}}}} ddd }}}} end
}
"""); }

@Test void inter_hash_mixed_outer_openers_literal(){ fail("""
In file: [###]/in_memory0.fear

002| .m:Str ->
003| #|' L {{R {{B.foo(C)}} R}} L
   | ------^^^^^-----------------

While inspecting method body > method declaration > type declaration body > type declaration > full file
String interpolation placeholder opened inside interpolation expression.
Note: "{" can not be used in single "#" interpolation expressions. Use at least "##".
Error 7  InterpolationNoClose
""","""
A:{
.m:Str ->
#|' L {{R {{B.foo(C)}} R}} L
}
"""); }

@Test void inter_hash_line_with_no_hash_ok_literal_brace(){ ok("""
[###]
""","""
A:{
.m:Str ->
|' this is always fine: } and { both literal
}
"""); }

@Test void inter_hash_h1_many_interps_and_text_ok(){ ok("""
[###]
[a,bc,de,fg,hi,j\\n]
[###]
""","""
A:{
.m:Str ->
#|' a {B.foo(C)} b c {B.foo(C)} d e {B.foo(C)} f g {B.foo(C)} h i {B.foo(C)} j
}
"""); }

@Test void inter_hash_h2_unclosed_due_to_missing_third_brace_fail(){ fail("""
In file: [###]/in_memory0.fear

002| .m:Str ->
003| ##|' start {{ foo.bar{ baz .toList }} end
   | --------------~~~~~~~^~~~~~~~~~~~~-------

While inspecting string interpolation expression > method body > method declaration > type declaration body > type declaration > full file
Interpolation expression ended while parsing a "{" group.
This "{" may be unintended.
Otherwise expected one of: "}id", "}".
Error 0  Unclosed
""","""
A:{
.m:Str ->
##|' start {{ foo.bar{ baz .toList }} end
}
"""); }

@Test void inter_hash_h2_fix_unclosed_with_space_and_extra_closer_ok(){ ok("""
[###]
""","""
A:{
.m:Str ->
##|' start {{ Foo.bar{ Baz .toList } }} end
}
"""); }


@Test void inter_hash_brace_mismatch_first_fail(){ ok("""
[###]
[a{,}b\\n]
[###]
""","""
A:{
.m:Str ->
#|'a{{B.foo(C)}}b
}
"""); }

@Test void inter_hash_brace_mismatch_first_ok(){ ok("""
[###]
[a,b\\n]
[###]
""","""
A:{
.m:Str ->
##|'a{{B.foo(C)}}b
}
"""); }

@Test void inter_two_interps_second_bad_fail(){ fail("""
In file: [###]/in_memory0.fear

002| .m:Str ->
003| #|'pre{B.foo(C)}mid{x.bar(1,2}post
   | --------------------~~~~~^~~~-----

While inspecting string interpolation expression > method body > method declaration > type declaration body > type declaration > full file
Interpolation expression ended while parsing a "(" group.
This "(" may be unintended.
Otherwise expected ")".
Error 0  Unclosed
""","""
A:{
.m:Str ->
#|'pre{B.foo(C)}mid{x.bar(1,2}post
}
"""); }

@Test void inter_two_interps_second_bad_ok(){ ok("""
[###]
[pre,mid,post\\n]
[###]
""","""
A:{
x ->
#|'pre{B.foo(C)}mid{x.bar(1,2)}post
}
"""); }

@Test void inter_expr_then_chain_bad_args_fail(){ fail("""
In file: [###]/in_memory0.fear

003| #|'ok'
004| #|'and then
005| .c(,)
   |    ^

While inspecting arguments list > method body > method declaration > type declaration body > type declaration > full file
Missing expression.
Expected one of: "name", "TypeName", "(", "{".
Error 2  UnexpectedToken
""","""
A:{
.m:Str ->
#|'ok'
#|'and then
.c(,)
}
"""); }

@Test void inter_expr_then_chain_bad_args_ok(){ ok("""
[###]
[ok'\\nand then\\n]
[###]
""","""
A:{
.m{.x}A ->
#|'ok'
|'and then
.c(xA)
}
"""); }

@Test void ok_no_interpolation(){ ok("""
[###]
""","""
A:{
.m(x:X):Str ->
x.b(1,2) |'pre{,}post
.d(3)
}
"""); }
@Test void fail_with_interpolation(){ fail("""
In file: [###]/in_memory0.fear

003| x.b(1,2) #|'pre{,}post
   |                 ^-
004| .d(3)

While inspecting string interpolation expression > method body > method declaration > type declaration body > type declaration > full file
Missing expression.
Found instead: ",".
Expected one of: "name", "TypeName", "(", "{".
Error 2  UnexpectedToken
""","""
A:{
.m(x:X):Str ->
x.b(1,2) #|'pre{,}post
.d(3)
}
"""); }

@Test void inter_ascii_illegal_char_is_not_unicode(){ ok("""
[###]
[cafe\\u00E9, // unicode inside simple string is just \\ u X X X X\\n]
[###]
""","""
A:{
.m:Str ->
#|'cafe\\u00E9{B.foo(C)} // unicode inside simple string is just \\ u X X X X
}
"""); }

//NOTE: kept in safe encoding for easier debuggability
@Test void inter_unicode_ok(){ ok("""
[###]
[cafe\\u00E9, // same text but unicode line string\\n]
[###]
""","""
A:{
.m:Str ->
#|"cafe\\u00E9{B.foo(C)} // same text but unicode line string
}
"""); }

@Test void inter_op_before_line_string_unicode_fail(){ fail("""
In file: [###]/in_memory0.fear

003|  ^-^|"a"
   |  ^^^^

While inspecting the file
Unrecognized text "^-^|".
A "|" immediately before a quote starts a line string (e.g. `|"abc"` or `|'abc'`).
Operators can also contain "|", making it ambiguous what, for example, `<--|'foo'` means.
It could be the "<--" operator followed by `|'foo'` but also the "<--|" operator followed by `'foo'`.
Please add spaces to disambiguate:  `<--| 'foo'`   or   `<-- |'foo'`
Error 2  UnexpectedToken
""","""
A:{ .m -> 
 |"b
 ^-^|"a"
}
"""); }

@Test void inter_op_before_line_string_unicode_ok(){ ok("""
[###]
""","""
A:{ .m ->
 |"b
 ^-^
 |"a"
}
"""); }

@Test void different_hashes1(){ ok("""
[###]
[L1,\\nL2 {{x.bar(1)}}\\n]
[###]
""","""
A:{
.m:Str ->
#|'L1 {B.foo(C)}
|'L2 {{x.bar(1)}}
}
"""); }

@Test void different_hashes2(){ ok("""
[###]
[L1,\\nL2 {x.bar(1)}\\n]
[###]

""","""
A:{
.m:Str ->
#|'L1 {B.foo(C)}
|'L2 {x.bar(1)}
}
"""); }

@Test void inter_two_and_three(){ ok("""
[###]
[head,mid{,}tail\\n]
[###]
""","""
A:{
dd ->
##|'head {{B.foo(C)}} mid {{{dd}}} tail
}
"""); }

@Test void inter_mix(){ ok("""
[###]body=Optional[
Inter[false][4][one\\n][]
Inter[true][3][two\\n][]
]]]]]]
""","""
A:{
.m:Str ->
####|"one
###|'two
}
"""); }

@Test void inter_mix_other(){ fail("""
In file: [###]/in_memory0.fear

002| .m:Str ->
   | ... 2 lines ...
005| x.y() |'two {B.foo(C)}'
   | ^
006| .z(3)

While inspecting method declaration > type declaration body > type declaration > full file
There is a missing ";", operator or method name here or before
Error 6  MissingSeparator
""","""
A:{
.m:Str ->
#|'one'
.k(1)
x.y() |'two {B.foo(C)}'
.z(3)
}
"""); }

@Test void comment_ok(){ ok("""
[###]
[pre,is cut out\\npost\\n]
[###]
""","""
A:{
x ->
#|'pre { x + 1 // comment seen as part of string, thus } is cut out
|'post
}
"""); }

@Test void never_new_line_inter(){ fail("""
In file: [###]/in_memory0.fear

004| } 'post
   |   ^^^^^

While inspecting the file
String literal [SQUOTE (') 0x27] reaches the end of the line.
Error 2  UnexpectedToken
""","""
A:{
x ->
#|'pre { x + 1 // not even comment allows new lines in interpolation
} 'post
}
"""); }

@Test void inter_unclosed_block_comment_fail(){ fail("""
In file: [###]/in_memory0.fear

002| .m:Str ->
003| #|'A { x + /* start
   | --^^^^-------------

While inspecting method body > method declaration > type declaration body > type declaration > full file
Unclosed string interpolation placeholder
Error 7  InterpolationNoClose
""","""
A:{
.m:Str ->
#|'A { x + /* start
}
"""); }

@Test void inter_unclosed_block_comment_ok(){ ok("""
[###]
[A,\\nB\\n]
[###]
""","""
A:{
x ->
#|'A { x + /* start */ 2 }
|'B
}
"""); }

//this ends up as two valid interpolations with broken code inside
@Test void inter_block_comment_not_shield_braces1(){ fail("""
In file: [###]/in_memory0.fear

002| .m:Str ->
003| #|'P { a /* }  {  */ + 3 } Q
   | -------~~^^-----------------

While inspecting string interpolation expression > method body > method declaration > type declaration body > type declaration > full file
Unterminated block comment. Add "*/" to close it.
Error 2  UnexpectedToken
""","""
A:{
.m:Str ->
#|'P { a /* }  {  */ + 3 } Q
}
"""); }

//this ends up as a double opener
@Test void inter_block_comment_not_shield_braces2(){ fail("""
In file: [###]/in_memory0.fear

002| .m:Str ->
003| #|'P { a /* {  }  */ + 3 } Q
   | -----^^^^^^^^---------------

While inspecting method body > method declaration > type declaration body > type declaration > full file
String interpolation placeholder opened inside interpolation expression.
Note: "{" can not be used in single "#" interpolation expressions. Use at least "##".
Error 7  InterpolationNoClose
""","""
A:{
.m:Str ->
#|'P { a /* {  }  */ + 3 } Q
}
"""); }

@Test void inter_double_hash_late_single_closer_ok(){ ok("""
[###]
[H1,\\nH2\\n]
[###]
""","""
A:{
x ->
##|'H1 {{ x +++++ +1 }}
|'H2
}
"""); }

@Test void inter_trailing_comma_inside_braces_ok(){ ok("""
[###]
""","""
A:{
x ->
#|'x { x.bar(1,) } y
}
"""); }

@Test void inter_square_arg_space_inside_braces_fail(){ fail("""
In file: [###]/in_memory0.fear

002| .m:Str ->
003| #|'S { x.foo [read] } T
   | -------~~~~~~^~~~~~----

While inspecting string interpolation expression > method body > method declaration > type declaration body > type declaration > full file
Unrecognized text "[".
Here we expect "[" as a generic/RC argument opener and must follow the name with no space.
Write "Foo[Bar]" not "Foo [Bar]".
Write "x.foo[read]" not "x.foo [read]".
Error 2  UnexpectedToken
""","""
A:{
.m:Str ->
#|'S { x.foo [read] } T
}
"""); }

@Test void inter_square_arg_space_inside_braces_ok(){ ok("""
[###]
""","""
A:{ x -> #|'S { x.foo[read] } T
}
"""); }

@Test void inter_receiver_line_comment_eats_closer(){ ok("""
[###]
[pre,post\\n]
[###]
""","""
A:{
.m(x:X):Str ->
x.b(1,2) #|'pre { x + 1 } post
}
"""); }

@Test void inter_expr_then_chain(){ ok("""
[###]
""","""
A:{
.m:Str ->
#|'ok {1 + 2}
.c( // new line is not an issue here
)
}
"""); }

@Test void good_error_for_plus_minus(){ fail("""
In file: [###]/in_memory0.fear

001| A:{ .m -> 1+2 }
   | ----~~~~~~~^^--

While inspecting method declaration > type declaration body > type declaration > full file
Here "+2" is seen as a single signed literal, not as a +/- operator followed by a literal.
Write "1 + 2" not "1+2".
Write "+1 + +2" not "+1+2".
Write "+0.53 + +2.32" not "0.53+2.32".
Write "+3/2 + +4/5" not "3/2+4/5".
Error 2  UnexpectedToken
""","""
A:{ .m -> 1+2 }
"""); }

@Test void inter_mixed_counts_with_comments_ok(){ ok("""
[###]
[head {literal} and,\\ntail\\n]
[###]
""","""
A:{
x ->
##|'head {literal} and {{ x /* c */ + 1 }}
|'tail
}
"""); }

@Test void bad_dq_str_eol_with_line_comment(){
  fail("""
In file: [###]/in_memory0.fear

003|     "foo // comment
   |     ^^^^^^

While inspecting the file
String literal [DQUOTE (") 0x22] reaches the end of the line.
A comment opening sign is present later on this line; did you mean to close the string before it?
Error 2  UnexpectedToken
""", """
A:{
  .m:Str ->
    "foo // comment
}
""");}

@Test void bad_sq_str_eol_with_line_comment(){
  fail("""
In file: [###]/in_memory0.fear

003|     'bar // comment
   |     ^^^^^^

While inspecting the file
String literal [SQUOTE (') 0x27] reaches the end of the line.
A comment opening sign is present later on this line; did you mean to close the string before it?
Error 2  UnexpectedToken
""", """
A:{
  .m:Str ->
    'bar // comment
}
""");
}

@Test void bad_sq_str_eol_with_line_comment2(){
  fail("""
In file: [###]/in_memory0.fear

003|     'bar /* comment */
   |     ^^^^^^

While inspecting the file
String literal [SQUOTE (') 0x27] reaches the end of the line.
A comment opening sign is present later on this line; did you mean to close the string before it?
Error 2  UnexpectedToken
""", """
A:{
  .m:Str ->
    'bar /* comment */
}
""");
}

@Test void bad_sq_str_eol_with_line_comment3(){
  fail("""
In file: [###]/in_memory0.fear

003|     'bar /* comment
   |     ^^^^^^

While inspecting the file
String literal [SQUOTE (') 0x27] reaches the end of the line.
A comment opening sign is present later on this line; did you mean to close the string before it?
Error 2  UnexpectedToken
""", """
A:{
  .m:Str ->
    'bar /* comment 
    */
}
""");
}

@Test void bad_dq_str_eol_plain_no_comment(){
  fail("""
In file: [###]/in_memory0.fear

003|     "no close here
   |     ^^^^^^^^^^^^^^

While inspecting the file
String literal [DQUOTE (") 0x22] reaches the end of the line.
Error 2  UnexpectedToken
""", """
A:{
  .m:Str ->
    "no close here
}
""");
}

@Test void bad_sq_str_eol_plain_no_comment(){
  fail("""
In file: [###]/in_memory0.fear

003|     'no close here
   |     ^^^^^^^^^^^^^^

While inspecting the file
String literal [SQUOTE (') 0x27] reaches the end of the line.
Error 2  UnexpectedToken
""", """
A:{
  .m:Str ->
    'no close here
}
""");
}

@Test void bad_dq_str_opener_swallowed_by_block_comment_tail(){
  fail("""
In file: [###]/in_memory0.fear

003|     /* something with a " on this last line */ "text that doesn't close
   |                         ^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
String literal [DQUOTE (") 0x22] reaches the end of the line.
A preceding block comment "/* ... */" on this line contains that quote.
Did it swallow the intended opening quote?
Error 2  UnexpectedToken
""", """
A:{
  .m:Str ->
    /* something with a " on this last line */ "text that doesn't close
}
""");
}

@Test void stray_block_comment_closer_with_pseudo_opener_in_string(){
  fail("""
In file: [###]/in_memory0.fear

003|     "this looks like /* an opener but is inside a string"
004|     some other text
005|     */

While inspecting the file
Unopened block comment close "*/".
Found a "/*" inside a string literal before this point.
Did you mean to place the opener outside the string/comment?
Error 2  UnexpectedToken
""", """
A:{
  .m:Str ->
    "this looks like /* an opener but is inside a string"
    some other text
    */
}
""");
}

@Test void stray_block_comment_closer_with_pseudo_opener_in_string2(){
  fail("""
In file: [###]/in_memory0.fear

003|     "this looks like /* an opener but is inside a string" some other text */
   |                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Unopened block comment close "*/".
Found a "/*" inside a string literal before this point.
Did you mean to place the opener outside the string/comment?
Error 2  UnexpectedToken
""", """
A:{
  .m:Str ->
    "this looks like /* an opener but is inside a string" some other text */
}
""");
}

@Test void stray_block_comment_closer_with_pseudo_opener_in_string3(){
  fail("""
In file: [###]/in_memory0.fear

003|     "this looks like /* an opener but is inside a string"
   | ... 4 lines ...
008|     */

While inspecting the file
Unopened block comment close "*/".
Found a "/*" inside a string literal before this point.
Did you mean to place the opener outside the string/comment?
Error 2  UnexpectedToken
""", """
A:{
  .m:Str ->
    "this looks like /* an opener but is inside a string"
    some other text 1
    some other text 2
    some other text 3
    some other text 4
    */
}
""");
}


@Test void stray_block_comment_closer_with_pseudo_opener_in_line_comment(){
  fail("""
In file: [###]/in_memory0.fear

003|     // not really opening: /*
004|     */

While inspecting the file
Unopened block comment close "*/".
Found a "/*" inside a line comment "//" before this point.
Did you mean to place the opener outside the string/comment?
Error 2  UnexpectedToken
""", """
A:{
  .m:Str ->
    // not really opening: /*
    */
}
""");
}

@Test void stray_block_comment_closer_basic_no_pseudo_opener_and_prior_real_block_comment_exists(){
  fail("""
In file: [###]/in_memory0.fear

004|     */
   |     ^^

While inspecting the file
Unopened block comment close "*/". Remove it or add a matching "/*" before.
Error 2  UnexpectedToken
""", """
A:{
  .m:Str ->
    /* real opener and closer */ 42
    */
}
""");
}

@Test void bad_unclosed_block_comment_runs_to_eof_with_eof_frame(){
  fail("""
In file: [###]/in_memory0.fear

003|     /* never closed
   |     ^^^^^^^^^^^^^^^

While inspecting the file
Unterminated block comment. Add "*/" to close it.
Error 2  UnexpectedToken
""", """
A:{
  .m:Str ->
    /* never closed
}
""");
}

@Test void bad_op_digit_minus_or_plus_before_digit_is_signed_literal(){
  fail("""
In file: [###]/in_memory0.fear

003|     <--5
   |     ^^^

While inspecting the file
Unrecognized text "<--".
An operator followed by a digit is parsed as a signed number (e.g. "+5", "-3").
Operators can also contain "+" and "-", making it ambiguous what, for example, "<--5" means.
It could be the "<--" operator followed by "5" but also the "<-" operator followed by "-5".
Please add spaces to disambiguate:  "<-- 5"   or   "<- -5"
Error 2  UnexpectedToken
""", """
A:{
  .m:Str ->
    <--5
}
""");
}


@Test void bad_float_requires_sign_and_digits_both_sides_of_dot(){
  fail("""
In file: [###]/in_memory0.fear

003|     1.2
   |     ^^^

While inspecting the file
Unrecognized text "1.2".
Float literals must have a sign and digits on both sides of ".".
Examples: "+1.0", "-0.5", "+12.0e-3".
Fearless does not allow float literals of form "1.2" or ".2".
Error 2  UnexpectedToken
""", """
A:{
  .m:Str ->
    1.2
}
""");
}

@Test void bad_rational_requires_sign(){
  fail("""
In file: [###]/in_memory0.fear

003|     1/2
   |     ^^^

While inspecting the file
Unrecognized text "1/2".
Rational literals must have a sign.
Examples: "+1/2", "-3/4".
Fearless does not allow rational literals of form "1/2"
Error 2  UnexpectedToken
""", """
A:{
  .m:Str ->
    1/2
}
""");
}

@Test void eatenCloserInDblQuote_thenWrongCloserParen(){
fail("""
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> "price is } dollars" ) }
   |   ^^^^^^^^^^^^^^^^^^^^^^^---------

While inspecting the file
Unclosed "{" group.
Found a matching closer inside a string literal between here and the stopping point.
Did you mean to place the closer outside the string literal?
Otherwise expected one of: "}id", "}".
Error 0  Unclosed
""","""
A:{ .m:Str -> "price is } dollars" ) }
""");}

@Test void eatenCloserInSglQuote_thenWrongCloserParen(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> 'oops } here' ) }
   |   ^^^^^^^^^^^^^^^^^^^------

While inspecting the file
Unclosed "{" group.
Found a matching closer inside a string literal between here and the stopping point.
Did you mean to place the closer outside the string literal?
Otherwise expected one of: "}id", "}".
Error 0  Unclosed
""",""" 
A:{ .m:Str -> 'oops } here' ) }
""");}

@Test void eatenCloserInLineStr_thenWrongCloserParen(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> |"hello } world" ) }
   |   ^^^^^^^^^^^^^^^^^^^^^-----------

While inspecting the file
Unclosed "{" group.
Found a matching closer inside a string literal between here and the stopping point.
Did you mean to place the closer outside the string literal?
Otherwise expected one of: "}id", "}".
Error 0  Unclosed
""",""" 
A:{ .m:Str -> |"hello } world" ) }
""");}

@Test void eatenCloserInBlockComment_thenWrongCloserParen(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> /* } inside */ ) }
   |   ^^^^^^^^^^^^^^^^----------

While inspecting the file
Unclosed "{" group.
Found a matching closer inside a block comment "/* ... */" between here and the stopping point.
Did you mean to place the closer outside the block comment "/* ... */"?
Otherwise expected one of: "}id", "}".
Error 0  Unclosed
""",""" 
A:{ .m:Str -> /* } inside */ ) }
""");}

@Test void eatenCloserInLineComment_thenWrongCloserParen(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> // } swallowed
   |   ^^^^^^^^^^^^^^^^----------

While inspecting the file
Unclosed "{" group.
Found a matching closer inside a line comment "//" between here and the stopping point.
Did you mean to place the closer outside the line comment "//"?
Otherwise expected one of: "}id", "}".
Error 0  Unclosed
""",""" 
A:{ .m:Str -> // } swallowed
) }
""");}

@Test void eatenRoundCloserInString_thenStopByCurly(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> ( ")]" + " has ) here ) inside" }
   |               ^^^^--

While inspecting the file
Unclosed "(" group.
Found a matching closer inside a string literal between here and the stopping point.
Did you mean to place the closer outside the string literal?
Otherwise expected ")".
Error 0  Unclosed
""",""" 
A:{ .m:Str -> ( ")]" + " has ) here ) inside" } 
""");}

@Test void eatenSquareCloserInString_thenStopByParen(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> W[ "list ] marker" ) ] }
   |                ^^^^^^^^^--------

While inspecting the file
Unclosed "[" group.
Found a matching closer inside a string literal between here and the stopping point.
Did you mean to place the closer outside the string literal?
Otherwise expected "]".
Error 0  Unclosed
""",""" 
A:{ .m:Str -> W[ "list ] marker" ) ] }
""");}

@Test void eatenCurlyCloserInString_thenEOF(){
fail("""
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> { "inner } hidden"
   |               ^^^^^^^^^^--------

While inspecting the file
Unclosed "{" group.
Found a matching closer inside a string literal between here and the stopping point.
Did you mean to place the closer outside the string literal?
Otherwise expected one of: "}id", "}".
Error 0  Unclosed
""","""
A:{ .m:Str -> { "inner } hidden"
""");}

@Test void eatenCurlyCloserInBlockComment_thenEOF(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> { /* } hidden */
   |               ^^^^^^----------

While inspecting the file
Unclosed "{" group.
Found a matching closer inside a block comment "/* ... */" between here and the stopping point.
Did you mean to place the closer outside the block comment "/* ... */"?
Otherwise expected one of: "}id", "}".
Error 0  Unclosed
""",""" 
A:{ .m:Str -> { /* } hidden */ 
""");}

@Test void eatenSquareCloserInBlockComment_thenWrongCloserCurly(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> Foo[ /* ] hidden */ } ]
   |                  ^^^^^^----------

While inspecting the file
Unclosed "[" group.
Found a matching closer inside a block comment "/* ... */" between here and the stopping point.
Did you mean to place the closer outside the block comment "/* ... */"?
Otherwise expected "]".
Error 0  Unclosed
""",""" 
A:{ .m:Str -> Foo[ /* ] hidden */ } ]
""");}

@Test void eatenRoundOpenerInDblQuote_thenStrayParen(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> "call (" ) }
   |               ------^^^^

While inspecting the file
Unopened ")".
Found a matching opener hidden inside a string literal before this point.
Did you mean to place the opener outside the string literal?
Error 1  Unopened
""",""" 
A:{ .m:Str -> "call (" ) }
""");}

@Test void eatenRoundOpenerInLineComment_thenStrayParen(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> // ( swallowed
002| ) }

While inspecting the file
Unopened ")".
Found a matching opener hidden inside a line comment "//" before this point.
Did you mean to place the opener outside the line comment "//"?
Error 1  Unopened
""",""" 
A:{ .m:Str -> // ( swallowed
) }
""");}

@Test void eatenSquareOpenerInBlockComment_thenStrayBracket(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> /* [ hidden */ ] }
   |               ---^^^^^^^^^^^^^

While inspecting the file
Unopened "]".
Found a matching opener hidden inside a block comment "/* ... */" before this point.
Did you mean to place the opener outside the block comment "/* ... */"?
Error 1  Unopened
""",""" 
A:{ .m:Str -> /* [ hidden */ ] }
""");}

@Test void eatenCurlyOpenerInDblQuote_thenStrayCurly(){
fail(""" 
In file: [###]/in_memory0.fear

001| .m:Str -> "start { here" }
   |           -------^^^^^^^^^

While inspecting the file
Unopened "}".
Found a matching opener hidden inside a string literal before this point.
Did you mean to place the opener outside the string literal?
Error 1  Unopened
""",""" 
.m:Str -> "start { here" } 
""");}

@Test void eatenRoundOpenerInBlockComment_thenStrayParenDeep(){
fail("""
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> 1 + 2 /* ( */ + 3 ) }
   |                     ---^^^^^^^^^^

While inspecting the file
Unopened ")".
Found a matching opener hidden inside a block comment "/* ... */" before this point.
Did you mean to place the opener outside the block comment "/* ... */"?
Error 1  Unopened
""","""
A:{ .m:Str -> 1 + 2 /* ( */ + 3 ) }
""");}

@Test void eatenSquareOpenerInLineStr_thenStrayBracket(){
fail("""
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> |"vec [ x" ] }
   |   ^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Unclosed "{" group.
Found a matching closer inside a string literal between here and the stopping point.
Did you mean to place the closer outside the string literal?
Otherwise expected one of: "}id", "}".
Error 0  Unclosed
""","""
A:{ .m:Str -> |"vec [ x" ] }
""");}

@Test void runOfRoundClosersBeforeStop(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> ((1 + 2)) ) }
   |   ^^^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Wrong closer for "{" group.
Found instead: ")".
This ")" may be unintended.
Otherwise expected one of: "}id", "}".
Error 2  UnexpectedToken
""","""
A:{ .m:Str -> ((1 + 2)) ) }
""");}

@Test void runOfSquareClosersBeforeStop(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> Foo[Bar] ] ) }
   |   ^^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Wrong closer for "{" group.
Found instead: "]".
Expected one of: "}id", "}".
Error 2  UnexpectedToken
""",""" 
A:{ .m:Str -> Foo[Bar] ] ) }
""");}

@Test void runOfRoundClosersThenWrongCurly(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m(a,b):Str -> (a + b)) }
   |   ^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Wrong closer for "{" group.
Found instead: ")".
This ")" may be unintended.
Otherwise expected one of: "}id", "}".
Error 2  UnexpectedToken
""",""" 
A:{ .m(a,b):Str -> (a + b)) } 
""");}

@Test void runOfSquareClosersThenWrongParen(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> A[mut,imm]] ) }
   |   ^^^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Wrong closer for "{" group.
Found instead: "]".
Expected one of: "}id", "}".
Error 2  UnexpectedToken
""",""" 
A:{ .m:Str -> A[mut,imm]] ) }
""");}

@Test void runOfRoundClosersNearEOF(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m(foo,bar):Str -> (foo + bar))
   |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Wrong closer for "{" group.
Found instead: ")".
This ")" may be unintended.
Otherwise expected one of: "}id", "}".
Error 2  UnexpectedToken
""",""" 
A:{ .m(foo,bar):Str -> (foo + bar)) 
""");}

@Test void runOfSquareClosersNearEOF(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> A[X,Y,Z]]
   |   ^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Wrong closer for "{" group.
Found instead: "]".
This "]" may be unintended.
Otherwise expected one of: "}id", "}".
Error 2  UnexpectedToken
""",""" 
A:{ .m:Str -> A[X,Y,Z]] 
""");}

@Test void runOfRoundOpenersBeforeStrayParen(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m(x,y):Str -> (((x + y))) + 1 ) }
   |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Wrong closer for "{" group.
Found instead: ")".
This ")" may be unintended.
Otherwise expected one of: "}id", "}".
Error 2  UnexpectedToken
""",""" 
A:{ .m(x,y):Str -> (((x + y))) + 1 ) }
""");}

@Test void runOfSquareOpenersBeforeStrayBracket(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> A[B[X,Y] , Z ] ] ]{} }
   |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Wrong closer for "{" group.
Found instead: "]".
Expected one of: "}id", "}".
Error 2  UnexpectedToken
""",""" 
A:{ .m:Str -> A[B[X,Y] , Z ] ] ]{} }
""");}

@Test void runOfRoundOpenersTightBeforeStrayParen(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> (((x))) ) }
   |   ^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Wrong closer for "{" group.
Found instead: ")".
This ")" may be unintended.
Otherwise expected one of: "}id", "}".
Error 2  UnexpectedToken
""",""" 
A:{ .m:Str -> (((x))) ) }
""");}

@Test void runOfSquareOpenersTightBeforeStrayBracket(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> A[B[X]] ] }
   |   ^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Wrong closer for "{" group.
Found instead: "]".
This "]" may be unintended.
Otherwise expected one of: "}id", "}".
Error 2  UnexpectedToken
""",""" 
A:{ .m:Str -> A[B[X]] ] }
""");}

@Test void wrongCloser_ParenClosedByBracket(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> (1 + 2 ] }
   |               ^^^^^^^^

While inspecting the file
Wrong closer for "(" group.
Found instead: "]".
Expected ")".
Error 2  UnexpectedToken
""",""" 
A:{ .m:Str -> (1 + 2 ] }
""");}

@Test void wrongCloser_BracketClosedByParen(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> E[1,2) }
   |                ^^^^^

While inspecting the file
Wrong closer for "[" group.
Found instead: ")".
Expected "]".
Error 2  UnexpectedToken
""",""" 
A:{ .m:Str -> E[1,2) }
""");}

@Test void eofInsideParen(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> (1 + 2
   |               ^

While inspecting the file
File ended while parsing a "(" group.
This "(" may be unintended.
Otherwise expected ")".
Error 0  Unclosed
""",""" 
A:{ .m:Str -> (1 + 2
""");}

@Test void eofInsideBracket(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> E[1, 2, 3
   |                ^

While inspecting the file
File ended while parsing a "[" group.
This "[" may be unintended.
Otherwise expected "]".
Error 0  Unclosed
""",""" 
A:{ .m:Str -> E[1, 2, 3
""");}
@Test void wrongCloser_CurlyClosedByParen(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> { x: 1 ) }
   |               ^^^^^^^^

While inspecting the file
Wrong closer for "{" group.
Found instead: ")".
This ")" may be unintended.
Otherwise expected one of: "}id", "}".
Error 2  UnexpectedToken
""",""" 
A:{ .m:Str -> { x: 1 ) }
""");}

@Test void wrongCloser_CurlyClosedByParen2(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> { x: 1 ) }
   |               ^^^^^^^^

While inspecting the file
Wrong closer for "{" group.
Found instead: ")".
This ")" may be unintended.
Otherwise expected one of: "}id", "}".
Error 2  UnexpectedToken
""",""" 
A:{ .m:Str -> { x: 1 ) }
B:{} C:{}
""");}

@Test void barrierSemicolonInsideParen(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> ( 1 + 2; ) }
   |               ^^^^^^^^

While inspecting the file
Unclosed "(" group before ";".
This ";" may be unintended.
Otherwise expected ")".
Error 0  Unclosed
""",""" 
A:{ .m:Str -> ( 1 + 2; ) }
""");}

//no repair can conceptually apply
@Test void nestedWrongCloser_Deep(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> ( Foo[ { a } ) ] }
   |                    ^^^

While inspecting the file
Unclosed "[" group before "{".
Expected "]".
Error 0  Unclosed
""",""" 
A:{ .m:Str -> ( Foo[ { a } ) ] }
""");}

@Test void curlyGroupUnclosedBeforeEOF(){
fail(""" 
In file: [###]/in_memory0.fear

001| A:{ .m:Str -> { a: 1, b: 2
   |               ^

While inspecting the file
File ended while parsing a "{" group.
This "{" may be unintended.
Otherwise expected one of: "}id", "}".
Error 0  Unclosed
""",""" 
A:{ .m:Str -> { a: 1, b: 2 
""");}

@Test void openerInStringThenEOF_shouldPreferEatenCloser(){
fail(""" 
In file: ~/.../___DBG___/in_memory0.fear

001| A:{ .m:Str -> { "json } aaa"
   |               ^^^^^^^^^-----

While inspecting the file
Unclosed "{" group.
Found a matching closer inside a string literal between here and the stopping point.
Did you mean to place the closer outside the string literal?
Otherwise expected one of: "}id", "}".
Error 0  Unclosed
""",""" 
A:{ .m:Str -> { "json } aaa" 
""");}


//A:{ .m(): -> ::.two( Block#.let x={5}, x ) }
//errors that could get better err messages: forgot ; may be detected by multiple -> in meth
//forgot : or added : in D:{..} //may be as well formedness later on? with : D must be new, without :, D must exists
//.foo atom atom or .foo atom,atom -> missing parenthesis
}