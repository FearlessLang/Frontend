package fearlessParser;

import static org.junit.Assert.*;

import java.util.stream.Collectors;

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
    var rres= err.render(o).stream().map(m->m.msg()).collect(Collectors.joining("\n"));
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
FileFull[renames=[],decs=[
Declaration[name=TName[s=Selfy,arity=0],bs=Optional.empty,cs=[],l=Literalself[
M[sig=Optional[
Sig[rc=Optional.empty,m=Optional[MName[s=.me,arity=0]],bs=Optional.empty,hasParenthesis=true,parameters=[],t=Optional[RCC[rc=Optional.empty,c=C[name=TName[s=Selfy,arity=0],ts=Optional.empty]]]]],
body=Optional[self]]]]]]
""","""
Selfy:{`self .me():Selfy -> self}
""");}
@Test void literal_with_thisname_and_method2(){ok("""
FileFull[renames=[],decs=[
Declaration[name=TName[s=Selfy,arity=0],bs=Optional.empty,cs=[],l=Literalself[
M[sig=Optional[
Sig[rc=Optional.empty,m=Optional[MName[s=.me,arity=0]],bs=Optional.empty,hasParenthesis=false,parameters=[],t=Optional[RCC[rc=Optional.empty,c=C[name=TName[s=Selfy,arity=0],ts=Optional.empty]]]]],
body=Optional[self]]]]]]
""","""
Selfy:{`self .me:Selfy -> self}
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
While inspecting method signature
001|A:{ .m(): -> (Block#.let x={5}) .use(x) }
   |    ^~~~~
002|

Searching for type name: Unexpected end of group after Colon `:` @1:9.
While inspecting method declaration
001|A:{ .m(): -> (Block#.let x={5}) .use(x) }
   |    ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
002|

While inspecting type declaration
001|A:{ .m(): -> (Block#.let x={5}) .use(x) }
   |  ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
002|

While inspecting type declaration
001|A:{ .m(): -> (Block#.let x={5}) .use(x) }
   |^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
002|

Error 2  EndOfGroup
""","""
A:{ .m(): -> (Block#.let x={5}) .use(x) }
""");}
@Test void useOutOfScope1(){fail("""
In file: [###]/in_memory0.fear
While inspecting arguments list
001|A:{ .m -> (Block#.let x={5}) .use(x) }
   |                                  ^
002|

Name `x` is not in scope
No names are in scope here.

While inspecting method declaration
001|A:{ .m -> (Block#.let x={5}) .use(x) }
   |    ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
002|

While inspecting type declaration
001|A:{ .m -> (Block#.let x={5}) .use(x) }
   |  ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
002|

While inspecting type declaration
001|A:{ .m -> (Block#.let x={5}) .use(x) }
   |^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
002|

Error 1  UnexpectedToken
""","""
A:{ .m -> (Block#.let x={5}) .use(x) }
""");}

//A:{ .m(): -> ::.two( Block#.let x={5}, x ) }
//errors that could get better err messages: forgot ; may be detected by multiple -> in meth
//forgot : or added : in D:{..} //may be as well formedness later on? with : D must be new, without :, D must exists
//.foo atom atom or .foo atom,atom -> missing parenthesis
}