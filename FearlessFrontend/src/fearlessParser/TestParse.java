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

001| A:{ .m(): -> (Block#.let x={5}) .use(x) }
   | ----~~~~^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~--

While inspecting method signature > method declaration > type declaration body > type declaration > full file
Missing type name. Expected: "TypeName"
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
No names are in scope here.

Error 2  UnexpectedToken
""","""
A:{ .m -> (Block#.let x={5}) .use(x) }
""");}

@Test void doubleComma(){fail("""
In file: [###]/in_memory0.fear

001| A:{ .m(a,,b):C }
   | ----~~~~~^~~~~--

While inspecting method parameters declaration > method declaration > type declaration body > type declaration > full file
Missing type name. Expected: "TypeName"
Error 2  UnexpectedToken
""","""
A:{ .m(a,,b):C }
""");}

@Test void doubleCommaArg(){fail("""
In file: [###]/in_memory0.fear

001| A:{ .m(x:C):C->x.foo(,) }
   | ---------------~~~~~~^~--

While inspecting arguments list > method body > method declaration > type declaration body > type declaration > full file
Missing expression. Expected: "name", "TypeName", "(", "{"
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
File ended while parsing "{".
Expected one of: "}id", "}"
Error 0  Unclosed
""","""
A:{
""");}

// \n\ is to avoid autoremoval of leading spaces
@Test void err_unclosed_curly_long(){fail("""
In file: [###]in_memory0.fear

001| A:{ fdfdds
   | \n\
   | ... 6 lines ...
008| fff

While inspecting the file
File ended while parsing "{".
Expected one of: "}id", "}"
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
Missing type name. Expected: "TypeName"
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
In scope: "x"
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
But that is not one of : "name", "TypeName", "(", "{"
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
Missing expression. Expected: "name", "TypeName", "(", "{"
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
   | ^^^^^^^
003| .n -> {}
004| /*comment2*/}//comment3

While inspecting method body > method declaration > type declaration body > type declaration > full file
Name "y" is not in scope
No names are in scope here.

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
   | ^^^^^^^
003| .n -> {}
004| }

While inspecting method body > method declaration > type declaration body > type declaration > full file
Name "y" is not in scope
No names are in scope here.

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
Unopened "}"
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
But that is not one of : "name", "TypeName", "(", "{"
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
"[" here is parsed as a generic/RC argument opener and must follow the name with no space.
Write "Foo[Bar]" not "Foo [Bar]".
Write "x.foo[read]" not "x.foo [read]".

Error 2  UnexpectedToken
""","""
A:{ x -> x.foo [read] }
""");}
@Test void err_bad_op_line_pipe_before_quote(){fail("""
In file: [###]in_memory0.fear

001| A:{ .m -> +|'a'
   |           ^

While inspecting the file
Unrecognized text "+|".
A "|" immediately before a quote starts a line string (e.g. `|"abc"` or `|'abc'`).
Operators can also contain "|", making it ambiguous what, for example, `<--|'foo'` means.
It could be the "<--" operator followed by `|'foo'` but also the "<--|" operator followed by `'foo'`.
Please add spaces to clarify:  `<--| 'foo'`   or   `<-- |'foo'`

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


//A:{ .m(): -> ::.two( Block#.let x={5}, x ) }
//errors that could get better err messages: forgot ; may be detected by multiple -> in meth
//forgot : or added : in D:{..} //may be as well formedness later on? with : D must be new, without :, D must exists
//.foo atom atom or .foo atom,atom -> missing parenthesis
}