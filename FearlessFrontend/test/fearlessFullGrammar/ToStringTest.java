package fearlessFullGrammar;

import java.util.stream.Collectors;

import org.junit.jupiter.api.Test;

import fearlessParser.Parse;
import message.FearlessException;
import message.SourceOracle;
import utils.Err;

public class ToStringTest {
  static void ok(String expected,String input){
    FileFull res;try{ res= Parse.from(SourceOracle.defaultDbgUri(0), input); }
    catch(FearlessException fe){ 
      SourceOracle o= SourceOracle.debugBuilder()
        .put(0, input)
        .build();
      System.out.println(fe.render(o));
      throw fe;
    }
    var got= res.decs().stream()
      .map(ToString::declaration)
      .collect(Collectors.joining("\n"))+"\n";
    Err.strCmp(expected,got);
  }
  @Test void decl_empty(){ ok("A: {}\n","A:{}"); }

  @Test void decl_generics_plain(){ ok(
    "Pair[X,Y]: {}\n",
    "Pair[X,Y]:{}"); }
  @Test void decl_generics_rc(){ ok(
    "Box[X:imm]: {}\n",
    "Box[X:imm]:{}"); }
  @Test void decl_generics_star(){ ok(
    "Vec[X:*]: {}\n",
    "Vec[X:*]:{}"); }
  @Test void decl_generics_starstar(){ ok(
    "Graph[X:**]: {}\n",
    "Graph[X:**]:{}"); }
  @Test void supertypes_one(){ ok(
    "A: B {}\n",
    "A: B{}"); }
  @Test void supertypes_two(){ ok(
    "A: B, C {}\n",
    "A: B,C{}"); }
  @Test void supertypes_three(){ ok(
    "A: B, C, D {}\n",
    "A: B,C,D{}"); }
  @Test void supertypes_with_args(){ ok(
    "A[X,Y]: B[X], C[Y] {}\n",//Note: normalized to no space in type args
    "A[X, Y]: B[X],C[Y]{}"); }
  @Test void meth_named_no_parens(){ ok(
    "A: {.id x -> x;}\n",
    "A:{ .id x -> x; }"); }
  @Test void meth_named_parens(){ ok(
    "A: {.id(x) -> x;}\n",
    "A:{ .id(x) -> x; }"); }
  @Test void meth_one_typed_param(){ ok(
    "A: {.id(x: X) -> x;}\n",
    "A:{ .id(x:X) -> x; }"); }
  @Test void meth_two_params_no_parens(){ ok(
    "A: {.sum x: X, y: Y -> x .plus y;}\n",
    "A:{ .sum x:X, y:Y -> x .plus y; }"); }
  @Test void meth_with_cap_mut(){ ok(
    "A: {mut .set x: X -> x;}\n",
    "A:{ mut .set x:X -> x; }"); }
  @Test void meth_two_params_parens(){ ok(
    "A: {.f(x: X, y: Y) -> x;}\n",
    "A:{ .f(x:X, y:Y) -> x; }"); }
  @Test void meth_anon_one_param(){ ok(
    "A: {x -> x;}\n",
    "A:{ x -> x; }"); }
  @Test void meth_anon_two_params(){ ok(
    "A: {x, y -> x;}\n",
    "A:{ x, y -> x; }"); }
  @Test void meth_sig_only_no_body(){ ok(
    "A: {.sigOnly(x: X);}\n",
    "A:{ .sigOnly(x:X) }"); }
  @Test void meth_many_in_one_literal(){ ok(
    "A: {.a -> this;.b x -> x;.c(x) -> x;}\n",
    "A:{ .a -> this; .b x -> x; .c(x) -> x; }"); }
  @Test void body_round_group(){ ok(
    "A: {.p(x: X) -> (x);}\n",
    "A:{ .p(x:X) -> (x) }"); }
  @Test void body_simple_name(){ ok(
    "A: {.body -> this;}\n",
    "A:{ .body -> this }"); }
  @Test void body_declaration_literal(){ ok(
    "A: {.make -> B: {};}\nB: {}\n",
    "A:{ .make -> B:{} } B:{}"); }
  @Test void body_typed_literal_unsigned(){ ok(
    "A: {.lit -> +5 {};}\n",
    "A:{ .lit -> +5{} }"); }
  @Test void body_typed_literal_with_rc(){ ok(
    "A: {.lit -> read +5 {};}\n",
    "A:{ .lit -> read +5{} }"); }
  @Test void call_with_square_targs_one_arg(){ ok(
    "A: {.g(x: X, y: X) -> x .foo[read, X] y;}\n",
    "A:{ .g(x:X, y:X) -> x .foo[read, X] y }");}
  @Test void param_type_rcx_mut(){ ok(
    "A: {.m(x: mut X) -> x;}\n",
    "A:{ .m(x:mut X) -> x }"); }
  @Test void param_type_rcc_read_name(){ ok(
    "A: {.m(x: read B) -> x;}\n",
    "A:{ .m(x:read B) -> x }"); }
  @Test void param_type_type_args(){ ok(
    "A: {.m(x: C[X, Y]) -> x;}\n",
    "A:{ .m(x:C[X, Y]) -> x }"); }
  @Test void destruct_param_simple(){ ok(
    "A: {.u({.a}P) -> A;}\n",
    "A:{ .u({.a}P) -> A }"); }
  @Test void destruct_param_nested_chain(){ ok(
    "A: {.u({.a.b}Name) -> bName;}\n",
    "A:{ .u({.a.b}Name) -> bName }"); }
  @Test void destruct_param_nested_chain2(){ ok(
      "A: {.u({.a.b}Name) -> A;}\n",
      "A:{ .u({.a.b}Name) -> A }"); }
  @Test void destruct_param_two_groups(){ ok(
    "A: {.u({.p.q, .r}s) -> rs;}\n",
    "A:{ .u({.p.q,.r}s) -> rs }"); }
  @Test void this_name_in_literal(){ ok(
    "Selfy: {`this .me -> this;}\n",
    "Selfy:{`this .me -> this}"); }
  @Test void package_header_is_ignored_in_print(){ ok(
    "A: {}\nB: {}\n",
    "package foo_bar; A:{} B:{}");}
  @Test void generics_many_bounds_mix(){ ok(
    "G[X:*,Y:**,Z:imm]: {}\n",
    "G[X:*,Y:**,Z:imm]:{}"); }
  @Test void multiple_methods_chained(){ ok(
    "A: {.a -> this;.b -> this;.c -> this;}\n",
    "A:{ .a -> this; .b -> this; .c -> this; }"); }
  @Test void implicit_receiver_call(){ ok(
    "A: {x, y -> :: .foo y;}\n",
    "A:{ x, y -> :: .foo y }"); }
  @Test void dot_call_no_parens_chain(){ ok(
    "A: {.m a: X, b: X -> a .foo b;}\n",
    "A:{ .m a:X, b:X -> a .foo b }"); }
  @Test void supertypes_with_pkg_names(){ ok(
    "A: foo.Bar, baz.Qux {}\n",
    "A:foo.Bar,baz.Qux{}"); }
  @Test void retType(){ ok(
      "A: {.a: A;}\n",
      "A:{.a:A}"); }
}