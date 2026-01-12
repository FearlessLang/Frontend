package fearlessFullGrammar;

import org.junit.jupiter.api.Test;

public class ToStringTest extends testUtils.FearlessTestBase{
  static void ok(String expected,String input){ toStringOk(expected, input);}
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
    "A: { .id x -> x;}\n",
    "A:{ .id x -> x; }"); }
  @Test void meth_named_parens(){ ok(
    "A: { .id(x) -> x;}\n",
    "A:{ .id(x) -> x; }"); }
  @Test void meth_one_typed_param(){ ok(
    "A: { .id(x: X) -> x;}\n",
    "A:{ .id(x:X) -> x; }"); }
  @Test void meth_two_params_no_parens(){ ok(
    "A: { .sum x: X, y: Y -> x .plus y;}\n",
    "A:{ .sum x:X, y:Y -> x .plus y; }"); }
  @Test void meth_with_cap_mut(){ ok(
    "A: { mut .set x: X -> x;}\n",
    "A:{ mut .set x:X -> x; }"); }
  @Test void meth_two_params_parens(){ ok(
    "A: { .f(x: X, y: Y) -> x;}\n",
    "A:{ .f(x:X, y:Y) -> x; }"); }
  @Test void meth_anon_one_param(){ ok(
    "A: { x -> x;}\n",
    "A:{ x -> x; }"); }
  @Test void meth_anon_two_params(){ ok(
    "A: { x, y -> x;}\n",
    "A:{ x, y -> x; }"); }
  @Test void meth_sig_only_no_body(){ ok(
    "A: { .sigOnly(x: X);}\n",
    "A:{ .sigOnly(x:X) }"); }
  @Test void meth_many_in_one_literal(){ ok(
    "A: { .a -> this; .b x -> x; .c(x) -> x;}\n",
    "A:{ .a -> this; .b x -> x; .c(x) -> x; }"); }
  @Test void body_round_group(){ ok(
    "A: { .p(x: X) -> (x);}\n",
    "A:{ .p(x:X) -> (x) }"); }
  @Test void body_simple_name(){ ok(
    "A: { .body -> this;}\n",
    "A:{ .body -> this }"); }
  @Test void body_declaration_literal(){ ok(
    "A: { .make -> B: {};}\nB: {}\n",
    "A:{ .make -> B:{} } B:{}"); }
  @Test void body_typed_literal_unsigned(){ ok(
    "A: { .lit -> +5 {};}\n",
    "A:{ .lit -> +5{} }"); }
  @Test void body_typed_literal_with_rc(){ ok(
    "A: { .lit -> read +5 {};}\n",
    "A:{ .lit -> read +5{} }"); }
  @Test void call_with_square_targs_one_arg(){ ok(
    "A: { .g(x: X, y: X) -> x .foo[read,X] y;}\n",
    "A:{ .g(x:X, y:X) -> x .foo[read, X] y }");}
  @Test void param_type_rcx_mut(){ ok(
    "A: { .m(x: mut X) -> x;}\n",
    "A:{ .m(x:mut X) -> x }"); }
  @Test void param_type_rcc_read_name(){ ok(
    "A: { .m(x: read B) -> x;}\n",
    "A:{ .m(x:read B) -> x }"); }
  @Test void param_type_type_args(){ ok(
    "A: { .m(x: C[X,Y]) -> x;}\n",
    "A:{ .m(x:C[X, Y]) -> x }"); }
  @Test void destruct_param_simple(){ ok(
    "A: { .u({.a}P) -> A;}\n",
    "A:{ .u({.a}P) -> A }"); }
  @Test void destruct_param_nested_chain(){ ok(
    "A: { .u({.a.b}Name) -> bName;}\n",
    "A:{ .u({.a.b}Name) -> bName }"); }
  @Test void destruct_param_nested_chain2(){ ok(
      "A: { .u({.a.b}Name) -> A;}\n",
      "A:{ .u({.a.b}Name) -> A }"); }
  @Test void destruct_param_two_groups(){ ok(
    "A: { .u({.p.q,.r}s) -> rs;}\n",
    "A:{ .u({.p.q,.r}s) -> rs }"); }
  @Test void this_name_in_literal(){ ok(
    "Selfy: {'this .me -> this;}\n",
    "Selfy:{'this .me -> this}"); }
  @Test void generics_many_bounds_mix(){ ok(
    "G[X:*,Y:**,Z:imm]: {}\n",
    "G[X:*,Y:**,Z:imm]:{}"); }
  @Test void multiple_methods_chained(){ ok(
    "A: { .a -> this; .b -> this; .c -> this;}\n",
    "A:{ .a -> this; .b -> this; .c -> this; }"); }
  @Test void implicit_receiver_call(){ ok(
    "A: { x, y -> :: .foo y;}\n",
    "A:{ x, y -> :: .foo y }"); }
  @Test void implicit_receiver_call_paren(){ ok(
      "A: { x, y -> :: .foo(y);}\n",
      "A:{ x, y -> :: .foo(y) }"); }
  @Test void dot_call_no_parens_chain(){ ok(
    "A: { .m a: X, b: X -> a .foo b;}\n",
    "A:{ .m a:X, b:X -> a .foo b }"); }
  @Test void supertypes_with_pkg_names(){ ok(
    "A: foo.Bar, baz.Qux {}\n",
    "A:foo.Bar,baz.Qux{}"); }
  @Test void retType(){ ok(
      "A: { .a: A;}\n",
      "A:{.a:A}"); }

  @Test void decl_generics_bounds_star(){ ok(
    "Vec[X:*]: {}\n",
    "Vec[X:*]:{}"); }
  @Test void decl_generics_bounds_starstar(){ ok(
    "Graph[X:**]: {}\n",
    "Graph[X:**]:{}"); }
  @Test void decl_generics_mixed_bounds(){ ok(
    "G[X:imm,Y:**,Z:*]: {}\n",
    "G[X:imm,Y:**,Z:*]:{}"); }
  @Test void supertypes_many(){ ok(
    "A: B, C, D {}\n",
    "A:B,C,D{}"); }
  @Test void supertypes_with_type_args(){ ok(
    "A: B[X], C[Y,Z] {}\n",
    "A:B[X],C[Y,Z]{}"); }
  @Test void meth_named_with_parens_and_ret(){ ok(
    "A: { .id(x: X): X -> x;}\n",
    "A:{ .id(x:X):X -> x }");}
  @Test void meth_named_ret_only(){ ok(
    "A: { .abs(): X;}\n",
    "A:{ .abs():X }");}
  @Test void meth_cap_mut_and_ret(){ ok(
    "A: { mut .set(x: X): A -> x;}\n",
    "A:{ mut .set(x:X):A -> x }");}
  @Test void literal_many_methods_spaced(){ ok(
    "A: { .a -> this; .b x -> x; .c(x) -> x;}\n",
    "A:{ .a -> this; .b x -> x; .c(x) -> x; }");}
  @Test void call_parens_zero_args(){ ok(
    "A: { .m x -> x .foo();}\n",
    "A:{ .m x -> x .foo() }");}
  @Test void call_parens_one_arg(){ ok(
    "A: { .m(x, y): X -> x .plus(y);}\n",
    "A:{ .m(x,y):X -> x .plus(y) }");}
  @Test void call_parens_two_args(){ ok(
    "A: { .m(x, y): X -> x .mix(y, x);}\n",
    "A:{ .m(x,y):X -> x .mix(y, x) }");}
  @Test void call_square_rc_only_should_not_emit_trailing_comma(){ ok(
    "A: { x -> x .foo[read];}\n",
    "A:{ x -> x .foo[read] }");}
  @Test void call_square_rc_and_types(){ ok(
    "A: { x -> x .foo[read,X,Y];}\n",
    "A:{ x -> x .foo[read, X, Y] }");}
  @Test void call_square_types_only(){ ok(
    "A: { x -> x .foo[X,Y];}\n",
    "A:{ x -> x .foo[X, Y] }");}
  @Test void call_operator_infix_prints_with_spaces(){ ok(
    "A: { x, y -> x + y;}\n",
    "A:{ x, y -> x + y }");}
  @Test void call_dotname_non_paren_two_args(){ ok(
    "A: { x, y -> x .foo y;}\n",
    "A:{ x, y -> x .foo y }");}
  @Test void round_group_single(){ ok(
    "A: { .p(x: X): X -> (x);}\n",
    "A:{ .p(x:X):X -> (x) }"); }
  @Test void round_group_nested(){ ok(
    "A: { .p(x: X): X -> (((x)));}\n",
    "A:{ .p(x:X):X -> (((x))) }");}
  @Test void typed_literal_unsigned_space_before_body(){ ok(
    "A: { .lit(): +45 -> +45 {};}\n",
    "A:{ .lit():+45 -> +45{} }"); }
  @Test void typed_literal_with_rc_prefix(){ ok(
    "A: { .lit2(): +45 -> read +45 {};}\n",
    "A:{ .lit2():+45 -> read +45{} }"); }
  @Test void decl_literal_no_rc(){ ok(
    "A: { .make -> B: {};}\nB: {}\n",
    "A:{ .make -> B:{} } B:{}");}
  @Test void decl_literal_with_rc(){ ok(
    "A: { .make -> read B: {};}\nB: {}\n",
    "A:{ .make -> read B:{} } B:{}"); }
  @Test void destruct_param_nested_multi(){ ok(
    "A: { .u({.a.b,.c}Name: T): T -> bName;}\n",
    "A:{ .u({.a.b,.c}Name:T):T -> bName }");}
  @Test void print_rcc_simple(){ ok(
    "A: { .t -> read B;}\n",
    "A:{ .t -> read B }");}
  @Test void print_rcx_and_readimmx_inside_types(){ ok(
    "A: { .t[X](x: mut X, y: read/imm X): X -> x;}\n",
    "A:{ .t[X](x:mut X, y:read/imm X):X -> x }");}
  @Test void implicit_receiver_token(){ ok(
    "A: { x, y -> :: .foo y;}\n",
    "A:{ x, y -> :: .foo y }");}
  @Test void string_inter_simple_s_quote_line(){ ok(
    "A: { .a: Str -> \n|`abc\n;}\n",
    "A:{.a:Str -> \n  |`abc\n}");}
  @Test void string_inter_hash_expr_oneMismatch(){ ok(
    "A: { .a: Str -> \n####|`pre {B.foo(C)} post\n;}\n",
    "A:{.a:Str ->\n####|`pre {B.foo(C)} post\n}");
  }
  @Test void string_inter_hash_expr_one(){ ok(
      "A: { .a: Str -> \n#|`pre {B .foo(C)} post\n;}\n",
      "A:{.a:Str ->\n#|`pre {B.foo(C)} post\n}");
    }
  @Test void multiple_decls_joined(){ ok(
    "A: { .id(x: X): X -> x;}\nB: {}\n",
    "A:{ .id(x:X):X -> x } B:{}");}
  @Test void require_space_between_methods_in_literal(){ ok(
    "A: { .a -> this; .b -> this;}\n",
    "A:{ .a -> this;.b -> this; }");}
  @Test void do_not_emit_trailing_comma_after_cap_only_in_targs(){ ok(
    "A: { x -> x .foo[read];}\n",
    "A:{ x -> x .foo[read,] }"); }

  @Test void decl_generics_plain_space_after_comma(){ok(
    "Pair[X,Y]: {}\n",
    "Pair[X,Y]:{}");}
  @Test void decl_generics_mixed_bounds_and_spacing(){ok(
    "G[X:imm,Y:**,Z:*]: {}\n",
    "G[X:imm,Y:**,Z:*]:{}");}
  @Test void decl_generics_param_with_multiple_rcs(){ok(
    "D[X:read,mut]: {}\n",
    "D[X:read,mut]:{}");}
  @Test void decl_generics_whitespace_normalization_inside_bounds(){ok(
    "E[X:read,mut]: {}\n",
    "E[X:read , mut]:{}");}
  @Test void supertypes_many_with_spaces(){ok(
    "A: B, C, D {}\n",
    "A:B,C,D{}");}
  @Test void supertypes_with_type_args_and_spacing(){ok(
    "A: B[X], C[Y,Z] {}\n",
    "A:B[X],C[Y,Z]{}");}
  @Test void meth_named_with_parens_and_ret_colon_required(){ ok(
    "A: { .id(x: X): X -> x;}\n",
    "A:{ .id(x:X):X -> x }");}
  @Test void meth_ret_only_signature(){ok(
    "A: { .abs(): X;}\n",
    "A:{ .abs():X }");}
  @Test void meth_generics_with_bounds_and_return(){ok(
    "A: { .map[X:*,Y:**](x: X): Y -> x;}\n",
    "A:{ .map[X:*,Y:**](x:X):Y -> x }");}
  @Test void meth_generics_no_bounds_two_params(){ok(
    "A: { .zip[X,Y](x: X, y: Y): X -> x;}\n",
    "A:{ .zip[X,Y](x:X,y:Y):X -> x }");}
  @Test void literal_many_methods_spaced_after_semicolons(){ok(
    "A: { .a -> this; .b x -> x; .c(x) -> x;}\n",
    "A:{ .a -> this; .b x -> x; .c(x) -> x; }");}
  @Test void literal_one_method_trailing_semicolon_ok(){ok(
    "A: { .a -> this;}\n",
    "A:{ .a -> this }");}
  @Test void call_parens_zero_args_must_close_paren(){ok(
    "A: { .m x -> x .foo();}\n",
    "A:{ .m x-> x .foo() }");}
  @Test void call_parens_one_arg_must_close_paren(){ok(
    "A: { .m(x, y): X -> x .plus(y);}\n",
    "A:{ .m(x,y):X -> x .plus(y) }");}
  @Test void call_parens_two_args_must_close_paren(){ok(
    "A: { .m(x, y): X -> x .mix(y, x);}\n",
    "A:{ .m(x,y):X -> x .mix(y, x) }");}
  @Test void call_square_rc_only_no_trailing_comma_in_output(){ok(
    "A: { x -> x .foo[read];}\n",
    "A:{ x -> x .foo[read,] }");}
  @Test void call_square_rc_and_types_spacing(){ok(
    "A: { x -> x .foo[read,X,Y];}\n",
    "A:{ x -> x .foo[read, X, Y] }");}
  @Test void call_square_types_only_spacing(){ok(
    "A: { x -> x .foo[X,Y];}\n",
    "A:{ x -> x .foo[X,Y] }");}
  @Test void call_operator_infix_spaces(){ok(
    "A: { x, y -> x + y;}\n",
    "A:{ x, y -> x + y }");}
  @Test void call_operator_rhs_parenthesized(){ok(
    "A: { x, y -> x +(y);}\n",
    "A:{ x, y -> x + (y) }");}
  @Test void call_chained_mixed_forms(){ok(
    "A: { x, y, z, w -> x .foo[read,X](y) .bar z + w;}\n",
    "A:{ x, y, z, w -> x .foo[read, X](y) .bar z + w }");}
  @Test void return_type_with_rc_prefix(){ ok(
    "A: { .m(): read B -> this;}\n",
    "A:{ .m(): read B -> this }");}
  @Test void method_decl_with_deep_nested_type_args(){ ok(
    "A: { .t: C[D[E],F[G,H]];}\n",
    "A:{ .t: C[D[E], F[G,H]] }");}
  @Test void destruct_param_mixed_many(){ok(
    "A: { .u(x, {.p.q}R, {.a,.b}S): R -> qR;}\n",
    "A:{ .u(x, {.p.q}R, {.a,.b}S): R -> qR }");}
  @Test void decl_literal_with_thisname_and_multi_methods(){ ok(
    "A: { .m -> B: {'s .a -> this; .b x -> x;};}\n",
    "A:{ .m -> B:{'s .a -> this; .b x -> x;} }");}
  @Test void decl_literal_with_rc_prefix_and_thisname(){ok(
    "A: { .m -> read B: {'s};}\n",
    "A:{ .m -> read B:{'s} }");}
  @Test void implicit_receiver_then_dot_call(){ok(
    "A: { x -> :: .a x;}\n",
    "A:{ x -> :: .a x }");}
  @Test void implicit_receiver_then_chained_calls_mixed(){ ok(
    "A: { x, y -> :: .a x .b y;}\n",
    "A:{ x, y -> :: .a x .b y }");}
  @Test void pkg_types_in_param_and_return(){ok(
    "A: { .m(x: foo.Bar): baz.Qux -> x;}\n",
    "A:{ .m(x:foo.Bar):baz.Qux -> x }");}
  @Test void method_no_parens_but_return_type(){ ok(
    "A: { .m: X;}\n",
    "A:{ .m:X }");}
  @Test void generic_method_with_bounds_and_ret(){ok(
    "A: { .id[X:*](x: X): X -> x;}\n",
    "A:{ .id[X:*](x:X):X -> x }");}
  @Test void round_group_as_receiver_then_dot_sugar(){ok(
    "A: { x, y -> (x) .foo y;}\n",
    "A:{ x, y -> (x) .foo y }");}
  @Test void literal_thisname_only_no_methods(){ok(
    "A: { .m -> B: {'s};}\n",
    "A:{ .m -> B:{'s} }");}
  @Test void eqSugar(){ok(
    "A: { .m -> Block # .let x= { 5;} .var y= { 6;} .return { x + y;};}\n",
    "A:{ .m -> Block#.let x= {5} .var y={6} .return{x+y} }");}

}