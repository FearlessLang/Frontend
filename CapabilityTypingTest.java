@Test void probe1(){ok(List.of("""
Foo:{}
Util:{ .m[Y:*]: read Y -> this.m[Y] }
A:{ .f: read Foo -> Util.m }
"""));}
@Test void probe2(){ok(List.of("""
Foo:{}
Box[T:*]:{}
Util:{ .m[Y:*](b: Box[read Y]): Foo -> Foo }
A:{ .f(b: Box[read Foo]): Foo -> Util.m(b) }
"""));}
@Test void probe3(){ok(List.of("""
Foo:{}
Cons[Y:*]:{ #(y: read Y): Foo }
Need:{ #[Y:*](c: Cons[Y]): Foo -> Foo }
A:{ .f: Foo -> Need#{ #(y: read Foo): Foo -> Foo } }
"""));}
@Test void probe4(){ok(List.of("""
Foo:{}
Util:{ .m[Y:*](y: Y): Foo -> Foo }
A:{ .f(x: iso Foo): Foo -> Util.m(x) }
"""));}
@Test void probe5(){ok(List.of("""
Foo:{}
Box[T:*]:{ .m(t: read T): Foo -> Foo }
A:{ .f(x: read Foo): Foo -> Box{}.m(x) }
"""));}
@Test void probe6(){ok(List.of("""
Foo:{}
Util:{ .m[Y:mut,read](y: read Y): Foo -> Foo }
A:{ .f(x: read Foo): Foo -> Util.m(x) }
"""));}
@Test void probe7(){ok(List.of("""
Foo:{}
Cons[Y:*]:{ #(y: read Y): Foo }
A:{ .f: Cons[read Foo] -> { #(y: read Foo): Foo -> Foo } }
"""));}
@Test void probe8(){ok(List.of("""
Foo:{}
Util:{ .m[Y:**](y: read Y): Y -> this.m(y) }
A:{ .f(x: read Foo): Foo -> Util.m(x) }
"""));}
}