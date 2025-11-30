package typeSystem;

/*
 
  - literals contains both signatures directly declared in the literal and cached expected results from meth.
    Thus, when using literal.ms() as input to those rules, you should filter and keep only the ones whose source is the current literal.    
  - Distinguish assertion errors (internal consistency expectations) from proper user facing errors (define/assume methods in the TypeSystemErrors class for them)
  - grouping methods by name: In the implementation we also have overloading via receiver RC, so name+rc should be the basis for grouping.
  - the Literal should be already caching not the result of sources but the result of meth(D[Ts],m); that is: grouping on Literal.ms()
    would give only groups of size one. I think we have to compute sources as in the formalism, then validate that the method present in ms is the correct `selection` that meth would do.
    -compatible should throw the (user facing) error directly instead of returning a bool. This is because it should be in the good position to know all the relevant data to give a clear and friendly error.
    - Here     var tsBound= s1.bs().stream().map(b->new T.X(b.x())).toList();
    you want     var tsBound= s1.bs().stream().<T>map(b->new T.X(b.x())).toList(); otherwise Java creates a list of T.X not a list of T
    -Contravariance: Arg(Super) <= Arg(Sub). r1 (Sub) <= r2 (Super)
    Yes, this is an extension of the metarules, allowing co/contra variance instead of asking for equality. Sorry for the confusion.
    - I'm not sure about your originSubtype algorithm. A few clarifications: We already verified the absence of cyclic inheritance so you can assume no cycles.
      If a TName inherits from a TName' indeed TName prime may not be in the decs. In that case it will be in OtherPackages (we need to somehow get that too and pass it around. Probably we need to not have Decs as a Map but as a method/lambda that just do the get(TName).
      This will require adding stuff in the top of class TypeSystem.
    - overall many of those notations in the formalism that take/give mType could instead take/give core.Sig
Define mtype(D[Ts], M) = m[∆]:RC D[Ts] T1 . . . T𝑛 → T
M = RC m[∆](_:T1, . . . , _:T𝑛):T _
Define sources(D[Ts]) = mtype(D[Ts], M1)[∆=Ts] . . . mtype(D[T], M𝑘 )[∆=Ts] mtype
  D[∆]:D1[T1] . . . D𝑛[T𝑛]{'𝑥 M1 . . . M𝑘} ∈ L
  mtype = sources(D1[T1][∆=Ts]) . . .sources(D𝑛[T𝑛][∆=Ts])

We use the notation sources(D[Ts]) to collect the set of all method signatures (represented as
mtypes) in the type D[Ts], including both directly defined and inherited methods. The first T in
mtype’s sequence of parameters is the type of the receiver. The notation mtype(D[Ts], M) trivially
constructs a mtype from a receiver type and a method.

Define overrideOk(D[Ts]) holds iff ∀mtype1 ∈ sources(D[Ts]), mtype2 ∈ sources(D[Ts]),
  if name(mtype1) = name(mtype2) then mtype1 ≃ mtype2

Our overrideOk(D[Ts]) notation ensures that all overriding method signatures within a type’s
inheritance hierarchy are compatible.

Define mtype1 ≃ mtype2
m[∆]:RC_ T1 . . . T𝑛 → T0 ≃ m[∆]:RC_ T1 . . . T𝑛 → T0
We use the notation ‘mtype1 ≃ mtype2’ to denote that two method types are structurally
compatible for the purpose of inheritance.
This compatibility holds if both method types share
the same name, the same generic bounds (if appropriately alpha renamed)
and they have the same receiver capability.
Alpha-renaming can help to make the two generic bounds equal.
Note that the concrete receiver type is not considered in this check;
only the capability matters.
Then the parameters and the return types need to obey the usual co/contra variance rules.

Define implementOk(D[Ts]) holds iff
∀mtype1∈ sources(D[Ts]), mtype2∈ sources(D[Ts]), conflict(mtype1, mtype2) implies
  ∃mtype3∈ sources(D[Ts]) such that mtype3 ≤ mtype1

Our notation ‘implementOk’ checks that no conflicting implementations exist for the same
method. That is, our inheritance model handles multiple inheritance and conflicts similarly to
Schärli et al.’s original traits model, where the order of implementation does not matter and
the programmer must specify an explicit override in case of conflicts.
The formal definition defined above relies on ‘conflict’ and ‘alternative’ and states that for all
conflicting pairs mtype1 mtype2, an mtype3 that beats them exists.
Note that both mtype1 and mtype2 could be selected as mtype3.

Define alternative(mtype1, mtype2) iff
RC𝑖 D𝑖[_] = recvT(mtype𝑖)
D1 ≠ D2
name(mtype1) = name(mtype2)

Define conflict(mtype1, mtype2) iff
  alternative(mtype1, mtype2)
  not abs(mtype1) or not abs(mtype2)

mtype1 and mtype2 are in ‘alternative’ if they have the same name but originate from different
types. We use the notation recvT(mtype) to extract the type of the receiver (the first type in the
sequence) from a mtype.
In our implementation we already have the full set of methods (including the inherited once) and flagged with their origin.
We should rely on this cached information in the happy path, but we need to verify that we cached it correctly in assertions.

mtype1 and mtype2 are in ‘conflict’ if they are alternatives and at least one of the two is not
abstract.
We use the notation abs to determine if a method is abstract or not by extracting name(mtype) and recvT(mtype), then looking up the corresponding L from the globally available L, and extracting
the method M from L.
Again, in our code we do have this information cached, but we should have dedicated methods called only in asserts that double check
Define abs(mtype)
  abs(m[_]:RC D[_]_) iff D[_]:_{_ M _} ∈ Decs and M = m[_](_):T,

We use the notation mtype1 ≤ mtype2
to check if the receiver of a method inherits from the
receiver of another one. We can use subtyping to this aim, but we need some care:
First we forge a type from the receiver’s type-name by (arbitrarily) using mut as the RC.
Then we use the empty ∆.
This approach has a subtle interaction with RC-sub.
It is either superfluous (behaving exactly like Refl-sub) or not applicable.

Define mtype1 ≤ mtype2
name(mtype1) = name(mtype2)
∅ ⊢ recvT(mtype1)[mut] ≤ recvT(mtype2)[mut]

Define meth(D[Ts], m) = mtype iff
mtype ∈ sources(D[Ts])
name(mtype) = m
∀mtype′ ∈ sources(D[Ts]), if conflict(mtype, mtype′) then mtype ≤ mtype′
The idea behind ‘meth’ is that there could be many methods with the same name in sources(D[Ts]),
and we select the one that is the most specific.
Such method must exist because ‘implementOk’ holds.
*/