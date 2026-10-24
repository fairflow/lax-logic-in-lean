import Meta.Audit

/-!
# Nuclear Esakia duality, the finite case: definitions and statements

Round 1 of the nuclear-Esakia campaign (`wip/esakia-STATUS.md`).  This file
holds DEFINITIONS and STATEMENTS only.  Every statement is a `def … : Prop`;
none is asserted.  The designed cells that test them are in
`wip/esakiaNuclearCells.lean`.

## Source

The finite statements transcribe

* G. Bezhanishvili, N. Bezhanishvili, L. Carai, D. Gabelaia, S. Ghilardi,
  M. Jibladze, *Diego's Theorem for nuclear implicative semilattices*,
  Indag. Math. 32(2) (2021) 498–535, doi:10.1016/j.indag.2020.12.005,
  arXiv:2001.11060 — cited below as **[BBCGGJ]**: Thm 3.4 with (†), §3
  (`j_S`, `S_j`), Lemma 3.15, Thm 3.16, Lemma 4.3, Lemma 4.12;

and the finite instances of

* G. Bezhanishvili, S. Ghilardi, *An algebraic approach to subframe logics.
  Intuitionistic case*, APAL 147 (2007) 84–100 — **[BG]** Thm 30, Cor 31,
  Thm 34, as restated verbatim in Ávila–Bezhanishvili–Morandi–Zaldívar,
  JPAA 224 (2020) 106302, arXiv:1906.03636, Thms 4.3 and 4.4 (**[ABMZ]**).

[BBCGGJ] works with implicative semilattices; at the level of OBJECTS a
finite implicative semilattice is a finite Heyting algebra ([BBCGGJ] §3,
before Def 3.6), so the object statements below are theirs verbatim.
Their MORPHISMS are implicative-semilattice homomorphisms (Köhler partial
maps); for Heyting homomorphisms and p-morphisms no fetched source states
the nuclear condition, and F10 is OURS (the computation of [BBCGGJ]
Lemma 4.3 with `f* = f⁻¹`).

## Encoding (choice-free, decidable)

A finite carrier is `{0, …, n-1}` with a Boolean order table; a subset is
its list of membership bits; a self-map is any `Nat → Nat` (only its values
on the carrier are read).  A finite Heyting algebra is presented by its
operation tables, which `isHA` checks against the order: `meetT` gives
greatest lower bounds, `joinT` least upper bounds, `himpT` relative
pseudocomplements (`x ∧ a ≤ b ↔ x ≤ a → b`), and `top`, `bot` the bounds.
No Mathlib, no `Fin`, no `Finset`: every statement instance at a concrete
cell is decided by the kernel.

Points of the dual are the MEET-PRIMES of the algebra, as in [BBCGGJ]
Def 3.5, ordered by the dual of the algebra's order:
`m ⊑ n ↔ n ≤ m`.  (In [ABMZ]/[BG] the points are prime filters ordered by
inclusion; a meet-prime `m` corresponds to the prime filter `A ∖ ↓m`, and
`m ⊑ n` to inclusion of prime filters.)

## The statements

Fragment first (CLAUDE.md rule 8): F1, F2 and F10a are the ◯-free
(plain Heyting) statements; F3–F9 and F10 add the nucleus.

| | statement | source |
|---|---|---|
| F1 | `α_A : A ≅ Up(X_A)`, Heyting | [BBCGGJ] Thm 3.4, (†) |
| F2 | `ε_X : X ≅ X_{Up(X)}`, order iso | [BBCGGJ] Thm 3.4, (†) |
| F3 | `j_S` is a nucleus on `Up(X)` for every `S ⊆ X` | [BBCGGJ] §3 |
| F4 | `α_A(j a) = j_{S_j}(α_A a)` | [BBCGGJ] Lemma 3.15 |
| F5 | `ε_X(S) = S_{j_S}` | [BBCGGJ] Lemma 4.12 |
| F6 | `S ↦ α⁻¹ ∘ j_S ∘ α` is a nucleus with `S_{…} = S` | [BG] Thm 30 (finite) |
| F7 | `j ≤ k ↔ S_k ⊆ S_j` | [BG] Thm 30 (finite) |
| F8 | `S_{j ∧ k} = S_j ∪ S_k` | [BG] Cor 31 (finite) |
| F9 | `S_{u_a} = X ∖ α(a)`, `S_{v_a} = α(a)`, `S_{w_a} = max(X ∖ α(a))` | [BG] Thm 34 (finite) |
| F10a | `h_*` is a p-morphism `X_B → X_A` with `α_B ∘ h = h_*⁻¹ ∘ α_A` | [BBCGGJ] Thm 3.4 |
| F10 | `h ∘ j = k ∘ h ↔ (∗)` for every Heyting hom `h` | OURS, after [BBCGGJ] L4.3 |
-/

namespace EsakiaNuclear

/-! ## 0. Subsets and self-maps of `{0, …, n-1}` -/

/-- A subset of `{0, …, n-1}`: its list of membership bits. -/
abbrev Bits := List Bool

/-- Membership; bits beyond the list are `false`. -/
def mem (s : Bits) (x : Nat) : Bool := s.getD x false

/-- Every subset of `{0, …, n-1}`, each of length `n`. -/
def allSubs : Nat → List Bits
  | 0 => [[]]
  | n + 1 => (allSubs n).flatMap fun s => [s ++ [false], s ++ [true]]

/-- Every self-map of `{0, …, n-1}`, as a table of length `n`. -/
def allTables (n : Nat) : List (List Nat) :=
  (List.range n).foldr
    (fun _ acc => acc.flatMap fun t => (List.range n).map fun v => v :: t) [[]]

/-- A table read as a self-map. -/
def tab (t : List Nat) : Nat → Nat := fun a => t.getD a 0

/-- Set complement within `{0, …, n-1}`. -/
def bcompl (s : Bits) : Bits := s.map (!·)

/-- Union of two subsets of the same carrier. -/
def bunion (s t : Bits) : Bits := List.zipWith (· || ·) s t

/-! ## 1. Finite orders, up-sets and the nucleus `j_S` -/

/-- A finite carrier `{0, …, n-1}` with a Boolean order table. -/
structure FinOrd where
  n : Nat
  le : Nat → Nat → Bool

namespace FinOrd

variable (P : FinOrd)

/-- The carrier `[0, …, n-1]`. -/
def pts : List Nat := List.range P.n

/-- `P` is a partial order: reflexive, antisymmetric, transitive. -/
def isPoset : Bool :=
  (P.pts.all fun x => P.le x x) &&
  (P.pts.all fun x => P.pts.all fun y => !(P.le x y && P.le y x) || x == y) &&
  (P.pts.all fun x => P.pts.all fun y => P.pts.all fun z =>
    !(P.le x y && P.le y z) || P.le x z)

/-- Inclusion of subsets of the carrier. -/
def subsetOf (U V : Bits) : Bool := P.pts.all fun x => !(mem U x) || mem V x

/-- `U` is an up-set: `x ∈ U`, `x ≤ y` imply `y ∈ U`. -/
def isUp (U : Bits) : Bool :=
  P.pts.all fun x => P.pts.all fun y => !(mem U x && P.le x y) || mem U y

/-- The up-sets of `P`, in the enumeration order of `allSubs`. -/
def ups : List Bits := (allSubs P.n).filter P.isUp

/-- The position of an up-set in `ups` (`0` if absent). -/
def upIdx (U : Bits) : Nat :=
  ((List.range P.ups.length).find? fun i => P.ups.getD i [] == U).getD 0

/-- `j_S(U) = X ∖ ↓(S ∖ U)` ([BBCGGJ] §3): `x ∈ j_S(U)` iff no `y ≥ x`
lies in `S` and outside `U`. -/
def jS (S U : Bits) : Bits :=
  P.pts.map fun x => !(P.pts.any fun y => P.le x y && mem S y && !(mem U y))

/-- `U → V = X ∖ ↓(U ∖ V)` ([BBCGGJ] Def 3.1). -/
def impUp (U V : Bits) : Bits :=
  P.pts.map fun x => !(P.pts.any fun y => P.le x y && mem U y && !(mem V y))

/-- The maximal points of `T`. -/
def maxOf (T : Bits) : Bits :=
  P.pts.map fun t => mem T t && !(P.pts.any fun s => mem T s && P.le t s && s != t)

/-- The up-set algebra `Up(P)` as a finite order: element `i` is `ups[i]`,
ordered by inclusion. -/
def upAlg : FinOrd :=
  ⟨P.ups.length, fun i k => P.subsetOf (P.ups.getD i []) (P.ups.getD k [])⟩

/-- `ε_X(x) = X ∖ ↓x` ([BBCGGJ] (†)), as an element of `Up(P)`. -/
def eps (x : Nat) : Nat := P.upIdx (P.pts.map fun y => !(P.le y x))

/-- `j_S` transported to the elements of `Up(P)`. -/
def jSIdx (S : Bits) (i : Nat) : Nat := P.upIdx (P.jS S (P.ups.getD i []))

end FinOrd

/-! ## 2. Finite Heyting algebras, meet-primes, `α`, `S_j` -/

/-- A finite Heyting algebra presented by its operation tables; `isHA`
checks the presentation. -/
structure FinHA where
  ord : FinOrd
  meetT : List (List Nat)
  joinT : List (List Nat)
  himpT : List (List Nat)
  top : Nat
  bot : Nat

namespace FinHA

variable (H : FinHA)

def pts : List Nat := H.ord.pts
def le (a b : Nat) : Bool := H.ord.le a b
def meet (a b : Nat) : Nat := (H.meetT.getD a []).getD b 0
def join (a b : Nat) : Nat := (H.joinT.getD a []).getD b 0
def himp (a b : Nat) : Nat := (H.himpT.getD a []).getD b 0

/-- The presentation is a Heyting algebra: `(n, le)` is a partial order
with top and bottom, `meet` is the glb, `join` the lub, and `himp` the
relative pseudocomplement, `x ∧ a ≤ b ↔ x ≤ a → b`.  (Distributivity
follows from the existence of `himp`.) -/
def isHA : Bool :=
  H.ord.isPoset && decide (H.top < H.ord.n) && decide (H.bot < H.ord.n) &&
  (H.pts.all fun x => H.le x H.top && H.le H.bot x) &&
  (H.pts.all fun a => H.pts.all fun b =>
    decide (H.meet a b < H.ord.n) && decide (H.join a b < H.ord.n) &&
    decide (H.himp a b < H.ord.n) &&
    H.le (H.meet a b) a && H.le (H.meet a b) b &&
    H.le a (H.join a b) && H.le b (H.join a b) &&
    H.pts.all fun x =>
      (!(H.le x a && H.le x b) || H.le x (H.meet a b)) &&
      (!(H.le a x && H.le b x) || H.le (H.join a b) x) &&
      (H.le (H.meet x a) b == H.le x (H.himp a b)))

/-- `m` is meet-prime ([BBCGGJ] Def 3.5): `m ≠ 1`, and `a ∧ b ≤ m` implies
`a ≤ m` or `b ≤ m`. -/
def isMeetPrime (m : Nat) : Bool :=
  m != H.top && H.pts.all fun a => H.pts.all fun b =>
    !(H.le (H.meet a b) m) || H.le a m || H.le b m

/-- `X_A`, the meet-primes, in increasing index order. -/
def mprimes : List Nat := H.pts.filter H.isMeetPrime

/-- The dual poset `A_* = (X_A, ⊑)`, `m ⊑ n ↔ n ≤ m` ([BBCGGJ] Def 3.5);
its point `i` is `mprimes[i]`. -/
def dual : FinOrd :=
  ⟨H.mprimes.length, fun i k => H.le (H.mprimes.getD k 0) (H.mprimes.getD i 0)⟩

/-- `α_A(a) = {x ∈ X_A | a ≰ x}` ([BBCGGJ] (†)). -/
def alpha (a : Nat) : Bits :=
  (List.range H.mprimes.length).map fun i => !(H.le a (H.mprimes.getD i 0))

/-- The element whose `α` is `U` (`0` if none). -/
def alphaInv (U : Bits) : Nat := (H.pts.find? fun a => H.alpha a == U).getD 0

/-- `j` is a nucleus ([ABMZ] Def 2.1): into the carrier, `a ≤ j a`,
`j (j a) ≤ j a`, `j (a ∧ b) = j a ∧ j b`. -/
def isNucleus (j : Nat → Nat) : Bool :=
  (H.pts.all fun a => decide (j a < H.ord.n) && H.le a (j a) && H.le (j (j a)) (j a)) &&
  (H.pts.all fun a => H.pts.all fun b => j (H.meet a b) == H.meet (j a) (j b))

/-- `S_j = X_A ∩ A_j`, the meet-primes fixed by `j` ([BBCGGJ] §3), as a
subset of the dual's points. -/
def Sj (j : Nat → Nat) : Bits :=
  (List.range H.mprimes.length).map fun i =>
    j (H.mprimes.getD i 0) == H.mprimes.getD i 0

/-- The nucleus on `A` named by a subset `S ⊆ X_A`: `α⁻¹ ∘ j_S ∘ α`. -/
def jA (S : Bits) : Nat → Nat := fun a => H.alphaInv (H.dual.jS S (H.alpha a))

/-- The closed nucleus `u_a(x) = a ∨ x` ([ABMZ] §2). -/
def u (a : Nat) : Nat → Nat := fun x => H.join a x
/-- The open nucleus `v_a(x) = a → x`. -/
def v (a : Nat) : Nat → Nat := fun x => H.himp a x
/-- The nucleus `w_a(x) = (x → a) → a`. -/
def w (a : Nat) : Nat → Nat := fun x => H.himp (H.himp x a) a
/-- The pointwise meet of two maps. -/
def jMeet (j k : Nat → Nat) : Nat → Nat := fun a => H.meet (j a) (k a)

/-- Tables of a finite order computed by search (untrusted: `isHA` judges
them). -/
def ofOrd (P : FinOrd) : FinHA :=
  let pts := P.pts
  let glb (a b : Nat) : Nat := (pts.find? fun c => P.le c a && P.le c b &&
    pts.all fun x => !(P.le x a && P.le x b) || P.le x c).getD 0
  let lub (a b : Nat) : Nat := (pts.find? fun c => P.le a c && P.le b c &&
    pts.all fun x => !(P.le a x && P.le b x) || P.le c x).getD 0
  let meetT := pts.map fun a => pts.map fun b => glb a b
  let rpc (a b : Nat) : Nat := (pts.find? fun c => pts.all fun x =>
    P.le ((meetT.getD x []).getD a 0) b == P.le x c).getD 0
  { ord := P
    meetT := meetT
    joinT := pts.map fun a => pts.map fun b => lub a b
    himpT := pts.map fun a => pts.map fun b => rpc a b
    top := (pts.find? fun c => pts.all fun x => P.le x c).getD 0
    bot := (pts.find? fun c => pts.all fun x => P.le c x).getD 0 }

end FinHA

/-- `Up(X)` as a finite Heyting algebra, with `∩`, `∪` and
`U → V = X ∖ ↓(U ∖ V)` ([BBCGGJ] Def 3.1). -/
def FinOrd.upHA (X : FinOrd) : FinHA :=
  let B := X.upAlg
  let U (i : Nat) : Bits := X.ups.getD i []
  { ord := B
    meetT := B.pts.map fun i => B.pts.map fun k => X.upIdx (List.zipWith (· && ·) (U i) (U k))
    joinT := B.pts.map fun i => B.pts.map fun k => X.upIdx (List.zipWith (· || ·) (U i) (U k))
    himpT := B.pts.map fun i => B.pts.map fun k => X.upIdx (X.impUp (U i) (U k))
    top := X.upIdx (X.pts.map fun _ => true)
    bot := X.upIdx (X.pts.map fun _ => false) }

/-! ## 3. Statements: the plain (◯-free) fragment -/

/-- **F1** at `H` ([BBCGGJ] Thm 3.4 with (†)): `α_A` lands in `Up(X_A)`, is
an order isomorphism `A ≅ Up(X_A)`, and preserves `→`. -/
abbrev AlphaIso (H : FinHA) : Prop :=
  (∀ a ∈ H.pts, H.dual.isUp (H.alpha a) = true) ∧
  (∀ a ∈ H.pts, ∀ b ∈ H.pts, H.le a b = H.dual.subsetOf (H.alpha a) (H.alpha b)) ∧
  (∀ U ∈ H.dual.ups, ∃ a ∈ H.pts, H.alpha a = U) ∧
  (∀ a ∈ H.pts, ∀ b ∈ H.pts,
    H.alpha (H.himp a b) = H.dual.impUp (H.alpha a) (H.alpha b))

/-- **F1.** Every finite Heyting algebra is `Up` of its dual poset. -/
def F1 : Prop := ∀ H : FinHA, H.isHA = true → AlphaIso H

/-- **F2** at `X` ([BBCGGJ] Thm 3.4 with (†)): `Up(X)` is a Heyting algebra
and `ε_X(x) = X ∖ ↓x` is an order isomorphism of `X` onto the meet-primes
of `Up(X)`, ordered dually. -/
abbrev EpsIso (X : FinOrd) : Prop :=
  X.upHA.isHA = true ∧
  (∀ x ∈ X.pts, X.upHA.isMeetPrime (X.eps x) = true) ∧
  (∀ m ∈ X.upHA.pts, X.upHA.isMeetPrime m = true → ∃ x ∈ X.pts, X.eps x = m) ∧
  (∀ x ∈ X.pts, ∀ y ∈ X.pts, X.le x y = X.upHA.le (X.eps y) (X.eps x))

/-- **F2.** Every finite poset is the dual of its up-set algebra. -/
def F2 : Prop := ∀ X : FinOrd, X.isPoset = true → EpsIso X

/-! ## 4. Statements: nuclei -/

/-- **F3** at `(X, S)` ([BBCGGJ] §3, "it is easy to check"): `j_S` maps
up-sets to up-sets and is a nucleus on `Up(X)`. -/
abbrev JSNucleus (X : FinOrd) (S : Bits) : Prop :=
  (∀ U ∈ X.ups, X.isUp (X.jS S U) = true) ∧ X.upHA.isNucleus (X.jSIdx S) = true

/-- **F3.** For every finite poset `X` and every `S ⊆ X`. -/
def F3 : Prop := ∀ X : FinOrd, X.isPoset = true → ∀ S ∈ allSubs X.n, JSNucleus X S

/-- **F4** at `(H, j)` ([BBCGGJ] Lemma 3.15): `α_A(j a) = j_{S_j}(α_A(a))`. -/
abbrev Rep (H : FinHA) (j : Nat → Nat) : Prop :=
  ∀ a ∈ H.pts, H.alpha (j a) = H.dual.jS (H.Sj j) (H.alpha a)

/-- **F4** (with F1 this is [BBCGGJ] Thm 3.16, `(A, j) ≅ (Up(X_A), j_{S_j})`). -/
def F4 : Prop :=
  ∀ (H : FinHA) (j : Nat → Nat), H.isHA = true → H.isNucleus j = true → Rep H j

/-- **F5** at `(X, S)` ([BBCGGJ] Lemma 4.12): `ε_X(S) = S_{j_S}`, i.e.
`x ∈ S` iff `ε_X(x)` is fixed by `j_S`. -/
abbrev EpsS (X : FinOrd) (S : Bits) : Prop :=
  ∀ x ∈ X.pts, mem S x = (X.jSIdx S (X.eps x) == X.eps x)

/-- **F5.** -/
def F5 : Prop := ∀ X : FinOrd, X.isPoset = true → ∀ S ∈ allSubs X.n, EpsS X S

/-- **F6** at `(H, S)` ([BG] Thm 30, finite case, the inverse map): for
`S ⊆ X_A`, `α⁻¹ ∘ j_S ∘ α` is a nucleus on `A` whose `S_j` is `S`.  With F4
(which gives `jA (S_j) = j`), `j ↦ S_j` is a bijection from the nuclei on
`A` onto the subsets of `X_A`. -/
abbrev Bij (H : FinHA) (S : Bits) : Prop :=
  H.isNucleus (H.jA S) = true ∧ H.Sj (H.jA S) = S

/-- **F6.** -/
def F6 : Prop := ∀ H : FinHA, H.isHA = true → ∀ S ∈ allSubs H.mprimes.length, Bij H S

/-- **F7** at `(H, j, k)` ([BG] Thm 30, "dually isomorphic"): `j ≤ k`
pointwise iff `S_k ⊆ S_j`. -/
abbrev OrdRev (H : FinHA) (j k : Nat → Nat) : Prop :=
  (H.pts.all fun a => H.le (j a) (k a)) = H.dual.subsetOf (H.Sj k) (H.Sj j)

/-- **F7.** -/
def F7 : Prop :=
  ∀ (H : FinHA) (j k : Nat → Nat), H.isHA = true →
    H.isNucleus j = true → H.isNucleus k = true → OrdRev H j k

/-- **F8** at `(H, j, k)` ([BG] Cor 31): `S_{j ∧ k} = S_j ∪ S_k`. -/
abbrev MeetUnion (H : FinHA) (j k : Nat → Nat) : Prop :=
  H.Sj (H.jMeet j k) = bunion (H.Sj j) (H.Sj k)

/-- **F8.** -/
def F8 : Prop :=
  ∀ (H : FinHA) (j k : Nat → Nat), H.isHA = true →
    H.isNucleus j = true → H.isNucleus k = true → MeetUnion H j k

/-- **F9** at `(H, a)` ([BG] Thm 34, = [ABMZ] Thm 4.4): the subsets of the
closed, open and `w`-nuclei. -/
abbrev Thm34 (H : FinHA) (a : Nat) : Prop :=
  H.Sj (H.u a) = bcompl (H.alpha a) ∧
  H.Sj (H.v a) = H.alpha a ∧
  H.Sj (H.w a) = H.dual.maxOf (bcompl (H.alpha a))

/-- **F9.** -/
def F9 : Prop := ∀ H : FinHA, H.isHA = true → ∀ a ∈ H.pts, Thm34 H a

/-! ## 5. Statements: morphisms -/

/-- `h` is a Heyting homomorphism `A → B` (bounds, `∧`, `∨`, `→`). -/
def isHAHom (A B : FinHA) (h : Nat → Nat) : Bool :=
  (A.pts.all fun a => decide (h a < B.ord.n)) && h A.top == B.top && h A.bot == B.bot &&
  (A.pts.all fun a => A.pts.all fun b =>
    h (A.meet a b) == B.meet (h a) (h b) && h (A.join a b) == B.join (h a) (h b) &&
    h (A.himp a b) == B.himp (h a) (h b))

/-- `h_*(y) = ⋁{a ∈ A | h(a) ≤ y}` ([BBCGGJ] §3, after Def 3.5), computed
as the greatest such `a`. -/
def hstar (A B : FinHA) (h : Nat → Nat) (y : Nat) : Nat :=
  (A.pts.find? fun a => B.le (h a) y &&
    A.pts.all fun b => !(B.le (h b) y) || A.le b a).getD 0

/-- **F10a** at `h` ([BBCGGJ] Thm 3.4, the ◯-free morphism part): `h_*` maps
`X_B` into `X_A`, is order-preserving and has the back condition for `⊑`
(a p-morphism), and `α_B(h a) = h_*⁻¹(α_A a)`. -/
abbrev PMorph (A B : FinHA) (h : Nat → Nat) : Prop :=
  (∀ x ∈ B.mprimes, A.isMeetPrime (hstar A B h x) = true) ∧
  (∀ x ∈ B.mprimes, ∀ x' ∈ B.mprimes, B.le x' x = true →
    A.le (hstar A B h x') (hstar A B h x) = true) ∧
  (∀ x ∈ B.mprimes, ∀ y ∈ A.mprimes, A.le y (hstar A B h x) = true →
    ∃ z ∈ B.mprimes, B.le z x = true ∧ hstar A B h z = y) ∧
  (∀ a ∈ A.pts, ∀ x ∈ B.mprimes, B.le (h a) x = A.le a (hstar A B h x))

/-- **F10a.** -/
def F10a : Prop :=
  ∀ (A B : FinHA) (h : Nat → Nat), A.isHA = true → B.isHA = true →
    isHAHom A B h = true → PMorph A B h

/-- Condition (∗) of [BBCGGJ] Lemma 4.3 for the p-morphism `f = h_*`,
`S = S_k ⊆ X_B`, `T = S_j ⊆ X_A`, at every `x ∈ X_B`:
`↑(↑f(x) ∩ T) = ↑f(↑x ∩ S)`, written for elements (`↑` in `⊑` is `↓` in
the algebra). -/
def starCond (A B : FinHA) (j k h : Nat → Nat) : Bool :=
  B.mprimes.all fun x => A.mprimes.all fun t =>
    (A.mprimes.any fun z => A.le z (hstar A B h x) && j z == z && A.le t z) ==
    (B.mprimes.any fun s => B.le s x && k s == s && A.le t (hstar A B h s))

/-- **F10** at `(A, j) → (B, k)` along `h` (OURS: [BBCGGJ] Lemma 4.3's
computation with `f* = f⁻¹`, for Heyting homomorphisms): `h` commutes with
the nuclei iff (∗) holds. -/
abbrev NuclearHom (A B : FinHA) (j k h : Nat → Nat) : Prop :=
  (A.pts.all fun a => h (j a) == k (h a)) = starCond A B j k h

/-- **F10.** -/
def F10 : Prop :=
  ∀ (A B : FinHA) (j k h : Nat → Nat), A.isHA = true → B.isHA = true →
    A.isNucleus j = true → B.isNucleus k = true → isHAHom A B h = true →
    NuclearHom A B j k h

/-- The NAIVE transfer of [BBCGGJ] Remark 4.6 to Heyting homomorphisms
(a total Köhler morphism is an S-morphism iff `f⁻¹(T) = S`): `h` commutes
with the nuclei iff `h_*⁻¹(S_j) = S_k`.  Not claimed; the cells test it. -/
abbrev NaiveHom (A B : FinHA) (j k h : Nat → Nat) : Prop :=
  (A.pts.all fun a => h (j a) == k (h a)) =
    (B.mprimes.all fun x => (k x == x) == (j (hstar A B h x) == hstar A B h x))

end EsakiaNuclear

/-! ## Axiom audit of the definitions -/

#axioms_within EsakiaNuclear.FinHA.isHA [propext, Quot.sound]
#axioms_within EsakiaNuclear.FinOrd.upHA [propext, Quot.sound]
#axioms_within EsakiaNuclear.FinHA.ofOrd [propext, Quot.sound]
#axioms_within EsakiaNuclear.F10 [propext, Quot.sound]
