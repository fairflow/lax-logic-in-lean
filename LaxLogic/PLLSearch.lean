import LaxLogic.PLLCountermodelEmit

/-!
# `PLLND.Search` — a sound-both-ways, incomplete decision aid for PLL sequents

This module packages a single entry point, `PLLND.Search.decide`, that
attempts to settle a propositional lax logic (PLL) sequent `Γ ⊢ C` **either
way**: it looks for a proof and, in parallel, for a finite countermodel.
Every non-`unknown` verdict carries a *kernel-checkable certificate*:

* a `.proved` verdict carries a proof term `G4cTm Γ C` of the terminating,
  contraction-free calculus G4iLL″ — Lean's typechecker validates it, so
  correctness is the type system's job, not the search code's;
* a `.refuted` verdict carries a finite constraint model `M`, a world `w`,
  and a proof `FinCM.checkB M w Γ C = true` produced by the **verified**
  countermodel checker (`PLLCountermodelEmit.lean`).  The certificate
  theorem `FinCM.not_provable_of_check` upgrades it to a machine-checked
  `¬ Nonempty (LaxND Γ C)`;
* `.unknown` is explicit and honest: it means only that the bounded stages
  below found nothing.  It never asserts anything about `Γ ⊢ C`.

The intended use is as a *tool* in the tools-vs-proofs discipline: the
search itself may be fallible, but its accepted outputs are verified, so a
wrong internal guess can only degrade a verdict to `.unknown` — never
produce a false `.proved` or `.refuted`.

## How to use

The configuration is the first argument; pass `{}` for the default search
(you cannot omit it and still give `Γ`, `C` positionally).

```
open PLLND PLLND.Search

-- Decide a sequent (returns an `Answer Γ C`).
#eval (match decide {} [] (((PLLFormula.prop "p").somehow).ifThen (.prop "p")) with
        | .proved _      => "provable"
        | .refuted _ _ _ => "refuted by a finite countermodel"
        | .unknown       => "unknown")

-- Extract the kernel-checked underivability theorem from a refutation:
example : ¬ Nonempty (LaxND [] (((PLLFormula.prop "p").somehow).ifThen (.prop "p"))) :=
  match h : decide {} [] (((PLLFormula.prop "p").somehow).ifThen (.prop "p")) with
  | .refuted _ _ hc => refuted_sound hc
  | _               => by simp_all  -- (does not arise for this sequent)
```

Pass a custom `Config` to widen or narrow the search — most usefully to
supply extra frames for the countermodel battery:

```
-- A five-world chain added to the default battery.
def myCfg : Config :=
  { frames := ⟨5, [(0,1),(1,2),(2,3),(3,4),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4)],
                  [(0,1)], [4]⟩ :: defaultFrames }
#eval (decide myCfg [] someSequent).toDecision
```

## Cost profile (honest)

* **Successes are cheap.**  A true sequent is closed by the fuel-free
  backward searcher `G4cTm.find`, and a false sequent with a small
  countermodel is caught by the frame battery; both are observed to return
  effectively instantly, even at large formula weight.
* **The worst case is exponential.**  `G4cTm.find` is backward proof search
  over a terminating calculus, so it *always* halts, but no polynomial
  bound exists: provability is already PSPACE-hard for the `◯`-free
  intuitionistic fragment.  A false sequent that escapes the battery forces
  `find` to grind through its (finite, exponential) search space before
  failing.
* **The battery is incomplete by design.**  It enumerates hereditary atom
  decorations of a fixed list of small frames (≤ 4 worlds by default) and
  stops any frame whose decoration count exceeds `comboCap`.  It is a
  cheap first filter, not a complete refuter.
* **`emit` is complete over the subformula closure, but exponential**, so
  it is gated by `emitClosureCap`: it is tried only when the closure is
  small enough to be affordable.

## Trust

Verified (kernel-checked):

* `FinCM.checkB` and the certificate theorem `FinCM.not_provable_of_check`
  — a `.refuted` answer's model genuinely refutes the sequent;
* the proof-term soundness chain `G4cTm.toG4c` ▸ `G4c.equiv_nd` — a
  `.proved` answer's term genuinely witnesses `Nonempty (LaxND Γ C)`.

Untrusted, but harmless:

* the fast vector scan `forceV` and the decoration enumeration.  They only
  ever *propose* candidate countermodels; every candidate must clear the
  verified `FinCM.checkB` before it is returned, so the scan can cause
  **misses**, never a wrong certificate;
* `G4cTm.find` returning `none` proves *nothing* — it is not a completeness
  oracle, only a (fuel-free, loop-checked) searcher.

No component uses `native_decide`; the certificates reduce in the kernel.
-/

open PLLFormula

namespace PLLND.Search

/-! ## 0. Normalisation (optional PLL-equivalence preprocessing)

The rewrites below are all PLL equivalences — Heyting `⊥`/`⊤` laws together
with `◯⊤ ≡ ⊤` and `◯◯ ≡ ◯` — so they are valid on every constraint model: a
model refutes the normalised form iff it refutes the original, and
provability transfers both ways.  Their *only* role here is to shrink
formulas before the untrusted stages (the vector scan and `emit`).  Every
certificate is re-checked against the **original** `Γ`, `C`, so this
preprocessing can never be load-bearing for soundness. -/

/-- Is this literally `⊤` (i.e. `⊥ → ⊥`)? -/
def isTop : PLLFormula → Bool
  | .ifThen .falsePLL .falsePLL => true
  | _ => false

/-- One layer of PLL-equivalence simplification at the root of a formula. -/
def smash : PLLFormula → PLLFormula
  | .and A B =>
      if A == .falsePLL || B == .falsePLL then .falsePLL
      else if isTop A then B else if isTop B then A
      else if A == B then A
      else .and A B
  | .or A B =>
      if isTop A || isTop B then truePLL
      else if A == .falsePLL then B else if B == .falsePLL then A
      else if A == B then A
      else .or A B
  | .ifThen A B =>
      if A == .falsePLL || isTop B then truePLL
      else if isTop A then B
      else if A == B then truePLL
      else .ifThen A B
  | .somehow A =>
      if isTop A then truePLL
      else match A with
        | .somehow B => .somehow B
        | _ => .somehow A
  | F => F

/-- Recursive normaliser: `smash` applied bottom-up.  A PLL equivalence. -/
def nf : PLLFormula → PLLFormula
  | .and A B    => smash (.and (nf A) (nf B))
  | .or A B     => smash (.or (nf A) (nf B))
  | .ifThen A B => smash (.ifThen (nf A) (nf B))
  | .somehow A  => smash (.somehow (nf A))
  | F => F

/-! ## 1. Frames and the countermodel battery -/

/-- A finite intuitionistic-with-fallibility frame, as raw data.  Worlds are
`0, …, n-1`; `ri` lists the *strict* intuitionistic order (assumed
transitively closed, reflexivity added on use); `rm ⊆ ri` is the constraint
relation; `fall` lists the fallible worlds (which force everything). -/
structure Frame where
  /-- Number of worlds; the carrier is `{0, …, n-1}`. -/
  n : Nat
  /-- Strict part of the intuitionistic order `Rᵢ`, transitively closed. -/
  ri : List (Nat × Nat)
  /-- The constraint relation `Rₘ`, a subset of `ri`. -/
  rm : List (Nat × Nat)
  /-- The fallible worlds (they force every formula, `⊥` included). -/
  fall : List Nat

/-- The default battery: ten small frames — the generic shapes that refute
most non-theorems of PLL.  Reading the list: (1) the classical point;
(2) the fallible point; (3) a two-world chain with `Rₘ = Rᵢ`; (4) the same
chain with `Rₘ` empty (a *rigid* modal step); (5) the chain with no
fallible top; (6) a three-world chain, rigid except for the middle step;
(7) the full three-world chain; (8) a four-world fork; (9) a three-world
`V`/branch; (10) a doubled two-world chain.  They are deliberately small
(≤ 4 worlds) and cheap to decorate; a caller who needs more can prepend
their own to `Config.frames`. -/
def defaultFrames : List Frame :=
  [ ⟨1, [], [], []⟩
  , ⟨1, [], [], [0]⟩
  , ⟨2, [(0,1)], [(0,1)], [1]⟩
  , ⟨2, [(0,1)], [], [1]⟩
  , ⟨2, [(0,1)], [(0,1)], []⟩
  , ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], [2]⟩
  , ⟨3, [(0,1),(1,2),(0,2)], [(0,1),(1,2),(0,2)], [2]⟩
  , ⟨4, [(0,1),(0,2),(2,3),(0,3)], [(2,3)], [3]⟩
  , ⟨3, [(0,1),(0,2)], [(0,2)], [2]⟩
  , ⟨4, [(0,1),(0,2),(0,3),(1,3),(2,3)], [(1,3),(2,3)], [3]⟩ ]

/-- Strict `Rᵢ`-edge test on a `Frame`. -/
def riStep (f : Frame) (w v : Nat) : Bool := decide ((w, v) ∈ f.ri)

/-! ## 2. Search configuration -/

/-- Tuning parameters for `decide`.  All fields default, so `({} : Config)`
gives the standard search. -/
structure Config where
  /-- Frames used by the countermodel battery.  Defaults to `defaultFrames`;
  prepend your own frames (as extra shapes) to search a wider space. -/
  frames : List Frame := defaultFrames
  /-- Skip a battery frame when its number of admissible decorations, raised
  to the number of atoms, exceeds this cap.  Guards the enumeration against
  combinatorial blow-up on atom-rich sequents. -/
  comboCap : Nat := 200000
  /-- Skip the (complete-over-the-closure but exponential) `emit` stage when
  the subformula closure of the sequent is larger than this. -/
  emitClosureCap : Nat := 12

/-- The standard configuration (all defaults). -/
def Config.default : Config := {}

instance : Inhabited Config := ⟨{}⟩

/-! ## 3. Fast untrusted evaluation: bottom-up world vectors

`FinCM.forceB` (the verified checker's forcing function) recomputes each
subformula once per visited world, so its cost is `n^depth` — prohibitive on
heavy formulas.  `forceV` instead evaluates each subformula *once* as a
Boolean vector over all worlds (total cost `weight × n²`).  It is untrusted:
the vectors are only used to *pick candidates*, which are then re-validated
by the verified `FinCM.checkB`. -/

/-- Reflexive `Rᵢ` test on a `FinCM`. -/
def riR (M : FinCM) (w v : Nat) : Bool :=
  decide ((w, v) ∈ M.ri) || decide (w = v)

/-- Reflexive `Rₘ` test on a `FinCM`. -/
def rmR (M : FinCM) (w v : Nat) : Bool :=
  decide ((w, v) ∈ M.rm) || decide (w = v)

/-- Forcing as a world-indexed Boolean vector.  Each entry `w` says whether
world `w` forces the formula; fallible worlds force everything.  This mirrors
`FinCM.forceB` but computes each subformula once. -/
def forceV (M : FinCM) : PLLFormula → Array Bool
  | .prop a => (Array.range M.n).map fun w =>
      decide ((w, a) ∈ M.val) || decide (w ∈ M.fall)
  | .falsePLL => (Array.range M.n).map fun w => decide (w ∈ M.fall)
  | .and A B =>
      let vA := forceV M A; let vB := forceV M B
      (Array.range M.n).map fun w => vA.getD w false && vB.getD w false
  | .or A B =>
      let vA := forceV M A; let vB := forceV M B
      (Array.range M.n).map fun w => vA.getD w false || vB.getD w false
  | .ifThen A B =>
      let vA := forceV M A; let vB := forceV M B
      (Array.range M.n).map fun w =>
        (List.range M.n).all fun v =>
          !(riR M w v) || !(vA.getD v false) || vB.getD v false
  | .somehow A =>
      let vA := forceV M A
      (Array.range M.n).map fun w =>
        (List.range M.n).all fun v =>
          !(riR M w v) ||
            (List.range M.n).any fun u => rmR M v u && vA.getD u false

/-! ## 4. Hereditary decorations of a frame

An atom's truth-set must be *hereditary* along `Rᵢ` (upward closed) and must
contain every fallible world.  We enumerate such truth-sets as `n`-bit masks,
then form all assignments of masks to the sequent's atoms. -/

/-- The admissible truth-sets of a frame, as bitmasks: hereditary along `ri`
and containing every fallible world. -/
def admissible (f : Frame) : List Nat :=
  (List.range (2 ^ f.n)).filter fun m =>
    ((List.range f.n).all fun w =>
      !(m.testBit w) ||
        (List.range f.n).all fun v => !(riStep f w v) || m.testBit v) &&
    (f.fall.all fun w => m.testBit w)

/-- All assignments of admissible masks to a list of atoms. -/
def assigns : List String → List Nat → List (List (String × Nat))
  | [], _ => [[]]
  | a :: as, adm =>
      (assigns as adm).flatMap fun rest => adm.map fun m => (a, m) :: rest

/-- Turn a frame together with a mask assignment into a concrete `FinCM`. -/
def toFinCM (f : Frame) (asgn : List (String × Nat)) : FinCM :=
  { n := f.n, ri := f.ri, rm := f.rm, fall := f.fall
    val := asgn.flatMap fun am =>
      (List.range f.n).filterMap fun w =>
        if am.2.testBit w then some (w, am.1) else none }

/-- The atoms occurring in a formula. -/
def atomList : PLLFormula → List String
  | .prop a => [a]
  | .falsePLL => []
  | .and A B | .or A B | .ifThen A B => atomList A ++ atomList B
  | .somehow A => atomList A

/-- The distinct atoms occurring in a list of formulas. -/
def atomsOf (l : List PLLFormula) : List String :=
  (l.flatMap atomList).eraseDups

/-! ## 5. The certified battery sweep

`sweepCert` scans the battery of frames, decorated over the sequent's atoms,
using the fast vector evaluator on the (normalised) formulas `Γ'`, `C'`.
Every scan hit is confirmed through a **dependent** application of the
verified `FinCM.checkB` **on the original** `Γ`, `C`, so the returned witness
carries a genuine proof `FinCM.checkB M w Γ C = true`.  A wrong scan can only
fail the gate and be skipped. -/

/-- A certified countermodel witness: a finite model `M`, a world `w`, and a
proof that the verified checker accepts it for the original sequent. -/
abbrev Witness (Γ : List PLLFormula) (C : PLLFormula) : Type :=
  (M : FinCM) × (w : Nat) ×' (FinCM.checkB M w Γ C = true)

/-- Scan the battery for a certified countermodel.  Candidates are picked by
the fast scan on the normalised forms `Γ'`, `C'`; each candidate is gated by
the verified checker on the **original** `Γ`, `C`. -/
def sweepCert (cfg : Config)
    (Γ' : List PLLFormula) (C' : PLLFormula)
    (Γ : List PLLFormula) (C : PLLFormula) : Option (Witness Γ C) :=
  let ats := atomsOf (C' :: Γ')
  cfg.frames.findSome? fun f =>
    let adm := admissible f
    if adm.length ^ ats.length > cfg.comboCap then none
    else
      (assigns ats adm).findSome? fun asgn =>
        let M := toFinCM f asgn
        let vΓ := Γ'.map (forceV M)
        let vC := forceV M C'
        (List.range f.n).findSome? fun w =>
          if vΓ.all (fun v => v.getD w false) && !(vC.getD w false) then
            if h : FinCM.checkB M w Γ C = true then some ⟨M, w, h⟩ else none
          else none

/-! ## 6. The certified `emit` stage

`CounterEmit.emit` proposes a countermodel from the subformula closure (it is
complete over that closure, but exponential).  Run on the normalised forms
and re-gated on the original sequent. -/

/-- Run the closure-based emitter on `Γ'`, `C'`; gate any proposal through the
verified checker on the original `Γ`, `C`, returning a certified witness. -/
def emitCert (Γ' : List PLLFormula) (C' : PLLFormula)
    (Γ : List PLLFormula) (C : PLLFormula) : Option (Witness Γ C) :=
  match CounterEmit.emit Γ' C' with
  | some (M, w) =>
      if h : FinCM.checkB M w Γ C = true then some ⟨M, w, h⟩ else none
  | none => none

/-! ## 7. The answer type and the decision procedure -/

/-- The result of a search, carrying its certificate.

* `proved t`      — `t : G4cTm Γ C` is a proof term of G4iLL″;
* `refuted M w h`  — `h` proves the verified checker accepts model `M` at
  world `w` as a countermodel to `Γ ⊢ C`;
* `unknown`        — the bounded stages found nothing; asserts nothing. -/
inductive Answer (Γ : List PLLFormula) (C : PLLFormula) where
  | proved  : G4cTm Γ C → Answer Γ C
  | refuted : (M : FinCM) → (w : Nat) → FinCM.checkB M w Γ C = true → Answer Γ C
  | unknown : Answer Γ C

/-- **The staged decision procedure.**  In order:

1. the certified battery sweep (`sweepCert`) — a cheap certified refutation;
2. the fuel-free backward searcher `G4cTm.find` on the **original** sequent —
   the positive engine, returning a kernel-checkable proof term for `Γ ⊢ C`;
3. the closure emitter `emitCert`, gated by `emitClosureCap` — a
   complete-over-the-closure but exponential refuter;
4. `unknown`.

The normaliser feeds only stages 1 and 3 (the untrusted proposers); the
proof term from stage 2 and both refutation certificates are about the
original `Γ`, `C`. -/
def decide (cfg : Config := {}) (Γ : List PLLFormula) (C : PLLFormula) :
    Answer Γ C :=
  let Γ' := Γ.map nf
  let C' := nf C
  match sweepCert cfg Γ' C' Γ C with
  | some ⟨M, w, h⟩ => .refuted M w h
  | none =>
    match G4cTm.find Γ C with
    | some t => .proved t
    | none =>
      if (CounterEmit.closureOf Γ' C').length ≤ cfg.emitClosureCap then
        match emitCert Γ' C' Γ C with
        | some ⟨M, w, h⟩ => .refuted M w h
        | none => .unknown
      else .unknown

/-! ## 8. Soundness — turning certificates into theorems

These are the two lemmas that make the interface trustworthy.  Each consumes
exactly the certificate that the corresponding `Answer` constructor carries,
so a user goes from a verdict to the corresponding (un)derivability theorem in
one application. -/

/-- A `.proved` certificate yields a natural-deduction derivation.  The chain
is `G4cTm.toG4c` (proof term ⇒ G4c derivation) followed by `G4c.equiv_nd`
(G4c = PLL natural deduction). -/
theorem proved_sound {Γ : List PLLFormula} {C : PLLFormula} (t : G4cTm Γ C) :
    Nonempty (LaxND Γ C) :=
  G4c.equiv_nd.mp t.toG4c

/-- A `.refuted` certificate yields underivability, by the certificate theorem
`FinCM.not_provable_of_check` (Kripke soundness of natural deduction). -/
theorem refuted_sound {Γ : List PLLFormula} {C : PLLFormula}
    {M : FinCM} {w : Nat} (h : FinCM.checkB M w Γ C = true) :
    ¬ Nonempty (LaxND Γ C) :=
  FinCM.not_provable_of_check h

/-- A certified verdict: the derivability status of `Γ ⊢ C` together with a
proof of it (or `dontKnow`). -/
inductive Decision (Γ : List PLLFormula) (C : PLLFormula) where
  | derivable   : Nonempty (LaxND Γ C) → Decision Γ C
  | underivable : ¬ Nonempty (LaxND Γ C) → Decision Γ C
  | dontKnow    : Decision Γ C

/-- Discharge an `Answer` into a certified `Decision` in one call. -/
def Answer.toDecision {Γ : List PLLFormula} {C : PLLFormula} :
    Answer Γ C → Decision Γ C
  | .proved t      => .derivable (proved_sound t)
  | .refuted _ _ h => .underivable (refuted_sound h)
  | .unknown       => .dontKnow

/-! ## 9. Convenience wrappers -/

/-- Positive engine only: the fuel-free backward searcher for `Γ ⊢ C`,
returning a proof term.  `none` proves nothing (see the trust note above). -/
def prove? (Γ : List PLLFormula) (C : PLLFormula) : Option (G4cTm Γ C) :=
  G4cTm.find Γ C

/-- Negative engines only (battery then emit, no proof search): a certified
countermodel witness, or `none`. -/
def refute? (cfg : Config := {}) (Γ : List PLLFormula) (C : PLLFormula) :
    Option (Witness Γ C) :=
  let Γ' := Γ.map nf
  let C' := nf C
  (sweepCert cfg Γ' C' Γ C).orElse fun _ =>
    if (CounterEmit.closureOf Γ' C').length ≤ cfg.emitClosureCap then
      emitCert Γ' C' Γ C
    else none

/-! ## 10. Smoke tests and axiom audit

Both verdicts are exercised on tiny sequents, and the two soundness theorems
are audited: their axiom sets are subsets of
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
`Lean.ofReduceBool` (hence no `native_decide`). -/

-- `⊢ p → p` is provable.
#guard (match decide {} [] ((PLLFormula.prop "p").ifThen (.prop "p")) with
          | .proved _ => true | _ => false)

-- `⊢ ◯p → p` is refuted by a finite countermodel from the battery.
#guard (match decide {} [] (((PLLFormula.prop "p").somehow).ifThen (.prop "p")) with
          | .refuted _ _ _ => true | _ => false)

-- `◯p ⊢ p` is refuted (the modality admits no escape).
#guard (match decide {} [(PLLFormula.prop "p").somehow] (PLLFormula.prop "p") with
          | .refuted _ _ _ => true | _ => false)

/-- info: 'PLLND.Search.proved_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms proved_sound

/-- info: 'PLLND.Search.refuted_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refuted_sound

end PLLND.Search
