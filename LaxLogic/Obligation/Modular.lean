/-
# Modular lax reasoning: borrowing a constraint instead of proving it

`LatchSynth` and `Adder` each synthesise the constraints of **one** circuit. This
module is about the step after: building a *second* proof on top of the first
while its constraint is still outstanding, so that the composite's constraint is
computed rather than restated.

The loop, in the order it actually runs:

1. **State the concrete aim.** `◯∀[from_ Tout] Q` — the output is available by
   the deadline.
2. **Abstract out the constraints.** Each component contributes a
   constraint/formula pair; nothing about times enters the functional
   specifications (`CellSpec`, `UnitSpec`).
3. **Reason freely at the abstract level**, using earlier *holed* theorems as
   ordinary lemmas. This is what `lax_apply` provides: it applies a
   `postponing theorem` and re-postpones that theorem's obligations into the
   current ledger, so the borrowed debt travels with the proof.
4. **Refine the component specs back in.** `carry_cell` and `buffer` are the
   two refinement rules; the offset between what a stage delivers and what the
   next stage demands is the new constraint, and `postpone` records it.
5. **Calculate the offsets.** `reduce_obligation` turns each recorded
   constraint into readable arithmetic, exactly the paper's (8) → (9).
6. **Fold them back in.** The finished statement is
   `C₁ ⊃ ⋯ ⊃ Cₙ ⊃ ◯φ`, which is Mendler's `weak` at the concatenated ledger
   (`pipeline_is_weak`), and curries into a single `Debt` at their conjunction
   (`pipeline_as_debt`) — the `C ⊃ φ` form.
7. **Discharge at a constraint model.** With the delays and the clock fixed,
   `discharge_obligation` closes every constraint by arithmetic, and the
   concrete theorem falls out of the abstract one with no new proof
   (`pipeline_concrete`).

## What the test is

Three stages, each borrowing from the last:

| stage | theorem | owes |
| --- | --- | --- |
| carry-lookahead block | `Adder.bal_meets_cycle` | 1 |
| + sum XOR | `datapath_meets_clock` | 2 (1 borrowed, 1 new) |
| + output buffer | `pipeline_meets_clock` | 3 (2 borrowed, 1 new) |

The borrowed obligations are not re-derived: `borrowed_is_bal` and
`borrowed_is_datapath` hold by `rfl`, so what the ledger records is the earlier
theorem's own obligation constant. Composition of constraints really is
concatenation of ledgers, which is `Mendler.weak_append`.

## The one thing to watch

`lax_apply` makes it possible to write a proof that owes something it should
have proved. That is a feature — it is the point of abstraction — but it means
the ledger, not the build's success, is the measure of what is finished.
`#obligations` and `#obligations_audit` are how a development is read.
-/

import LaxLogic.Obligation.Adder
import LaxLogic.Obligation.Mendler

namespace LaxLogic.Obligation.Modular

open LaxLogic.Obligation LaxLogic.Obligation.Timing LaxLogic.Obligation.Adder

/-! ## A one-input stage

`carry_cell` covers two-input combinational logic. A buffer, an inverter or a
register stage takes one input, and pretending otherwise (`carry_cell h h`)
leaves a `max a a` in every constraint. -/

/-- The specification of a one-input cell of delay `δ`: functional behaviour
only, no times. -/
def UnitSpec (In Out : Refined Nat) (δ : Nat) : Prop :=
  ∀ t, (∃ s, s + δ ≤ t ∧ In s) → Out t

/-- **The one-input refinement rule.** Availability shifts by the delay: the
`image (· + δ)` row of `Timing.lean`'s table, with no `meet`. -/
theorem buffer {In Out : Refined Nat} {a δ : Nat}
    (h : ◯∀[from_ a] In) (hc : UnitSpec In Out δ) :
    ◯∀[from_ (a + δ)] Out := by
  intro t ht
  exact hc t ⟨a, by simpa only [from_] using ht, h a (Nat.le_refl a)⟩

/-! ## Stage 2: the sum bit

The carry-lookahead block of `Adder.lean` delivers the group `(generate,
propagate)` pair; the sum bit is an XOR of that pair with the bit's own
propagate line. `bal_meets_cycle` is used here as an **abstract lemma** — its
cycle-time constraint is borrowed, not proved. -/

/-- **The adder plus its sum stage.** Two obligations: the block's, borrowed
through `lax_apply`, and the XOR's, recorded by `postpone`. Neither is a
hypothesis of the statement as written; both are computed. -/
postponing theorem datapath_meets_clock
    (Gp Pb Sum : Refined Nat) (δ δsum T tp Tclk k : Nat)
    (hm : MergeNet Gp δ) (hleaf : ◯∀[from_ 0] Gp)
    (hpb : ◯∀[from_ tp] Pb) (hxor : CellSpec Gp Pb Sum δsum) :
    ◯∀[from_ Tclk] Sum := by
  -- Stage 1, as an abstract lemma. Its constraint travels with the proof.
  have hgp : ◯∀[from_ T] Gp := by
    lax_apply (bal_meets_cycle Gp δ k T hm hleaf)
  -- Reason at the abstract level: refine the XOR's spec back in.
  have hsum : ◯∀[from_ (max T tp + δsum)] Sum := carry_cell hgp hpb hxor
  -- The offset between what the stage delivers and what the clock demands.
  refine laxAll_mono (fun z (hz : Tclk ≤ z) => ?_) hsum
  postpone

/-- **The borrowed debt is the sub-theorem's own obligation**, verbatim: this
holds by `rfl`. The ledger did not re-derive the block's constraint, it recorded
a reference to it. -/
theorem borrowed_is_bal
    (Gp Pb Sum : Refined Nat) (δ δsum T tp Tclk k : Nat)
    (hm : MergeNet Gp δ) (hleaf : ◯∀[from_ 0] Gp)
    (hpb : ◯∀[from_ tp] Pb) (hxor : CellSpec Gp Pb Sum δsum) :
    datapath_meets_clock.obligation1 Gp Pb Sum δ δsum T tp Tclk k hm hleaf hpb hxor
      = bal_meets_cycle.obligation1 Gp δ k T hm hleaf := rfl

/-! ## Stage 3: the output buffer

And again, one level up: `datapath_meets_clock` is itself holed, and
`lax_apply` borrows **both** of its obligations at once. -/

/-- **The whole pipeline.** Three obligations: two inherited from
`datapath_meets_clock` (one of which it had itself inherited from
`bal_meets_cycle`) and one new. Borrowing is transitive. -/
postponing theorem pipeline_meets_clock
    (Gp Pb Sum Q : Refined Nat) (δ δsum δbuf T tp Tclk Tout k : Nat)
    (hm : MergeNet Gp δ) (hleaf : ◯∀[from_ 0] Gp)
    (hpb : ◯∀[from_ tp] Pb) (hxor : CellSpec Gp Pb Sum δsum)
    (hbuf : UnitSpec Sum Q δbuf) :
    ◯∀[from_ Tout] Q := by
  have hsum : ◯∀[from_ Tclk] Sum := by
    lax_apply (datapath_meets_clock Gp Pb Sum δ δsum T tp Tclk k hm hleaf hpb hxor)
  have hq : ◯∀[from_ (Tclk + δbuf)] Q := buffer hsum hbuf
  refine laxAll_mono (fun z (hz : Tout ≤ z) => ?_) hq
  postpone

/-- Transitivity of borrowing, by `rfl`: the pipeline's first obligation is the
datapath's first, which is the block's. -/
theorem borrowed_is_datapath
    (Gp Pb Sum Q : Refined Nat) (δ δsum δbuf T tp Tclk Tout k : Nat)
    (hm : MergeNet Gp δ) (hleaf : ◯∀[from_ 0] Gp)
    (hpb : ◯∀[from_ tp] Pb) (hxor : CellSpec Gp Pb Sum δsum)
    (hbuf : UnitSpec Sum Q δbuf) :
    pipeline_meets_clock.obligation1 Gp Pb Sum Q δ δsum δbuf T tp Tclk Tout k
        hm hleaf hpb hxor hbuf
      = bal_meets_cycle.obligation1 Gp δ k T hm hleaf := rfl

/-! ## 5. Calculating the offsets

Every one of the seven obligations now outstanding reduces by the *same*
tactic. None of them was written down in advance. -/

section Reduce
variable (Gp Pb Sum Q : Refined Nat) (δ δsum δbuf T tp Tclk Tout k : Nat)
variable (hm : MergeNet Gp δ) (hleaf : ◯∀[from_ 0] Gp)
variable (hpb : ◯∀[from_ tp] Pb) (hxor : CellSpec Gp Pb Sum δsum)
variable (hbuf : UnitSpec Sum Q δbuf)

/-- The datapath's inherited constraint: the lookahead tree must fit before `T`. -/
theorem datapath_obligation1_iff :
    datapath_meets_clock.obligation1 Gp Pb Sum δ δsum T tp Tclk k hm hleaf hpb hxor
      ↔ k * δ ≤ T := by
  reduce_obligation

/-- The datapath's own constraint: the sum XOR must fit after the later of the
group carry and the local propagate. -/
theorem datapath_obligation2_iff :
    datapath_meets_clock.obligation2 Gp Pb Sum δ δsum T tp Tclk k hm hleaf hpb hxor
      ↔ max T tp + δsum ≤ Tclk := by
  reduce_obligation

@[inherit_doc datapath_obligation1_iff]
theorem pipeline_obligation1_iff :
    pipeline_meets_clock.obligation1 Gp Pb Sum Q δ δsum δbuf T tp Tclk Tout k
        hm hleaf hpb hxor hbuf ↔ k * δ ≤ T := by
  reduce_obligation

@[inherit_doc datapath_obligation2_iff]
theorem pipeline_obligation2_iff :
    pipeline_meets_clock.obligation2 Gp Pb Sum Q δ δsum δbuf T tp Tclk Tout k
        hm hleaf hpb hxor hbuf ↔ max T tp + δsum ≤ Tclk := by
  reduce_obligation

/-- The pipeline's own constraint: the output buffer must fit before the
deadline. -/
theorem pipeline_obligation3_iff :
    pipeline_meets_clock.obligation3 Gp Pb Sum Q δ δsum δbuf T tp Tclk Tout k
        hm hleaf hpb hxor hbuf ↔ Tclk + δbuf ≤ Tout := by
  reduce_obligation

/-! ## 6. Folding them back in

Two equivalent presentations of the same finished theorem. The first is
Mendler's: the statement *is* `weak` at the ledger, read as a list. The second
curries the list into one obligation, giving the `C ⊃ φ` form. -/

/-- **The statement is `weak` at the ledger.** `weak [C₁,C₂,C₃] φ` is
`C₁ ⊃ C₂ ⊃ C₃ ⊃ φ` by definition, so this typechecks with the theorem itself as
its proof: the fold-back is not a further construction, it is what
`postponing theorem` already produced. -/
theorem pipeline_is_weak :
    weak [pipeline_meets_clock.obligation1 Gp Pb Sum Q δ δsum δbuf T tp Tclk Tout k
            hm hleaf hpb hxor hbuf,
          pipeline_meets_clock.obligation2 Gp Pb Sum Q δ δsum δbuf T tp Tclk Tout k
            hm hleaf hpb hxor hbuf,
          pipeline_meets_clock.obligation3 Gp Pb Sum Q δ δsum δbuf T tp Tclk Tout k
            hm hleaf hpb hxor hbuf]
      (◯∀[from_ Tout] Q) :=
  pipeline_meets_clock Gp Pb Sum Q δ δsum δbuf T tp Tclk Tout k hm hleaf hpb hxor hbuf

/-- **And the ledger of a modular proof is the concatenation of the ledgers.**
`weak_append` is Mendler's monoid law `(Ω*, [], @)`; here it says the two
obligations borrowed from `datapath_meets_clock` and the one added by
`pipeline_meets_clock` combine by appending, which is precisely what
`lax_apply` does operationally. -/
theorem pipeline_ledger_append (C₁ C₂ C₃ : Prop) :
    weak ([C₁, C₂] ++ [C₃]) (◯∀[from_ Tout] Q)
      = weak [C₁, C₂] (weak [C₃] (◯∀[from_ Tout] Q)) :=
  weak_append [C₁, C₂] [C₃] _

end Reduce

/-- **The `C ⊃ φ` form.** The three constraints curried into one obligation:
the pipeline delivers its output by the deadline *modulo* the conjunction of
the three timing constraints, every one of them derived. -/
theorem pipeline_as_debt
    (Gp Pb Sum Q : Refined Nat) (δ δsum δbuf T tp Tclk Tout k : Nat)
    (hm : MergeNet Gp δ) (hleaf : ◯∀[from_ 0] Gp)
    (hpb : ◯∀[from_ tp] Pb) (hxor : CellSpec Gp Pb Sum δsum)
    (hbuf : UnitSpec Sum Q δbuf) :
    Debt (k * δ ≤ T ∧ max T tp + δsum ≤ Tclk ∧ Tclk + δbuf ≤ Tout)
      (◯∀[from_ Tout] Q) := by
  rintro ⟨h1, h2, h3⟩
  exact pipeline_meets_clock Gp Pb Sum Q δ δsum δbuf T tp Tclk Tout k
    hm hleaf hpb hxor hbuf
    ((pipeline_obligation1_iff Gp Pb Sum Q δ δsum δbuf T tp Tclk Tout k
        hm hleaf hpb hxor hbuf).mpr h1)
    ((pipeline_obligation2_iff Gp Pb Sum Q δ δsum δbuf T tp Tclk Tout k
        hm hleaf hpb hxor hbuf).mpr h2)
    ((pipeline_obligation3_iff Gp Pb Sum Q δ δsum δbuf T tp Tclk Tout k
        hm hleaf hpb hxor hbuf).mpr h3)

/-! ## 7. Discharging at a constraint model

Fix the delays and the deadline and the constraints become decidable
arithmetic. `discharge_obligation` closes all three, so the concrete theorem is
obtained from the abstract one by *evaluation* — no new proof, and nothing
restated.

The model: prefix merge `120 ps` over a depth-5 tree (`Adder`'s 32-bit
lookahead block, ready at `600`), local propagate at `200`, sum XOR `60`,
output buffer `90`, deadline `1 ns`. -/

/-- **The concrete theorem, derived automatically from the abstract one.** No
timing hypothesis survives: `1000 ps` is enough. -/
theorem pipeline_concrete (Gp Pb Sum Q : Refined Nat)
    (hm : MergeNet Gp 120) (hleaf : ◯∀[from_ 0] Gp)
    (hpb : ◯∀[from_ 200] Pb) (hxor : CellSpec Gp Pb Sum 60)
    (hbuf : UnitSpec Sum Q 90) :
    ◯∀[from_ 1000] Q :=
  pipeline_meets_clock Gp Pb Sum Q 120 60 90 600 200 700 1000 5
    hm hleaf hpb hxor hbuf
    (by discharge_obligation) (by discharge_obligation) (by discharge_obligation)

/-- And it bites: at a `750 ps` deadline the buffer's constraint is **false**,
`700 + 90 = 790 > 750`. The model decides the design, in both directions. -/
theorem pipeline_too_tight (Gp Pb Sum Q : Refined Nat)
    (hm : MergeNet Gp 120) (hleaf : ◯∀[from_ 0] Gp)
    (hpb : ◯∀[from_ 200] Pb) (hxor : CellSpec Gp Pb Sum 60)
    (hbuf : UnitSpec Sum Q 90) :
    ¬ pipeline_meets_clock.obligation3 Gp Pb Sum Q 120 60 90 600 200 700 750 5
        hm hleaf hpb hxor hbuf := by
  rw [pipeline_obligation3_iff]
  decide

/-! ## Gates

The strongest of these is the pair of `rfl`s: `borrowed_is_bal` and
`borrowed_is_datapath` depend on **no axioms at all**, so the claim that the
debt propagates verbatim rather than being re-derived is definitional, not a
theorem about the mechanism. -/

/--
info: conservativity audit passed for 4 declaration(s); base-theory axioms only:
  LaxLogic.Obligation.Adder.ripple_meets_cycle — [propext, Quot.sound]
  LaxLogic.Obligation.Adder.bal_meets_cycle — [propext, Quot.sound]
  LaxLogic.Obligation.Modular.datapath_meets_clock — [propext, Quot.sound]
  LaxLogic.Obligation.Modular.pipeline_meets_clock — [propext, Quot.sound]
-/
#guard_msgs in
#obligations_audit

/-- info: 'LaxLogic.Obligation.Modular.borrowed_is_bal' does not depend on any axioms -/
#guard_msgs in
#print axioms borrowed_is_bal

/-- info: 'LaxLogic.Obligation.Modular.borrowed_is_datapath' does not depend on any axioms -/
#guard_msgs in
#print axioms borrowed_is_datapath

/-- info: 'LaxLogic.Obligation.Modular.buffer' does not depend on any axioms -/
#guard_msgs in
#print axioms buffer

/-- info: 'LaxLogic.Obligation.Modular.pipeline_meets_clock' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipeline_meets_clock

/-- info: 'LaxLogic.Obligation.Modular.pipeline_as_debt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipeline_as_debt

/-- info: 'LaxLogic.Obligation.Modular.pipeline_concrete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipeline_concrete

-- `lax_apply` on a theorem that owes nothing is plain `apply`, and says so
-- rather than pretending to have borrowed something.
/--
warning: lax_apply: no obligation was borrowed; this is plain `apply`. Was the lemma built with `postponing theorem`?
-/
#guard_msgs in
example (In Out : Refined Nat) (a δ : Nat)
    (h : ◯∀[from_ a] In) (hc : UnitSpec In Out δ) : ◯∀[from_ (a + δ)] Out := by
  lax_apply (buffer h hc)


end LaxLogic.Obligation.Modular
