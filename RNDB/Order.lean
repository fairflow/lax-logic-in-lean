/-
# The order view: strict order and SCOPED covers

`Rel.le`/`Rel.nle` entries are the FACTS.  This module is the first
slice of the VIEW layer over them: the strict order as a `Prop`, and
cover-ness — which, the fragment being proved infinite, exists ONLY
relative to a named representative set (Matthew, 2026-08-24: "we don't
have a reliable way of determining covers anywhere"; the standing rule
is store `<`, expose covers as a scoped view).

Notation (Matthew, 2026-08-24): the strict order is plain `<`/`>`
(scoped instance); `≺/≻` is NOT used — many order-theory texts reserve
it for covering, so it invites exactly the confusion it caused.  The
covering relation is `⋖` ("is covered by") / `⋗` ("covers"), and it
appears ONLY in scoped form `a ⋖[S] b` — no element of `S` strictly
between — until emptiness of an open interval `(a, b)` is proved for
the WHOLE fragment, which the bare `Covers`/`⋖` below states and
nothing yet inhabits.

The worked example ρ6/ρ12 shows the machinery AND its coupling to the
frontier: deciding one candidate Hasse edge reduced, via the banked
entries, to two OPEN cells — which become frontier members below, not
assumptions.
-/
import RNDB.RhoEntries

open PLLND PLLND.SemUI PLLFormula

namespace RNDB

/-- Strict order: derivable one way, refuted the other. -/
def Lt (a b : PLLFormula) : Prop := Deriv [a] b ∧ ¬ Deriv [b] a

/-- `a < b` on formulas is the derivability order, scoped to `RNDB`. -/
scoped instance : LT PLLFormula := ⟨Lt⟩

/-- Cover RELATIVE TO a named set: `a < b` and no element of `S` sits
strictly between. -/
def CoversIn (S : List PLLFormula) (a b : PLLFormula) : Prop :=
  Lt a b ∧ ∀ c ∈ S, ¬ (Lt a c ∧ Lt c b)

@[inherit_doc CoversIn] notation:50 a:51 " ⋖[" S "] " b:51 => CoversIn S a b
/-- `a ⋗[S] b` = `b ⋖[S] a` ("covers", within `S`). -/
notation:50 a:51 " ⋗[" S "] " b:51 => CoversIn S b a

/-- The ABSOLUTE cover — the open interval `(a, b)` empty over ALL
formulas.  Stated so the target of a generalisation is on record;
nothing inhabits it yet, and any scoped `⋖[S]` result is strictly
weaker.  (Quantifying over all of `PLLFormula` makes this the cover in
the full PLL derivability order; a variable-carrying interposer can
defeat it even where every closed one fails.) -/
def Covers (a b : PLLFormula) : Prop :=
  Lt a b ∧ ∀ c, ¬ (Lt a c ∧ Lt c b)

@[inherit_doc Covers] infix:50 " ⋖ " => Covers
/-- `a ⋗ b` = `b ⋖ a` ("covers", absolutely). -/
infix:50 " ⋗ " => fun a b => Covers b a

/-! ## The worked example: ρ6 < ρ12, and what its cover question needs

ρ6 = `¬◯⊥ ∨ ¬¬◯⊥`, ρ9 = `◯¬◯⊥ ∨ ¬¬◯⊥`, ρ12 = `(¬¬◯⊥ ⊃ ◯⊥) ⊃ ◯¬◯⊥`. -/

open RhoOrder RNReps

/-- `[ρ6] ⊢ ρ12`, hand-authored (`rncCertPos` style): case split on the
disjunction; the `¬◯⊥` branch closes by ◯-intro, the `¬¬◯⊥` branch
fires the hypothesis to get `◯⊥` and escapes through `laxElim`. -/
def nd_6_12 : LaxND [q7] q14 :=
  .impIntro <|
    .orElim (.iden (show q7 ∈ [q10, q7] by decide))
      (.laxIntro (.iden (show q3 ∈ q3 :: [q10, q7] by decide)))
      (.laxElim
        (.impElim (.iden (show q10 ∈ q6 :: [q10, q7] by decide))
          (.iden (show q6 ∈ q6 :: [q10, q7] by decide)))
        (.falsoElim (.somehow q3)
          (.iden (show falsePLL ∈ q0 :: q6 :: [q10, q7] by decide))))

/-- `[ρ6] ⊢ ρ9`: inject each disjunct (`¬◯⊥ ⊢ ◯¬◯⊥` is ◯-intro). -/
def nd_6_9 : LaxND [q7] q9 :=
  .orElim (.iden (show q7 ∈ [q7] by decide))
    (.orIntro1 (.laxIntro (.iden (show q3 ∈ q3 :: [q7] by decide))))
    (.orIntro2 (.iden (show q6 ∈ q6 :: [q7] by decide)))

/-- **ρ6 < ρ12** — Matthew's example, both halves kernel-checked: the
hand derivation above, and the banked 4-world countermodel entry
`nle_12_6` ("rho-0094") for strictness. -/
theorem rho6_lt_rho12 : rhoF 6 < rhoF 12 :=
  ⟨⟨nd_6_12⟩, nle_12_6.holds⟩

@[deprecated rho6_lt_rho12 (since := "2026-08-24")]
theorem rho12_gt_rho6 : rhoF 12 > rhoF 6 := rho6_lt_rho12

/-- ρ6 < ρ9, strict: the derivation above plus the banked `nle_9_6`
(one of the 48 cells the ground truth left unknown and FRJ(◯) settled). -/
theorem rho6_lt_rho9 : rhoF 6 < rhoF 9 :=
  ⟨⟨nd_6_9⟩, nle_9_6.holds⟩

/-- `[q9] ⊢ q14` (= ρ9 ⊢ ρ12): case split on `q9 = q5∨q6`; the `q6`
branch turns `q10 q6 = ◯⊥` into `◯q3` by ex falso under `◯`.
Restated from `wip/rncCertPos.lean`'s `PLLND.RNC.nd_9_14` so this
module closes wip-free; the wip original remains the discovery record. -/
def nd_9_14 : LaxND [q9] q14 :=
  .impIntro <|
    .orElim (.iden (show q9 ∈ [q10, q9] by decide))
      (.iden (show q5 ∈ q5 :: [q10, q9] by decide))
      (.laxElim
        (.impElim (.iden (show q10 ∈ q6 :: [q10, q9] by decide))
          (.iden (show q6 ∈ q6 :: [q10, q9] by decide)))
        (.laxIntro (.falsoElim q3
          (.iden (show falsePLL ∈ q0 :: q6 :: [q10, q9] by decide)))))

/-- ρ9 ≤ ρ12 (`wip/rncCertPos.lean`'s hand derivation `nd_9_14`;
ρ9 = q9, ρ12 = q14). -/
theorem rho9_le_rho12 : Deriv [rhoF 9] (rhoF 12) :=
  ⟨nd_9_14⟩

/-- **The cover question, reduced to one open cell.**  If `ρ12 ⊬ ρ9`
— currently OPEN (G4c unknown, FRJ(◯) found nothing) — then ρ9 sits
strictly between, and ρ12 does NOT cover ρ6 in the catalogue.  The
hypothesis is a `frontierOrder` member below, never an assumption
smuggled in. -/
theorem not_coversIn_of_open (h : ¬ Deriv [rhoF 12] (rhoF 9)) :
    ¬ rhoF 6 ⋖[rhoScope] rhoF 12 := fun hc =>
  hc.2 (rhoF 9) (by decide)
    ⟨rho6_lt_rho9, ⟨rho9_le_rho12, h⟩⟩

/-- The open cells the ρ6/ρ12 cover question NEEDS, recorded as frontier
data (asserting nothing): `ρ12 ⊬ ρ9?` decides interposition of ρ9;
`ρ13 ⊬ ρ6?` likewise for ρ13 (whose other three sides are settled). -/
def frontierOrder : Frontier :=
  [ ⟨rhoF 12, rhoF 9, Rel.nle, some rhoScope⟩,
    ⟨rhoF 13, rhoF 6, Rel.nle, some rhoScope⟩ ]

/-! ## Pins — UNGUARDED as emitted; guard via tools/pin-backfill.py -/

/-- info: 'RNDB.rho6_lt_rho12' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rho6_lt_rho12

/-- info: 'RNDB.rho6_lt_rho9' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rho6_lt_rho9

/-- info: 'RNDB.not_coversIn_of_open' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_coversIn_of_open

end RNDB
