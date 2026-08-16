/-
# FRJ◯ — statement screen: `ExtractForces` (W3b) is REFUTED for worldOK v3

The completeness direction (`FRJO/Recon.lean`) is proved.  This file
screens the SOUNDNESS direction before any of it is scoped, per the
repo's testing mandate, and the screen fails: **`ExtractForces G b` is
false**, at three separate cells, each certified here.

The defect is structural, not a budget artefact (that was v2's).  v3's
`worldOK` asks of the stable zone `S` only that its members lie in the
universe; it asks NOTHING about closure.  So a `world` node may carry a
zone that no world can force:

* `S = [⊥]`            — the extracted root is infallible by construction;
* `S = [p ∧ q]`        — the root forces `p ∧ q` only if it forces `p`;
* `S = [p, p ⊃ q]`     — the root forces `p ⊃ q` only if it forces `q`.

Each of the three is a legal `world` node whose sequent is PLL-DERIVABLE,
so it contradicts `not_laxND_of_FRJD`, which is exactly `ExtractForces`'s
consequence.  Hence `ExtractForces` is refuted, and with it the
biconditional `frjd_iff_not_laxND` stays OPEN until `worldOK` changes.

**The repair the screen names (v4).**  Add to `worldOK`, as further
decidable conjuncts on `S` (all of them free on the reconstruction side,
where the zone is a world's restricted theory):

1. `⊥ ∉ S`;
2. for `A ∧ B ∈ sfPlus G`:  `A ∧ B ∈ S ↔ (A ∈ S ∧ B ∈ S)`;
3. for `A ∨ B ∈ sfPlus G`:  `A ∨ B ∈ S ↔ (A ∈ S ∨ B ∈ S)`;
4. for `A ⊃ B ∈ S`:         `A ∈ S → B ∈ S`;
5. SATURATION, for `A ⊃ B ∈ sfPlus G \ S`: a witness — either
   `A ∈ S ∧ B ∉ S`, or a kid `K` with `A ∈ K.stable`, `B ∉ K.stable`;
6. SATURATION, for `◯A ∈ sfPlus G \ S`: either the cone misses `A`
   (`¬leaf`, `A ∉ S`, no cone kid carries `A`) or some kid omits `◯A`.

1–4 are what makes the root force `S`; 5–6 are what makes the zone a
COMPLETE description of the root, which is what the `⊃`/`◯` clauses of
the forcing induction consume.  With them the goal conjunct collapses to
the uniform `C ∉ S`, and `impOut`/`circOut` become derived rules — the
second defect this screen records is that those two constructors build a
fresh root with no valuation and no cone at all (`FRJO/Extract.lean`),
so they cannot carry a zone with atoms or boxes either.
-/
import FRJO.Extract

namespace FRJO

open PLLND PLLFormula

/-- A `world` node with NO kids, no cone and no leaf: under v3 this is
legal for any zone inside the universe whose goal is a shape-fitting
non-member. -/
def bareWorld (G : Cell) (b : Nat) (S : List PLLFormula) (C : PLLFormula)
    (ok : worldOK G b S C [] [] false = true) : FRJD G b ⟨S, C⟩ :=
  .world [] [] false (fun _ hK => absurd hK List.not_mem_nil) ok

/-! ## (1) A fallible zone -/

def cellBot : Cell := ⟨[.falsePLL], .prop "p"⟩

theorem okBot (b : Nat) :
    worldOK cellBot b [PLLFormula.falsePLL] (.prop "p") [] [] false = true := by
  unfold worldOK; decide

def proofBot : LaxND [PLLFormula.falsePLL] (.prop "p") :=
  .falsoElim _ (.iden (by simp))

theorem not_extractForces_bot (b : Nat) : ¬ ExtractForces cellBot b :=
  fun hE => not_laxND_of_FRJD hE (bareWorld cellBot b _ _ (okBot b)) ⟨proofBot⟩

/-! ## (2) A zone not closed under ∧-elimination -/

def cellAnd : Cell := ⟨[.and (.prop "p") (.prop "q")], .prop "p"⟩

theorem okAnd (b : Nat) :
    worldOK cellAnd b [PLLFormula.and (.prop "p") (.prop "q")] (.prop "p")
      [] [] false = true := by
  unfold worldOK; decide

def proofAnd : LaxND [PLLFormula.and (.prop "p") (.prop "q")] (.prop "p") :=
  .andElim1 (ψ := .prop "q") (.iden (by simp))

theorem not_extractForces_and (b : Nat) : ¬ ExtractForces cellAnd b :=
  fun hE => not_laxND_of_FRJD hE (bareWorld cellAnd b _ _ (okAnd b)) ⟨proofAnd⟩

/-! ## (3) A zone not closed under modus ponens -/

def cellMP : Cell :=
  ⟨[.prop "p", .ifThen (.prop "p") (.prop "q")], .prop "q"⟩

theorem okMP (b : Nat) :
    worldOK cellMP b [PLLFormula.prop "p", .ifThen (.prop "p") (.prop "q")]
      (.prop "q") [] [] false = true := by
  unfold worldOK; decide

def proofMP :
    LaxND [PLLFormula.prop "p", .ifThen (.prop "p") (.prop "q")] (.prop "q") :=
  .impElim (φ := .prop "p") (.iden (by simp)) (.iden (by simp))

theorem not_extractForces_mp (b : Nat) : ¬ ExtractForces cellMP b :=
  fun hE => not_laxND_of_FRJD hE (bareWorld cellMP b _ _ (okMP b)) ⟨proofMP⟩

/-! ## Pins

`Classical.choice` here is not the refutation's: it rides in through
`extract`'s `while` loops (a `partial` definition), which appear in
`ExtractForces`'s own statement. -/

/--
info: 'FRJO.not_extractForces_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms not_extractForces_bot

/--
info: 'FRJO.not_extractForces_and' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms not_extractForces_and

/--
info: 'FRJO.not_extractForces_mp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms not_extractForces_mp

end FRJO
