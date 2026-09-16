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
import FRJO.Recon

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

/-! ## The repair, checked both ways

The ZONE half of the v4 specification (conjuncts 1–4 of the header) as a
decidable predicate.  Two checks: it REJECTS all three refuting nodes
above, and it is SATISFIED by exactly the zones the reconstruction
builds — a world's restricted theory at an infallible world.  So the
repair is neither too weak (it kills the counterexamples) nor too strong
(it costs the completeness direction nothing).

The SATURATION half (conjuncts 5–6) is not stated here: it constrains
the kid list as well as the zone, so it belongs with a revised `world`
constructor, which is a design decision for the calculus, not a lemma. -/

/-- v4's zone conjuncts: `⊥`-freedom, ∧ and ∨ closure both ways over the
universe, and detachment.  These are what make the extracted root force
the whole zone. -/
def zoneOK4 (G : Cell) (S : List PLLFormula) : Bool :=
  decide (PLLFormula.falsePLL ∉ S) &&
  (sfPlus G).all fun φ => match φ with
    | .and A B => decide ((PLLFormula.and A B ∈ S) ↔ (A ∈ S ∧ B ∈ S))
    | .or A B => decide ((PLLFormula.or A B ∈ S) ↔ (A ∈ S ∨ B ∈ S))
    | .ifThen A B => decide ((PLLFormula.ifThen A B ∈ S) → A ∈ S → B ∈ S)
    | _ => true

/-- **The repair rejects all three refuting nodes.** -/
theorem zoneOK4_rejects :
    zoneOK4 cellBot [PLLFormula.falsePLL] = false ∧
    zoneOK4 cellAnd [PLLFormula.and (.prop "p") (.prop "q")] = false ∧
    zoneOK4 cellMP [PLLFormula.prop "p", .ifThen (.prop "p") (.prop "q")] = false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **The repair costs completeness nothing**: the restricted theory of
any infallible world satisfies it.  Every zone `recon` builds is of that
form (`FRJO/Recon.lean`), so the v4 conjuncts are already discharged on
the reconstruction side. -/
theorem zoneOK4_of_theory {M : ConstraintModel} {w : M.W} {G : Cell}
    {S : List PLLFormula}
    (hS : ∀ φ, φ ∈ S ↔ (φ ∈ sfPlus G ∧ M.force w φ))
    (hinf : ¬ M.force w .falsePLL) : zoneOK4 G S = true := by
  simp only [zoneOK4, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨fun hc => hinf ((hS _).mp hc).2, fun φ hφ => ?_⟩
  match φ, hφ with
  | .prop _, _ | .falsePLL, _ | .somehow _, _ => rfl
  | .and A B, hφ =>
      simp only [decide_eq_true_eq, hS]
      constructor
      · rintro ⟨-, h1, h2⟩
        exact ⟨⟨sfPlus_and_left hφ, h1⟩, ⟨sfPlus_and_right hφ, h2⟩⟩
      · rintro ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
        exact ⟨hφ, h1, h2⟩
  | .or A B, hφ =>
      simp only [decide_eq_true_eq, hS]
      constructor
      · rintro ⟨-, h1 | h2⟩
        · exact Or.inl ⟨sfPlus_or_left hφ, h1⟩
        · exact Or.inr ⟨sfPlus_or_right hφ, h2⟩
      · rintro (⟨-, h1⟩ | ⟨-, h2⟩)
        · exact ⟨hφ, Or.inl h1⟩
        · exact ⟨hφ, Or.inr h2⟩
  | .ifThen A B, hφ =>
      simp only [decide_eq_true_eq, hS]
      rintro ⟨-, himp⟩ ⟨-, hA⟩
      exact ⟨sfPlus_imp_right hφ, himp w (M.refl_i w) hA⟩

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

/-- info: 'FRJO.zoneOK4_rejects' depends on axioms: [propext] -/
#guard_msgs in
#print axioms zoneOK4_rejects

/-- info: 'FRJO.zoneOK4_of_theory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms zoneOK4_of_theory

end FRJO
