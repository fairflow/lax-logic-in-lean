import FRJ.SoundV
import FRJ.Fallible
import wip.gbu_search

/-!
# Tag-preserving weakening for `FRJV`, REFUTED

The database of Gbu(G) answers a query with a SUBSUMING row, so the
question for divergence D8 is whether cleanliness of a tag survives
enlarging the context.  It does not, and the witness is the sharp one:
`◯p ⊃ p`.
-/
namespace FRJ.V
open FRJ

/-- **Tag-preserving weakening FAILS.**  A derivation whose context closes
`◯C` — the goal under the modality — can never carry a liftable tag.
The root forces `◯C`, so SOME `Rm`-successor forces `C`; `tag_cone` says
every PROPER successor refutes `C`; so that successor is the root, and the
root forces `C`, contradicting `lemma39R`. -/
theorem not_clean_of_clo_circ {G : Form} {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJVr G t Γ C) (hcirc : Clo Γ (.circ C))
    (htag : t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W C) : False := by
  obtain ⟨hlbl, hnC⟩ := lemma39R d
  have hroot : (modR d).force (modR d).root (.circ C) :=
    clo_forces (fun X hX => hlbl _ X ((preR_root_lbl d).symm.subset hX)) hcirc
  obtain ⟨c, hRm, hcC⟩ := (Kripke.force_circ (K := modR d) _ C).mp hroot _ ((modR d).le_refl _)
  by_cases hc : c = (modR d).root
  · exact hnC (hc ▸ hcC)
  · exact tag_cone d C htag c hRm hc hcC


/-- info: 'FRJ.V.not_clean_of_clo_circ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_clean_of_clo_circ

namespace WCounter
open FRJ FRJ.V

/-- `G = ◯p ⊃ p`. -/
def Gw : Form := .imp (.circ (.atom "p")) (.atom "p")


/-- The fallible `⋈^At_F` row: goal `p`, whole modal zone kept, so the
context closes `◯p`.  Mirrors `FRJ.provable_circ_imp`. -/
theorem dirty_exists :
    ∃ (Γ' : List Form) (t : Tag), Nonempty (FRJVr Gw t Γ' (.atom "p")) ∧
      Clo Γ' (.circ (.atom "p")) ∧ (rm (gAt Gw) (Form.atom "p")) ⊆ Γ' := by
  refine ⟨_, _, ⟨FRJVr.joinAtF (G := Gw) (n := 0)
    (stab := fun _ => []) (rhs := fun _ => .atom "p") (F := .atom "p")
    (fun _ => .axI (.atom "p") rfl (by decide) (CtxEq.refl _))
    (by intro i j h; exact absurd ((Fin.fin_one_eq_zero i).trans (Fin.fin_one_eq_zero j).symm) h)
    (by intro A B h; simp [unionAll, impPart] at h)
    rfl (by simp [unionAll, atPart]) (by decide) (CtxEq.refl _)⟩, ?_, ?_⟩
  · exact .base (by decide)
  · decide

/-- The clean row at the SMALLER context: `Ax^R`, tag `barren`. -/
def clean : FRJVr Gw .barren (rm (gAt Gw) (.atom "p")) (.atom "p") :=
  .axR (.atom "p") rfl (by decide) (CtxEq.refl _)

/-- **Tag-preserving weakening is REFUTED**, at `G = ◯p ⊃ p`.

    []  ⇒ p   has a BARREN derivation          (`clean`)
    []  ⊆ [◯p]
    [◯p] ⇒ p   is derivable                     (`⋈^At_F`, tag `blocked`)
    [◯p] ⇒ p   has NO clean derivation          (`not_clean_of_clo_circ`)

So a subsuming row can be untaggable even when the row it subsumes is
clean, and (DB2) cannot be asked to preserve cleanliness in place. -/
theorem tag_weakening_refuted :
    ∃ (Γ Γ' : List Form) (C : Form),
      Nonempty (FRJVr Gw .barren Γ C) ∧
      Γ ⊆ Γ' ∧
      (∃ t, Nonempty (FRJVr Gw t Γ' C)) ∧
      (∀ (t : Tag), FRJVr Gw t Γ' C →
        ¬ (t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ' W C)) := by
  obtain ⟨Γ', t, hd, hclo, hsub⟩ := dirty_exists
  exact ⟨_, Γ', _, ⟨clean⟩, hsub, ⟨t, hd⟩,
    fun _ d htag => not_clean_of_clo_circ d hclo htag⟩

/-- info: 'FRJ.V.WCounter.tag_weakening_refuted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tag_weakening_refuted

/-! ## (★★) is FALSE

(★★) said: over a critical `◯`-free context with all antecedents dead,
every refutation can be taken CLEAN.  The induction that would prove it
breaks at the `⊃` case — `⊃∈` hands the sub-derivation the context
`A :: Ω`, which leaves the hypotheses — and that is exactly where the
counterexample lives.

    Ω = ∅   (critical, `◯`-free, no implications at all),   Z = ◯p ⊃ p

`∅ ⇒ ◯p ⊃ p` is refutable (`⋈^At_F` then `⊃∈`) but has NO clean
derivation: `⊃∈` propagates its premise's tag, and the premise's context
closes `◯p`, which `not_clean_of_clo_circ` makes dirty.  The `chain`
escape — pledging the GOAL itself — is closed by `tag_cone`: the modal
successor that `◯p` supplies forces `p`, hence forces `◯p ⊃ p`, so it
cannot be a proper cone member of a `chain (◯p ⊃ p)` root. -/

theorem not_refutedCleanly_imp_self :
    ¬ FRJ.Gbu.RefutedCleanly Gw [] (Form.imp (.circ (.atom "p")) (.atom "p")) := by
  rintro ⟨Γ, t, ⟨d⟩, htag, -⟩
  cases d with
  | axR F hF hg hΓ => exact Bool.noConfusion hF
  | joinAt _ _ _ _ _ hF _ _ _ => exact Bool.noConfusion hF
  | joinAtP _ _ _ _ _ _ _ hF _ _ _ => exact Bool.noConfusion hF
  | joinAtF _ _ _ hF _ _ _ => exact Bool.noConfusion hF
  | impIn d' hA hg =>
      rcases htag with hb | ⟨W, hch, hcov⟩
      · exact not_clean_of_clo_circ d' hA (Or.inl hb)
      · cases hcov with
        | imp hc _ => exact not_clean_of_clo_circ d' hA (Or.inr ⟨W, hch, hc⟩)
        | refl =>
            obtain ⟨hlbl, hnC⟩ := lemma39R d'
            have hroot : (modR d').force (modR d').root (.circ (.atom "p")) :=
              clo_forces (fun X hX => hlbl _ X ((preR_root_lbl d').symm.subset hX)) hA
            obtain ⟨c, hRm, hcp⟩ :=
              (Kripke.force_circ (K := modR d') _ (Form.atom "p")).mp hroot _ ((modR d').le_refl _)
            by_cases hc : c = (modR d').root
            · exact hnC (hc ▸ hcp)
            · exact tag_cone (FRJVr.impIn d' hA hg) _ (Or.inr ⟨_, hch, .refl⟩) c hRm hc
                (fun b hb _ => (modR d').force_mono hb hcp)

/-- The other half: `∅ ⇒ ◯p ⊃ p` IS refutable — `⋈^At_F` then `⊃∈`. -/
theorem evalR_imp_self :
    FRJ.Gbu.EvalR (FRJ.Gbu.FDerivable Gw) [] (Form.imp (.circ (.atom "p")) (.atom "p")) := by
  obtain ⟨Γ', t, ⟨d⟩, hclo, -⟩ := dirty_exists
  exact ⟨Γ', ⟨t, ⟨.impIn d hclo (by decide)⟩⟩, fun X hX => absurd hX List.not_mem_nil⟩

/-- **(★★) is REFUTED.**  Its hypotheses hold at `Ω = ∅`, `Z = ◯p ⊃ p`
— the context is critical, `◯`-free and has no implications at all, so
the `Υ` condition is vacuous — and `∅ ⇒ Z` is refutable but not cleanly
so.  The `⊃` case is exactly where the induction that would prove (★★)
leaves its own hypotheses. -/
theorem not_starstar :
    ¬ (∀ (G : Form) (D : FRJ.Gbu.FSeq → Prop), FRJ.Gbu.Saturated G D →
        ∀ (Ω : List Form) (Z : Form),
          (∀ X ∈ Ω, X ∈ gAt G ++ gImp G) →
          (∀ A B, Form.imp A B ∈ Ω → FRJ.Gbu.EvalI D Ω A) →
          Z ∈ sfR G → FRJ.Gbu.EvalR D Ω Z → FRJ.Gbu.EvalRC D Ω Z) := by
  intro h
  refine not_refutedCleanly_imp_self
    ((FRJ.Gbu.evalRC_iff_refutedCleanly (FRJ.Gbu.saturated_fderivable Gw)).mp
      (h Gw (FRJ.Gbu.FDerivable Gw) (FRJ.Gbu.saturated_fderivable Gw) []
        (Form.imp (.circ (.atom "p")) (.atom "p"))
        (fun X hX => absurd hX List.not_mem_nil)
        (fun A B hAB => absurd hAB List.not_mem_nil)
        (by decide) evalR_imp_self))

/-- info: 'FRJ.V.WCounter.not_starstar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_starstar

/-- info: 'FRJ.V.WCounter.not_refutedCleanly_imp_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_refutedCleanly_imp_self

/-! ## Why the six sweep misses happen: `◯(◯Z ⊃ Z)` is IRREGULARLY irrefutable

The completed ρ-sweep misses six banked `⊬` cells, five of them targeting

    ρ18 = ((◯¬◯⊥ ∨ ¬¬◯⊥) ⊃ (◯⊥ ∨ ¬◯⊥)) ∨ (◯¬◯⊥ ∨ ¬¬◯⊥)

whose right disjunct is `q9 = q5 ∨ q6` with `q5 = ◯¬◯⊥ = ◯(◯⊥ ⊃ ⊥)`.
That is `◯(◯Z ⊃ Z)` at `Z := ⊥` — and the two theorems below say FRJV
can never refute that shape IRREGULARLY, for any `Z`.

Since all three `⋈^∨` variants take IRREGULAR premises, a disjunction
with such a formula as a disjunct cannot be joined, and neither can any
disjunction built over it.  That is the mechanism. -/

/-- **`◯Z ⊃ Z` has no CLEANLY tagged regular refutation**, for any `Z`.
`⊃∈` propagates its premise's tag, and the premise's context closes
`◯Z`; the `chain` escape — pledging the goal itself — is closed by
`tag_cone`, because the successor `◯Z` supplies forces `Z` and hence
forces `◯Z ⊃ Z`. -/
theorem not_clean_imp_self {G : Form} {t : Tag} {Γ : List Form} {Z : Form}
    (d : FRJVr G t Γ (.imp (.circ Z) Z))
    (htag : t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W (.imp (.circ Z) Z)) :
    False := by
  cases d with
  | axR F hF hg hΓ => exact Bool.noConfusion hF
  | joinAt _ _ _ _ _ hF _ _ _ => exact Bool.noConfusion hF
  | joinAtP _ _ _ _ _ _ _ hF _ _ _ => exact Bool.noConfusion hF
  | joinAtF _ _ _ hF _ _ _ => exact Bool.noConfusion hF
  | impIn d' hA hg =>
      rcases htag with hb | ⟨W, hch, hcov⟩
      · exact not_clean_of_clo_circ d' hA (Or.inl hb)
      · cases hcov with
        | imp hc _ => exact not_clean_of_clo_circ d' hA (Or.inr ⟨W, hch, hc⟩)
        | refl =>
            obtain ⟨hlbl, hnC⟩ := lemma39R d'
            have hroot : (modR d').force (modR d').root (.circ Z) :=
              clo_forces (fun X hX => hlbl _ X ((preR_root_lbl d').symm.subset hX)) hA
            obtain ⟨c, hRm, hcp⟩ :=
              (Kripke.force_circ (K := modR d') _ Z).mp hroot _ ((modR d').le_refl _)
            by_cases hc : c = (modR d').root
            · exact hnC (hc ▸ hcp)
            · exact tag_cone (FRJVr.impIn d' hA hg) _ (Or.inr ⟨_, hch, .refl⟩) c hRm hc
                (fun b hb _ => (modR d').force_mono hb hcp)

/-- **`◯(◯Z ⊃ Z)` has NO irregular refutation at all**, for any `Z`.
Only `◯∉` and `Ax^I◯` conclude a `◯` goal.  `◯∉` needs a clean regular
refutation of `◯Z ⊃ Z`, which `not_clean_imp_self` forbids; and
`Ax^I◯` needs `classForce ats (◯Z ⊃ Z) = false`, which is impossible —
`◯` is transparent to `classForce`, so the body evaluates to the
classical tautology `¬x ∨ x`. -/
theorem no_irregular_circ_imp_self {G : Form} {Z : Form} {St Th : List Form}
    (d : FRJVi G St Th (.circ (.imp (.circ Z) Z))) : False := by
  cases d with
  | axI F hF hg hTh => exact Bool.noConfusion hF
  | circNotIn dr htag hTh hg => exact not_clean_imp_self dr htag
  | axIC F ats hats hFf hg hTh =>
      have htaut : classForce ats (Form.imp (.circ Z) Z) = true := by
        show (!classForce ats Z || classForce ats Z) = true
        cases classForce ats Z <;> rfl
      rw [htaut] at hFf
      exact Bool.noConfusion hFf

/-- info: 'FRJ.V.WCounter.not_clean_imp_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_clean_imp_self

/-- info: 'FRJ.V.WCounter.no_irregular_circ_imp_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms no_irregular_circ_imp_self

end WCounter
end FRJ.V
