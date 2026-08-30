import FRJ.SoundV
import FRJ.Fallible

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

end WCounter
end FRJ.V
