/-
# `LaxLogic.QLL.ModalRelation` — why the modal relation is a parameter

A side note to the model theory.  In a model whose modal relation is its
intuitionistic order, `◯` is the double-negation modality (with no fallible
worlds it is forced exactly where `¬¬` is), and such models validate formulas
QLL does not prove.  One such formula:

    (◯A ⊃ ◯B) ⊃ ◯(A ⊃ B)

`circ_imp_of_rm_eq_ri` shows it is forced everywhere once `RE = Ri`;
`not_prv_circ_imp` shows QLL does not prove it.  So a class of models with
`Rm = Ri` is not complete for QLL, and constructions over Herbrand frames keep
their modal relation as a parameter (`HFrame.m`).
-/
import LaxLogic.QLL.Prov

namespace LaxLogic.QLL

/-- With `RE = Ri`, `(◯A ⊃ ◯B) ⊃ ◯(A ⊃ B)` is forced at every world. -/
theorem circ_imp_of_rm_eq_ri (M : KModel) (hRE : ∀ s v, M.RE s v ↔ M.Ri s v)
    (A B : Form) (s : M.S) (ρ : String → M.D) (β : List M.D) :
    M.force (.imp (.imp (.circ .ex A) (.circ .ex B)) (.circ .ex (.imp A B))) s ρ β := by
  intro w _ H v hwv
  rcases Classical.em (∃ u, M.Ri v u ∧ ∀ u', M.Ri u u' → ¬ M.force A u' ρ β) with hdead | hdead
  · obtain ⟨u, hvu, hu⟩ := hdead
    exact ⟨u, (hRE v u).2 hvu, fun u' huu' hA => absurd hA (hu u' huu')⟩
  · have hcA : M.force (.circ .ex A) v ρ β := fun v' hvv' =>
      Classical.byContradiction fun hno =>
        hdead ⟨v', hvv', fun u' hv'u' hA => hno ⟨u', (hRE v' u').2 hv'u', hA⟩⟩
    obtain ⟨u, hvu, hBu⟩ := H v hwv hcA v (M.refl_i v)
    exact ⟨u, hvu, fun u' huu' _ => M.hered B ρ β huu' hBu⟩

/-- Three worlds `r < s < f`. -/
inductive W3 | r | s | f
  deriving DecidableEq

/-- The order `r < s < f`. -/
def W3.le : W3 → W3 → Bool
  | .r, _   => true
  | .s, .s  => true
  | .s, .f  => true
  | .f, .f  => true
  | _,  _   => false

/-- The modal relation: the identity, and `s → f`. -/
def W3.m : W3 → W3 → Bool
  | .r, .r  => true
  | .s, .s  => true
  | .s, .f  => true
  | .f, .f  => true
  | _,  _   => false

/-- `f` is fallible, `P` holds at `s`, and `Q` at no sound world. -/
def m3 : KModel where
  S := W3
  D := Unit
  Dom _ _ := True
  Ri a b := W3.le a b = true
  RA a b := W3.le a b = true
  RE a b := W3.m a b = true
  Fl w := w = .f
  refl_i a := by cases a <;> rfl
  trans_i := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  refl_A a := by cases a <;> rfl
  trans_A := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  sub_A h := h
  refl_E a := by cases a <;> rfl
  trans_E := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  sub_E := by intro a b; cases a <;> cases b <;> decide
  dom_mono _ _ := trivial
  d₀ := ()
  dom_d₀ _ := trivial
  hered_Fl := by intro a b; cases a <;> cases b <;> decide
  fn _ _ := ()
  I w p _ := match w with
    | .r => False
    | .s => p = "P"
    | .f => True
  hered_I := by
    intro a b p _ h hI
    cases a <;> cases b <;> first | exact hI | exact (Bool.noConfusion h) | exact trivial | exact hI.elim
  fn_dom _ := trivial

/-- QLL does not prove `(◯P ⊃ ◯Q) ⊃ ◯(P ⊃ Q)`. -/
theorem not_prv_circ_imp :
    ¬ Prv [] (.imp (.imp (.circ .ex (.pred "P" [])) (.circ .ex (.pred "Q" [])))
      (.circ .ex (.imp (.pred "P" []) (.pred "Q" [])))) := by
  intro h
  have hs := Prv.sound h m3 W3.r (fun _ => ()) (fun _ _ => trivial) (fun _ hB => nomatch hB)
  have hpre : m3.force (.imp (.circ .ex (.pred "P" [])) (.circ .ex (.pred "Q" [])))
      W3.r (fun _ => ()) [] := by
    intro v _ hP
    cases v with
    | r =>
        obtain ⟨u, hu, hPu⟩ := hP W3.r rfl
        cases u with
        | r =>
            rcases hPu with h' | h'
            · exact (W3.noConfusion h' : False).elim
            · exact (h' : False).elim
        | s => exact (Bool.noConfusion hu : False).elim
        | f => exact (Bool.noConfusion hu : False).elim
    | s =>
        intro v' hv'
        cases v' with
        | r => exact (Bool.noConfusion hv' : False).elim
        | s => exact ⟨W3.f, rfl, Or.inl rfl⟩
        | f => exact ⟨W3.f, rfl, Or.inl rfl⟩
    | f =>
        intro v' hv'
        cases v' with
        | f => exact ⟨W3.f, rfl, Or.inl rfl⟩
        | _ => exact (Bool.noConfusion hv' : False).elim
  obtain ⟨u, hu, hPQ⟩ := hs W3.r rfl hpre W3.r rfl
  cases u with
  | r =>
      rcases hPQ W3.s rfl (Or.inr rfl) with h' | h'
      · exact (W3.noConfusion h' : False).elim
      · have h'' : ("Q" : String) = "P" := h'
        exact absurd h'' (by decide)
  | s => exact (Bool.noConfusion hu : False).elim
  | f => exact (Bool.noConfusion hu : False).elim

/-- info: 'LaxLogic.QLL.not_prv_circ_imp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms not_prv_circ_imp

end LaxLogic.QLL
