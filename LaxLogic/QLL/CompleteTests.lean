/-
# `LaxLogic.QLL.CompleteTests` — the model theory, instantiated

Three things worth pinning.

*Soundness bites.*  A two-state model separates `◯∀` from `◯∃` in both
directions, so neither is derivable from the other.  That is the fact the
whole two-relation design exists to respect: with a single reachability
relation the two modalities would be interderivable, and they are not.

*Completeness bites.*  A semantic fact about `∧` is turned into a derivation
by `completeness`, with no derivation written by hand.

Both use the same model.  It has two states, `false ≤ true`; `P` holds at
`true` only; `◯∀` may look ahead along the order, `◯∃` may not.
-/
import LaxLogic.QLL.Complete

namespace LaxLogic.QLL.CompleteTests

open LaxLogic.QLL

/-- Two states, `false ≤ true`.  `RA` is the whole order, `RE` is equality:
`◯∀` can reach forward, `◯∃` cannot. -/
def two : KModel where
  S := Bool
  D := Unit
  Dom _ _ := True
  Ri b b' := b = true → b' = true
  RA b b' := b = true → b' = true
  RE b b' := b = b'
  Fl _ := False
  refl_i _ := id
  trans_i h h' := fun x => h' (h x)
  refl_A _ := id
  trans_A h h' := fun x => h' (h x)
  sub_A h := h
  refl_E _ := rfl
  trans_E h h' := h.trans h'
  sub_E h := fun x => h ▸ x
  dom_mono _ _ := trivial
  d₀ := ()
  dom_d₀ _ := trivial
  hered_Fl _ h := h
  fn _ _ := ()
  I b _ _ := b = true
  hered_I h hw := h hw
  fn_dom _ := trivial

/-- The atom. -/
def P : Form := .pred "P" []

def ρ₂ : String → two.D := fun _ => ()

/-! ## `◯∀ P` holds at the bottom state, `◯∃ P` does not -/

theorem all_holds : two.force (.circ .all P) false ρ₂ [] :=
  fun _ _ => ⟨true, fun _ => rfl, Or.inr rfl⟩

theorem ex_fails : ¬ two.force (.circ .ex P) false ρ₂ [] := by
  intro h
  obtain ⟨u, hu, hP⟩ := h false (fun x => x)
  rcases hP with hF | hI
  · exact hF
  · exact Bool.noConfusion (hu.trans (show u = true from hI))

/-- **`◯∀ P ⊬ ◯∃ P`** — proved by soundness against the model above. -/
theorem all_not_ex : ¬ Prv [.circ .all P] (.circ .ex P) := by
  intro h
  exact ex_fails (h.sound two false ρ₂ (fun _ => trivial) (fun B hB => by
    rcases List.mem_singleton.mp hB with rfl
    exact all_holds))

/-! ## And the other way round, on the mirrored model -/

/-- The same frame with the two relations exchanged. -/
def two' : KModel :=
  { two with
    RA := two.RE
    RE := two.RA
    refl_A := two.refl_E
    trans_A := two.trans_E
    sub_A := two.sub_E
    refl_E := two.refl_A
    trans_E := two.trans_A
    sub_E := two.sub_A }

def ρ₂' : String → two'.D := fun _ => ()

theorem ex_holds' : two'.force (.circ .ex P) false ρ₂' [] :=
  fun _ _ => ⟨true, fun _ => rfl, Or.inr rfl⟩

theorem all_fails' : ¬ two'.force (.circ .all P) false ρ₂' [] := by
  intro h
  obtain ⟨u, hu, hP⟩ := h false (fun x => x)
  rcases hP with hF | hI
  · exact hF
  · exact Bool.noConfusion (hu.trans (show u = true from hI))

/-- **`◯∃ P ⊬ ◯∀ P`**.  With the two facts together, neither modality is
definable from the other, and one reachability relation would not do. -/
theorem ex_not_all : ¬ Prv [.circ .ex P] (.circ .all P) := by
  intro h
  exact all_fails' (h.sound two' false ρ₂' (fun _ => trivial) (fun B hB => by
    rcases List.mem_singleton.mp hB with rfl
    exact ex_holds'))

/-! ## Completeness, used

The commutativity of `∧` is read off the semantics and handed to
`completeness`, which returns a derivation.  Nothing below builds one. -/

def Q : Form := .pred "Q" []

theorem and_comm_valid : [Form.and P Q] ⊫ Form.and Q P := by
  intro M s ρ _ hΓ
  have h := hΓ (Form.and P Q) (List.mem_singleton.mpr rfl)
  exact ⟨h.2, h.1⟩

theorem and_comm_prv : Prv [Form.and P Q] (Form.and Q P) :=
  completeness (by
    intro B hB
    rcases List.mem_singleton.mp hB with rfl
    exact ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩)
    ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ and_comm_valid

/-! ## Why the domains must vary

The Constant Domain axiom

    ∀x(A ∨ B x) ⊃ (A ∨ ∀x B x)          (`x` not free in `A`)

is not intuitionistically valid, and it is refuted here by a model whose two
states have *different* domains: one individual below, two above.  So the
canonical model of a completeness proof for the full language cannot have
constant domains, and the parameter set available at a state has to grow along
the order.  That is the obstacle the quantifier-free restriction on
`completeness` records, made concrete.

The cell also exercises the quantifier clauses of `force`, including the one
correction we took from the literature: `∀` ranges over the domain of the
*successor*.  Read with the domain at the current state, `cd_holds` below
would still go through but heredity would fail. -/

/-- Two states and two individuals: `false` exists everywhere, `true` only
above.  `A` holds above only; `B` holds of `false` only. -/
def dom2 : KModel where
  S := Bool
  D := Bool
  Dom s d := s = true ∨ d = false
  Ri b b' := b = true → b' = true
  RA b b' := b = true → b' = true
  RE b b' := b = true → b' = true
  Fl _ := False
  refl_i _ := id
  trans_i h h' := fun x => h' (h x)
  refl_A _ := id
  trans_A h h' := fun x => h' (h x)
  sub_A h := h
  refl_E _ := id
  trans_E h h' := fun x => h' (h x)
  sub_E h := h
  dom_mono h hd := hd.imp h id
  d₀ := false
  dom_d₀ _ := Or.inr rfl
  hered_Fl _ h := h
  fn _ _ := false
  I s P ds := (P = "A" ∧ s = true) ∨ (P = "B" ∧ ds = [false])
  hered_I h hw := hw.imp (fun x => ⟨x.1, h x.2⟩) id
  fn_dom _ := Or.inr rfl

def ρ₃ : String → dom2.D := fun _ => false

/-- `A`, with no free individual. -/
def FA : Form := .pred "A" []
/-- `B x`, with `x` the bound individual. -/
def FB : Form := .pred "B" [.bvar 0]

theorem cd_holds : dom2.force (.forall_ (.or FA FB)) false ρ₃ [] := by
  intro v _ d hd
  cases d
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · rcases hd with hv | hd
    · exact Or.inl (Or.inr (Or.inl ⟨rfl, hv⟩))
    · exact Bool.noConfusion hd

theorem cd_fails : ¬ dom2.force (.or FA (.forall_ FB)) false ρ₃ [] := by
  rintro (hA | hall)
  · rcases hA with hF | hI
    · exact hF
    · rcases hI with h | h
      · exact Bool.noConfusion h.2
      · exact absurd h.1 (by decide)
  · rcases hall true (fun _ => rfl) true (Or.inl rfl) with hF | hI
    · exact hF
    · rcases hI with h | h
      · exact absurd h.1 (by decide)
      · have h2 : ([true] : List Bool) = [false] := h.2
        simp at h2

/-- **The Constant Domain axiom is not derivable.**  By soundness, against a
model whose two states have different domains. -/
theorem cd_not_prv : ¬ Prv [.forall_ (.or FA FB)] (.or FA (.forall_ FB)) := by
  intro h
  exact cd_fails (h.sound dom2 false ρ₃ (fun _ => Or.inr rfl) (fun B hB => by
    rcases List.mem_singleton.mp hB with rfl
    exact cd_holds))

/-! ## Axioms -/

/-- info: 'LaxLogic.QLL.CompleteTests.all_not_ex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms all_not_ex

/-- info: 'LaxLogic.QLL.CompleteTests.and_comm_prv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms and_comm_prv

end LaxLogic.QLL.CompleteTests
