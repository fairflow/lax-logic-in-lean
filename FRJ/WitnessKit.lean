/-
# The witness kit — the generic helpers of every FRJV hand witness

Hoisted from `FRJ/WitnessV1215.lean` (2026-08-26, Matthew's review: the
helpers are generic — quantified over any goal and any zones — but were
STRANDED in one witness's namespace, so the tactic built on them read as
single-use).  Everything here is goal-polymorphic; the witness files and
the interactive constructions import this and nothing witness-specific.

`frjv_side` is the side-condition tactic distilled from the witness
corpus: the eight closed moves that discharged every non-premise goal in
all seven witnesses.  For the completeness campaign each arm names one
helper obligation of the general recursion (docs/next-session.md).
-/
import FRJ.CalculusV

namespace FRJ

/-- Subset of formula lists is decidable (a bounded `∀`). -/
instance decSubForm (l m : List Form) : Decidable (l ⊆ m) :=
  decidable_of_iff (∀ x ∈ l, x ∈ m)
    ⟨fun h _ hx => h _ hx, fun h _ hx => h hx⟩

/-- Zone split: any sublist `Λ` of `Θ` splits it, up to `≐`. -/
theorem zoneSplit {Θ Λ : List Form} (hΛ : ∀ x ∈ Λ, x ∈ Θ) :
    Θ ≐ FRJ.sdiff Θ Λ ++ Λ := by
  intro x
  constructor
  · intro h
    by_cases hl : x ∈ Λ
    · exact List.mem_append_right _ hl
    · exact List.mem_append_left _ (mem_sdiff.mpr ⟨h, hl⟩)
  · intro h
    rcases List.mem_append.mp h with h | h
    · exact (mem_sdiff.mp h).1
    · exact hΛ _ h

/-- Boolean form of the joins' (J2): every implication of `l` has its
antecedent in `Υ`. -/
def impAnteB (Υ l : List Form) : Bool :=
  l.all fun f => match f with | .imp A _ => decide (A ∈ Υ) | _ => true

theorem hJ2_of_impAnteB {Υ l : List Form} (h : impAnteB Υ l = true) :
    ∀ A B : Form, Form.imp A B ∈ l → A ∈ Υ := fun _ _ hm =>
  of_decide_eq_true (List.all_eq_true.mp h _ hm)

/-- The promise joins' (J5) is vacuous when the joint stable modal zone
is empty. -/
theorem hJ5_of_nil {n k : Nat} {stab : Fin (n + 1) → List Form}
    {Δs : Fin (k + 1) → List Form}
    (h : unionAll (fun j => circPart (stab j)) = []) :
    ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
      ∃ i, Clo (Δs i) Y :=
  fun _ hY => absurd (h ▸ hY) List.not_mem_nil

/-- A derived irregular row, packaged so a mixed premise family can be
indexed by `Fin (n+1)` definitionally. -/
structure IRow (G : Form) where
  st : List Form
  th : List Form
  rhs : Form
  der : FRJVi G st th rhs

def istF {G : Form} (a : IRow G) (rest : List (IRow G)) :
    Fin (rest.length + 1) → List Form := fun j => ((a :: rest).get j).st

def ithF {G : Form} (a : IRow G) (rest : List (IRow G)) :
    Fin (rest.length + 1) → List Form := fun j => ((a :: rest).get j).th

def irhsF {G : Form} (a : IRow G) (rest : List (IRow G)) :
    Fin (rest.length + 1) → Form := fun j => ((a :: rest).get j).rhs

def ipremF {G : Form} (a : IRow G) (rest : List (IRow G)) :
    ∀ j, FRJVi G (istF a rest j) (ithF a rest j) (irhsF a rest j) :=
  fun j => ((a :: rest).get j).der

end FRJ

/-- The eight closed side-condition moves of the FRJV witness corpus,
cheapest first.  Goal-polymorphic: every lemma cited is quantified over
the goal and the zones. -/
macro "frjv_side" : tactic =>
  `(tactic| first
    | exact FRJ.CtxEq.refl _
    | exact FRJ.keptOf_ok _ _ _
    | exact FRJ.cap_sdiff_eq_nil
    | exact FRJ.zoneSplit (by decide)
    | exact FRJ.hJ2_of_impAnteB (by decide)
    | exact FRJ.hJ5_of_nil (by decide)
    | exact FRJ.cloB_iff.mp (by decide)
    | decide)
