/-
Route (B), node **N4**, refutation stage: the LITERAL form of N1 is FALSE at
every saturated parked ◯-free station carrying a parked compound implication.

`wip/ui_routeB_n3.lean` states stabilisation in two forms:

    EStabEq   p done    := Σ′ f₀, ∀ f ≥ f₀,  E_f = E_{f₀}        (LITERAL)
    AStabEq   p done G  := Σ′ f₀, ∀ f ≥ f₀,  A_f(G) = A_{f₀}(G)  (LITERAL)
    EStabilises / AStabilises                                     (INTERDERIVABLE)

and N3 forward (`hasUI_of_stabEq`) consumes the literal pair.  This file
refutes the literal pair, from the structure of `interpP`'s rows, on three
DESIGNED ◯-free cells (rule 9 of `CLAUDE.md`: no enumeration, no sweep).

**The structural reason.**  `interpP`'s attack row for a parked implication
`Q ⊃ N ∈ done` at a goal `↑G` is (`LJF/OFuelPMin.lean`, `truStationRowsP`)

    A_f(done ⇒ ↑Q)  ∧  A_f(N :: rest ⇒ ↑G)

— the guard is taken at the FULL station `done`, which is what route (B)'s
retention principle demands.  When the goal `↑G` IS the antecedent's own goal
`↑Q`, that row contains the SAME call one fuel lower, so

    A_{f+1}(done ⇒ ↑Q)  ⊋  A_f(done ⇒ ↑Q)      as a formula.

The ∃p row of the same shape (`eConjRowsP`) carries the same guard, so `E_{f+1}`
determines `A_f` and the ∃p chain is not constant either.  No fuel level ever
repeats a formula: the chains are strictly ascending in `sizeNeg`.

**What is refuted, and what is not.**  The literal form of N1 is refuted, hence
the literal reading of N4 (`interpP p (f+1) [] done g = interpP p f [] done g`
at a saturated station) and with it the usefulness of `FuelIrrelevance`, whose
hypothesis `FuelStep` is never satisfiable at these stations (`not_fuelStep*`
below).  The INTERDERIVABLE form is untouched: the self-attack disjunct
`A_f ∧ …` is implied by `A_{f+1}` and adds no consequence, so
`EStabilises`/`AStabilises` remain open (and, on ◯-free stations, are proved in
`wip/ui_routeB_n4.lean`).

Cells, all ◯-free, all saturated, all parked:

  (i)   `done = [(a ∨ b) ⊃ ↑c]`,                goal `↑(a ∨ b)`  — the self-attack
  (ii)  `done = [(a ∨ b) ⊃ ↑c, (c ∨ d) ⊃ ↑a]`,  goal `↑(a ∨ b)`  — a 2-cycle
  (iii) `done = [↓(a ⊃ ↑b) ⊃ ↑c]`,              goal `↑↓(a ⊃ ↑b)` — the Dyckhoff shape

Cell (ii) is designed so that the refutation does not depend on the direct
self-attack: its cross-guards alone (`(a∨b) ⊃ ↑c` guarding at `↑(a∨b)` inside
the `↑(c∨d)` aggregate and back) force a strict two-step ascent, so pruning
rows whose guard goal equals the aggregate's goal would not rescue the literal
form.
-/
import wip.ui_routeB_n3
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 0 · The measure

`sizeNeg` (`LJF/OCore.lean`) is the plain term size.  Every refutation below
is: the chain is strictly `sizeNeg`-ascending, so no two of its members are
equal, so it is not eventually constant. -/

/-- A strictly `sizeNeg`-ascending chain is not eventually constant.  The
witness is `f₀ + 1`: `Σ′` gives equality with `f₀` at both `f₀` and `f₀+1`. -/
theorem not_stabEq_of_ascending {F : Nat → Neg}
    (asc : ∀ f, sizeNeg (F f) < sizeNeg (F (f + 1)))
    (h : Σ' f₀ : Nat, ∀ f, f₀ ≤ f → F f = F f₀) : False := by
  obtain ⟨f₀, hf⟩ := h
  have h1 : F (f₀ + 1) = F f₀ := hf (f₀ + 1) (Nat.le_succ _)
  have h2 := asc f₀
  rw [h1] at h2
  exact Nat.lt_irrefl _ h2

/-- **The guard projection.**  Every ∃p aggregate of a station whose single
parked shape is a compound implication has the form

    (↓A_f(done ⇒ ↑Q) ⊃ E(N :: rest))  ∧  R    ∧  ⊤

(`eConjRowsP`, the `oimp`/`shimp`/`aimp`/`dyk`/`cimp` arms).  `guardOf` reads
`A_f` back out of it, so an equality of two ∃p aggregates yields an equality of
two ∀p aggregates by `congrArg` — no constructor-injection chain, and the
extraction is stated as a lemma per cell (`guard1`, `guard3`). -/
def guardOf : Neg → Neg
  | .and (.and (.imp (.down A) _) _) _ => A
  | _ => nTop

/-! # Part 1 · Cell (i): the self-attack

    done = [(a ∨ b) ⊃ ↑c],   goal ↑(a ∨ b)

Saturated (no parked implication has an atomic antecedent), parked
(`ParkedNP.oimp`), ◯-free. -/

/-- The station of cell (i). -/
def cell1 : List Neg := [.imp (.or (.atom "a") (.atom "b")) (.up (.atom "c"))]

/-- The goal of cell (i): the antecedent's own goal. -/
def goal1 : Neg := .up (.or (.atom "a") (.atom "b"))

theorem cell1_sat : Saturated cell1 := rfl

theorem cell1_parked : ParkedCtxP cell1 :=
  ParkedCtxP.cons (.oimp _ _ _) ParkedCtxP.nil

/-- **The ∀p aggregate of cell (i), in full.**  Two goal-inversion disjuncts
and ONE station row, and that row's left conjunct is the aggregate itself one
fuel down. -/
theorem aRow1 (p : String) (f : Nat) :
    interpP p (f + 1) [] cell1 (some goal1) =
      nOrAll ([interpP p f [] cell1 (some (.up (.atom "a"))),
               interpP p f [] cell1 (some (.up (.atom "b")))] ++
        [nAnd (interpP p f [] cell1 (some goal1))
              (interpP p f [.up (.atom "c")] [] (some goal1))]) :=
  interpPA_or_eq cell1_sat _ _

/-- **The ∀p chain of cell (i) is strictly ascending.** -/
theorem aSize1 (p : String) (f : Nat) :
    sizeNeg (interpP p f [] cell1 (some goal1)) <
      sizeNeg (interpP p (f + 1) [] cell1 (some goal1)) := by
  rw [aRow1]
  have h1 := sizeNeg_pos (interpP p f [] cell1 (some (.up (.atom "a"))))
  have h2 := sizeNeg_pos (interpP p f [] cell1 (some (.up (.atom "b"))))
  have h3 := sizeNeg_pos (interpP p f [.up (.atom "c")] [] (some goal1))
  simp only [nOrAll, nOr, nAnd, nBot, List.cons_append, List.nil_append,
    List.foldr_cons, List.foldr_nil, sizeNeg, sizePos]
  omega

/-- **REFUTED: the literal ∀p stabilisation of cell (i).** -/
theorem not_aStabEq1 (p : String) : AStabEq p cell1 goal1 → False :=
  not_stabEq_of_ascending (aSize1 p)

/-- **The ∃p aggregate of cell (i), in full.**  One row; its left conjunct is
`↓A_f(done ⇒ ↑(a∨b))`, the ∀p aggregate whose chain ascends. -/
theorem eRow1 (p : String) (f : Nat) :
    interpP p (f + 1) [] cell1 none =
      Neg.and
        (Neg.and (.imp (.down (interpP p f [] cell1 (some goal1)))
                       (interpP p f [.up (.atom "c")] [] none))
                 (interpP p f [] [] none))
        nTop :=
  interpPE_eq cell1_sat

/-- The ∃p aggregate of cell (i) DETERMINES its ∀p aggregate one fuel down. -/
theorem guard1 (p : String) (f : Nat) :
    guardOf (interpP p (f + 1) [] cell1 none) = interpP p f [] cell1 (some goal1) := by
  rw [eRow1]; rfl

/-- **REFUTED: the literal ∃p stabilisation of cell (i).** -/
theorem not_eStabEq1 (p : String) : EStabEq p cell1 → False := by
  rintro ⟨f₀, hf⟩
  have h1 : interpP p (f₀ + 1) [] cell1 none = interpP p f₀ [] cell1 none :=
    hf (f₀ + 1) (Nat.le_succ _)
  have h2 : interpP p (f₀ + 1 + 1) [] cell1 none = interpP p f₀ [] cell1 none :=
    hf (f₀ + 1 + 1) (by omega)
  have h3 : interpP p (f₀ + 1) [] cell1 none = interpP p (f₀ + 1 + 1) [] cell1 none := by
    rw [h1, h2]
  have h4 := congrArg guardOf h3
  rw [guard1, guard1] at h4
  have h5 := aSize1 p f₀
  rw [h4] at h5
  exact Nat.lt_irrefl _ h5

/-- The hypothesis of `aStabEq_of_fuelStep` is UNSATISFIABLE at cell (i): the
recursion never bottoms out below its fuel, so `FuelIrrelevance` — whatever its
truth value — can never be used to establish literal stabilisation here. -/
theorem not_fuelStep1A (p : String) (f : Nat) :
    ¬ FuelStep p [] cell1 (some goal1) f := by
  intro h
  have h' : interpP p (f + 1) [] cell1 (some goal1)
      = interpP p f [] cell1 (some goal1) := h
  have h2 := aSize1 p f
  rw [h'] at h2
  exact Nat.lt_irrefl _ h2

/-! # Part 2 · Cell (ii): a 2-cycle

    done = [(a ∨ b) ⊃ ↑c, (c ∨ d) ⊃ ↑a],   goals ↑(a ∨ b) and ↑(c ∨ d)

Designed so that the refutation survives the pruning of direct self-attacks:
the row of `(c∨d) ⊃ ↑a` inside the `↑(a∨b)` aggregate guards at `↑(c∨d)`, and
the row of `(a∨b) ⊃ ↑c` inside the `↑(c∨d)` aggregate guards at `↑(a∨b)`, so

    A_{f+1}(⇒ ↑(a∨b))  ⊋  A_f(⇒ ↑(c∨d))  ⊋  A_{f-1}(⇒ ↑(a∨b)) .
-/

/-- The station of cell (ii). -/
def cell2 : List Neg :=
  [.imp (.or (.atom "a") (.atom "b")) (.up (.atom "c")),
   .imp (.or (.atom "c") (.atom "d")) (.up (.atom "a"))]

/-- The first goal of cell (ii). -/
def goal2ab : Neg := .up (.or (.atom "a") (.atom "b"))
/-- The second goal of cell (ii). -/
def goal2cd : Neg := .up (.or (.atom "c") (.atom "d"))

theorem cell2_sat : Saturated cell2 := rfl

theorem cell2_parked : ParkedCtxP cell2 :=
  ParkedCtxP.cons (.oimp _ _ _) (ParkedCtxP.cons (.oimp _ _ _) ParkedCtxP.nil)

/-- **The `↑(a∨b)` aggregate of cell (ii), in full**: two goal-inversion
disjuncts and TWO station rows.  The second row is the CROSS guard, at
`↑(c∨d)`. -/
theorem aRow2ab (p : String) (f : Nat) :
    interpP p (f + 1) [] cell2 (some goal2ab) =
      nOrAll ([interpP p f [] cell2 (some (.up (.atom "a"))),
               interpP p f [] cell2 (some (.up (.atom "b")))] ++
        [nAnd (interpP p f [] cell2 (some goal2ab))
              (interpP p f [.up (.atom "c")]
                 [.imp (.or (.atom "c") (.atom "d")) (.up (.atom "a"))] (some goal2ab)),
         nAnd (interpP p f [] cell2 (some goal2cd))
              (interpP p f [.up (.atom "a")]
                 [.imp (.or (.atom "a") (.atom "b")) (.up (.atom "c"))] (some goal2ab))]) :=
  interpPA_or_eq cell2_sat _ _

/-- **The `↑(c∨d)` aggregate of cell (ii), in full.**  Its FIRST station row is
the cross guard back at `↑(a∨b)`. -/
theorem aRow2cd (p : String) (f : Nat) :
    interpP p (f + 1) [] cell2 (some goal2cd) =
      nOrAll ([interpP p f [] cell2 (some (.up (.atom "c"))),
               interpP p f [] cell2 (some (.up (.atom "d")))] ++
        [nAnd (interpP p f [] cell2 (some goal2ab))
              (interpP p f [.up (.atom "c")]
                 [.imp (.or (.atom "c") (.atom "d")) (.up (.atom "a"))] (some goal2cd)),
         nAnd (interpP p f [] cell2 (some goal2cd))
              (interpP p f [.up (.atom "a")]
                 [.imp (.or (.atom "a") (.atom "b")) (.up (.atom "c"))] (some goal2cd))]) :=
  interpPA_or_eq cell2_sat _ _

/-- **The cross step, one way**: the `↑(a∨b)` aggregate at `f+1` is strictly
larger than the `↑(c∨d)` aggregate at `f`.  Uses ONLY the second station row
(the cross guard), not the self-attack. -/
theorem cross2_ab (p : String) (f : Nat) :
    sizeNeg (interpP p f [] cell2 (some goal2cd)) <
      sizeNeg (interpP p (f + 1) [] cell2 (some goal2ab)) := by
  rw [aRow2ab]
  have h1 := sizeNeg_pos (interpP p f [] cell2 (some (.up (.atom "a"))))
  have h2 := sizeNeg_pos (interpP p f [] cell2 (some (.up (.atom "b"))))
  have h3 := sizeNeg_pos (interpP p f [] cell2 (some goal2ab))
  have h4 := sizeNeg_pos (interpP p f [.up (.atom "c")]
    [.imp (.or (.atom "c") (.atom "d")) (.up (.atom "a"))] (some goal2ab))
  have h5 := sizeNeg_pos (interpP p f [.up (.atom "a")]
    [.imp (.or (.atom "a") (.atom "b")) (.up (.atom "c"))] (some goal2ab))
  simp only [nOrAll, nOr, nAnd, nBot, List.cons_append, List.nil_append,
    List.foldr_cons, List.foldr_nil, sizeNeg, sizePos]
  omega

/-- **The cross step, the other way.**  Uses ONLY the first station row. -/
theorem cross2_cd (p : String) (f : Nat) :
    sizeNeg (interpP p f [] cell2 (some goal2ab)) <
      sizeNeg (interpP p (f + 1) [] cell2 (some goal2cd)) := by
  rw [aRow2cd]
  have h1 := sizeNeg_pos (interpP p f [] cell2 (some (.up (.atom "c"))))
  have h2 := sizeNeg_pos (interpP p f [] cell2 (some (.up (.atom "d"))))
  have h3 := sizeNeg_pos (interpP p f [] cell2 (some goal2cd))
  have h4 := sizeNeg_pos (interpP p f [.up (.atom "c")]
    [.imp (.or (.atom "c") (.atom "d")) (.up (.atom "a"))] (some goal2cd))
  have h5 := sizeNeg_pos (interpP p f [.up (.atom "a")]
    [.imp (.or (.atom "a") (.atom "b")) (.up (.atom "c"))] (some goal2cd))
  simp only [nOrAll, nOr, nAnd, nBot, List.cons_append, List.nil_append,
    List.foldr_cons, List.foldr_nil, sizeNeg, sizePos]
  omega

/-- **The 2-cycle ascends**, by the two cross steps alone. -/
theorem aSize2 (p : String) (f : Nat) :
    sizeNeg (interpP p f [] cell2 (some goal2ab)) <
      sizeNeg (interpP p (f + 2) [] cell2 (some goal2ab)) :=
  Nat.lt_trans (cross2_cd p f) (cross2_ab p (f + 1))

/-- **REFUTED: the literal ∀p stabilisation of cell (ii)**, at the `↑(a∨b)`
goal, through the 2-cycle only. -/
theorem not_aStabEq2 (p : String) : AStabEq p cell2 goal2ab → False := by
  rintro ⟨f₀, hf⟩
  have h1 : interpP p (f₀ + 2) [] cell2 (some goal2ab)
      = interpP p f₀ [] cell2 (some goal2ab) := hf (f₀ + 2) (by omega)
  have h2 := aSize2 p f₀
  rw [h1] at h2
  exact Nat.lt_irrefl _ h2

/-- And at the `↑(c∨d)` goal. -/
theorem not_aStabEq2cd (p : String) : AStabEq p cell2 goal2cd → False := by
  rintro ⟨f₀, hf⟩
  have h1 : interpP p (f₀ + 2) [] cell2 (some goal2cd)
      = interpP p f₀ [] cell2 (some goal2cd) := hf (f₀ + 2) (by omega)
  have h2 : sizeNeg (interpP p f₀ [] cell2 (some goal2cd)) <
      sizeNeg (interpP p (f₀ + 2) [] cell2 (some goal2cd)) :=
    Nat.lt_trans (cross2_ab p f₀) (cross2_cd p (f₀ + 1))
  rw [h1] at h2
  exact Nat.lt_irrefl _ h2

/-! # Part 3 · Cell (iii): the Dyckhoff shape's guard

    done = [↓(a ⊃ ↑b) ⊃ ↑c],   goal ↑↓(a ⊃ ↑b)

Since 2026-09-05 (`docs/ui-ljfo-clause-table.md` §4.16) the Dyckhoff row guards
by the ANTECEDENT'S OWN GOAL `↑↓(Q′ ⊃ N′)`, which is exactly this cell's goal —
so the Dyckhoff shape self-attacks in the same way, and the fix that made
`DykAntP` an instance of `ParkAntP` is also what makes this chain ascend. -/

/-- The parked antecedent body of cell (iii). -/
def dykBody : Neg := .imp (.atom "a") (.up (.atom "b"))

/-- The station of cell (iii). -/
def cell3 : List Neg := [.imp (.down dykBody) (.up (.atom "c"))]

/-- The goal of cell (iii): the antecedent's own goal `↑↓(a ⊃ ↑b)`. -/
def goal3 : Neg := .up (.down dykBody)

theorem cell3_sat : Saturated cell3 := rfl

theorem cell3_parked : ParkedCtxP cell3 :=
  ParkedCtxP.cons (.dyk _ _ _) ParkedCtxP.nil

/-- **The ∀p aggregate of cell (iii), in full**: one goal-inversion disjunct
and one station row, whose left conjunct is the aggregate one fuel down. -/
theorem aRow3 (p : String) (f : Nat) :
    interpP p (f + 1) [] cell3 (some goal3) =
      nOrAll ([interpP p f [] cell3 (some dykBody)] ++
        [nAnd (interpP p f [] cell3 (some goal3))
              (interpP p f [.up (.atom "c")] [] (some goal3))]) :=
  interpPA_down_eq cell3_sat _

/-- **The ∀p chain of cell (iii) is strictly ascending.** -/
theorem aSize3 (p : String) (f : Nat) :
    sizeNeg (interpP p f [] cell3 (some goal3)) <
      sizeNeg (interpP p (f + 1) [] cell3 (some goal3)) := by
  rw [aRow3]
  have h1 := sizeNeg_pos (interpP p f [] cell3 (some dykBody))
  have h2 := sizeNeg_pos (interpP p f [.up (.atom "c")] [] (some goal3))
  simp only [nOrAll, nOr, nAnd, nBot, List.cons_append, List.nil_append,
    List.foldr_cons, List.foldr_nil, sizeNeg, sizePos]
  omega

/-- **REFUTED: the literal ∀p stabilisation of cell (iii).** -/
theorem not_aStabEq3 (p : String) : AStabEq p cell3 goal3 → False :=
  not_stabEq_of_ascending (aSize3 p)

/-- **The ∃p aggregate of cell (iii), in full.**  The Dyckhoff row is a pair:
the guarded fire, and the residual station's ∃p. -/
theorem eRow3 (p : String) (f : Nat) :
    interpP p (f + 1) [] cell3 none =
      Neg.and
        (Neg.and (.imp (.down (interpP p f [] cell3 (some goal3)))
                       (interpP p f [.up (.atom "c")] [] none))
                 (interpP p f [.imp (.down (.up (.atom "b"))) (.up (.atom "c"))] [] none))
        nTop :=
  interpPE_eq cell3_sat

/-- The ∃p aggregate of cell (iii) determines its ∀p aggregate one fuel down. -/
theorem guard3 (p : String) (f : Nat) :
    guardOf (interpP p (f + 1) [] cell3 none) = interpP p f [] cell3 (some goal3) := by
  rw [eRow3]; rfl

/-- **REFUTED: the literal ∃p stabilisation of cell (iii).** -/
theorem not_eStabEq3 (p : String) : EStabEq p cell3 → False := by
  rintro ⟨f₀, hf⟩
  have h1 : interpP p (f₀ + 1) [] cell3 none = interpP p f₀ [] cell3 none :=
    hf (f₀ + 1) (Nat.le_succ _)
  have h2 : interpP p (f₀ + 1 + 1) [] cell3 none = interpP p f₀ [] cell3 none :=
    hf (f₀ + 1 + 1) (by omega)
  have h3 : interpP p (f₀ + 1) [] cell3 none = interpP p (f₀ + 1 + 1) [] cell3 none := by
    rw [h1, h2]
  have h4 := congrArg guardOf h3
  rw [guard3, guard3] at h4
  have h5 := aSize3 p f₀
  rw [h4] at h5
  exact Nat.lt_irrefl _ h5

/-! # Part 4 · What this does to N1, N3 forward and `FuelIrrelevance`

The literal form is refuted; the interderivable form is not.  Stated as three
consequences, in the vocabulary of `wip/ui_routeB_n3.lean`. -/

/-- **N4 in its literal (termination) reading is FALSE.**  There is no fuel at
which `interpP`'s recursion at cell (i) repeats itself, in either mode. -/
theorem not_fuelStep1E (p : String) (f : Nat) : ¬ FuelStep p [] cell1 none f := by
  intro hs
  have h : interpP p (f + 1) [] cell1 none = interpP p f [] cell1 none := hs
  -- `h : E_{f+1} = E_f`.  At `f = 0` the right-hand side is the fuel-0 default
  -- `⊤`, which is not an `∧`; at `f = g+1` both sides are rows, and their
  -- guards `A_{g+1}`, `A_g` are equal — which the ascent forbids.
  cases f with
  | zero =>
      rw [eRow1] at h
      have h0 : interpP p 0 [] cell1 none = nTop := rfl
      rw [h0, nTop] at h
      exact Neg.noConfusion h
  | succ g =>
      have h4 := congrArg guardOf h
      rw [guard1, guard1] at h4
      have h5 := aSize1 p g
      rw [h4] at h5
      exact Nat.lt_irrefl _ h5

/-- **The three cells refute `hasUI_of_stabEq`'s hypotheses**, not its
conclusion: each cell is saturated, parked and ◯-free, so N3 forward can never
be applied at it in the literal form.  This is the statement that route (B)'s
N4 must be posed interderivably. -/
theorem literal_N1_unusable (p : String) :
    (AStabEq p cell1 goal1 → False) ∧ (EStabEq p cell1 → False) ∧
    (AStabEq p cell2 goal2ab → False) ∧
    (AStabEq p cell3 goal3 → False) ∧ (EStabEq p cell3 → False) :=
  ⟨not_aStabEq1 p, not_eStabEq1 p, not_aStabEq2 p, not_aStabEq3 p, not_eStabEq3 p⟩

/-! # Part 5 · Kernel sanity check at low fuel, one cell

A `decide` at the bottom of cell (i)'s chain, confirming that the ascent is not
an artefact of the size argument: the formulas at fuels 1, 2, 3 are pairwise
distinct.  Kernel-level (`decide +kernel`), one cell. -/

example : interpP "p" 1 [] cell1 (some goal1) ≠ interpP "p" 2 [] cell1 (some goal1) := by
  decide +kernel

example : interpP "p" 2 [] cell1 (some goal1) ≠ interpP "p" 3 [] cell1 (some goal1) := by
  decide +kernel

example : interpP "p" 1 [] cell1 none ≠ interpP "p" 2 [] cell1 none := by
  decide +kernel

end LJFO

/-! ## Pins

Measured with `#axioms_within_pin`, not retyped.  Everything here is a size
computation on a concrete station, so the sets are small. -/

#axioms_within LJFO.not_stabEq_of_ascending []
#axioms_within LJFO.guardOf [propext]
#axioms_within LJFO.cell1_sat [propext]
#axioms_within LJFO.cell1_parked [propext]
#axioms_within LJFO.aRow1 [propext]
#axioms_within LJFO.aSize1 [propext, Quot.sound]
#axioms_within LJFO.not_aStabEq1 [propext, Quot.sound]
#axioms_within LJFO.eRow1 [propext]
#axioms_within LJFO.guard1 [propext]
#axioms_within LJFO.not_eStabEq1 [propext, Quot.sound]
#axioms_within LJFO.not_fuelStep1A [propext, Quot.sound]
#axioms_within LJFO.cell2_sat [propext]
#axioms_within LJFO.cell2_parked [propext]
#axioms_within LJFO.aRow2ab [propext]
#axioms_within LJFO.aRow2cd [propext]
#axioms_within LJFO.cross2_ab [propext, Quot.sound]
#axioms_within LJFO.cross2_cd [propext, Quot.sound]
#axioms_within LJFO.aSize2 [propext, Quot.sound]
#axioms_within LJFO.not_aStabEq2 [propext, Quot.sound]
#axioms_within LJFO.not_aStabEq2cd [propext, Quot.sound]
#axioms_within LJFO.cell3_sat [propext]
#axioms_within LJFO.cell3_parked [propext]
#axioms_within LJFO.aRow3 [propext]
#axioms_within LJFO.aSize3 [propext, Quot.sound]
#axioms_within LJFO.not_aStabEq3 [propext, Quot.sound]
#axioms_within LJFO.eRow3 [propext]
#axioms_within LJFO.guard3 [propext]
#axioms_within LJFO.not_eStabEq3 [propext, Quot.sound]
#axioms_within LJFO.not_fuelStep1E [propext, Quot.sound]
#axioms_within LJFO.literal_N1_unusable [propext, Quot.sound]
