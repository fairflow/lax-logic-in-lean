/-
Route (B), node **N4**, stage 3: the remaining structural features of
`interpP`'s recursion, as DESIGNED cells (rule 9), and the dividing line they
draw.

`wip/ui_routeB_n4_lit.lean` refutes the literal form of N1 on three cells — the
self-attack, a 2-cycle, the Dyckhoff shape.  Three structural features of the
definition are not exercised there, and they are the ones the BOUNDED form of
N4 (`docs/n4-circfree-cases.md`) has to be tested against:

  (iv)  `done = [↓↑a ⊃ ↑b]`,  goal `↑↓↑a`
        the SHIFT shape — the second clause `interpP` parks where `interpF`
        reshaped (`↓↑P′ ⊃ N ↦ P′ ⊃ N`).
  (v)   `done = [p ⊃ ↑c, ↑p]`, goal `↑c`
        the ELIMINATED ATOM PRESENT — the station is NOT saturated, the parked
        implication FIRES, and the `pGuard` rows are reached.
  (vi)  `done = [(a∨b) ⊃ ↑c, ↓↑c ⊃ ↑d]`, goal `↑d`
        TWO parked implications whose guards NEST: the goal `↑d` is neither
        antecedent's own goal, so the ascent has to travel through the guard
        chains at `↑(a∨b)` and `↑↓↑c`.

**The dividing line.**  (iv) and (vi) ascend, like (i)–(iii); (v) is literally
CONSTANT from fuel 3 on, in both modes.  The difference is saturation, not
weight: at (v) the parked implication's atom has arrived, so `findFire` fires it
and the recursion leaves the station for a residual that retains no compound
implication.  So the refutation of the literal form is exactly co-extensive with
`Saturated done` plus a retained compound implication — which is the hypothesis
`hasUI_of_stabEq` was stated under, and the reason it has no instances.
-/
import wip.ui_routeB_n4_lit
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Cell (iv) · the shift shape

    done = [↓↑a ⊃ ↑b],   goal ↑↓↑a

`ParkedNP.simp`, saturated, ◯-free.  The guard of the `↓↑Pa ⊃ N` row is the
antecedent's own goal `↑↓↑a` (`LJF/OFuelP.lean` (b)), which is the goal, so the
row is a self-attack exactly as in cell (i). -/

def cell4 : List Neg := [.imp (.down (.up (.atom "a"))) (.up (.atom "b"))]
def goal4 : Neg := .up (.down (.up (.atom "a")))

theorem cell4_sat : Saturated cell4 := rfl

theorem cell4_parked : ParkedCtxP cell4 :=
  ParkedCtxP.cons (.simp _ _) ParkedCtxP.nil

/-- The ∀p aggregate of cell (iv): one goal-inversion disjunct and one station
row whose left conjunct is the aggregate one fuel down. -/
theorem aRow4 (p : String) (f : Nat) :
    interpP p (f + 1) [] cell4 (some goal4) =
      nOrAll ([interpP p f [] cell4 (some (.up (.atom "a")))] ++
        [nAnd (interpP p f [] cell4 (some goal4))
              (interpP p f [.up (.atom "b")] [] (some goal4))]) :=
  interpPA_down_eq cell4_sat _

theorem aSize4 (p : String) (f : Nat) :
    sizeNeg (interpP p f [] cell4 (some goal4)) <
      sizeNeg (interpP p (f + 1) [] cell4 (some goal4)) := by
  rw [aRow4]
  have h1 := sizeNeg_pos (interpP p f [] cell4 (some (.up (.atom "a"))))
  have h2 := sizeNeg_pos (interpP p f [.up (.atom "b")] [] (some goal4))
  simp only [nOrAll, nOr, nAnd, nBot, List.cons_append, List.nil_append,
    List.foldr_cons, List.foldr_nil, sizeNeg, sizePos]
  omega

/-- **REFUTED: the literal ∀p stabilisation of the shift shape.** -/
theorem not_aStabEq4 (p : String) : AStabEq p cell4 goal4 → False :=
  not_stabEq_of_ascending (aSize4 p)

/-- The ∃p aggregate of cell (iv), and its guard projection. -/
theorem eRow4 (p : String) (f : Nat) :
    interpP p (f + 1) [] cell4 none =
      Neg.and
        (Neg.and (.imp (.down (interpP p f [] cell4 (some goal4)))
                       (interpP p f [.up (.atom "b")] [] none))
                 (interpP p f [] [] none))
        nTop :=
  interpPE_eq cell4_sat

theorem guard4 (p : String) (f : Nat) :
    guardOf (interpP p (f + 1) [] cell4 none) = interpP p f [] cell4 (some goal4) := by
  rw [eRow4]; rfl

/-- **REFUTED: the literal ∃p stabilisation of the shift shape.** -/
theorem not_eStabEq4 (p : String) : EStabEq p cell4 → False := by
  rintro ⟨f₀, hf⟩
  have h1 : interpP p (f₀ + 1) [] cell4 none = interpP p f₀ [] cell4 none :=
    hf (f₀ + 1) (Nat.le_succ _)
  have h2 : interpP p (f₀ + 1 + 1) [] cell4 none = interpP p f₀ [] cell4 none :=
    hf (f₀ + 1 + 1) (by omega)
  have h3 : interpP p (f₀ + 1) [] cell4 none = interpP p (f₀ + 1 + 1) [] cell4 none := by
    rw [h1, h2]
  have h4 := congrArg guardOf h3
  rw [guard4, guard4] at h4
  have h5 := aSize4 p f₀
  rw [h4] at h5
  exact Nat.lt_irrefl _ h5

/-! # Cell (v) · the eliminated atom present — the chain DOES stabilise

    done = [p ⊃ ↑c, ↑p],   goal ↑c

NOT saturated: `atomMem p done`, so `findFire` fires `p ⊃ ↑c` and the recursion
leaves for `[↑c] ⇒ [↑p]`, whose station retains no compound implication.  Both
chains are then literally constant from fuel 3.  This is the boundary of the
refutation, and it is drawn by SATURATION, not by weight. -/

def cell5 : List Neg := [.imp (.atom "p") (.up (.atom "c")), .up (.atom "p")]
def goal5 : Neg := .up (.atom "c")

/-- Cell (v) is NOT saturated: the parked implication's atom has arrived. -/
theorem cell5_fires :
    findFire cell5 (splits cell5) =
      some ("p", .up (.atom "c"), [.up (.atom "p")]) := rfl

theorem cell5_parked : ParkedCtxP cell5 :=
  ParkedCtxP.cons (.qimp _ _) (ParkedCtxP.cons (.atom _) ParkedCtxP.nil)

/-- **The ∀p aggregate of cell (v) is `⊤` from fuel 3 on**: fire, park `↑c`,
and the goal atom is then present in the station. -/
theorem a5_eq (p : String) (f : Nat) :
    interpP p (f + 3) [] cell5 (some goal5) = nTop := by
  rw [interpPFire_eq cell5_fires, interpP]
  exact interpPA_atomT_eq (by rfl) (by rfl)

/-- **The ∃p aggregate of cell (v) is constant from fuel 3 on.** -/
theorem e5_eq (p : String) (f : Nat) :
    interpP p (f + 3) [] cell5 none =
      nAndAll [pGuard p "c" nTop (.up (.atom "c")),
               pGuard p "p" nTop (.up (.atom "p"))] := by
  rw [interpPFire_eq cell5_fires, interpP]
  exact interpPE_eq (by rfl)

/-- **PROVED: the literal ∀p stabilisation of cell (v)**, at fuel 3. -/
def aStabEq5 (p : String) : AStabEq p cell5 goal5 :=
  ⟨3, fun f hf => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hf
    rw [Nat.add_comm 3 k, a5_eq p k, a5_eq p 0]⟩

/-- **PROVED: the literal ∃p stabilisation of cell (v)**, at fuel 3. -/
def eStabEq5 (p : String) : EStabEq p cell5 :=
  ⟨3, fun f hf => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hf
    rw [Nat.add_comm 3 k, e5_eq p k, e5_eq p 0]⟩

/-! # Cell (vi) · two parked implications whose guards nest

    done = [(a∨b) ⊃ ↑c, ↓↑c ⊃ ↑d],   goal ↑d

Saturated, parked, ◯-free.  The goal `↑d` is NEITHER antecedent's own goal, so
the aggregate at `↑d` has no self-attack row; the ascent travels through the two
guard chains, at `↑(a∨b)` and at `↑↓↑c`, each of which self-attacks inside its
own aggregate.  This is the shape a bounded `W done` has to account for: the
weight of the OUTER goal's chain is governed by the guards' chains, at the FULL
station, not by any residual. -/

def cell6 : List Neg :=
  [.imp (.or (.atom "a") (.atom "b")) (.up (.atom "c")),
   .imp (.down (.up (.atom "c"))) (.up (.atom "d"))]
def goal6ab : Neg := .up (.or (.atom "a") (.atom "b"))
def goal6c : Neg := .up (.down (.up (.atom "c")))
def goal6d : Neg := .up (.atom "d")

theorem cell6_sat : Saturated cell6 := rfl

theorem cell6_parked : ParkedCtxP cell6 :=
  ParkedCtxP.cons (.oimp _ _ _) (ParkedCtxP.cons (.simp _ _) ParkedCtxP.nil)

/-- The INNER chain at `↑(a∨b)`: the first hypothesis's row is a self-attack. -/
theorem aRow6ab (p : String) (f : Nat) :
    interpP p (f + 1) [] cell6 (some goal6ab) =
      nOrAll ([interpP p f [] cell6 (some (.up (.atom "a"))),
               interpP p f [] cell6 (some (.up (.atom "b")))] ++
        [nAnd (interpP p f [] cell6 (some goal6ab))
              (interpP p f [.up (.atom "c")]
                 [.imp (.down (.up (.atom "c"))) (.up (.atom "d"))] (some goal6ab)),
         nAnd (interpP p f [] cell6 (some goal6c))
              (interpP p f [.up (.atom "d")]
                 [.imp (.or (.atom "a") (.atom "b")) (.up (.atom "c"))] (some goal6ab))]) :=
  interpPA_or_eq cell6_sat _ _

theorem aSize6ab (p : String) (f : Nat) :
    sizeNeg (interpP p f [] cell6 (some goal6ab)) <
      sizeNeg (interpP p (f + 1) [] cell6 (some goal6ab)) := by
  rw [aRow6ab]
  have h1 := sizeNeg_pos (interpP p f [] cell6 (some (.up (.atom "a"))))
  have h2 := sizeNeg_pos (interpP p f [] cell6 (some (.up (.atom "b"))))
  have h3 := sizeNeg_pos (interpP p f [.up (.atom "c")]
    [.imp (.down (.up (.atom "c"))) (.up (.atom "d"))] (some goal6ab))
  have h4 := sizeNeg_pos (interpP p f [] cell6 (some goal6c))
  have h5 := sizeNeg_pos (interpP p f [.up (.atom "d")]
    [.imp (.or (.atom "a") (.atom "b")) (.up (.atom "c"))] (some goal6ab))
  simp only [nOrAll, nOr, nAnd, nBot, List.cons_append, List.nil_append,
    List.foldr_cons, List.foldr_nil, sizeNeg, sizePos]
  omega

/-- **REFUTED at the inner goal.** -/
theorem not_aStabEq6ab (p : String) : AStabEq p cell6 goal6ab → False :=
  not_stabEq_of_ascending (aSize6ab p)

/-- The OUTER chain at `↑d`, in full, for the eliminated variable `p`.  The atom
head is `[↑d]` (`d ≠ p`) and there are two station rows; the FIRST row's left
conjunct is the inner aggregate at `↑(a∨b)`. -/
theorem aRow6d (f : Nat) :
    interpP "p" (f + 1) [] cell6 (some goal6d) =
      nOrAll ([Neg.up (.atom "d")] ++
        [nAnd (interpP "p" f [] cell6 (some goal6ab))
              (interpP "p" f [.up (.atom "c")]
                 [.imp (.down (.up (.atom "c"))) (.up (.atom "d"))] (some goal6d)),
         nAnd (interpP "p" f [] cell6 (some goal6c))
              (interpP "p" f [.up (.atom "d")]
                 [.imp (.or (.atom "a") (.atom "b")) (.up (.atom "c"))] (some goal6d))]) :=
  interpPA_atom_eq cell6_sat (by decide +kernel)

/-- Read the first station row's guard out of an atom-goal aggregate whose atom
head is a single disjunct: `↑d ∨ ((A ∧ _) ∨ (_ ∨ ⊥))`. -/
def guardAtom : Neg → Neg
  | .up (.or _ (.down (.up (.or (.down (.and A _)) _)))) => A
  | _ => nTop

theorem guard6 (f : Nat) :
    guardAtom (interpP "p" (f + 1) [] cell6 (some goal6d)) =
      interpP "p" f [] cell6 (some goal6ab) := by
  rw [aRow6d]; rfl

/-- **REFUTED at the outer goal**, through the nested guard alone: the outer
aggregate DETERMINES the inner one one fuel down, and that one ascends. -/
theorem not_aStabEq6d : AStabEq "p" cell6 goal6d → False := by
  rintro ⟨f₀, hf⟩
  have h1 : interpP "p" (f₀ + 1) [] cell6 (some goal6d)
      = interpP "p" f₀ [] cell6 (some goal6d) := hf (f₀ + 1) (Nat.le_succ _)
  have h2 : interpP "p" (f₀ + 1 + 1) [] cell6 (some goal6d)
      = interpP "p" f₀ [] cell6 (some goal6d) := hf (f₀ + 1 + 1) (by omega)
  have h3 : interpP "p" (f₀ + 1) [] cell6 (some goal6d)
      = interpP "p" (f₀ + 1 + 1) [] cell6 (some goal6d) := by rw [h1, h2]
  have h4 := congrArg guardAtom h3
  rw [guard6, guard6] at h4
  have h5 := aSize6ab "p" f₀
  rw [h4] at h5
  exact Nat.lt_irrefl _ h5

/-! # The chains, measured — kernel-checked

The ascent theorems above say the chains grow; these say by how much, at the
bottom, for `p := "p"`.  Kernel-level (`decide +kernel`), so the table in
`docs/n4-circfree-cases.md` is a proved statement and not an `#eval`. -/

/-- `sizeNeg` of the six chains at fuels 0–5. -/
theorem chainSizes :
    ((List.range 6).map (fun f => sizeNeg (interpP "p" f [] cell1 none))
       = [4, 18, 39, 93, 204, 465]) ∧
    ((List.range 6).map (fun f => sizeNeg (interpP "p" f [] cell1 (some goal1)))
       = [2, 23, 74, 185, 446, 929]) ∧
    ((List.range 6).map (fun f => sizeNeg (interpP "p" f [] cell3 (some goal3)))
       = [2, 17, 43, 81, 168, 297]) ∧
    ((List.range 6).map (fun f => sizeNeg (interpP "p" f [] cell4 (some goal4)))
       = [2, 17, 47, 104, 215, 383]) ∧
    ((List.range 6).map (fun f => sizeNeg (interpP "p" f [] cell5 (some goal5)))
       = [2, 2, 2, 4, 4, 4]) ∧
    ((List.range 6).map (fun f => sizeNeg (interpP "p" f [] cell6 (some goal6d)))
       = [2, 26, 80, 283, 922, 3033]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! # The dividing line, as one statement -/

/-- **The literal form of N1 is refuted at every one of the five SATURATED
cells and HOLDS at the one unsaturated cell.**  Saturation plus a retained
compound implication is exactly the condition; `hasUI_of_stabEq`'s hypotheses
are the ones that make it unsatisfiable. -/
theorem literal_N1_dividing_line (p : String) :
    (AStabEq p cell1 goal1 → False) ∧
    (AStabEq p cell2 goal2ab → False) ∧
    (AStabEq p cell3 goal3 → False) ∧
    (AStabEq p cell4 goal4 → False) ∧
    (AStabEq p cell6 goal6ab → False) ∧
    Nonempty (AStabEq p cell5 goal5) :=
  ⟨not_aStabEq1 p, not_aStabEq2 p, not_aStabEq3 p, not_aStabEq4 p,
   not_aStabEq6ab p, ⟨aStabEq5 p⟩⟩

end LJFO

/-! ## Pins -/

#axioms_within LJFO.cell4_sat [propext]
#axioms_within LJFO.cell4_parked [propext]
#axioms_within LJFO.aRow4 [propext]
#axioms_within LJFO.aSize4 [propext, Quot.sound]
#axioms_within LJFO.not_aStabEq4 [propext, Quot.sound]
#axioms_within LJFO.eRow4 [propext]
#axioms_within LJFO.guard4 [propext]
#axioms_within LJFO.not_eStabEq4 [propext, Quot.sound]
#axioms_within LJFO.cell5_fires [propext]
#axioms_within LJFO.cell5_parked [propext]
#axioms_within LJFO.a5_eq [propext]
#axioms_within LJFO.e5_eq [propext]
#axioms_within LJFO.aStabEq5 [propext]
#axioms_within LJFO.eStabEq5 [propext]
#axioms_within LJFO.cell6_sat [propext]
#axioms_within LJFO.cell6_parked [propext]
#axioms_within LJFO.aRow6ab [propext]
#axioms_within LJFO.aSize6ab [propext, Quot.sound]
#axioms_within LJFO.not_aStabEq6ab [propext, Quot.sound]
#axioms_within LJFO.aRow6d [propext]
#axioms_within LJFO.guardAtom [propext]
#axioms_within LJFO.guard6 [propext]
#axioms_within LJFO.not_aStabEq6d [propext, Quot.sound]
#axioms_within LJFO.literal_N1_dividing_line [propext, Quot.sound]
#axioms_within LJFO.chainSizes [propext]
