/-
# Corner-trigger probe over the residue frames (2026-08-26, FRJV
completeness campaign, docs/frjv-completeness-plan.md, S1 extension).

FINDING: on all four residue frames every CircSupply corner demand is
Z = ⊥ and the axIC route (empty valuation; gAt = [] on the closed
fragment) is AVAILABLE — including the six non-maximal corner fires
on frame 9900 (they are all world 2, duplicated per sfR occurrence).
sepM and the (20,12)-frame fire only at their maximal corner world
(circWit_of_maximal territory).  So Lemma B never blocks on the
residue corpus; the four hard cells are Lemma-A territory, and they
are exactly the frames with TWO circ-carrying infallible worlds
(9900: {4,1}; the (20,12)-frame: {2,1}) vs sepM's one — chained
promise structure. -/
import FRJ.Search.Pin
import FRJ.Bridge
import FRJ.Complete
import LaxLogic.RN.Rho

open FRJ FRJ.Search RhoOrder

def mkTab (n root : Nat) (leT rmT : List (List Bool)) (falT : List Bool) : Tab :=
  { n := n, root := root, leT := leT, rmT := rmT, falT := falT,
    atomsT := List.replicate n [] }

/-- sepM: the #80/#81 frame (order 01,02,03,04,12,13,23; modal 2R3; fallible 3). -/
def sepM : Tab := mkTab 5 0
  [[true,true,true,true,true],[false,true,true,true,false],[false,false,true,true,false],
   [false,false,false,true,false],[false,false,false,false,true]]
  [[true,false,false,false,false],[false,true,false,false,false],[false,false,true,true,false],
   [false,false,false,true,false],[false,false,false,false,true]]
  [false,false,false,true,false]

/-- Frame 9900 (cells (19,18),(20,18): order 01,02,03,04,12,13,14,23,43; modal 1R2,4R3; fallible 3). -/
def fr9900 : Tab := mkTab 5 0
  [[true,true,true,true,true],[false,true,true,true,true],[false,false,true,true,false],
   [false,false,false,true,false],[false,false,false,true,true]]
  [[true,false,false,false,false],[false,true,true,false,false],[false,false,true,false,false],
   [false,false,false,true,false],[false,false,false,true,true]]
  [false,false,false,true,false]

/-- The (20,12)/(20,13) frame (from Certified/RhoRefutations cm_rho_20_12). -/
def fr2012 : Tab := mkTab 5 0
  [[true,true,true,true,true],[false,true,true,true,true],[false,false,true,true,false],
   [false,false,false,true,false],[false,false,false,false,true]]
  [[true,false,false,false,false],[false,true,false,false,true],[false,false,true,true,false],
   [false,false,false,true,false],[false,false,false,false,true]]
  [false,false,false,true,false]

def goalF (i j : Nat) : Form := ofPLL (PLLFormula.ifThen (rhoF i) (rhoF j))

def corners (T : Tab) (G : Form) : List (Nat × String × Bool) := Id.run do
  match h : T.okB, hr : decide (T.root < T.n) with
  | true, true =>
    let K := T.toKripke h (of_decide_eq_true hr)
    let mut out := []
    for a in K.elems do
      -- corner world: modal cone = {a}
      let sole := K.elems.all (fun c => !(decide (K.Rm a c)) || decide (c = a))
      if sole then
        for Z in (sfR G) do
          match Z with
          | .circ Z' =>
            let hyp1 := !(decide (K.force a (.circ Z')))
            let hyp2 := K.elems.all (fun u =>
              !(decide (K.le a u)) || decide (u = a) || decide (K.force u Z'))
            if hyp1 && hyp2 then
              -- fires; is a maximal? (then circWit_of_maximal handles it)
              let amax := K.elems.all (fun u => !(decide (K.le a u)) || decide (u = a))
              -- axIC route over the empty valuation (gAt = [] on the closed fragment):
              -- every Λ*_a-member classically forced, Z classically refuted
              let lam := lamStar K a G
              let axic := lam.all (fun X => classForce [] X) && !(classForce [] Z')
              out := (0, s!"Z={repr Z'} axIC={axic} lam={lam.length}", amax) :: out
          | _ => pure ()
    return out
  | _, _ => return [(999, "BAD TAB", false)]

def circCarrying (T : Tab) (G : Form) : List Nat := Id.run do
  match h : T.okB, hr : decide (T.root < T.n) with
  | true, true =>
    let K := T.toKripke h (of_decide_eq_true hr)
    let mut out := []
    let mut idx := 0
    for a in K.elems do
      if (circPart (lamStar K a G)) ≠ [] && !(decide (K.Fal a)) then
        out := idx :: out
      idx := idx + 1
    return out
  | _, _ => return [999]

#eval show IO Unit from do
  let cells : List (String × Tab × Form) :=
    [ ("sepM/G80", sepM, goalF 12 9), ("sepM/(12,18)", sepM, goalF 12 18),
      ("sepM/(13,18)", sepM, goalF 13 18),
      ("9900/(19,18)", fr9900, goalF 19 18), ("9900/(20,18)", fr9900, goalF 20 18),
      ("2012/(20,12)", fr2012, goalF 20 12), ("2012/(20,13)", fr2012, goalF 20 13) ]
  for (nm, T, G) in cells do
    IO.println s!"{nm}: circ-carrying-infallible-worlds={circCarrying T G}"
    for (_, s, amax) in corners T G do
      IO.println s!"    fire: {s} maximal={amax}"
