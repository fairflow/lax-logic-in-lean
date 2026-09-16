/-
# FRJ◯ W3a — extraction: from a derivation, the countermodel

`extract` reads the model off an `FRJD` derivation, RK(Ξ)-style:
`orR`/`impIn` change nothing (same world); `impOut`/`circOut` pass to
the child's model; `world` takes the disjoint union of the child
models, adds a fresh root wired `Rᵢ` to the child roots, `Rₘ` to the
declared cone children, plus the optional fallible leaf.  Output is a
`FinCM` (worlds numbered, root = 0) so the VERIFIED checker can gate
every use today.

W3b — the once-and-for-all theorem `extract_forces` (root forces the
stable zone, refutes the goal; by induction on the derivation,
consuming `Reject.addRoot_force_some`/`join_force_comp`/
`boxRefuteHere`/`boxRefuteAbove`) — is STATED and, for `worldOK` v3,
**REFUTED** (`FRJO/Screen.lean`, 2026-08-16: three certified cells).
v3 constrains the stable zone only by membership in the universe, so a
`world` node may carry a zone no world forces; the v4 repair is
specified and checked in that file.  Until it lands, everything below
that depends on `ExtractForces` is VACUOUS.  Until it
lands, soundness of each concrete refutation is delivered by
`FinCM.checkB` + `not_provable_of_check`, the same trust base as the
rest of the repo; the theorem retires the per-instance gate.
-/
import FRJO.Calc
import LaxLogic.PLLCountermodelEmit

namespace FRJO

open PLLND PLLFormula

/-- Shift a `FinCM`'s worlds by `k`. -/
def shiftCM (k : Nat) (M : FinCM) : FinCM :=
  ⟨M.n + k, M.ri.map (fun p => (p.1 + k, p.2 + k)),
   M.rm.map (fun p => (p.1 + k, p.2 + k)),
   M.fall.map (· + k), M.val.map (fun p => (p.1 + k, p.2))⟩

/-- Extraction, by recursion on the derivation.  Root is world 0. -/
def extract (G : Cell) (b : Nat) : {S : Reg G} → FRJD G b S → FinCM
  | _, .orR d _ => extract G b d
  | _, .andR1 d => extract G b d
  | _, .andR2 d => extract G b d
  | _, .impIn d _ => extract G b d
  | _, .impOut d _ _ =>
      -- fresh root below the child's model
      let M := shiftCM 1 (extract G b d)
      ⟨M.n, (0, 1) :: M.ri, M.rm, M.fall, M.val⟩
  | _, .circOut d _ =>
      let M := shiftCM 1 (extract G b d)
      ⟨M.n, (0, 1) :: M.ri, M.rm, M.fall, M.val⟩
  | _, .world (S := S) kids cone leaf prems _ => Id.run do
      -- assemble child models side by side above a fresh root 0
      let mut n := 1
      let mut ri : List (Nat × Nat) := []
      let mut rm : List (Nat × Nat) := []
      let mut fal : List Nat := []
      let mut val : List (Nat × String) :=
        (S.filterMap fun φ => match φ with
          | .prop a => some (0, a)
          | _ => none)
      let mut i := 0
      for K in kids.attach do
        let M := shiftCM n (extract G b (prems K.1 K.2))
        ri := (0, n) :: M.ri ++ ri
        rm := (if cone.getD i false then [(0, n)] else []) ++ M.rm ++ rm
        fal := M.fall ++ fal
        val := M.val ++ val
        n := M.n
        i := i + 1
      if leaf then
        ri := (0, n) :: ri
        rm := (0, n) :: rm
        fal := n :: fal
        n := n + 1
      -- transitive closure of ri and rm (roots reach grandchildren)
      let mut riC := ri
      let mut changed := true
      while changed do
        changed := false
        for (x, y) in riC do
          for (y', z) in riC do
            if y == y' && x != z && !(riC.contains (x, z)) then
              riC := (x, z) :: riC; changed := true
      let mut rmC := rm
      changed := true
      while changed do
        changed := false
        for (x, y) in rmC do
          for (y', z) in rmC do
            if y == y' && x != z && !(rmC.contains (x, z)) then
              rmC := (x, z) :: rmC; changed := true
      return ⟨n, riC, rmC, fal, val⟩

/-- **W3b**: extraction is sound, once and for all.  **REFUTED for
`worldOK` v3** — `FRJO.not_extractForces_bot`/`_and`/`_mp` in
`FRJO/Screen.lean`. -/
def ExtractForces (G : Cell) (b : Nat) : Prop :=
  ∀ (S : Reg G) (d : FRJD G b S),
    FinCM.checkB (extract G b d) 0 S.stable S.goal = true

/-- With W3b, every derivation is a PLL underivability certificate. -/
theorem not_laxND_of_FRJD {G : Cell} {b : Nat}
    (hE : ExtractForces G b) {S : Reg G} (d : FRJD G b S) :
    ¬ Nonempty (PLLND.LaxND S.stable S.goal) :=
  FinCM.not_provable_of_check (hE S d)

/-! ## Pins -/

/-- info: 'FRJO.not_laxND_of_FRJD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_laxND_of_FRJD

end FRJO
