/-
LJF◯ — the backward search skeleton (route (B), layer 3a).

The sequent type covering the four judgments and the backward
rule-instance enumerator `succs`: for a goal sequent, the list of rule
instances with that conclusion, each given as its premise list.  Pure
definitions — the soundness/completeness round-trip (which yields the
pigeonhole height bound, as `PLLG4Dec` does for G4c) is the next layer.
Zero imports beyond the frozen core.
-/
import LaxLogic.LJFOCore

namespace LJFO

/-- A sequent of any of the four judgments. -/
inductive LSeq where
  | stab (Γ : List Neg) (j : JD) (P : Pos)
  | rfocus (Γ : List Neg) (j : JD) (P : Pos)
  | lfoc (Γ : List Neg) (N : Neg) (j : JD) (P : Pos)
  | inv (Γ : List Neg) (Ω : List Pos) (j : JD) (C : Neg)
deriving DecidableEq

namespace LSeq

/-- Backward rule instances for a stable sequent: right focus, a left
focus per context member, and the truth-to-lax coercion at `lax`. -/
def succsStab (Γ : List Neg) (j : JD) (P : Pos) : List (List LSeq) :=
  [[rfocus Γ j P]]
    ++ Γ.map (fun N => [lfoc Γ N j P])
    ++ (match j with
        | .lax => [[stab Γ .tru P]]
        | .tru => [])

/-- Backward rule instances under right focus, by the positive's shape. -/
def succsRFocus (Γ : List Neg) (j : JD) : Pos → List (List LSeq)
  | .atom a => if Neg.up (Pos.atom a) ∈ Γ then [[]] else []
  | .fls => []
  | .or P Q => [[rfocus Γ j P], [rfocus Γ j Q]]
  | .down N => [[inv Γ [] j N]]

/-- Backward rule instances under left focus, by the hypothesis's shape;
`circL` is the lax-only box opening. -/
def succsLFoc (Γ : List Neg) (j : JD) (P : Pos) : Neg → List (List LSeq)
  | .up Q => [[inv Γ [Q] j (.up P)]]
  | .imp Q N => [[stab Γ .tru Q, lfoc Γ N j P]]
  | .and M N => [[lfoc Γ M j P], [lfoc Γ N j P]]
  | .circ Q =>
      match j with
      | .lax => [[inv Γ [Q] .lax (.up P)]]
      | .tru => []

/-- Backward rule instances in inversion: the goal-driven rules (`impR`
and `andR` at `tru`, `circR` at either flag, `stable` at an empty list
and a shifted goal) together with the `Ω`-head rules. -/
def succsInv (Γ : List Neg) (Ω : List Pos) (j : JD) (C : Neg) :
    List (List LSeq) :=
  (match C, j with
    | .imp Q N, .tru => [[inv Γ (Q :: Ω) .tru N]]
    | .and M N, .tru => [[inv Γ Ω .tru M, inv Γ Ω .tru N]]
    | .circ P, _ => [[inv Γ Ω .lax (.up P)]]
    | _, _ => [])
  ++ (match Ω, C with
    | [], .up P => [[stab Γ j P]]
    | _, _ => [])
  ++ (match Ω with
    | [] => []
    | X :: Ω' =>
        match X with
        | .or P Q => [[inv Γ (P :: Ω') j C, inv Γ (Q :: Ω') j C]]
        | .fls => [[]]
        | .down M => [[inv (M :: Γ) Ω' j C]]
        | .atom a => [[inv (Neg.up (Pos.atom a) :: Γ) Ω' j C]])

/-- The enumerator. -/
def succs : LSeq → List (List LSeq)
  | stab Γ j P => succsStab Γ j P
  | rfocus Γ j P => succsRFocus Γ j P
  | lfoc Γ N j P => succsLFoc Γ j P N
  | inv Γ Ω j C => succsInv Γ Ω j C

end LSeq

/-- Derivability of a sequent, uniformly over the four judgments — the
target of the search round-trip. -/
def LSeq.holds : LSeq → Type
  | .stab Γ j P => Stab Γ j P
  | .rfocus Γ j P => RFocus Γ j P
  | .lfoc Γ N j P => LFoc Γ N j P
  | .inv Γ Ω j C => Inv Γ Ω j C

end LJFO
