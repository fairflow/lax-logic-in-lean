/-
# FRJ◯ — the refutation calculus, derived as the DUAL of LJF◯ search

Matthew's /goal (2026-08-15): derive the refutation calculus — (1) the
judgment, (2) refutation completeness, (3) extraction soundness — on
the basis of FRJ extended to ◯, continue to an efficient refutation
procedure, test on the existing corpus.

## The derivation of the rules

LJF◯'s searcher (`LSeq.succs`) enumerates, for each sequent, its rule
INSTANCES — each a list of premises.  A sequent is derivable iff SOME
instance has ALL premises derivable.  Dually:

    a sequent is REFUTED iff EVERY instance has SOME refuted premise.

So the refutation calculus has exactly one rule per instance-shape of
`succs` — that is, one per connective and phase, the FRJ discipline —
and a derivation selects, for each instance, the premise that fails:

  * an instance with NO premises (`init` with the atom present, `flsL`)
    admits no selection: sequents with such an instance are DERIVABLE
    and no refutation tree exists — the checker rejects;
  * a sequent with NO instances (right focus on `fls`; left focus on
    `◯Q` at `tru` — the lax-only condition; `init` with the atom
    absent) is refuted OUTRIGHT: these are the axioms of refutation,
    and each is a per-connective side condition inherited from
    `succs`;
  * `⊃`/`∧`-right at `lax` have no instances by the calculus's own
    flag discipline — their refutations are axioms too, which is
    exactly F&M's "succedent must be ◯-shaped" working for disproof.

## The loop device (FRJ's saturation, as a HISTORY)

Backward, a stable sequent can recur (focus on `↑Q`, re-stabilise to
the same context).  The calculus carries the stable sequents of the
current branch as a HISTORY `H`; the rule

    cyc :  s stable, s ∈ H  ⟹  s refuted

is the coinductive step read inductively: in the extracted MODEL the
recurrence is the same world revisited, so the back-edge closes a
finite loop instead of opening an infinite branch.  Contexts grow
monotonically inside the finite subformula universe and `H` blocks
revisits, so every branch of the SEARCH terminates without any fuel —
the feasible termination argument, replacing `decideFuel`-style bound
arithmetic with canonical-sequent counting.

## Trust architecture (the repo's oracle pattern, unchanged)

A derivation `RT` is FINITE SYNTAX; `wf H s t` is the DECIDABLE
rule-application predicate (per-connective, through `succs`).  The
searcher is untrusted.  Soundness of a concrete refutation is
delivered by EXTRACTION + the verified checker:

    derivation ──extract──▶ FinCM ──FinCM.checkB──▶ not_provable_of_check

so every "refuted" this module emits is kernel-checkable, today.  The
once-and-for-all theorems are STATED below as named propositions and
carried OPEN:

  * `SoundnessFRJO`  — every wf derivation's sequent is LJF◯-underivable
    (with `bridge_iff`, PLL-underivable);
  * `CompletenessFRJO` — every LJF◯-underivable sequent has a wf
    derivation (the pigeonhole/loop-check theorem, item 2).

They are the formal debts of the calculus, kept rigidly distinct from
what is proved per instance.
-/
import LJF.OSearch
import LJF.OBridge
import LaxLogic.PLLCountermodelEmit
import wip.ljfo_unravel

namespace FRJO

open LJFO PLLND

/-! ## 1. Derivations -/

/-- A refutation derivation: for each rule instance of the sequent (in
`succs` order), the index of the refuted premise and its refutation;
or a back-edge to the history. -/
inductive RT : Type where
  | mk (ks : List (Nat × RT)) : RT
  | cyc : RT
deriving Repr, Inhabited

partial def RT.size : RT → Nat
  | .cyc => 1
  | .mk ks => 1 + (ks.map (fun p => p.2.size)).sum

def isStable : LSeq → Bool
  | .stab .. => true
  | _ => false

/-- **The rule-application checker** — the calculus's definition of
validity, one clause per `succs` shape.  Decidable by construction. -/
partial def wf (H : List String) (s : LSeq) : RT → Bool
  | .cyc => isStable s && H.contains (Unravel.seqKey s)
  | .mk ks =>
      let pss := s.succs
      let H' := if isStable s then Unravel.seqKey s :: H else H
      ks.length == pss.length &&
      (List.zip ks pss).all fun (k, ps) =>
        decide (k.1 < ps.length) && wf H' (ps.getD k.1 (LSeq.stab [] .tru .fls)) k.2

/-! ## 2. The searcher (untrusted, terminating by history + universe) -/

partial def find (H : List String) (s : LSeq) : Option RT :=
  if isStable s && H.contains (Unravel.seqKey s) then some .cyc
  else
    let H' := if isStable s then Unravel.seqKey s :: H else H
    let pss := s.succs
    (pss.mapM fun ps =>
      (List.zipIdx ps).findSome? fun (p, i) => (find H' p).map ((i, ·))).map .mk

/-! ## 3. Extraction and the certified verdict -/

/-- Worlds AND `Rₘ`-edges of the extracted model, read off the
derivation: worlds are the stable contexts it visits; an edge is
recorded when the derivation passes through a `circL` instance — the
lax-only box opening — from the nearest enclosing stable context to
each stable context inside that premise.  `par` is that enclosing
context's key ("" at the root). -/
partial def worldsEdgesOf (par : String) (s : LSeq) :
    RT → List (List Neg) × List (String × String)
  | .cyc => ([], [])
  | .mk ks =>
      let (here, par') := match s with
        | .stab Γ _ _ => ([Unravel.canonCtx Γ], Unravel.ctxKey Γ)
        | _ => ([], par)
      let isJump := match s with
        | .lfoc _ (.circ _) .lax _ => true
        | _ => false
      let sub := (List.zip ks s.succs).map fun (k, ps) =>
        if k.1 < ps.length then
          worldsEdgesOf par' (ps.getD k.1 (LSeq.stab [] .tru .fls)) k.2
        else ([], [])
      let ws := here ++ sub.flatMap (·.1)
      let es := sub.flatMap (·.2) ++
        (if isJump && par' != "" then
          (sub.flatMap (·.1)).map fun c => (par', Unravel.ctxKey c)
        else [])
      (ws, es)

def worldsOf (s : LSeq) (t : RT) : List (List Neg) :=
  (worldsEdgesOf "" s t).1

/-- Transitive closure of a pair list (the grafted `Rₘ` edges must be
re-closed or `wellB` rejects the frame). -/
def closePairs (ps : List (Nat × Nat)) : List (Nat × Nat) := Id.run do
  let mut c := ps.eraseDups
  let mut changed := true
  while changed do
    changed := false
    for (x, y) in c do
      for (y', z) in c do
        if y == y' && x != z && !(c.contains (x, z)) then
          c := (x, z) :: c
          changed := true
  return c

/-- Unfold a positive into the negatives a cone-realising world must
park (the `Cl`-closure step for `◯`, synthesised at assembly).  `side`
biases `∨`-splits.  `none` = the body reaches `fls`: only a FALLIBLE
world can realise it (the leaf strategies' job). -/
partial def unfoldPos (side : Bool) : Pos → Option (List Neg)
  | .atom a => some [.up (.atom a)]
  | .fls => none
  | .or P Q => unfoldPos side (if side then P else Q)
  | .down N => some [N]

/-- One round of cone closure: for each world and each `◯Q` in its
context, the child world parking `Q`'s content, with an `Rₘ`-edge.
Refutation derivations never explore hypothesis truth, so these
worlds are absent from the trace and must be synthesised. -/
def coneCloseRound (side : Bool) (ws : List (List Neg)) :
    List (List Neg) × List (String × String) := Id.run do
  let mut acc := ws
  let mut es : List (String × String) := []
  for c in ws do
    for nn in c do
      match nn with
      | .circ Q =>
          match unfoldPos side Q with
          | some more =>
              let child := Unravel.canonCtx (more ++ c)
              es := (Unravel.ctxKey c, Unravel.ctxKey child) :: es
              if !(acc.contains child) then acc := child :: acc
          | none => pure ()
      | _ => pure ()
  return (acc, es)

def coneClose (side : Bool) (ws : List (List Neg)) :
    List (List Neg) × List (String × String) := Id.run do
  let mut cur := ws
  let mut es : List (String × String) := []
  for _ in [0:3] do
    let (cur', es') := coneCloseRound side cur
    cur := cur'
    es := es' ++ es
  return (cur, es.eraseDups)

/-- The refutation procedure, end to end: search for a derivation,
check it, extract the model, gate with the VERIFIED checker.  A
`some (t, M, w)` is consumable by `FinCM.not_provable_of_check` — a
kernel-checkable refutation of `Γ ⊢ φ` in PLL. -/
inductive Fail where
  | noDeriv | wfReject | gateMiss
deriving Repr, DecidableEq

def Fail.str : Fail → String
  | .noDeriv => "no-derivation" | .wfReject => "wf-reject" | .gateMiss => "gate-miss"

def refute? (Γ : List PLLFormula) (φ : PLLFormula) :
    Option (RT × FinCM × Nat) := Id.run do
  let s : LSeq := .inv (Γ.map negOfO) [] .tru (negOfO φ)
  match find [] s with
  | none => return none
  | some t =>
      if !wf [] s t then return none   -- searcher self-check (control)
      let (ws0, es) := worldsEdgesOf "" s t
      let ws := ws0.eraseDups
      if ws.isEmpty then return none
      -- derivation-directed assembly FIRST: Rm from the circL edges of
      -- the derivation itself, with and without fallible leaves over
      -- the ⊆-maximal worlds; then the generic ladder as fallback
      let keyed := ws.map fun c => (Unravel.ctxKey c, c)
      let idxOf := fun k => (keyed.zipIdx.find? (fun p => p.1.1 == k)).map (·.2)
      let jumpPairs := es.filterMap fun (a, b) => do
        let i ← idxOf a
        let j ← idxOf b
        if i != j then pure (i, j) else none
      -- the ladder: box-carrying leaves first (the semantically right
      -- placement), each with and without the derivation's jump edges
      -- grafted; then cone closure (Cl for ◯) in both ∨-biases; then
      -- the generic completions
      for strat in [4, 0, 2] do
        for graft in [true, false] do
          let base := Unravel.assemble ws strat
          let M : FinCM :=
            if graft then { base with rm := closePairs (jumpPairs ++ base.rm) }
            else base
          for w in List.range M.n do
            if FinCM.checkB M w Γ φ then
              return some (t, M, w)
      for side in [true, false] do
        let (ws', ces) := coneClose side ws
        let keyed' := ws'.map fun c => (Unravel.ctxKey c, c)
        let idxOf' := fun (k : String) =>
          (keyed'.zipIdx.find? (fun p => p.1.1 == k)).map (·.2)
        let conePairs := (ces ++ es).filterMap fun (a, b) => do
          let i ← idxOf' a
          let j ← idxOf' b
          if i != j then pure (i, j) else none
        for strat in [4, 0] do
          let base := Unravel.assemble ws' strat
          let M : FinCM := { base with rm := closePairs (conePairs ++ base.rm) }
          for w in List.range M.n do
            if FinCM.checkB M w Γ φ then
              return some (t, M, w)
      for strat in [1, 3] do
        let M := Unravel.assemble ws strat
        for w in List.range M.n do
          if FinCM.checkB M w Γ φ then
            return some (t, M, w)
      return none

/-! ## 4. The formal debts, stated -/

/-- **Item 3, once and for all (OPEN)**: validity of a refutation
derivation entails LJF◯-underivability of its sequent. -/
def SoundnessFRJO : Prop :=
  ∀ (s : LSeq) (t : RT), wf [] s t = true → IsEmpty s.holds

/-- **Item 2 (OPEN)**: every LJF◯-underivable sequent has a
refutation derivation — the pigeonhole/loop-check theorem. -/
def CompletenessFRJO : Prop :=
  ∀ s : LSeq, IsEmpty s.holds → ∃ t : RT, wf [] s t = true

/-- Diagnostic verdict: which stage failed. -/
def diagnose (Γ : List PLLFormula) (φ : PLLFormula) : Sum (RT × FinCM × Nat) Fail :=
  Id.run do
    let s : LSeq := .inv (Γ.map negOfO) [] .tru (negOfO φ)
    match find [] s with
    | none => return .inr .noDeriv
    | some t =>
        if !wf [] s t then return .inr .wfReject
        match refute? Γ φ with
        | some r => return .inl r
        | none => return .inr .gateMiss

end FRJO
