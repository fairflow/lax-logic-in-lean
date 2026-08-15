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
import LaxLogic.LJFOSearch
import LaxLogic.LJFOBridge
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

/-- Worlds of the extracted model: the stable contexts the derivation
actually visits (a `cyc` re-uses its history occurrence). -/
partial def worldsOf (s : LSeq) : RT → List (List Neg)
  | .cyc => []
  | .mk ks =>
      let here := match s with
        | .stab Γ _ _ => [Unravel.canonCtx Γ]
        | _ => []
      here ++ (List.zip ks s.succs).flatMap fun (k, ps) =>
        if k.1 < ps.length then worldsOf (ps.getD k.1 (LSeq.stab [] .tru .fls)) k.2
        else []

/-- The refutation procedure, end to end: search for a derivation,
check it, extract the model, gate with the VERIFIED checker.  A
`some (t, M, w)` is consumable by `FinCM.not_provable_of_check` — a
kernel-checkable refutation of `Γ ⊢ φ` in PLL. -/
def refute? (Γ : List PLLFormula) (φ : PLLFormula) :
    Option (RT × FinCM × Nat) := Id.run do
  let s : LSeq := .inv (Γ.map negOfO) [] .tru (negOfO φ)
  match find [] s with
  | none => return none
  | some t =>
      if !wf [] s t then return none   -- searcher self-check (control)
      let ws := (worldsOf s t).eraseDups
      if ws.isEmpty then return none
      for strat in [0, 1, 2, 3] do
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

end FRJO
