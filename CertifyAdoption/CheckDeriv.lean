/-
# `checkDeriv` as a Lean certify certifier (stage 2, `docs/outline.md` §7c)

`LJF/OCheckDeriv.lean` (checker and soundness) packaged as
`Certify.Certifier`s and an `Engine`, with the untrusted producer, the
lints, and the exemplars that replace fuelled kernel re-search:

* `edge_rho3_rho4` — `[¬◯⊥] ⊢ ¬◯⊥ ∨ ◯⊥`, the proof-side exemplar of
  `wip/two_sided_pins.lean` (there `laxND_of_searchProves (f := 16)`);
* `probe_or_11_18` — `ρ11 ∨ ρ18 ≡ ρ15`, the calibration cell of
  `wip/rcells_probe.lean` (there `f := 44`, 17.7 s and 30.5 s of kernel
  time at 7.65 GB; here two trees of 208 and 104 nodes).

The tree literals were emitted by `emitTree` below (regenerate with
`#eval emitTree 40 g`); the emitter is untrusted, and only `checkDeriv`
judges its output. Each gate is watched rejecting three corruptions: a
wrong rule index, a wrong arity, and a subtree moved to another premise.
-/
import LJF.OCheckDeriv
import LaxLogic.RN.Rho
import LaxLogic.Interd
import CertifyAdoption

open PLLND PLLFormula LJFO Certify

namespace CertifyAdoption.CheckDeriv

/-! ## The certifiers -/

/-- At `u = 1`: the property is the derivation type itself. -/
def derivCertifier : Certifier LSeq DerivTree LSeq.holds :=
  ⟨checkDeriv, provable_of_checkDeriv⟩

/-- At `u = 0`, for PLL. -/
def laxNDCertifier :
    Certifier (List PLLFormula × PLLFormula) DerivTree (fun s => Nonempty (LaxND s.1 s.2)) :=
  ⟨fun s t => checkDeriv (decideSeq s.1 s.2) t, fun _ _ h => laxND_of_checkDeriv h⟩

/-! ## The producer (untrusted, compiled) -/

/-- Depth-bounded backward search emitting a tree; `partial`, unproved. -/
partial def emitAt : Nat → LSeq → Option DerivTree
  | 0, _ => none
  | n + 1, s =>
    let rec kids : List LSeq → Option (List DerivTree)
      | [] => some []
      | p :: ps => do let t ← emitAt n p; let ts ← kids ps; pure (t :: ts)
    ((LSeq.succs s).zipIdx).findSome? fun (ps, i) => (kids ps).map (.node i)

/-- Iterative deepening up to the budget `b`: a cheap bound supplied at
call time, never computed from the sequent space (R1). -/
def emitTree (b : Nat) (s : LSeq) : Option DerivTree :=
  (List.range (b + 1)).findSome? fun d => emitAt d s

/-- The engine: no refutation side here (that is `countermodel`). -/
def derivEngine : Engine LSeq DerivTree Empty LSeq.holds where
  yes := derivCertifier
  no := .empty
  produce s b := match emitTree b s with
    | some t => .pass t
    | none => .flag

/-! ## The lints -/

/-- info: R3 passes: the evaluation path of derivCertifier is structural -/
#guard_msgs in #certify_structural derivCertifier

/-- info: R3 passes: the evaluation path of laxNDCertifier is structural -/
#guard_msgs in #certify_structural laxNDCertifier

/-- info: R3 passes: the evaluation path of derivEngine is structural -/
#guard_msgs in #certify_structural derivEngine

/-- info: R2 passes: the property of derivCertifier mentions no budget -/
#guard_msgs in #certify_statement derivCertifier

/-- info: R2 passes: the property of laxNDCertifier mentions no budget -/
#guard_msgs in #certify_statement laxNDCertifier

/-- info: R2 passes: the property of derivEngine mentions no budget -/
#guard_msgs in #certify_statement derivEngine

/-- info: R1: nothing to report on emitTree -/
#guard_msgs in #certify_domain emitTree

/-! ## Corruptions, for the negative tests -/

/-- Wrong rule index at the root. -/
def badIndex : DerivTree → DerivTree
  | .node i ks => .node (i + 1) ks

/-- Wrong arity at the root: one subtree too many. -/
def badArity : DerivTree → DerivTree
  | .node i ks => .node i (ks ++ [.node 0 []])

/-- A subtree moved to another premise: the first two subtrees of the
first node with at least two are swapped. -/
def swapKids : DerivTree → DerivTree
  | .node i (a :: b :: ks) => .node i (b :: a :: ks)
  | .node i [a] => .node i [swapKids a]
  | t => t

/-! ## Exemplar 1: `[¬◯⊥] ⊢ ¬◯⊥ ∨ ◯⊥` (was `f := 16`) -/

def oBot : PLLFormula := .somehow .falsePLL
def nOBot : PLLFormula := .ifThen oBot .falsePLL

def treeEdge : DerivTree :=

    (.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 2 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [])])])])])])]),
    (.node 0 [(.node 0 [])])])])])])])])])])])

theorem edge_rho3_rho4 : Nonempty (LaxND [nOBot] (.or nOBot oBot)) :=
  laxNDCertifier.verdict ([nOBot], .or nOBot oBot) treeEdge

example : checkDeriv (decideSeq [nOBot] (.or nOBot oBot)) (badIndex treeEdge) = false := by
  decide +kernel
example : checkDeriv (decideSeq [nOBot] (.or nOBot oBot)) (badArity treeEdge) = false := by
  decide +kernel
example : checkDeriv (decideSeq [nOBot] (.or nOBot oBot)) (swapKids treeEdge) = false := by
  decide +kernel

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  laxNDCertifier.check ([nOBot], nOBot ∨ oBot) (swapKids treeEdge) = true
is false
-/
#guard_msgs in
example : Nonempty (LaxND [nOBot] (.or nOBot oBot)) :=
  laxNDCertifier.verdict ([nOBot], .or nOBot oBot) (swapKids treeEdge)

/-! ## Exemplar 2: `ρ11 ∨ ρ18 ≡ ρ15` (was `f := 44`, 17.7 s + 30.5 s) -/

open RhoOrder in
def treeOr : DerivTree :=

    (.node 0 [(.node 1 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 2 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [(.node 0 [(.node 5 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 2 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [])])])])])])]),
    (.node 0 [(.node 0 [])])])])])])])])])])])])])])])])])]),
    (.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [])])])])])])])])])]),
    (.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 2 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [])])])])])])]),
    (.node 0 [(.node 0 [])])])])])])])])])])])])])])])])])])])])])])])]),
    (.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 2 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [(.node 0 [(.node 5 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 2 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [])])])])])])]),
    (.node 0 [(.node 0 [])])])])])])])])])])])])])])])])])])]),
    (.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [])])])])])])])])])]),
    (.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 2 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [])])])])])])]),
    (.node 0 [(.node 0 [])])])])])])])])])])])])])])])])])])])])])])])]),
    (.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [(.node 0 [(.node 2 [(.node 0 [(.node 0 [(.node 0 [(.node 5 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 2 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [])])])])])])]),
    (.node 0 [(.node 0 [])])])])])])])])])])])])])])])])])])])])])])])])]),
    (.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [(.node 0 [(.node 3 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 2 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [])])])])])])]),
    (.node 0 [(.node 0 [])])])])])])])])]),
    (.node 0 [(.node 0 [])])])])])])])])])])])])])])])])])])])])])])])])])])])

open RhoOrder in
def treeOrBack : DerivTree :=

    (.node 0 [(.node 1 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 2 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [(.node 0 [(.node 5 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 2 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [])])])])])])]),
    (.node 0 [(.node 0 [])])])])])])])])])])])])])])])])])]),
    (.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [])])])])])])])])])]),
    (.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 2 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [])])])])])])]),
    (.node 0 [(.node 0 [])])])])])])])])])])])])])])])])])])])])])])])]),
    (.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 1 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [(.node 0 [(.node 2 [(.node 0 [(.node 0 [(.node 0 [(.node 5 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 2 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 0 [(.node 1 [(.node 0 [(.node 0 [])])])])])])]),
    (.node 0 [(.node 0 [])])])])])])])])])])])])])])])])])])])])])])])])])])])])])])])

open RhoOrder in
theorem probe_or_11_18 : PLLND.SemUI.Interd ((rhoF 11).or (rhoF 18)) (rhoF 15) :=
  ⟨laxNDCertifier.verdict ([(rhoF 11).or (rhoF 18)], rhoF 15) treeOr,
   laxNDCertifier.verdict ([rhoF 15], (rhoF 11).or (rhoF 18)) treeOrBack⟩

open RhoOrder in
example : checkDeriv (decideSeq [(rhoF 11).or (rhoF 18)] (rhoF 15)) (badIndex treeOr) = false := by
  decide +kernel
open RhoOrder in
example : checkDeriv (decideSeq [(rhoF 11).or (rhoF 18)] (rhoF 15)) (badArity treeOr) = false := by
  decide +kernel
open RhoOrder in
example : checkDeriv (decideSeq [(rhoF 11).or (rhoF 18)] (rhoF 15)) (swapKids treeOr) = false := by
  decide +kernel
open RhoOrder in
example : checkDeriv (decideSeq [rhoF 15] ((rhoF 11).or (rhoF 18))) (swapKids treeOrBack) = false := by
  decide +kernel

/-! ## Pins -/

/-- info: 'CertifyAdoption.CheckDeriv.edge_rho3_rho4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms edge_rho3_rho4

/-- info: 'CertifyAdoption.CheckDeriv.probe_or_11_18' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms probe_or_11_18

end CertifyAdoption.CheckDeriv
