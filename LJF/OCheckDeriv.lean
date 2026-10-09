/-
# LJF◯ — derivation trees as certificates (`checkDeriv`)

The proof side of the two-sided engine without fuel: a derivation tree
is checked against the sequent, instead of the kernel re-running the
fuelled search (`wip/ljfo_link.lean`, `laxND_of_searchProves (f := …)`).
Queued 2026-08-26 (`docs/next-session.md`); built 2026-10-09 as stage 2
of Lean certify (`github.com/fairflow/lean-certify`, `docs/outline.md`
§7c). Statements approved by Matthew (R10, 2026-10-09).

* `DerivTree` — at each node, the index of the rule instance in
  `LSeq.succs s` (the enumerator's one existential, as a listed witness)
  and one subtree per premise of that instance, in order.
* `checkDeriv` — structural on the tree, no fuel.  **Argument order:
  sequent first** (`LSeq → DerivTree → Bool`), departing from the queued
  spec's `Tree → LSeq → Bool` by Matthew's decision, to match the
  spec-first convention of `Certify.Certifier`.
* `provable_of_checkDeriv` — the one soundness result, a `def` (the
  derivation is data: `LSeq.holds` is a type), built from `succs_sound`.
* `laxND_of_checkDeriv` — the same, carried to PLL by `bridge_iff`.

The producer (an untrusted compiled search emitting trees) and the
`Certify.Certifier` packaging live outside this library, in
`CertifyAdoption/CheckDeriv.lean`, so that `LJF` does not depend on
lean-certify.
-/
import LJF.OSearch
import LJF.OBridge
import Meta.Audit

open PLLND

namespace LJFO

/-- A derivation certificate for LJF◯: the index of the rule instance in
`LSeq.succs s`, and one subtree per premise of that instance, in order. -/
inductive DerivTree where
  | node (i : Nat) (kids : List DerivTree)
  deriving Repr, Inhabited

mutual
/-- **The checker**: structural on the tree, no fuel. -/
def checkDeriv : LSeq → DerivTree → Bool
  | s, .node i kids =>
    match (LSeq.succs s)[i]? with
    | some ps => checkKids ps kids
    | none => false

/-- Premise-wise check: one subtree per premise, in order, and no more. -/
def checkKids : List LSeq → List DerivTree → Bool
  | [], [] => true
  | p :: ps, t :: ts => checkDeriv p t && checkKids ps ts
  | _, _ => false
end

namespace LSeq

/-- Premise package for a cons: a derivation of the head and a package for
the tail. -/
def premsCons {p : LSeq} {ps : List LSeq} (d : p.holds) (k : Prems ps) :
    Prems (p :: ps) := fun q hq =>
  if h : q = p then h ▸ d
  else k q ((List.mem_cons.mp hq).resolve_left h)

end LSeq

mutual
/-- **Soundness**: a checked tree rebuilds the derivation. -/
def provable_of_checkDeriv : ∀ (s : LSeq) (t : DerivTree),
    checkDeriv s t = true → s.holds
  | s, .node i kids, h =>
    match hm : (LSeq.succs s)[i]? with
    | some ps =>
      LSeq.succs_sound s ps (List.mem_of_getElem? hm)
        (prems_of_checkKids ps kids (by simpa [checkDeriv, hm] using h))
    | none => absurd h (by simp [checkDeriv, hm])

/-- Premise-wise soundness. -/
def prems_of_checkKids : ∀ (ps : List LSeq) (ts : List DerivTree),
    checkKids ps ts = true → LSeq.Prems ps
  | [], [], _ => LSeq.prems0
  | p :: ps, t :: ts, h =>
    have h' : checkDeriv p t = true ∧ checkKids ps ts = true := by
      simpa [checkKids] using h
    LSeq.premsCons (provable_of_checkDeriv p t h'.1) (prems_of_checkKids ps ts h'.2)
  | [], _ :: _, h => absurd h (by simp [checkKids])
  | _ :: _, [], h => absurd h (by simp [checkKids])
end

/-- The PLL sequent `Γ ⊢ φ` as an LJF◯ goal, under the bridge's
◯-preserving polarisation (as `decideSeq` in `wip/ljfo_link.lean`). -/
def decideSeq (Γ : List PLLFormula) (φ : PLLFormula) : LSeq :=
  .inv (Γ.map negOfO) [] .tru (negOfO φ)

/-- **PLL derivability from a checked tree.** -/
theorem laxND_of_checkDeriv {t : DerivTree} {Γ : List PLLFormula}
    {φ : PLLFormula} (h : checkDeriv (decideSeq Γ φ) t = true) :
    Nonempty (LaxND Γ φ) :=
  (bridge_iff Γ φ).mpr ⟨provable_of_checkDeriv _ t h⟩

end LJFO

/-! ## Pins

Bounds at what `bridge_iff` uses, `[propext, Quot.sound]`; the exact sets
below (`provable_of_checkDeriv` needs only `propext`). -/

#axioms_within LJFO.provable_of_checkDeriv [propext, Quot.sound]
#axioms_within LJFO.laxND_of_checkDeriv [propext, Quot.sound]


/-- info: 'LJFO.provable_of_checkDeriv' depends on axioms: [propext] -/
#guard_msgs in #print axioms LJFO.provable_of_checkDeriv

/-- info: 'LJFO.laxND_of_checkDeriv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms LJFO.laxND_of_checkDeriv
