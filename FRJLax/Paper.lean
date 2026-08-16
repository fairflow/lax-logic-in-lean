/-
# FRJ◯ — the paper's own refutations, replayed as kernel-checked terms

The W2 screen (`docs/frj-lax-plan.md` §6, round A), in the corpus-replay
direction of the counterexample mandate: before any soundness proof is
scoped, the rule table is tested by building **the paper's own worked
refutations** in it.  If a side condition has been mis-transcribed, the
paper's derivation does not type-check.

The example is Example 3.6 of Fiorentini–Ferrari (ACM TOCL 21(3), 2020),
with

    G = (p ∧ H) ⊃ (q₁ ∨ q₂),        H = p ⊃ q₁ ∨ q₂

which the paper uses to show that the unsound rule `R∨` of the
introduction cannot be simulated, and then, in Example 3.15, that an
irregular sequent carrying the *valid* goal `G` on the right is
nevertheless refutable — the trap that the soundness property (SIRR)
exists to close.  It is the discriminating cell of the corpus.

Imports: `FRJLax.Calculus` and nothing else.
-/
import FRJLax.Calculus

namespace FRJLax
namespace Paper36

/-! ## The goal formula and its subformula sets

The paper: `Sf^L(G) = {p ∧ H, H, q₁∨q₂, p, q₁, q₂}` and
`Sf^R(G) = {G, q₁∨q₂, p, q₁, q₂}`. -/

def p : Form := .atom "p"
def q₁ : Form := .atom "q1"
def q₂ : Form := .atom "q2"
def H : Form := .imp p (.or q₁ q₂)
def G : Form := .imp (.and p H) (.or q₁ q₂)

/-- `Sf^L(G)` is the paper's, on the nose. -/
example : sfL G = [.and p H, p, H, .or q₁ q₂, q₁, q₂] := by decide

/-- `Sf^R(G)` is the paper's, on the nose. -/
example : sfR G = [G, p, .or q₁ q₂, q₁, q₂] := by decide

/-- `Ĝ_at = {p, q₁, q₂}` and `Ĝ_imp = {H}`. -/
example : gAt G = [p, q₁, q₂] := by decide
example : gImp G = [H] := by decide

/-! ## The three irregular axioms

The paper displays `· ; p, q₂, H → q₁`, `· ; p, q₁, H → q₂` and
`· ; q₁, q₂, H → p`.  Each is `Ax^→` at its own `F`, and the `Θ` the rule
computes is exactly the one displayed. -/

/-- `· ; p, q₂, H → q₁`. -/
def axq₁ : FRJi G [] [p, q₂, H] q₁ :=
  .axI (by decide) (by decide) (by decide) (by decide)

/-- `· ; p, q₁, H → q₂`. -/
def axq₂ : FRJi G [] [p, q₁, H] q₂ :=
  .axI (by decide) (by decide) (by decide) (by decide)

/-- `· ; q₁, q₂, H → p`. -/
def axp : FRJi G [] [q₁, q₂, H] p :=
  .axI (by decide) (by decide) (by decide) (by decide)

/-! ## `⋈^∨` with two premises: `p ⇒ q₁ ∨ q₂`

The paper: "the side conditions (J1) and (J2) trivially hold, since the
`Σ`-sets of the premises are empty.  In the conclusion, `H` is left out
since it is not supported (no premise has `p` in the right)."

That is the `restrict` operator doing its work: `H = p ⊃ (q₁ ∨ q₂)` and
`p ∉ Υ = {q₁, q₂}`, so `Θ^⊃ = ∅`. -/

/-- The conclusion context the rule computes is exactly `{p}` — `H`
dropped, as the paper says. -/
example : joinCtxOr [⟨[], [p, q₂, H], q₁⟩, ⟨[], [p, q₁, H], q₂⟩] = [p] := by decide

/-- `p ⇒ q₁ ∨ q₂`. -/
def refuteP : FRJr G [p] (.or q₁ q₂) :=
  .joinOr (.cons axq₁ (.one axq₂))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## `⋈^∨` with three premises: `H ⇒ q₁ ∨ q₂`

The paper: "In the conclusion, `p` is omitted since it does not occur as
left formula in the right-most premise."  Now `p ∈ Υ`, so `H` survives
the restriction, while `Θ^At` loses `p` to the intersection. -/

/-- The conclusion context the rule computes is exactly `{H}`. -/
example :
    joinCtxOr [⟨[], [p, q₂, H], q₁⟩, ⟨[], [p, q₁, H], q₂⟩, ⟨[], [q₁, q₂, H], p⟩]
      = [H] := by decide

/-- `H ⇒ q₁ ∨ q₂`. -/
def refuteH : FRJr G [H] (.or q₁ q₂) :=
  .joinOr (.cons axq₁ (.cons axq₂ (.one axp)))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## `∨` then `⊃∈`: the irregular sequent carrying the valid goal

Example 3.15.  The `∨` rule gives `· ; p, H → q₁ ∨ q₂`, and `⊃∈`
irregular shifts `Λ = {p, H}` across the semicolon, giving

    p, H ; ·  →  (p ∧ H) ⊃ (q₁ ∨ q₂)

whose right formula `G` is VALID.  The paper: "At first sight, this
contradicts the soundness of the calculus… Actually, we conclude that the
hypothesis of the soundness property (SIRR) does not hold, namely, `σ₁`
cannot be used to derive in `FRJ(G)` a regular sequent."

So this refutation *must* exist, and the W3 statement of (SIRR) must be
the one that survives it.  A formalisation in which this term fails to
type-check has mis-stated the rules; one in which the corresponding
regular sequent is derivable has mis-stated the calculus. -/

/-- `Θ₁ ∩ Θ₂ = {p, H}`. -/
example : cap [p, q₂, H] [p, q₁, H] = [p, H] := by decide

/-- `· ; p, H → q₁ ∨ q₂`. -/
def orStep : FRJi G [] [p, H] (.or q₁ q₂) :=
  .orI axq₁ axq₂ (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `p, H ; · → (p ∧ H) ⊃ (q₁ ∨ q₂)`, the sequent of Example 3.15.
`Λ = {p, H}`, and the side condition `A ∈ Cl(Σ ∪ Λ)` holds because
`p ∧ H ∈ Cl({p, H})` by the `X ∧ X` clause of the closure grammar. -/
def refuteG : FRJi G [p, H] [] G :=
  .impInI (Λ := [p, H]) orStep
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## What this screen establishes

Four constructors exercised — `axI`, `orI`, `impInI`, `joinOr` — and with
them `interAll`, `restrict`, `atPart`/`impPart`, `cap`, `rm`, `ups` and
both join conclusion contexts.  Every computed context agrees with the
paper's displayed sequent **by `decide`**, including the two the paper
comments on: `H` dropped from `p ⇒ q₁ ∨ q₂` for want of support, and `p`
dropped from `H ⇒ q₁ ∨ q₂` by the `Θ^At` intersection.

Not yet exercised, and owed before W3 closes: `axR`, `andR₁`/`andR₂`,
`andI₁`/`andI₂`, `impInR`, `impNotIn`, `joinAt`. -/

end Paper36

/-! # The `∧` and `⊃∈`-regular example of Section 3

The paper motivates the side condition `A ∈ Cl(Γ)` of `⊃∈` with the goal
`G = p₁ ∧ p₂ ⊃ q`: with the naive side condition `A ∈ Γ` the calculus
cannot refute it, because "the formula `p₁ ∧ p₂` is not allowed in the
left of sequents"; with `A ∈ Cl(Γ)` it can, in two steps.  This is the
smallest cell that exercises `Ax^⇒` and `⊃∈` regular. -/

namespace Paper3Imp

def p₁ : Form := .atom "p1"
def p₂ : Form := .atom "p2"
def q : Form := .atom "q"
def G : Form := .imp (.and p₁ p₂) q

example : sfL G = [.and p₁ p₂, p₁, p₂] := by decide
example : sfR G = [G, q] := by decide
example : gAt G = [p₁, p₂] := by decide

/-- `Ax^⇒`: `p₁, p₂ ⇒ q`. -/
def axq : FRJr G [p₁, p₂] q :=
  .axR (by decide) (by decide) (by decide)

/-- `⊃∈`: `p₁, p₂ ⇒ p₁ ∧ p₂ ⊃ q`, the paper's displayed refutation, with
its side condition `p₁ ∧ p₂ ∈ Cl({p₁, p₂})`. -/
def refute : FRJr G [p₁, p₂] G :=
  .impInR axq (by decide) (by decide)

/-- Hence `⊢_FRJ(G) G`: a `Refutation` is data, and here is one. -/
def refutation : Refutation G := ⟨[p₁, p₂], refute⟩

theorem provable : Provable G := .intro refutation

end Paper3Imp

/-! # A conjunctive goal: the `∧` rules

The smallest cells exercising `∧` in both polarities.  `G = q₁ ∧ q₂` has
`Ĝ = ∅`, so both axioms have empty contexts and the `∧` rules simply
weaken the goal. -/

namespace AndCell

def q₁ : Form := .atom "q1"
def q₂ : Form := .atom "q2"
def G : Form := .and q₁ q₂

example : sfR G = [G, q₁, q₂] := by decide
example : sfL G = [] := by decide
example : gHat G = [] := by decide

/-- `∧` regular, `k = 1`: `· ⇒ q₁` then `· ⇒ q₁ ∧ q₂`. -/
def andR₁ : FRJr G [] G :=
  .andR₁ (.axR (by decide) (by decide) (by decide)) (by decide)

/-- `∧` regular, `k = 2`. -/
def andR₂ : FRJr G [] G :=
  .andR₂ (.axR (by decide) (by decide) (by decide)) (by decide)

/-- `∧` irregular, `k = 1`: `· ; · → q₁` then `· ; · → q₁ ∧ q₂`. -/
def andI₁ : FRJi G [] [] G :=
  .andI₁ (.axI (by decide) (by decide) (by decide) (by decide)) (by decide)

/-- `∧` irregular, `k = 2`. -/
def andI₂ : FRJi G [] [] G :=
  .andI₂ (.axI (by decide) (by decide) (by decide) (by decide)) (by decide)

theorem provable : Provable G := .intro ⟨[], andR₁⟩

end AndCell

/-! # Figure 2: the refutation of Scott's principle

The paper's worked `FRJ(S)`-refutation `D_S` of

    S = ((¬¬p ⊃ p) ⊃ ¬p ∨ p) ⊃ ¬¬p ∨ ¬p          (Example 3.7, Figure 2)

an instance of Scott's principle, equivalent to the Nishimura formula
`N₁₀`, classically valid and not in IPL, with `h(S) = 2`.  Twelve lines,
replayed here one term per line with the paper's own numbering.

This is the branch-coverage half of the W2 screen: it exercises `⋈^At`
and `⊃∉`, the two rules Example 3.6 leaves untouched, and with them
`joinCtxAt`, the `Θ^⊃` restriction at three different `Υ`, and the
`Cl(Γ) \ Cl(Θ)` condition in both its positive and its negative part.
Every side condition is discharged by `decide`, and every conclusion
context is the paper's displayed sequent up to membership. -/

namespace PaperScott

def p : Form := .atom "p"
/-- `¬p`. -/
def np : Form := .imp p .bot
/-- `¬¬p`. -/
def nnp : Form := .imp np .bot
/-- `¬¬p ⊃ p`. -/
def nnpp : Form := .imp nnp p
/-- `H = (¬¬p ⊃ p) ⊃ (¬p ∨ p)`. -/
def H : Form := .imp nnpp (.or np p)
/-- `S = H ⊃ (¬¬p ∨ ¬p)`. -/
def S : Form := .imp H (.or nnp np)

/-! The paper displays `Sf^L(S) = {H, ¬p ∨ p, ¬¬p, ¬p, p}` and
`Sf^R(S) = {S, ¬¬p ∨ ¬p, ¬¬p ⊃ p, ¬¬p, ¬p, p, ⊥}`.  Ours agree, with two
presentational differences that cost nothing: the lists carry repeated
occurrences (they are lists, and everything downstream is up to
membership), and `Sf^L(S)` additionally contains `⊥`, which the paper's
display elides — `¬p = p ⊃ ⊥` is a left subformula, so `⊥` is one too.
`⊥` lies in neither zone (`Ĝ_at = Sf^L ∩ PV`, `Ĝ_imp = Sf^L ∩ Fm⊃`), so
it never enters a context. -/

example : ∀ X ∈ sfL S, X ∈ [H, .or np p, nnp, np, p, Form.bot] := by decide
example : ∀ X ∈ [H, Form.or np p, nnp, np, p, Form.bot], X ∈ sfL S := by decide
example : ∀ X ∈ sfR S, X ∈ [S, .or nnp np, nnpp, nnp, np, p, Form.bot] := by decide
example : ∀ X ∈ [S, Form.or nnp np, nnpp, nnp, np, p, Form.bot], X ∈ sfR S := by decide

/-- `Ĝ_at = {p}` and `Ĝ_imp = {H, ¬¬p, ¬p}`. -/
example : gAt S ≐ [p] := by decide
example : gImp S ≐ [H, nnp, np] := by decide

/-! ## Iteration 0: the axioms -/

/-- (1) `· ; p, H, ¬¬p, ¬p → ⊥`. -/
def s₁ : FRJi S [] [p, H, nnp, np] .bot :=
  .axI (by decide) (by decide) (by decide) (by decide)

/-- (2) `· ; H, ¬¬p, ¬p → p`. -/
def s₂ : FRJi S [] [H, nnp, np] p :=
  .axI (by decide) (by decide) (by decide) (by decide)

/-! ## Iteration 1 -/

/-- (3) `p ; H, ¬¬p, ¬p → ¬p`, by `⊃∈` from (1), shifting `Λ = {p}`. -/
def s₃ : FRJi S [p] [H, nnp, np] np :=
  .impInI (Λ := [p]) s₁ (by decide) (by decide) (by decide) (by decide) (by decide)

/-- (4) `¬¬p ; H, ¬p → (¬¬p ⊃ p)`, by `⊃∈` from (2), shifting `Λ = {¬¬p}`. -/
def s₄ : FRJi S [nnp] [H, np] nnpp :=
  .impInI (Λ := [nnp]) s₂ (by decide) (by decide) (by decide) (by decide) (by decide)

/-- (5) `¬p ⇒ ⊥`, by `⋈^At` from (2), one premise.

`Σ^At = Σ^⊃ = Θ^At = ∅`, and `Θ^⊃ = {H, ¬¬p, ¬p}/{p}` keeps only `¬p`,
whose antecedent is `p`, the right formula of the premise.  So the whole
conclusion context is what the support condition lets through. -/
def s₅ : FRJr S [np] .bot :=
  .joinAt (.one s₂) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-! ## Iteration 2 -/

/-- (6) `p, ¬¬p ⇒ ⊥`, by `⋈^At` from (3).  Now `Υ = {¬p}`, so the
restriction keeps `¬¬p = ¬p ⊃ ⊥` instead, and `Σ^At = {p}` survives. -/
def s₆ : FRJr S [p, nnp] .bot :=
  .joinAt (.one s₃) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- (7) `· ; H → ¬¬p`, by `⊃∉` from (5).

`Θ = {H} ⊆ Cl({¬p}) ∩ Ĝ` — `H` is in the closure by the `A ⊃ X` and
`X ∨ A` clauses of the grammar — while `A = ¬p ∈ Cl({¬p}) \ Cl({H})`. -/
def s₇ : FRJi S [] [H] nnp :=
  .impNotIn (A := np) (B := .bot) s₅ (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-! ## Iteration 3 -/

/-- (8) `· ; H, ¬¬p → ¬p`, by `⊃∉` from (6). -/
def s₈ : FRJi S [] [H, nnp] np :=
  .impNotIn (A := p) (B := .bot) s₆ (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-! ## Iteration 4 -/

/-- (9) `H, ¬¬p ⇒ p`, by `⋈^At` from (4) and (8) — the first join with two
premises.  (J1) needs `Σ₄ = {¬¬p} ⊆ Σ₈ ∪ Θ₈ = {H, ¬¬p}`, (J2) needs the
antecedent of `¬¬p` — namely `¬p` — to be among the premises' right
formulas, and it is, as the right formula of (8). -/
def s₉ : FRJr S [H, nnp] p :=
  .joinAt (.cons s₄ (.one s₈)) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-! ## Iteration 5 -/

/-- (10) `· ; H → (¬¬p ⊃ p)`, by `⊃∉` from (9). -/
def s₁₀ : FRJi S [] [H] nnpp :=
  .impNotIn (A := nnp) (B := p) s₉ (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-! ## Iteration 6 -/

/-- (11) `H ⇒ ¬¬p ∨ ¬p`, by `⋈^∨` from (7), (8) and (10).  `Υ` is now
`{¬¬p, ¬p, ¬¬p ⊃ p}`, which contains both disjuncts, and `H` survives the
restriction because its antecedent `¬¬p ⊃ p` is the right formula of
(10). -/
def s₁₁ : FRJr S [H] (.or nnp np) :=
  .joinOr (.cons s₇ (.cons s₈ (.one s₁₀))) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-! ## Iteration 7 -/

/-- (12) `H ⇒ S`, by `⊃∈` regular from (11), with `H ∈ Cl({H})`. -/
def s₁₂ : FRJr S [H] S :=
  .impInR s₁₁ (by decide) (by decide)

/-- `⊢_FRJ(S) S`: Scott's principle is refuted, and the refutation is
data. -/
def refutation : Refutation S := ⟨[H], s₁₂⟩

theorem provable : Provable S := .intro refutation

end PaperScott

/-! # What the W2 screen covers

Every constructor of the calculus is now exercised by a refutation taken
from the paper:

| constructor | cell |
|---|---|
| `axR` | `Paper3Imp.axq`, `AndCell.andR₁` |
| `axI` | `Paper36.axq₁`, `PaperScott.s₁` |
| `andR₁`, `andR₂` | `AndCell.andR₁`, `AndCell.andR₂` |
| `andI₁`, `andI₂` | `AndCell.andI₁`, `AndCell.andI₂` |
| `orI` | `Paper36.orStep` |
| `impInR` | `Paper3Imp.refute`, `PaperScott.s₁₂` |
| `impInI` | `Paper36.refuteG`, `PaperScott.s₃`, `s₄` |
| `impNotIn` | `PaperScott.s₇`, `s₈`, `s₁₀` |
| `joinAt` | `PaperScott.s₅`, `s₆`, `s₉` |
| `joinOr` | `Paper36.refuteP`, `refuteH`, `PaperScott.s₁₁` |

and with them `interAll`, `restrict` at four different `Υ`, `atPart` and
`impPart`, `cap`, `rm`, `ups`, `joinCtxAt`, `joinCtxOr`, `J1`, `J2`, and
`Clo` in both a positive and a negative position.

**What it does not cover, and what is therefore still owed.**  This is a
positive screen: it shows the table admits what the paper says it admits.
The negative half — that `p, H ⇒ q₁ ∨ q₂` is *not* refutable, which is
what keeps the calculus sound — is an underivability claim, and the
paper proves it from Lemma 3.5(i).  It belongs to W3 and cannot be run
here. -/

/-! ## Axiom audit

The replayed refutations are terms, so their axiom budget is the budget
of the whole chain — the rule table, every side-condition decision
procedure, and `decide` itself.  `Classical.choice` is absent. -/

/-- info: 'FRJLax.PaperScott.refutation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PaperScott.refutation

/-- info: 'FRJLax.PaperScott.provable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PaperScott.provable

/-- info: 'FRJLax.Paper36.refuteG' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Paper36.refuteG

/-- info: 'FRJLax.Paper3Imp.provable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Paper3Imp.provable

end FRJLax
