# P2LL definability: status note (tracked)

Campaign: P2LL (second-order propositional lax logic, `PLL2` in
`docs/pll2-plan.md`) and the definability of ◯ by a relativised quantifier ∀°.
Branch `p2ll-definability`, cut from `origin/main` at 667fa6d (PR #87), local
only, never pushed.  Worktree `.claude/worktrees/p2ll-definability`, `.lake`
seeded by `cp -Rc` from `agent-ad132f5974d72ca18`.  This note is tracked so that
a pause cannot lose it (the first worktree, `agent-a646e46446b1a3307`, was
removed at a restart together with its untracked note).

Status labels as in `docs/pll2-plan.md`: PROVED / REFUTED / OPEN.  Nothing in
this note is PROVED until the file named next to it builds with its pins.

## 1. The question (Matthew's)

The plan's Proposition C,

    ◯φ  ⊣⊢  ∀°p.((φ → p) → p),        ∀°p.ψ := ∀p.((◯p → p) → ψ),

is a characterisation, not a definition: the guard mentions ◯.  Wanted: a
calculus with a PRIMITIVE relativised quantifier ∀° and no ◯, in which

    ◯φ := ∀°q.((φ → q) → q)

satisfies the PLL rules; conversely P2LL (◯ primitive) interprets ∀°; the two
systems mutually interpretable, derivability preserved both ways.

Algebraic guide (`wip/f0MacNeille.lean`, Goldblatt 2011 §2): in a complete
Heyting algebra the fixed-point set `Fix(j)` of a nucleus is exactly a subset
closed under arbitrary meets and under `x ↠ (−)`, and then
`j x = ⋀{s ∈ Fix(j) : x ≤ s}`.  So ∀° ranges over a class J of propositions
closed under ⊤, ∧, ∀, ∀° and `φ → (−)`; J-variables range over Fix(j).

## 2. Design (decided; Matthew sees it at the statements report)

### 2.1 One formula type, locally nameless (plan §6.1)

    P2LL.Fm ::= fvar s | bvar n | bot | and φ ψ | or φ ψ | imp φ ψ | circ φ | all ψ | allJ ψ

String atoms, Nat indices, bare inductive (no `Fin`).  P2LL formulas are the
`allJ`-free ones, the guarded calculus's formulas the `circ`-free ones
(predicates `allJFree`, `circFree`).  Each calculus has NO rule for the other's
connective, which is inert in it.  One type saves duplicating the binder layer
(plan §7 names that layer as the biggest risk); the syntax module is kept small
so that a switch to two types is cheap if Matthew asks for it.

* `openRec k u`; `ψ.opn u := openRec 0 u ψ` opens the outermost binder.
* `lcAt k : Fm → Prop`, BOUNDED (QLL `Lc.lean` style: no loose index ≥ k);
  `LC := lcAt 0`; decidable by structural recursion.  Not the cofinite `LC`
  of Charguéraud, so `openRec_lcAt : lcAt k φ → openRec k u φ = φ` needs no
  fresh-name supply.
* `shiftAt d` raises the indices ≥ d by one.  Needed at exactly one place:
  `◯φ ↦ ∀°q.((φ → q) → q)` puts φ under a NEW binder (otherwise
  `toJ (all (circ (bvar 0)))` captures).  `rel` (∀° ↦ relativised ∀) replaces
  a binder by a binder and needs no shift.
* `rpBody φ := imp (imp (shiftAt 0 φ) (bvar 0)) (bvar 0)`;
  `circJ φ := allJ (rpBody φ)`   the DEFINED ◯ of the guarded calculus;
  `rp φ    := all  (rpBody φ)`   Aczel's RP (plain ∀);
  `allNuc ψ := all (imp (imp (circ (bvar 0)) (bvar 0)) ψ)`   P2LL's ∀°p.ψ;
  `circNuc φ := allNuc (rpBody φ)`   P2LL's ∀°p.((φ → p) → p).
  For `LC φ`: `(rpBody φ).opn u = imp (imp φ u) u`.
* Translations: `toJ` (°): `circ φ ↦ circJ (toJ φ)`, homomorphic elsewhere;
  `rel` (*): `allJ ψ ↦ allNuc (rel ψ)`, homomorphic elsewhere;
  `guards Θ := Θ.map (fun s => imp (circ (fvar s)) (fvar s))`.

### 2.2 The guarded calculus `JND`

The J-sort of a variable lives in the JUDGEMENT, not in the variable:

    JND (J : List String → Fm → Prop) : List String → List Fm → Fm → Type
    JND J Θ Γ φ   "under J-declarations Θ and hypotheses Γ, φ"

Rules: the IPC rules of `PLLND.LaxND` (membership `iden`, no structural rules),
and

    allIntro  (L : List String) (∀ s, s ∉ L → JND J Θ Γ (ψ.opn (fvar s))) : JND J Θ Γ (all ψ)
    allElim   (LC χ) (JND J Θ Γ (all ψ)) (θ = ψ.opn χ) : JND J Θ Γ θ
    allJIntro (L) (∀ s, s ∉ L → JND J (s :: Θ) Γ (ψ.opn (fvar s))) : JND J Θ Γ (allJ ψ)
    allJElim  (LC χ) (J Θ χ) (JND J Θ Γ (allJ ψ)) (θ = ψ.opn χ) : JND J Θ Γ θ

Elimination in the slime-free equation form (QLL `Prv.allE`).  Admissible:
`rename` (context membership), `weaken`, `weakenΘ` (for J monotone in Θ).
The relativisation translation sends Θ to `guards Θ`.  Variables are untagged,
so both translations are the identity on atoms.

The `LC χ` side condition is NECESSARY: without it `⊢ ⊥` (cell C5).

### 2.3 The J-grammar `IsJ Θ : Fm → Prop` (syntactic, Θ-relative)

    IsJ Θ (fvar s)     if s ∈ Θ
    IsJ Θ ⊤            (⊤ := imp bot bot; its own clause, since ⊥ ∉ J)
    IsJ Θ (imp φ ψ)    if IsJ Θ ψ
    IsJ Θ (and φ ψ)    if IsJ Θ φ and IsJ Θ ψ
    IsJ Θ (all ψ)      if ∀ s ∉ L, IsJ Θ (ψ.opn (fvar s))
    IsJ Θ (allJ ψ)     if ∀ s ∉ L, IsJ (s :: Θ) (ψ.opn (fvar s))

Each clause is a closure property of `Fix(j)`: ⊤ and ∧ (finite meets), ∀ and
∀° (arbitrary meets), `φ → (−)` (`nucleus_himp_fix`, `wip/f0MacNeille.lean`).
Excluded: ⊥ (`◯⊥ → ⊥` fails at the fallible model) and ∨ (cell C6).  A
"semantic" J (χ ∈ J iff Γ ⊢ ◯°χ → χ) would be the characterisation again, so it
is rejected.  Load-bearing for the J-side round trip: `fvar`, `imp`, `allJ`
(to instantiate at `circJ (fvar s)`); `top`, `and`, `all` are there for the
algebra.

### 2.4 P2LL itself: `LaxND2`

`PLLND.LaxND`'s rules plus `laxIntro`/`laxElim` plus `allIntro`/`allElim`
(as above, no Θ).  `IPC2ND : Prop` is the same without the lax rules: the
◯-free fragment, the target of rule 8.

## 3. Cells (rule 8: fragment first), files `wip/p2ll*.lean`

F1  IPC2ND, LC φ:  `[φ] ⊢ rp φ` and `[rp φ] ⊢ φ`.  Aczel's RP is the IDENTITY
    nucleus in IPC2; the plan's Props A and B reduce to the unit law and to
    `◯φ ⊬ φ`.  (The identity is the ◯-free instance of the defined ◯.)
F2  `JND (fun _ _ => True) Θ [circJ φ] φ`: with the guard dropped entirely the
    defined ◯ collapses to the identity (instance of C3).
C1  unit:  `JMono J → LC φ → JND J Θ Γ φ → JND J Θ Γ (circJ φ)`.
C2  bind:  `JMono J → JVars J → LC φ → LC ψ → JND J Θ Γ (circJ φ) →
           JND J Θ (φ :: Γ) (circJ ψ) → JND J Θ Γ (circJ ψ)`.
    Only J-VARIABLE instances are used.  Derived: ◯R, ◯M, ◯S, ◯bind for circJ.
C3  guard drop:  `J Θ χ → LC χ → JND J Θ [circJ χ] χ`: admitting χ to J makes
    χ a fixpoint; instance χ = ⊥.  `¬ IsJ Θ bot`, `¬ IsJ Θ (or φ ψ)`.
C5  LC drop:  `IPC2NoLC [] bot` for the fragment without the side condition:
    `A := ∀p.((∀q.(q → p)) → p)` is provable; A at χ := bvar 0 gives
    `(∀q.(q → q)) → bvar 0`, so `⊢ bvar 0`; `B := ∀p.(p → ∀q.p)` is provable;
    B at bvar 0 gives `bvar 0 → ∀q.q`; so `⊢ ∀q.q`; at ⊥: `⊢ ⊥`.
C6  ∨ excluded, PLL level, kernel-checked on `modelOrSplit` (Frames.lean):
    `⊬ ((◯A ↠ A) ∧ (◯B ↠ B)) ↠ (◯(A ∨ B) ↠ (A ∨ B))`.  Transfer to P2LL waits
    for plan M2 (soundness for second-order models), not built.
C7  Proposition C in P2LL, LC φ:  `[circ φ] ⊢ circNuc φ`, `[circNuc φ] ⊢ circ φ`.

## 4. OPEN statements (`wip/p2llStatements.lean`, `def … : Prop`, no sorry)

    I₁   LaxND2 Γ φ  →  ∀ Θ, JND IsJ Θ (Γ.map toJ) (toJ φ)
    I₂   JND IsJ Θ Γ φ  →  LaxND2 (guards Θ ++ Γ.map rel) (rel φ)
    Fix  IsJ Θ χ → LC χ  →  LaxND2 (guards Θ) (imp (circ (rel χ)) (rel χ))
    RTP  LC φ  →  [φ] ⊢ rel (toJ φ)  and  [rel (toJ φ)] ⊢ φ        (Prop C generalised)
    RTJ  LC φ  →  JND IsJ Θ [φ] (toJ (rel φ))  and  JND IsJ Θ [toJ (rel φ)] φ
    MP   LaxND2 Γ φ  ↔  JND IsJ [] (Γ.map toJ) (toJ φ)              (from I₁, I₂, RTP)
    MJ   JND IsJ Θ Γ φ  ↔  LaxND2 (guards Θ ++ Γ.map rel) (rel φ)   (from I₂, I₁, RTJ)

Not attempted: cut elimination, Girard candidates (plan §4, §6.5).

## 5. Log

* 2026-10-24: design fixed; first worktree lost at a restart; this note
  recreated and committed before any Lean file.
* 2026-10-24 (later): all five modules build by name (`lake build
  wip.p2llStatements` covers Syntax, ND, JND, Statements; `wip.p2llOrCell`
  separately).  Every pin was first run at `[]` and watched failing, then bounded.
  PROVED (kernel-checked): F1 `IPC2ND.rp_intro`, `IPC2ND.rp_elim`;
  F2 `JND.circJ_collapse_unguarded`; C1 `JND.circJ_intro`; C2 `JND.circJ_bind`;
  C3 `JND.circJ_collapse`, `JND.circJ_bot_collapse`, `IsJ.not_bot`, `IsJ.not_or`;
  C5 `IPC2NoLC.inconsistent`; C6 `or_not_fixed` (PLL level); C7
  `LaxND2.circ_to_circNuc`, `LaxND2.circNuc_to_circ`; the derived laws
  `JND.OI`, `JND.OM`, `JND.OS`, `JND.Obind`.
  Pins: `[propext]` wherever `simp`, `rw` or `rcases` is used; `[]` for
  `circFree_toJ`, `allJFree_rel`, `IsJ.not_bot`, `IsJ.not_or` and the seven OPEN
  statements of §4; `[propext, Classical.choice, Quot.sound]` for `or_not_fixed`,
  the ledger's profile of its sibling `PLLND.not_provable_somehow_or_dist`.
  Finding: with `Finset String` for the excluded names of the cofinite rules,
  EVERY declaration mentioning a calculus carried `propext, Quot.sound` (Finset
  membership is a quotient), the Prop-valued statements included; `List String`
  (as QLL's `Prv.allI`) removes both axioms and the Mathlib import.  Switched.
  Two defects caught by the build, both mine, neither in a statement: an
  underdetermined antecedent in C7's `.iden (by simp)`, and a circular
  instantiation `q := s` in C5's derivation of A (now `q := ⊤`).
  §4 unchanged: OPEN.  Design points for Matthew: one formula type with inert
  constructors (vs two types); Aczel's RP is the identity in IPC2 (F1).

## 6. Revision 2 of the rules (2026-10-24, after Matthew's GO): well-formedness

Found while planning I₁, before any proof was built on it (rule 7).

**I₁ was FALSE for the rules of §2.2/§2.4.**  The statements quantify over
all formulas, dangling indices included, and the rules derived ill-formed
sequents: `[bvar 0] ⊢_P2LL ◯(bvar 0)` by `iden`, `laxIntro`.  Its translation
`[bvar 0] ⊢_J ∀°q.((bvar 1 → q) → q)` (the body shifts under the new binder) is
not derivable: the two-element Boolean algebra with ∀ and ∀° as meets over
{0, 1}, `bvar 0 ↦ 1`, `bvar 1 ↦ 0`, satisfies the hypothesis and refutes the
conclusion, and `JND IsJ` is sound for it.  (Derivability half: two rule
applications; refutation half: a paper argument, not mechanised, since no
semantics for `JND` is built.)  The inductive proof of I₁ needs `LC` at every
`laxIntro`/`laxElim` node (C1/C2 need it: for non-closed `φ` the body of `◯°φ`
is `(shiftAt 0 φ → q) → q`, not `(φ → q) → q`), and with the old rules an
inner node could be ill-formed even under a well-formed end-sequent (`impIntro`
on a dangling hypothesis, then a cut through it).

**Repair, uniform principle:** every rule whose conclusion is not locally closed
by virtue of its premises carries the missing closure as a side condition:

    iden      (LC φ)        falsoElim (LC φ)        impIntro (LC φ)   [the discharged hypothesis]
    orIntro1  (LC ψ)        orIntro2  (LC φ)        allIntro, allJIntro (lcAt 1 ψ)   [the body]
    allElim, allJElim (LC χ)   [as before]

in `LaxND2`, `IPC2ND`, `JND` (and `IPC2NoLC`, which keeps all of them except
the one on `∀E`; C5 still derives ⊥, so the cell is sharper).  Consequence,
PROVED: `LaxND2.lc : LaxND2 Γ φ → LC φ` and `JND.lc : JND J Θ Γ φ → LC φ`,
`[propext]` (through `lc_opn`).  The seven statements of §4 are unchanged in
text; their calculi now enforce well-formedness, so they are about locally
closed formulas, as intended.  The cells of §3 all re-prove with `LC` proofs at
the leaves; the `LC` hypotheses of C1–C3 and C7 are now also derivable from
the premises (`lc`) but kept as reported.

**Why `lcAt 1 ψ` on `∀I` rather than a fresh name.**  The condition is
redundant given one fresh name (`lcAt_of_openRec`: an opened body closed at 0
was closed at 1), but a fresh-name supply over `String` is classical in core:
`String.length_push`/`length_append` go through the UTF-8 decoder and
`Classical.propDecidable`, so `freshStr L := (String.join L).push 'x'` with
`freshStr ∉ L` was `[propext, Classical.choice, Quot.sound]` (built and
traced with `#axiom_path`, then dropped).  No fresh name is chosen anywhere in
the development.

**Also found:** plain `simp` decides `0 = k + 1` by `Nat.right_eq_add`, whose
proof is classical; `rel_openRec` and `toJ_openRec` use `simp only` with an
explicit `if_neg`.  Syntax lemmas added for the proofs: `lcAt_shiftAt`,
`shiftAt_openRec`, `lcAt_of_openRec`, `lcAt_toJ`/`lc_toJ`, `lcAt_rel`/`lc_rel`,
`rel_openRec`/`rel_opn` (`(ψ^χ)* = ψ*^χ*`), `toJ_openRec`/`toJ_opn`
(`(ψ^χ)° = ψ°^χ°` for `LC χ`), all `[]` or `[propext]`.

Naming (Matthew): Aczel's operator is RP, `RP(φ) := ∀p.((φ → p) → p)`; the
Lean name `rp` stays; J is the class of J-formulas and the guarded calculus.

## 5. Log (continued)

* 2026-10-24 (GO received): rules revised as in §6 before any theorem was
  built; everything rebuilt and re-pinned (`LaxND2.lc`, `JND.lc` new); report
  to the manager, then wait, per rule 7.
