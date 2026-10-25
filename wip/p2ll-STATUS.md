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

## 7. Phase 2, step 1 (2026-10-24): I₁, Fix, I₂ PROVED (`wip/p2llInterp.lean`)

Theorems (each a `theorem x : X` for the unchanged `def X : Prop` of §4; the
proof is a function on derivations, then packaged as the proposition):

    interpToJ    : InterpToJ      by toJD   (recursion on LaxND2)         [propext]
    fixOfIsJ     : FixOfIsJ       by fixD   (recursion on IsJ)            [propext]
    interpToP2LL : InterpToP2LL   by relD   (recursion on JND IsJ)        [propext]

Each pin was first run at `[]` and failed with `propext, Quot.sound`.
`Quot.sound` came from core's `List.mem_map` (`#print axioms`:
`[propext, Quot.sound]`, as `List.mem_map_of_mem`; `List.mem_append_left`,
`List.mem_append_right`, `List.mem_cons_self`, `List.mem_cons_of_mem` are
axiom-free): replaced by `mem_map_of_mem`, induction on `List.Mem`, `[]`
(`mem_append_cons`, the context step of `∀°I`/`→I` in I₂, likewise `[]`).
`propext` is `Fm.lc_opn`'s, through `LaxND2.lc`/`JND.lc` (the `LC` proofs at
the `◯` nodes of I₁) and the binder cases.

**Representation change, not a statement change.**  `IsJ` and `IPC2ND` are
now `Type`-valued (data), `JND`'s parameter is `J : List String → Fm → Type`,
`JMono`/`JVars` likewise; §2.2–2.4 record the earlier `Prop` wording.  Reason:
Fix is proved by recursion on the J-derivation producing a `LaxND2`
derivation; the cofinite clauses `all`/`allJ` supply one J-derivation per fresh
name and `LaxND2.allIntro` needs one derivation per name, which `Nonempty`
hypotheses give only through choice.  The text of the seven statements is
unchanged: `IsJ Θ χ → …` and `JND IsJ Θ Γ φ → …` are propositions as before.
The ◯-free instance of I₁ (rule 8), IPC2 ⊆ the guarded calculus for every `J`
(`JND.ofIPC2`, `[]`, with `toJ` the identity on ◯-free formulas,
`toJ_eq_self_of_circFree`), needed `IPC2ND` as data for the same reason.

Proof shapes.  I₁: `laxIntro`/`laxElim` are C1/C2 with the `LC` hypotheses
from `LaxND2.lc`; `∀I` rewrites by `toJ_opn_fvar`, `∀E` by `toJ_opn` (`LC χ`
from the rule).  Fix: `var` is the guard `◯s → s ∈ guards Θ`; `top` is
`◯⊤ → ⊤`; `imp` is `◯(φ* → ψ*) → φ* → ψ*` by bind and the IH; `and` by two
binds and both IHs; `all` is `◯∀ψ* → ∀ψ*` by cofinite `∀I` at `s`, `∀E` at `s`
inside a bind, and the IH at `ψ^s` via `rel_opn_fvar`; `allJ` the same with
`→I` on the new guard `◯s → s`, the IH living under `guards (s :: Θ)`, which is
`(◯s → s) :: guards Θ` definitionally.  I₂: `∀°I` is `∀I` plus `→I` on the new
guard; `∀°E` is `∀E` at `χ*` (`rel_opn`), its guard premise discharged by
`fixD` weakened into the context.  Two syntax corollaries added:
`rel_opn_fvar`, `toJ_opn_fvar`.

Files: `wip/p2llInterp.lean` new (in the `wipshared` globs); docstrings of I₁,
Fix, I₂ in `wip/p2llStatements.lean` now say PROVED with the theorem names,
the other four OPEN, statement text byte-identical.  Builds: `lake build
wip.p2llInterp` (covers the chain), 1–2 s per module.  df: 138218 MB free
before, 138205 after.

## 5. Log (continued)

* 2026-10-24 (phase 2, step 1): I₁, Fix, I₂ PROVED, `[propext]`; `IsJ`,
  `IPC2ND` moved to `Type` (§7); checkpoint report to the manager, then RTP,
  substitution of equivalents, RTJ, MP, MJ.

## 8. Phase 2, step 3 (2026-10-24): RTP, RTJ, MP, MJ are REFUTED as stated (`wip/p2llBoolSem.lean`)

Found at the start of step 3, before any proof was built on them (rule 7);
reported to the manager, work stopped there pending the repaired statements.

**The fault is in the statements, not the calculi.**  The four statements
quantify over the whole shared type `Fm` (§2.1: one formula type, each
calculus without rules for the other's connective).  A P2LL formula may
contain `allJ`, inert in `LaxND2`; `(−)°` is the identity on it and `(−)*`
turns it into a relativised `∀` that P2LL CAN use.  Dually for `circ` in the
guarded calculus.  So each round trip fails on formulas outside its fragment:

    RTP   ∀°q.q ⊬_P2LL ∀p.((◯p → p) → p)                         (rtp_fails₁)
          ∀p.((◯p → p) → (p → p)) ⊬_P2LL ∀°q.(q → q)             (rtp_fails₂)
    MP    Γ = [], φ = ∀°q.(q → q):   ⊢_J φ (jd_allJ_refl),  ⊬_P2LL φ (mp_fails)
    RTJ   ◯⊥ ⊬_J ∀°q.((⊥ → q) → q)                                (rtj_fails₁)
          ∀°q.((⊤ → q) → q) ⊬_J ◯⊤                                (rtj_fails₂)
    MJ    Θ = [], Γ = [], φ = ◯⊤:   ⊢_P2LL ◯⊤ (pd_circ_top),  ⊬_J ◯⊤ (mj_fails)

REFUTED, kernel-checked:

    roundTripP2LL_false : ¬ RoundTripP2LL        roundTripJ_false : ¬ RoundTripJ
    mutualP2LL_false    : ¬ MutualP2LL           mutualJ_false    : ¬ MutualJ

**The countermodels.**  A two-valued semantics on the whole type,
`beval : BSem → (String → Bool) → Fm → (Nat → Bool) → Bool`: atoms by a
valuation, indices by an environment, connectives Boolean, `∀` the meet over
`Bool`, and the two connectives inert in one calculus by the parameters of
`BSem`: `SP c` (`circ` the identity, `allJ` the constant `c`) for P2LL, `SJ c`
(`circ` the constant `c`, `allJ` the meet) for the guarded calculus.
Soundness `LaxND2.bsound` (every `S` with `circ = id`) and `JND.bsound` (every
`S` with `allJ` the meet, every class `J`: `∀°E` has full comprehension on
this model), by recursion on the derivation; substitution lemma `beval_opn`
(`beval_openRec` + `insE_zero`); the cofinite `∀I` needs one name outside a
finite list (`fresh`).  I₁, Fix, I₂ hold on the whole type (§7), so nothing of
§7 is touched.

**Pins.**  The environment and evaluation lemmas and the two witness
derivations are `[]`.  `fresh_not_mem`, both soundness theorems and the
refutations are `[propext, Classical.choice, Quot.sound]`, the C6 profile:
core's infinitude of `String` is classical (`String.toList_ofList`,
`String.ext`, `String.length_pushn`, `Nat.repr_inj`, each
`[propext, Classical.choice, Quot.sound]`; `String` is a UTF-8 `ByteArray`
in v4.31), and `collectAxioms` charges every constant mentioned, so even the
statements of `sumLen` and `fresh` carry it (watched: `len_le_sumLen`, a
pure `Nat` argument, failed at `[]` with the full profile).  With `Nat`
variables the refutations would be `[propext]`.  The positive theorems of the
campaign choose no names and stay at `[propext]`.

**Proposed repaired statements (NOT adopted; await the manager, rule 7):**

    RTP'  ∀ φ, LC φ → allJFree φ →
            Nonempty (LaxND2 [φ] (rel (toJ φ))) ∧ Nonempty (LaxND2 [rel (toJ φ)] φ)
    RTJ'  ∀ Θ φ, LC φ → circFree φ →
            Nonempty (JND IsJ Θ [φ] (toJ (rel φ))) ∧ Nonempty (JND IsJ Θ [toJ (rel φ)] φ)
    MP'   ∀ Γ φ, (∀ ψ ∈ Γ, LC ψ ∧ allJFree ψ) → LC φ → allJFree φ →
            (Nonempty (LaxND2 Γ φ) ↔ Nonempty (JND IsJ [] (Γ.map toJ) (toJ φ)))
    MJ'   ∀ Θ Γ φ, (∀ ψ ∈ Γ, LC ψ ∧ circFree ψ) → LC φ → circFree φ →
            (Nonempty (JND IsJ Θ Γ φ) ↔ Nonempty (LaxND2 (guards Θ ++ Γ.map rel) (rel φ)))

`allJFree`/`circFree` are the fragment predicates of §2.1
(`wip/p2llSyntax.lean`).  The hypothesis on `Γ` is needed as well: at
`Γ = [∀°q.(q → q) → ⊥]`, `φ = ⊥` (allJ-free) the right side of MP holds and
the left fails, by the same model.

**Planned proofs of the repaired statements (OPEN, not started).**  RTP' by
simultaneous induction on the size of `φ` (size is invariant under opening at
an atom), cut by `→I`/`→E`, the `◯` case from C7 with
`rel (circJ χ) = circNuc (rel χ)` (needs `rel_shiftAt`).  RTJ' likewise; its
`∀°` case instantiates at `◯°s` (a J-formula by the `allJ` and `imp` clauses)
and needs the congruence `Γ ⊢ A ↔ B  ⟹  Γ ⊢ openRec k A ψ ↔ openRec k B ψ`,
to be proved for ALL `k` at once so that the binder case opens with the rule's
own eigenvariable and commutes the two openings: no fresh name is chosen, and
the pins stay `[propext]`.  MP', MJ' from I₁, I₂, RTP'/RTJ' and a multi-cut
(substitution of derivations for hypotheses); MJ' also discharges the
translated guards `◯°s → s` by C3 at the declared `s`.

## 5. Log (continued)

* 2026-10-24 (phase 2, step 3): RTP, RTJ, MP, MJ REFUTED as stated (§8),
  kernel-checked on a two-valued semantics; repaired statements proposed;
  STOP, report to the manager, nothing built on the repair.

## 9. Phase 2, step 3 resumed (2026-10-25): the repair ADOPTED, four statements REPLACED

Matthew's decision, relayed by the manager: adopt the repair of §8 and
replace the four statements.  In `wip/p2llStatements.lean` the names
`RoundTripP2LL`, `RoundTripJ`, `MutualP2LL`, `MutualJ` now carry exactly the
text of RTP', RTJ', MP', MJ' of §8:

    RTP  ∀ φ, LC φ → allJFree φ →
           Nonempty (LaxND2 [φ] (rel (toJ φ))) ∧ Nonempty (LaxND2 [rel (toJ φ)] φ)
    RTJ  ∀ Θ φ, LC φ → circFree φ →
           Nonempty (JND IsJ Θ [φ] (toJ (rel φ))) ∧ Nonempty (JND IsJ Θ [toJ (rel φ)] φ)
    MP   ∀ Γ φ, (∀ ψ ∈ Γ, LC ψ ∧ allJFree ψ) → LC φ → allJFree φ →
           (Nonempty (LaxND2 Γ φ) ↔ Nonempty (JND IsJ [] (Γ.map toJ) (toJ φ)))
    MJ   ∀ Θ Γ φ, (∀ ψ ∈ Γ, LC ψ ∧ circFree ψ) → LC φ → circFree φ →
           (Nonempty (JND IsJ Θ Γ φ) ↔ Nonempty (LaxND2 (guards Θ ++ Γ.map rel) (rel φ)))

The wording of 2026-10-24 lives on in `wip/p2llBoolSem.lean` as
`RoundTripP2LLUnrestricted`, `RoundTripJUnrestricted`,
`MutualP2LLUnrestricted`, `MutualJUnrestricted` (docstrings "wording of
2026-10-24, REFUTED"); the four refutations `…_false` now name them, pins
unchanged.  I₁, Fix, I₂ are untouched.  The three changes of the campaign so
far, each with its reason: (1) well-formedness side conditions on the rules,
§6 (I₁ was false for ill-formed sequents); (2) `IsJ`, `IPC2ND` as data, §7
(Fix by recursion on the J-derivation without choice; meaning unchanged, as
`IsJ Θ χ → P` is `Nonempty (IsJ Θ χ) → P` for a proposition `P`); (3) the
fragment hypotheses on RTP, RTJ, MP, MJ, §8–9 (false on the inert connective
of the other calculus).

Proof plan for the four (from §8), to be carried out in
`wip/p2llRoundTrip.lean` (RTP, RTJ) and `wip/p2llMutual.lean` (MP, MJ),
one commit per theorem, no fresh name anywhere, pins aimed at `[propext]`.

## 5. Log (continued)

* 2026-10-25: repair adopted; RTP, RTJ, MP, MJ replaced by the fragment-
  restricted wording (§9); old wording moved to `wip/p2llBoolSem.lean`;
  committed before any proof.

## 10. Phase 2, step 4 (2026-10-25): RTP PROVED (`wip/p2llRoundTrip.lean`)

    roundTripP2LL : RoundTripP2LL     by rtpD   (induction on size φ, both directions at once)   [propext]

`rtpD n φ : size φ < n → LC φ → allJFree φ → LaxND2 [φ] (φ°)* × LaxND2 [(φ°)*] φ`
by recursion on the bound `n` (no well-founded recursion); the binder case
uses the hypothesis on `ψ^s` for the eigenvariable `s` of the rule's own
cofinite premise (`size_opn_fvar`, `allJFree_opn_fvar`, `lc_opn`), so no name
is chosen; the `◯` case is C7 (`circ_to_circNuc`, `circNuc_to_circ`) at
`(φ°)*` composed with the hypothesis, through `((◯φ)°)* = ∀°p.(((φ°)* → p) → p)`
(`rel_toJ_circ`, from `rel_shiftAt`); cut is `→I`/`→E` (`LaxND2.cut1`).
Pins watched at `[]`: `size_openRec_fvar`, `allJFree_openRec_fvar`,
`circFree_openRec_fvar`, `rel_shiftAt`, `rel_circJ` hold at `[]`;
`rt_opn_fvar`, `tr_opn_fvar`, the cuts, `rtpD`, `roundTripP2LL` are
`[propext]` (through `toJ_openRec`/`rel_openRec` and `rename`).

## 5. Log (continued)

* 2026-10-25: RTP PROVED (§10); next RTJ (substitution of equivalents
  `JND.congrD`, then `rtjD`), then MP, MJ in `wip/p2llMutual.lean`.

## 11. Phase 2, step 4 (2026-10-25): RTJ PROVED (`wip/p2llRoundTrip.lean`)

    roundTripJ : RoundTripJ     by rtjD   (induction on size φ, Θ generalised, both directions)   [propext]

Substitution of equivalents, the infrastructure item of the plan:

    JND.congrD : A ↔ B under Γ  ⟹  Γ ⊢ ψ[A/k] → ψ[B/k]     (ψ ◯-free, LC (ψ[A/k]))      [propext]

by recursion on a size bound, for EVERY index `k` at once, so that the binder
cases open the body with the eigenvariable `t` of the rule's own cofinite
premise and commute the two openings (`openRec_comm`, `[propext]`;
`lcAt_openRec_swap`, `[]`): no fresh name is chosen.  The `→` case uses the
lemma with `A`, `B` swapped on the antecedent.  `rtjD`'s `∀°` case: forward,
`∀I` at `s`, `→I` on `◯°s → s`, `∀°E` of the hypothesis at `◯°s` (a J-formula,
`isJ_circJ_fvar`, `[]`), then `congrD` with `A := ◯°s`, `B := s` (`◯°s → s` the
hypothesis, `s → ◯°s` the unit law `JND.OI`), then the hypothesis on `ψ^s`;
converse, `∀°I` at `s`, `∀E` at `s`, the guard `◯°s → s` from C3 at the
declared `s`, then the hypothesis on `ψ^s` under `s :: Θ` (hence `Θ`
generalised).  Pins watched at `[]`: `lcAt_openRec_swap`, `isJ_circJ_fvar`,
`lc_trAllJ` hold at `[]`; `openRec_comm` (by_cases), `congrD`, `rtjD`,
`roundTripJ` are `[propext]`.

## 5. Log (continued)

* 2026-10-25: RTJ PROVED (§11); next MP, MJ in `wip/p2llMutual.lean`.

## 12. Phase 2, step 4 (2026-10-25): MP PROVED (`wip/p2llMutual.lean`)

    mutualP2LL : MutualP2LL     [propext]

Left to right is I₁ (`toJD`).  Right to left: I₂ (`relD`) brings the
derivation back to P2LL with hypotheses `(ψ°)*`, `ψ ∈ Γ`, and conclusion
`(φ°)*`; `ctxBackP` translates the context back one hypothesis at a time
(`→I`, RTP on `ψ`, `→E`), recursing on the list, so that no membership proof
is decoded into data; RTP on `φ` gives `φ`.  Pins watched at `[]`:
`ctxBackP`, `mutualP2LL` are `[propext]`.

## 5. Log (continued)

* 2026-10-25: MP PROVED (§12); MJ next (same file).

## 13. Phase 2, step 4 (2026-10-25): MJ PROVED (`wip/p2llMutual.lean`)

    mutualJ : MutualJ     [propext]

Left to right is I₂ (`relD`).  Right to left: I₁ (`toJD`, at the same `Θ`)
brings the derivation back to the guarded calculus with hypotheses
`(◯s → s)° = ◯°s → s` for `s ∈ Θ` and `(ψ*)°` for `ψ ∈ Γ` (`map_append'`,
`[]`, splits the translated context); `peelGuards` discharges the guards by
C3 at the declared `s` (`→I`, `JND.circJ_collapse`, `→E`), `ctxBackJ`
translates the rest back by RTJ as in §12, RTJ on `φ` gives `φ`.  Pins
watched at `[]`: `peelGuards`, `ctxBackJ`, `mutualJ` are `[propext]`.

## 14. The seven statements: all PROVED (2026-10-25)

    interpToJ     : InterpToJ        wip/p2llInterp.lean      [propext]
    fixOfIsJ      : FixOfIsJ         wip/p2llInterp.lean      [propext]
    interpToP2LL  : InterpToP2LL     wip/p2llInterp.lean      [propext]
    roundTripP2LL : RoundTripP2LL    wip/p2llRoundTrip.lean   [propext]
    roundTripJ    : RoundTripJ       wip/p2llRoundTrip.lean   [propext]
    mutualP2LL    : MutualP2LL       wip/p2llMutual.lean      [propext]
    mutualJ       : MutualJ          wip/p2llMutual.lean      [propext]

The statements are the `def … : Prop` of `wip/p2llStatements.lean`: I₁, Fix,
I₂ as reported on 2026-10-24 (after the well-formedness revision of §6); RTP,
RTJ, MP, MJ in the fragment-restricted wording of 2026-10-25 (§9), their
2026-10-24 wording REFUTED (§8, `wip/p2llBoolSem.lean`, pins
`[propext, Classical.choice, Quot.sound]` from `String` only).  All seven are
about locally closed formulas (`LaxND2.lc`, `JND.lc`).  No theorem chooses a
fresh name; `propext` is the floor of every proof, through `Fm.lc_opn` and the
context lemmas.

## 5. Log (continued)

* 2026-10-25: MJ PROVED (§13); all seven statements PROVED (§14); docstrings
  of `wip/p2llStatements.lean` updated; final report to the manager.
