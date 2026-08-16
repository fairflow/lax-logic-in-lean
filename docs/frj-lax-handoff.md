# FRJ◯ from scratch — handoff for a fresh session

*Written 2026-08-16 on branch `frj-lax` (cut from `frj-ipc`).
Commissioned by Matthew: "start a new branch and a fresh directory for
this extension. Do not import any recent work you have done on
implementing FRJ◯. We will start afresh, using the FRJ calculus but
making it effective and choice free. See PLL for templates for a
slime-free inductive type approach."*

Read this file, then `docs/frj-fidelity.md` (the fidelity record of the
IPC base), then `docs/calculus-formalisation-method.md` (the six-step
method), then the repo `CLAUDE.md` (the machine-checked mandate and the
counterexample-first testing mandate). Read `docs/calculus-map.md`
before asserting which proof system any result belongs to.

---

## 1. The task

**Extend the finished FRJ(G) development with the lax modality ◯.** Not
rebuild it. `FRJ/` on this branch is complete: soundness and completeness
proved, sorry-free, `List`-based, canonical contexts, decidable forcing,
and a `Type`-valued completeness construction that computes a derivation
from a countermodel. Read it, reuse it, extend it.

The mid-range goal this serves: an efficient, verifiable *disproof*
procedure for PLL. The existing PLL decision procedure gives an effective
proof procedure but an exhaustive generate-and-test disproof procedure. A
refutation calculus reads a countermodel off a derivation directly. See
`docs/why-chain.md` for the full goal chain.

## 2. Where things stand

### START HERE — branch, directory, commit

```bash
git checkout frj-lax
mkdir -p FRJLax          # already created, holding only README.md
```

| | |
|---|---|
| **Branch** | **`frj-lax`**, cut from `frj-ipc` |
| **Tip commit** | **`7393ed1`** — the choice-free FRJ development, merged |
| **Directory to build in** | **`FRJLax/`** — created, contains only `README.md`. It is deliberately NOT `FRJO`. |
| **Lake** | add a `[[lean_lib]] name = "FRJLax"` entry to `lakefile.toml` with your first module, and an `FRJLax.lean` root importing it |

`FRJ/` on this branch is **finished**: eight modules, `lake build FRJ`
green from scratch, zero sorries, no `native_decide`, and
`[propext, Quot.sound]` throughout — with the pins `#guard_msgs`-guarded
in `FRJ/Audit.lean`, so any regression is a build failure. That is your
starting point, not something to reproduce.

Read also `docs/why-chain.md` on the same branch: the goal chain this
work sits in, from the mid-range goal down.

### What `FRJ/` contains (on THIS branch — read it here, not on `frj-ipc`)

FRJ(G) over IPC, transcribed from the arXiv LaTeX source of
arXiv:1804.06689 (Fiorentini–Ferrari, TOCL 21(3), 2020),
**sorry-free, builds green, choice-free**:

| File | Content |
|---|---|
| `Basic.lean` | §2: `Form`, Kripke semantics, `Sf^R`/`Sf^L`, `Ĝ_at`/`Ĝ_imp`, the closure `Cl` with (Cl1)–(Cl6) |
| `Calculus.lean` | §3 rule table: mutual `FRJr`/`FRJi`, one constructor per published rule |
| `Step.lean` | The `↦` relation, **Lemma 3.4**, occurrences, `wf` |
| `Model.lean`, `Extract.lean` | `Mod(D)`: the p-sequents-as-worlds model |
| `Sound.lean` | **Lemma 3.9**, **Theorem 3.10**, **Theorem 3.1** (soundness) |
| `Complete.lean` | §6 groundwork: `Λ*_α`, Lemma 6.5, decidable `⊩*`, the height `ht`, the minimal `η` (`minEta`) |
| `Minimal.lean` | **Lemma 6.4** (`minMod`, `Type`-valued), **Theorem 6.2(i)**, `completenessData`, and both biconditionals |
| `Audit.lean` | the `#guard_msgs`-guarded axiom pins — **extend this as you go** |

Branch `frj-ipc` (tag `frj-classical-complete` = `8c711df`) holds the
earlier `Finset`-based, classical version of the same results. It is
kept only for comparison; do not build on it.

Two divergences from the paper are recorded in `docs/frj-fidelity.md`
and both are real: Lemma 6.5's stated set equality `Λ_α = Cl(Λ_α)` is
literally false (the `Cl` grammar lets `A` range over all formulas, so
`Cl(Λ_α)` contains `Z ⊃ C` for arbitrary `Z`, outside `Sf^L(G)`) —
the two directions actually used are true and are proved; and the
regular `C₁ ∧ C₂` case cites (IH2) where it must be (IH3).

### The development is choice-free (verified, and pinned)

`Classical.choice` appears in **exactly one** place, and it is a property
of the statement rather than of the proof.

| | axioms |
|---|---|
| `soundness`, `completeness`, `completenessData`, `frj_iff_countermodel`, `minMod`, `minEta`, `modR_countermodel`, `lemma39R`, `lemma39I`, `lhs_clo_of_steps` | `[propext, Quot.sound]` |
| `nf_ext` | `[propext]` |
| `Kripke.decForce`, `Kripke.force_mono`, `not_IPL_of_countermodel`, `maxOn`, `eq_nil_of_forall_not_mem` | **none at all** |
| `frj_iff_not_IPL` | `[propext, Classical.choice, Quot.sound]` |

The exception is unavoidable: `IPL G` is `∀ K, K.valid G`, and passing
from `¬ ∀ K, K.valid G` to `∃ K, ¬ K.valid G` is not constructively
valid. So the development states the biconditional twice —

```
frj_iff_countermodel : Provable G ↔ ∃ K : Kripke, ¬ K.valid G   -- choice-free
frj_iff_not_IPL      : Provable G ↔ ¬ IPL G                     -- the paper's
```

**Keep both shapes when you extend to ◯**, and keep the modal results on
the countermodel side of that line.

### Three pieces to understand before you touch anything

1. **Completeness is `Type`-valued.** Lemma 6.4's halves are records
   carrying the derivation (`IrrWit`, `RegWit`), because extracting a
   derivation from an `∃` needs `choose` or `Nonempty.some`, both
   choice. The same constraint made `enumOf` and `minEta` data: a `Prop`
   cannot be eliminated into `Type`. The payoff is
   `completenessData : (K : Kripke) → ¬ K.valid G → Derivation G`, an
   algorithm from countermodel to derivation. **This is the property the
   whole campaign wants; do not lose it.**
2. **Forcing is decidable** (`Kripke.decForce`, no axioms at all),
   because `Kripke` carries `elems`/`complete` with `decEq`/`decLe`/
   `decV` instead of a `Finite` instance. Adding ◯ to `force` means
   extending `decForce` with the modal clause — plan for that.
3. **Contexts are canonical** — see §4.3. This is load-bearing, not
   cosmetic, and the ◯ rules must respect it.

## 3. DO NOT IMPORT `FRJO/`

`FRJO/` is the first attempt at the modal extension. It is kept for the
record and must not be imported, copied, or used as a template.

**Why, precisely.** `ExtractForces` (the statement that the model read
off a derivation forces what it must) is **REFUTED** for `worldOK` v3 —
three kernel-checked cells, commit `4730e30`, pinned as
`FRJO.not_extractForces_bot`, `…_and`, `…_mp`. v3's `worldOK`
constrains the stable zone only by membership in the universe, with no
closure condition, so `world [] [] false` is legal at zones no world can
force. The three cells are

    [⊥] ⊢ p          [p ∧ q] ⊢ p          [p, p ⊃ q] ⊢ q

each PLL-derivable (explicit `LaxND` terms) yet FRJ◯-derivable
(`worldOK … = true` by `decide`). Consequently `frjd_iff_not_laxND` is
OPEN and `frjd_iff'` (commit `0f17381`) is vacuous.

A v4 zone repair was screened both ways (commit `8acfbc0`): `zoneOK4`
adds ⊥-freedom, ∧ and ∨ closure both ways over the universe, and
detachment; `zoneOK4_rejects` kills all three cells by `decide`, and
`zoneOK4_of_theory` shows it holds of the restricted theory of any
infallible world, so it costs completeness nothing. The **saturation**
half — the ⊃ and ◯ witnesses for formulas outside the zone — was
deliberately not coded, because it constrains the kid list as well as
the zone and therefore changes the `world` constructor. That is a
statement-level decision, left for Matthew.

**The root cause, and the lesson that must not be repeated.** The FRJ◯
rule table was formalised from `docs/frj-lifting.md`, an in-repo
*paraphrase* written for orientation, rather than from the paper source.
`docs/frj-fidelity.md` records this: formalising from the paraphrase "is
exactly what produced the unsound FRJ◯ rule table". Rule tables come
from the source, read in full, prose as well as figure, appendix
included.

---

## 4. The hard constraints

### 4.1 Effective: Type-valued and slime-free

Derivations are **data**, not existence claims. Judgments live in
`Type`, and the completeness construction must *return a derivation*,
not assert one exists — `choose` and `Nonempty.some` are themselves
choice, and an existence proof yields no procedure.

The template is `LaxLogic/PLLNDCore.lean`. Its design rules, quoted
from its own header:

* Contexts are `List`, extended only by `φ :: Γ` — **every index in a
  constructor return type is a variable or a constructor form**
  (McBride's no-green-slime rule).
* The identity rule takes a membership hypothesis `φ ∈ Γ` instead of
  pinning `φ` at a position.
* Exchange, weakening and contraction are then **admissible**, not
  structural, so no cast is ever needed. The erasure translation and
  both conservativity theorems are entirely cast-free — no `▸`, no
  `cast`, no `HEq`.

**The existing `FRJ/Calculus.lean` violates this rule in almost every
constructor**, and that is the concrete reason `Extract.lean` fights the
kernel. Compare the return-type indices:

    axR     : FRJr G ((gAt G).erase F) F
    joinAt  : FRJr G (joinCtxAt stab th rhs F) F
    axI     : FRJi G ∅ (((gAt G).erase F) ∪ gImp G) F
    orI     : FRJi G (St₁ ∪ St₂) (Th₁ ∩ Th₂) (C₁ ∨ C₂)
    impInI  : FRJi G (St ∪ Lam) Th (A ⊃ B)

Every index is a *computed term*. Re-present each rule with the index a
variable and the computation moved into a hypothesis, e.g.

    orI {St Th St₁ Th₁ St₂ Th₂ C₁ C₂}
        (d₁ : FRJi G St₁ Th₁ C₁) (d₂ : FRJi G St₂ Th₂ C₂)
        (hSt : St ≐ St₁ ++ St₂) (hTh : Th ≐ cap Th₁ Th₂)
        … : FRJi G St Th (C₁ ∨ C₂)

where `≐` is equality up to membership (mutual inclusion), not list
equality. Using membership-equality rather than list equality also
removes any need for `List.dedup` (which is classical) and kills all
order dependence.

`LaxLogic/LJFOCore.lean` is the second template: **zero imports**, so
that no other calculus can carry any part of the proof. That
auditability property is worth preserving for the core module.

### 4.2 Choice-free

Target pin: **`[propext, Quot.sound]`** at worst, and no axioms at all
wherever attainable. Reason: the target is a decision procedure, and
choice blocks extraction. `FRJ/` meets this; keep it that way as you add
◯, and extend `FRJ/Audit.lean` with a `#guard_msgs`-guarded pin for
every new headline result.

The findings from the IPC campaign, as a checklist. Each cost real time
to locate; none needs locating twice.

* **Mathlib's `Finset` union, erase and image are choice-tainted at the
  DEFINITION level** — `Finset.instUnion`, `Finset.erase`,
  `Finset.image`, `Multiset.ndunion` — so any term merely *mentioning*
  `s ∪ t` carries choice however it is proved. Re-deriving membership
  lemmas by hand does not help. Only `Finset.filter` is clean.
* **The `List` API is axiom-free at definition level**: `List.union`,
  `List.inter`, `List.filter`, `List.map`, `List.flatMap`,
  `List.finRange`, `List.instMembership`. `List.mem_append`,
  `mem_filter`, `mem_cons` cost `[propext]`. **Avoid `List.dedup` and
  `List.erase`** — both classical; filter instead.
* **Three more Mathlib list lemmas carry choice**: `List.argmax_mem`,
  `List.le_of_mem_argmax` (though `List.argmax` itself is clean), and
  `List.eq_nil_iff_forall_not_mem`. Replacements are already in
  `FRJ/Basic.lean`: `maxOn` with `maxOn_mem`/`le_maxOn`, and
  `eq_nil_of_forall_not_mem`. Use them.
* **`Finite` costs choice to eliminate** (`Fintype.ofFinite`). Carry a
  constructive enumeration instead — `Kripke` already does.
* **The tactics.** `tauto` and `push_neg` reason classically, and so
  does `Classical.propDecidable`. **`simp` can too, but indirectly**: on
  an inequality goal it routes through Mathlib's ordered-algebra
  instances and out through `lt_or_eq_of_le`, which is genuinely
  classical (deciding `a = b` in a partial order needs excluded middle).
  `simp` on a goal with no order in it is clean, and `omega` on a goal
  `simp` taints is clean. So: **prefer `omega` to `simp` for arithmetic
  and order goals.**
* Shape predicates (`isPV`, `isPrime`, `isImp`) are `Bool`, not `Prop`.

**Use the bisector; do not guess.** `Meta/Audit.lean` (branch
`meta-tools`) provides

```
#choice_path f      -- shortest chain from f to Classical.choice,
                    -- each step annotated with its module
#choice_sources f   -- which direct dependencies are tainted
#axiom_pin f        -- emit the #guard_msgs block, ready to paste
```

It exists because guessing failed: the first diagnosis of the `simp`
case in this campaign was wrong, and `#choice_path` corrected it in one
command by naming `lt_or_eq_of_le` as the actual source. When a pin
comes out dirty and the mathematics looks constructive, run the tool
before changing anything.

### 4.3 Contexts are canonical — do not break this

The irregular `⊃∈` rule needs, in Lemma 6.4, the zone `Θ₁` of a *given*
derivation split as `Θ ∪ Λ`. On `Finset` that split is a literal
equality of the rule's own index; on `List` it is not, because `++` is
neither commutative nor idempotent. Nor is there a transport: "same
members implies same derivations" is **false**, because `Ax^I` pins its
own zone.

The resolution — a change of carrier, not of calculus — is to represent
contexts canonically:

```
nf G l = (gHat G).filter (· ∈ l)
```

legitimate exactly because `wfR`/`wfI` prove every context of a
derivation is a subset of `Ĝ`, so `nf G` preserves membership, and every
side condition in the rule table is membership-based. Two contexts with
the same members are then *literally the same list* (`nf_ext`) — the
property `++` lacks and `Finset` had.

`Ax^I`, `∨` and **both sides** of the irregular `⊃∈` write their computed
zones canonically; canonicalising both sides of `⊃∈` is what keeps Lemma
3.4(i) going through with no extra side condition. `IrrWit` carries a
`thNf` field recording that its zone is canonical.

**Consequence for the ◯ rules**: any new rule with a COMPUTED context in
its conclusion must write it as `nf G (...)`, and any rule that consumes
a given derivation's zone must be able to split it via `nf_ext`. Design
for this from the first rule, not afterwards.

---

## 5. The ◯ extension is NEW MATHEMATICS

FRJ(G) has a source. **FRJ◯ does not.** The modal rules are our own, and
this is exactly where the first attempt failed.

Therefore, per the repo `CLAUDE.md` testing mandate: **every candidate
modal rule gets an extensional attack before any proof is scoped**, in
the four directions (corpus replay, boundary cells, frontier extension,
branch coverage), and the *statement* of the rule is Matthew's call, not
the implementer's. Surface each proposed rule as a displayed inference
figure with its side conditions, together with the screen results, and
wait.

Related literature to consult (but never to paraphrase-then-formalise):
RK(Ξ) — CEUR 2214 paper 8 — is read at source in
`docs/frjo-calculus-plan.md`, whose rule table and completeness
induction were transcribed there. Treat that plan as a record of what
was *tried*, not as a specification.

---

## 6. Staging

Matthew's standing rule for this campaign is **implement existing results
before trying to extend them**. That rule is now DISCHARGED for the IPC
base: the results exist, on this branch, machine-checked. So the staging
below reuses them; it does not re-derive them.

| Stage | Content | Exit criterion |
|---|---|---|
| **W0** | Read `FRJ/` end to end, and `docs/frj-fidelity.md` beside it. Read the source (arXiv:1804.06689 LaTeX `frj-corr.tex`, **including the appendix**) for §3 and §6 only as far as you need to understand what is already formalised. | You can state where each numbered result of the paper lives in `FRJ/` |
| **W1** | Add ◯ to `Form` and to forcing — including the modal clause of `decForce`, so forcing stays decidable. Everything ◯-free must still build; the point of doing this first is that the eight modules then tell you, by breaking or not breaking, exactly which proofs are modality-sensitive. | Library builds with ◯ in the syntax and no ◯ rules; `Audit.lean` pins unchanged |
| **W2** | Design the ◯ rules. **New mathematics — see §5.** Screen every candidate rule before proving anything, and get Matthew's sign-off on each rule statement. | Screens recorded; rules signed off |
| **W3** | Extend soundness: Lemma 3.4, `wf`, Lemma 3.9, Thm 3.10, Thm 3.1, with the ◯ cases added | Sorry-free; a new `#guard_msgs` pin in `Audit.lean` reading `[propext, Quot.sound]` |
| **W4** | Extend completeness: `Λ*`, Lemma 6.5, `minMod`, Thm 6.2(i), with the ◯ cases | Sorry-free; pinned; and `completenessData` still *computes* a derivation |
| **W5** | The searcher extracted from `completenessData`, plus a `decide`-checkable certificate | Runs as a `lean_exe` |
| **W6** | Test on the existing corpus and stretch it | Corpus results recorded |

Bank at every stage boundary: commit, push, and append a dated section
to `HANDOFF.md` at the repo root (append, never rewrite).

**How to reuse `FRJ/`.** Two options, and W1 will tell you which is
right: either extend the modules in place (simplest, if the ◯-free
proofs survive the syntax change unchanged), or have `FRJLax/` import
`FRJ` and add the modal layer beside it. Do NOT copy files.

## 7. What not to do — failure modes observed, stated factually

1. **Extending before the base is verified.** FRJ◯ was built before FRJ
   was; its soundness came out refuted, which forced the step back.
2. **Formalising from a paraphrase.** The unsound rule table came from
   `docs/frj-lifting.md`, not the paper.
3. **Transcribing a rule table from the figure alone.** The prose
   carries side conditions and PS1–PS4.
4. **Bundling part of a conclusion into a definition as a field.** In
   the IPC pass, `forces_lhs` (= Lemma 3.9(i)) was briefly a field of
   the model structure — assuming what was to be proved. Construction
   data only.
5. **Treating choice as a property to report in the axiom pin rather
   than a constraint to design against.** It is a design constraint, and
   it is cheapest to honour at line one.
6. **Computed indices in constructor return types.** See §4.1, and
   §4.3 for the canonical-context discipline that makes the irregular
   `⊃∈` rule usable at all.
7. **Blaming the mathematics for a dirty axiom pin.** Twice in this
   campaign the `Classical.choice` was in a tool, not an argument —
   Mathlib's `Finset` operations at definition level, and the `simp`
   tactic. Bisect with `#print axioms` before redesigning anything.

---

## 8. Open decisions for Matthew — do not settle these unilaterally

1. **Syntax staging.** Recommended: carry ◯ in the syntax from W1 and
   stage only the *rules*, so the ◯-free results transfer literally and
   no retrofit is needed. The alternative is to reproduce FRJ over IPC
   verbatim and extend the syntax later. Reversible either way, but
   cheaper the recommended way.
2. **The saturation half of the v4 repair** (§3) — it changes the
   `world` constructor and decides whether the other rules survive as
   primitive or become derived. Explicitly left for Matthew by the
   earlier session.
3. **Every modal rule statement** (§5).

---

## 9. Operational notes

* Fresh Claude worktrees have no `.lake`. Before building:
  `cp -Rc <repo-root>/.lake .lake` (APFS clone, instant). The repo root
  is `lax-logic-in-lean`, not `LaxLogic/`. Never remove a worktree to
  tidy up.
* Build: `lake build FRJLax`. Discovery runs on the certificate engines
  (`PLLND.Search.prove?Bounded` / `refute?`, or the two-sided engine
  `lean_exe twosided`), **never** through the decidability theorem
  `decideFuel`, whose fuel bounds are infeasible.
* Matthew cannot open worktree paths, and often not repo paths, from the
  session UI. Inline short content in full; publish documents as
  Artifacts.
* A claim is PROVED only when sorry-free with a pinned `#print axioms`.
  Otherwise it is REFUTED (kernel-checked countermodel) or OPEN. Keep
  the three rigidly distinct.
