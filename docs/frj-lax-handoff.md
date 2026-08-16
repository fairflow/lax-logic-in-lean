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

Build the refutation calculus FRJ◯ — FRJ(G) extended with the lax
modality ◯ — in a fresh namespace, **effective and choice-free from line
one**, and reprise over it the whole chain of results already proved for
the IPC base: soundness, completeness, and then the countermodel search
that is the point of the exercise.

The mid-range goal this serves: an efficient, verifiable *disproof*
procedure for PLL. The existing PLL decision procedure gives an
effective proof procedure but an exhaustive generate-and-test disproof
procedure. A refutation calculus reads a countermodel off a derivation
directly. See `docs/why-chain.md` for the full goal chain.

---

## 2. Where things stand

### START HERE — branch, directory, commit

```bash
git checkout frj-lax
mkdir -p FRJLax          # already created, holding only README.md
```

| | |
|---|---|
| **Branch** | **`frj-lax`**, cut from `frj-ipc` |
| **Tip commit** | **`7cb7806`** — "docs: the why-chain and the calculus-adoption skill proposal" |
| **Directory to build in** | **`FRJLax/`** — created, contains only `README.md`. It is deliberately NOT `FRJO`. |
| **Lake** | add a `[[lean_lib]] name = "FRJLax"` entry to `lakefile.toml` with your first module, and an `FRJLax.lean` root importing it |

Nothing in `FRJLax/` is Lean yet. That is the point: the first Lean file
in it is yours, written to the constraints in §4, not a copy of anything.

Read also `docs/why-chain.md` on the same branch: the goal chain this
work sits in, from the mid-range goal down.

### What is PROVED and may be read (branch `frj-ipc`, tag `frj-classical-complete` = `8c711df`)

`FRJ/` — FRJ(G) over IPC, transcribed from the arXiv LaTeX source of
arXiv:1804.06689 (Fiorentini–Ferrari, TOCL 21(3), 2020), 2961 lines,
**sorry-free, builds green**:

| File | Content |
|---|---|
| `Basic.lean` | §2: `Form`, Kripke semantics, `Sf^R`/`Sf^L`, `Ĝ_at`/`Ĝ_imp`, the closure `Cl` with (Cl1)–(Cl6) |
| `Calculus.lean` | §3 rule table: mutual `FRJr`/`FRJi`, one constructor per published rule |
| `Step.lean` | The `↦` relation, **Lemma 3.4**, occurrences, `wf` |
| `Model.lean`, `Extract.lean` | `Mod(D)`: the p-sequents-as-worlds model |
| `Sound.lean` | **Lemma 3.9**, **Theorem 3.10**, **Theorem 3.1** (soundness) |
| `Complete.lean`, `Minimal.lean` | §6: `Λ*_α`, Lemma 6.5, **Lemma 6.4** (`minMod`), **Theorem 6.2(i)**, and `frj_iff_not_IPL : Provable G ↔ ¬ IPL G` |

Two divergences from the paper are recorded in `docs/frj-fidelity.md`
and both are real: Lemma 6.5's stated set equality `Λ_α = Cl(Λ_α)` is
literally false (the `Cl` grammar lets `A` range over all formulas, so
`Cl(Λ_α)` contains `Z ⊃ C` for arbitrary `Z`, outside `Sf^L(G)`) —
the two directions actually used are true and are proved; and the
regular `C₁ ∧ C₂` case cites (IH2) where it must be (IH3).

### The choice-free conversion (branch `frj-choicefree`, tip `0a050df`)

Six of the seven modules are converted and green: `Basic`, `Calculus`,
`Step`, `Model`, `Extract`, `Sound`, `Complete`. **`Minimal.lean` is
still being converted** — it is the one that needs the completeness
*construction* made `Type`-valued, since `choose` and `Nonempty.some`
are themselves choice. Check the branch tip before relying on this
paragraph.

This branch is the **working reference for how the constraints of §4.2
are met in practice**. Retrieve any converted file with, e.g.

```bash
git show frj-choicefree:FRJ/Basic.lean
```

Three pieces of it are worth lifting wholesale rather than reinventing:

* `Kripke` carrying `elems : List W`, `complete : ∀ w, w ∈ elems`,
  `decEq`, `decLe`, `decV` in place of a `Finite` instance;
* `decForce : Decidable (K.force a A)`, which makes forcing a
  **computation** — the `⊃` clause is decided over `K.elems` by
  `List.decidableBAll`;
* `countP_mono` / `countP_lt_countP`, replacing `Finset.card_lt_card`
  for the height of a world, and `List.argmax` replacing
  `Finset.exists_max_image`.

Verified by `#print axioms` against the built oleans (2026-08-16):

* **no axioms at all**: `clo_forces`, `clo_trans`, `clo_pv`,
  `Kripke.force_mono`, `not_IPL_of_countermodel`
* **`[propext]`**: `sfPos_closed`, `sfR_imp`, `clo_sf`
* **`[propext, Quot.sound]`**: `mem_unionAll`, `mem_interAll`,
  `lhs_subset_of_step`, `lhs_clo_of_step₀`, `lhs_clo_of_steps`,
  `occR_steps`, `wfR`, `wfI`, `axI_not_mem_lhs`, `addRoot_force_comp`,
  `addRoot_le_comp`

`Classical.choice` is absent throughout the converted part.

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

## 4. The two hard constraints

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
wherever attainable. `Classical.choice` must not appear. Reason: the
target is a decision procedure, and choice blocks extraction.

The reusable findings from the IPC conversion — check each of these:

* **Mathlib's `Finset` union, erase and image are choice-tainted at the
  DEFINITION level.** `Finset.instUnion`, `Finset.erase`,
  `Finset.image`, `Multiset.ndunion` all report `Classical.choice`, so
  any term merely *mentioning* `s ∪ t` on a `Finset` carries choice
  however it is proved. Re-deriving membership lemmas by hand does not
  help. Only `Finset.filter` is clean.
* **The `List` API is axiom-free at definition level**: `List.union`,
  `List.inter`, `List.filter`, `List.map`, `List.flatMap`,
  `List.finRange`, `List.instMembership`. `List.mem_append`,
  `mem_filter`, `mem_cons` cost `[propext]`. **Avoid `List.dedup` and
  `List.erase`** — both classical; filter instead.
* **`tauto` reasons classically.** Do not use it. Same for
  `Classical.propDecidable`.
* **`Finite` costs choice to eliminate** (`Fintype.ofFinite`). Carry a
  constructive enumeration instead: the converted `Kripke` has
  `elems : List W`, `complete : ∀ w, w ∈ elems`, plus `decEq`, `decLe`,
  `decV`, which makes forcing computable.
* Shape predicates (`isPV`, `isPrime`, `isImp`) as `Bool`, not `Prop`.

Pin the axioms with `#guard_msgs` in the module itself, so a regression
is a build failure and not a discovery months later. `native_decide`
taints; `collectAxioms` (i.e. `#print axioms`) is the only sound oracle.

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

The standing rule Matthew states for this campaign: **implement existing
results before trying to extend them.** The first attempt inverted this
and the extension came out unsound.

| Stage | Content | Exit criterion |
|---|---|---|
| **W0** | Read the source: arXiv:1804.06689 LaTeX (`frj-corr.tex`, 6682 lines), **including any appendix** — journal page limits push proof detail there. Re-read the prose, not only the rule figure: side conditions and the proof-search restrictions PS1–PS4 live in the prose. | A written plan listing every numbered result to be reproduced |
| **W1** | Syntax, semantics, subformula sets, closure `Cl` — **with ◯ present in the syntax from line one** | Builds; `Cl` properties (Cl1)–(Cl6) proved; axioms pinned |
| **W2** | The FRJ(G) rule table, slime-free, Type-valued, `List`-based; ◯-free rules only | Builds; every constructor's index a variable |
| **W3** | Soundness of the ◯-free fragment: Lemma 3.4, `wf`, Lemma 3.9, Thm 3.10, Thm 3.1 | Sorry-free, pinned, no `Classical.choice` |
| **W4** | Completeness of the ◯-free fragment: §6, `Λ*`, Lemma 6.5, `minMod` (Lemma 6.4), Thm 6.2(i) — **returning a derivation**, i.e. `Type`-valued | Sorry-free, pinned; the construction *computes* |
| **W5** | The ◯ rules: screen first (§5 above), then Matthew signs off, then extend W2–W4 | Screens recorded; rules signed off; results re-proved |
| **W6** | The searcher extracted from the completeness construction, plus a `decide`-checkable certificate; test on the existing corpus and stretch it | Runs as a `lean_exe`; corpus results recorded |

Bank at every stage boundary: commit, push, and append a dated section
to `HANDOFF.md` at the repo root (append, never rewrite).

---

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
6. **Computed indices in constructor return types.** See §4.1.

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
