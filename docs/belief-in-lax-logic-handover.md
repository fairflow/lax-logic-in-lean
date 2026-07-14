# Handover — writing *Belief in Lax Logic* with Matthew

**For:** the next Opus session that will help Matthew Fairtlough draft the paper
**From:** the session of 2026-07-14
**Status:** paper not yet started; this is the brief. No code task is pending.

---

## 0. Before anything else — two ground rules

**(a) Whose paper this is.** Matthew Fairtlough is the *Fairtlough* of
Fairtlough–Mendler. This is his logic and his paper. You are an assistant:
you draft, you formalise claims, you compute examples, you check the
literature, you pressure-test arguments. You are **not a byline co-author** —
do not offer to be one, and say so plainly if the question of authorship
arises. Within that role, be a real collaborator: if something Matthew
proposes is wrong, say it is wrong and show why. He explicitly values
`PROVED` / `REFUTED` / `OPEN` kept apart and honest reporting over
agreement — the whole prior thread turned on machine-refuting a shortcut he
had hoped would work, and he was glad of it.

**(b) Register — the one hard rule.** Use **standard proof-theoretic and
modal-logic language only.** No invented vocabulary. A previous thread was
derailed by home-made jargon ("fuel", "seals", "the zoo", "the cascade",
"ambient budget", …) that Matthew could not and would not follow; he stopped
the work over it. Write lemmas as **displayed formulas**, name notions by
their standard names (nucleus, closure operator, Heyting algebra, Kripke
model, forcing, …), and if you must coin a term, define it once on first use
as a displayed definition and never drape prose over it. When in doubt,
write the formula, not a metaphor for the formula.

---

## 1. The paper in one paragraph

*Belief in Lax Logic* argues that Propositional Lax Logic (PLL) is a
legitimate **logic of belief** — read `◯M` as "M is believed" — and, on the
way, gives an argument for constructive logic. The engine of the paper is a
contrast the mechanised results make precise: **classically, belief is
degenerate** (every believer is "the truths, plus one fixed dogma"), whereas
**constructively, belief is rich and evidential** (a proof of `◯M` carries
the grounds for believing M). Since evidential belief — belief whose grounds
you can demand — is non-trivial *only* intuitionistically, wanting belief to
be more than prejudice is itself a reason to work constructively. The
argument does not presuppose constructivism; it earns it from a
pre-theoretic desideratum about belief.

---

## 2. The argument, distilled

Read `◯M` as "M is believed", equivalently "M holds subject to the
believer's grounds". A believer is a **nucleus** `j` on the algebra of
propositions: an inflationary, idempotent, meet-preserving closure operator.
This is exactly what PLL's `◯` is, so the belief reading is not an analogy —
it is the intended algebra with a doxastic gloss.

**(A) Classical belief is degenerate.**
On a Boolean algebra every nucleus is *closed*:
> `j(x) = x ∨ a`,  where `a = j(0)` fixed;  equivalently  `◯M ⟺ M ∨ a`.
(The finitary proof uses only `x ∨ ¬x = 1`.) So a classical believer believes
exactly the truths, plus one fixed proposition `a` (a "dogma") and its
consequences — a one-parameter family `c_a`, one believer per proposition.
The extremes are Matthew's two kinds:
> `a = ⊥` : the **total sceptic** — `◯M ⟺ M`, believes only truths (`j = id`).
> `a = ⊤` : the **totally credulous** — `◯M ⟺ ⊤`, believes everything.
Classically a believer can be *nothing but* truth-plus-a-prejudice. No
conditional belief, no evidential structure. Belief is boring.

**(B) Constructive belief is rich.**
Off Boolean, nuclei are no longer all closed. Standard families reappear as
genuinely distinct notions:
> **closed**  `c_a(x) = x ∨ a`      — dogmatic belief;
> **open**    `u_a(x) = a → x`      — *hypothetical* belief ("I would believe M given a");
> **double-negation-like** `(x → a) → a`.
On a Boolean algebra the open family collapses into the closed one —
`a → x = x ∨ ¬a`, i.e. `u_a = c_{¬a}` — so hypothetical belief is *invisible*
classically. Intuitionistically it is a separate thing, and the space of
believers is large: the free lax structure on no generators (the closed
`◯`-fragment) is **infinite** (machine-checked, §3). The constructive
believer simply has more available attitudes than the classical one can
express.

**(C) Belief is evidential — the constraint reading, made exact.**
F&M's own reading of `◯M` is "M holds up to constraints". The
context-completeness theorem (machine-checked, §3) makes this a completeness
statement:
> `PLL ⊢ φ`  ⟺  for every standard constraint `C`,  `IPL ⊢ φ^C`.
Doxastic gloss: the constraint `C` is the believer's **grounds**; `φ^C` is
what `φ` amounts to once those grounds are discharged. A proof of `◯M` is a
proof carrying a constraint (a body of evidence) under which M holds — so
Matthew's slogan
> *"a proof of `◯M` contains the evidence for believing M"*
is exact, not metaphorical. The strong-monad structure (`unitC`/`bindC`, the
C_I/C_M/C_S combinators of the Curry paper) are the **operations on
evidence**: believe a truth (unit), chain grounds (multiplication /
`bindC`), combine grounds for a conjunction (strength). This is the
BHK / propositions-as-types reading applied to a belief modality.

**(D) The argument for constructivism.**
Evidential belief — belief you can demand the grounds of — is non-degenerate
*only* intuitionistically, because classically it collapses to "truth ∨
dogma", with no evidence anywhere in the picture. So if you want belief to be
more than prejudice, you are pushed into constructive logic — not by fiat but
because that is the only setting in which the modality has room to carry
content. A reason to be a constructivist that does not presuppose
constructivism. This is, I think, the paper's real engine; give it its own
section.

**(E) The idealisation to own up front.**
The unit `M ⊢ ◯M` makes the believer believe *every* truth — logical
omniscience over the true, belief as a closure operator on truth. This is
exactly what makes `◯` a nucleus, so it is not a bug to hide but a scope to
declare: this is a logic of **idealised, truth-closed, evidential** belief.
The interest is the evidential and constructive structure, not
resource-bounded or fallible-about-truth belief. A referee reaches for this
first — put it in the introduction, not the rebuttal.

Two further doxastic facts worth a subsection each:
- **Full introspection.** `◯◯M ⊣⊢ ◯M` (unit gives `◯M ⊢ ◯◯M`, multiplication
  the converse). Believing-that-you-believe coincides with believing; the lax
  believer is transparently introspective (both the `4`/positive-introspection
  direction and its converse hold).
- **No consistency axiom.** PLL does **not** have `¬◯⊥` (the doxastic `D`).
  `◯⊥` is a genuine, non-trivial element — the free generator of the closed
  fragment, `◯⊥ ≠ ⊤`. By monotonicity `◯⊥ ⊢ ◯M` for all M, so a believer who
  "believes the absurd" believes everything (credulous collapse *at the
  `◯`-level*), yet `◯⊥` does not make everything *true*. The inconsistency is
  quarantined. This is a clean point of contrast with KD45 belief — develop it
  carefully.

---

## 3. The machine-checked ledger (cite these; they are solid)

All of the following are `sorry`-free and axiom-audited. **They live on the
git branch `worktree-g4ill` (HEAD `df2b0e6`), in the worktree at
`.claude/worktrees/g4ill/`.** That branch is ~10 commits ahead of `main` and
is **not yet merged** — see §7. Re-verify with the Lean toolchain (v4.31.0)
before leaning hard on any statement in print.

Axiom key: **clean** = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`
— the ordinary axioms of classical Lean, i.e. an honest proof.

| Result | Lean name / location | Statement (as mechanised) | Axioms |
|---|---|---|---|
| **Context completeness** (F&M Curry Thm 6) — *"belief = provability under a constraint"* | `PLLND.Ctx.thm6`, `wip/context_completeness.lean:651` | `Nonempty (LaxND [] φ) ↔ ∀ C : StdCtx, Nonempty (LaxND [] (subC C φ))` | clean |
| **Constructive belief is infinite** — the closed `◯`-fragment `RN(◯,{})` | `PLLND.LaxInfinite.closed_lax_infinite`, `wip/lax_infinite.lean:616` | `Infinite (Quotient closedSetoid)` | clean |
| **The constraint algebra 𝕊 is Boolean** | `PLLND.Ctx.thm2_boolean_algebra`, `wip/context_completeness.lean:1588` | 𝕊 is a bounded distributive lattice with complements (`BooleanAlgebra CQuot`) | clean |
| **No finite set of constraints suffices** (F&M Cor 10) | `PLLND.Ctx.corollary10`, `wip/context_completeness.lean:981` | no finite `𝔻 ⊆ StdCtx` is complete for PLL | clean |
| supporting: `◯⊥` is a free Heyting generator | `force_subOb`, `lax_infinite.lean:393` | `p ↦ ◯⊥` embeds the Rieger–Nishimura lattice | `propext` |
| supporting: RN ladder staircase invariant | `rn_staircase`, `lax_infinite.lean:521` | de Jongh one-variable universal model | clean |

Provenance for §2's claims:
- **(C)** rests on `thm6` (+ `lemma7`, the semantic-completion lemma at
  `context_completeness.lean:546`). This is the strongest single anchor for
  the paper's thesis — belief is completely captured by constrained
  provability.
- **(B)**'s "infinite" rests on `closed_lax_infinite`. Note the sharp
  finding recorded in memory: chain/comb Kripke models provably cap the
  one-variable fragment at ≤ 5–9 classes, so an *infinite* model is genuinely
  required — the richness is real, not an artefact.
- **(A)**'s collapse `j(x) = x ∨ j(0)` is **literature + elementary, NOT
  machine-checked** (see §4). Do not present it as mechanised. What *is*
  mechanised near it is `thm2_boolean_algebra` (𝕊 Boolean) — a different
  statement; keep them apart.

---

## 4. Literature — the backbone, and the prior art you must engage

**The classical-collapse backbone (literature, mostly not mechanised).**
See `docs/nuclei-noncomplete-lit.md` (verified citations):
- On any Boolean algebra `B`, every nucleus is closed, `j(x) = x ∨ j(0)`, so
  `N(B) ≅ B`. Elementary (finitary via `x ∨ ¬x = 1`); Beazer–Macnab territory.
  **Matthew already knows this** — do not re-derive it to him as news (the
  previous session over-sold it as a surprise and was corrected). Its value in
  the paper is as the stated hinge of §2(A), carrying a citation, not as a
  discovery.
- Off Boolean and off *complete*: for a non-complete Heyting algebra, the
  nuclei `N(H)` form in general only a bounded meet-semilattice — both `∨` and
  `→` on `N(H)` are extremal-fixpoint constructions needing completeness
  (Erné 2022); `N(H)` is a frame iff `H` is complete. Consequence for the
  paper: be careful with any "algebra of believers" claim over RN or 𝕊 — it
  need not itself be a Heyting algebra. (This killed a tempting "assembly
  tower over RN" line; see `docs/assembly-tower-lit.md`.)
- Macnab 1981 ("Modal operators on Heyting algebras", *Algebra Universalis*
  12) is the right primary source for nuclei on a possibly-incomplete Heyting
  algebra. It stayed **paywalled** in the prior session — only reached
  second-hand via Erné 2022. Getting it is the one open literature errand.

**Prior art the paper MUST position against (verify details — do not assert
from memory).** This is the biggest gap in the current thinking and your most
valuable early contribution:
- **Justification logic** (Artemov): `t : F`, "`t` is evidence/justification
  for `F`". Matthew's slogan "a proof of `◯M` is the evidence for M" is
  squarely this territory. Is PLL's `◯` a *forgetful* justification modality
  `∃t. t : M`? Could be a section or a related-work paragraph. **Verify.**
- **Intuitionistic epistemic logic** (Artemov & Protopopescu, 2016,
  *Review of Symbolic Logic*): an intuitionistic `K` with co-reflection
  `A → KA` and *without* `KA → A`, motivated verificationally (a proof is a
  verification). This is very likely the **closest published neighbour** and
  the paper must say clearly how PLL's belief reading relates — complementary,
  a special case, or genuinely different (PLL predates it by ~20 years and
  comes from a type-theoretic/hardware-verification motivation, not an
  epistemic one). **Read it early; verify the exact axioms.** It may reshape
  the paper's positioning.
- **Doxastic logic** (Hintikka; KD45): the classical baseline the paper
  contrasts against. §2(E)'s "no `D` axiom, full introspection" is the precise
  comparison.
- **BHK / propositions-as-types**; **Goldblatt 1981** ("Grothendieck topology
  as geometric modality") and the nucleus-as-modality literature — the
  algebraic lineage of `◯`.

---

## 5. A proposed skeleton (a starting point, not a cage)

1. **Introduction** — PLL and its history (Curry's problem, hardware
   verification, the `◯` modality); the belief reading; the thesis; the
   idealisation declared up front (§2E); contributions.
2. **Lax logic recalled** — syntax; the three `◯`-laws (unit, multiplication,
   strength); nucleus semantics; constraint semantics. Lift precise statements
   from the codebase.
3. **Belief as a nucleus** — `◯M` = "M is believed"; believer = nucleus;
   truth-closure; the unit as "believe every truth".
4. **Classical belief is degenerate** — `N(B) ≅ B`; `◯M ⟺ M ∨ a`; the `c_a`
   spectrum; sceptic and credulous extremes; contrast with KD45 (no `D`,
   `◯⊥` non-trivial, full introspection).
5. **Constructive belief is rich** — open vs closed nuclei; hypothetical
   belief `a → (−)` invisible classically; the infinite closed fragment
   (machine-checked); **worked examples on small Heyting algebras** (enumerate
   the nuclei on the 3- and 4-element chains and a small non-linear Heyting
   algebra: exhibit sceptic, credulous, and genuinely-intermediate believers
   side by side — the algebra-enumeration code already computes nuclei on
   small Heyting algebras, so this is cheap and concrete).
6. **Belief is evidential** — constraint semantics; Theorem 6; constraint as
   grounds; `λ`-terms as evidence operations; "a proof of `◯M` contains the
   evidence".
7. **The argument for constructivism** — evidential belief is non-degenerate
   only intuitionistically; the desideratum-to-constructivism move (§2D).
8. **Related work** — justification logic; intuitionistic epistemic logic;
   doxastic logic; BHK; geometric-modality/nucleus lineage.
9. **Limitations and further work** — truth-closure idealisation;
   resource-bounded / fallible belief; multi-agent; *belief about belief* and
   the assembly tower `N(N(…))` as a speculative meta-belief structure
   (flag as open — see `nucleus-assembly-direction` memory; the tower over RN
   is genuinely open and delicate, do not overclaim).
10. **Conclusion.**

---

## 6. Pitfalls — what NOT to claim

- **Do not** call `j(x) = x ∨ j(0)` / `N(B) ≅ B` machine-checked. It is
  literature-grade and elementary; the machine-checked neighbour is
  `thm2_boolean_algebra` (a different statement).
- **Do not** claim an "assembly tower over RN" is a Heyting algebra, or that
  RN's tower height is known. Off-frame `N(RN)` may fail both `∨` and `→`; the
  height is **open** in the literature (`assembly-tower-lit.md`,
  `nucleus-assembly-direction` memory).
- **Do not** conflate "believes everything" (`◯M` for all M, the credulous
  `a = ⊤` / `◯⊥`) with "everything is true" (`⊤`). The distinction is a
  feature (§2E).
- **Do not** assert the justification-logic or Artemov–Protopopescu details
  from this document — verify against the primary sources before print.
- **Do not** overstate the belief model: it is truth-closed and logically
  omniscient over truths. Say so.

---

## 7. Logistics

- **This handover:** `docs/belief-in-lax-logic-handover.md` (main checkout).
- **The proofs:** branch `worktree-g4ill`, worktree `.claude/worktrees/g4ill/`,
  files `wip/context_completeness.lean` and `wip/lax_infinite.lean`. That
  branch is ~10 commits ahead of `main` and **unmerged** — this is the "stuff
  on my repo that requires work" Matthew flagged. **Recommend running the
  paper session inside the `g4ill` worktree** so the Lean files are directly
  openable and re-verifiable; the `docs/` there is the same set as on `main`.
  (If you work from `main` instead, `git checkout worktree-g4ill -- wip/…` or
  read the files via the worktree path.)
- **Toolchain:** Lean v4.31.0 + Mathlib v4.31.0 (see `toolchain-bump-v431`
  memory). `#print axioms <name>` is the honest-proof check; run it before
  citing.
- **The Curry paper (source for §6 / Theorem 6):** F&M, "On the Logical
  Content of Computational Type Theory: A Solution to Curry's Problem",
  TYPES 2000, LNCS 2277, pp. 63–78. Durable copy:
  `https://ncatlab.org/nlab/files/MendlerComputationalTypeTheory.pdf`.
  (A scratchpad copy from the prior session will not persist — use the URL.)
- **Do not commit to `main`** without asking; if committing, branch first.
  Matthew asks for commits explicitly.

---

## 8. Pointers

- **Memory** (`…/memory/`): `communication-register` (the register rule —
  read it), `curry-problem-paper` (Theorem 6 provenance),
  `nucleus-assembly-direction` (the collapse, off-frame results, tower),
  `ui-route-status`, `toolchain-bump-v431`.
- **Docs** (`docs/`): `nuclei-noncomplete-lit.md` (collapse + off-frame
  backbone for §4/§2A), `assembly-tower-lit.md` (§9 further-work),
  `opus-handover.md` (the *previous*, proof-effort handover — different
  purpose, but shows house style and the register in action).
- **Codebase:** `wip/context_completeness.lean` (the Curry paper, ~1745 lines,
  the source of §6), `wip/lax_infinite.lean` (~495 lines, the source of §5's
  "infinite"). `PLLCompleteness.lean` on `main` is the F&M-1997 Kripke
  completeness the Curry work builds on.

**First move, suggested:** read the `communication-register` memory and
`nuclei-noncomplete-lit.md`, skim `thm6` and `closed_lax_infinite` in the
worktree, then read Artemov–Protopopescu IEL and report to Matthew where PLL
belief sits relative to it — that positioning is the highest-value thing to
settle before any prose is written.
