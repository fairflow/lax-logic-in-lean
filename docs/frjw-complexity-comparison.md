# The Fiorentini–Ferrari duality: paper, IPC mechanisation, and the `◯` extension

*A complexity comparison, written 2026-09-02 on Matthew's question: "a
comparison in complexity between the original IPC paper and its proof
here and the extra components required for the ◯ rules would be useful;
the development still seems extremely complex despite your
simplification efforts."*

**Everything measured below comes from two fixed points**: the paper's
arXiv LaTeX source `frj-corr.tex` (arXiv:1804.06689, 6682 lines, located
in a prior session's scratchpad and read directly for this document),
and the repository at commit **`b2f2525`** (local branch
`claude/frjw-w1-w2-lean-5aabff`, also `origin/frjw-dev`). The IPC
baseline is measured at **`05994d5`**, the last commit at which
`FRJ/Calculus.lean` is still `◯`-free. Every number says how it was
obtained. Where I could not verify a claim I write UNCERTAIN and say
what would settle it.

Terminology, per the standing rule: objects of `FRJr`/`FRJi`,
`FRJVr`/`FRJVi`, `FRJWr`/`FRJWi` are **disproofs**. "Proof" and
"derivation" are reserved for `Gbu(G)`, `Gbu◯(G)`, `LaxND`, `G4c`, `SC`.

---

## 0. Summary table

Sizes are physical lines of source. "Here (IPC)" is `05994d5`; "here
(◯)" is `b2f2525`. Verdicts are argued in §5.

| Component | Paper (IPC) | Here (IPC) | Here (◯) | What `◯` adds | Verdict |
|---|---|---|---|---|---|
| **The refutation calculus** | Fig. `fig:FRJ` (source 1370–1500): 10 rule schemas (5 regular-conclusion, 5 irregular) | `FRJ/Calculus.lean` 191 lines, 12 constructors (6+6) | `FRJ/CalculusW.lean` 374 lines, 21 constructors (13+8); definition closure with `CalculusV` + `RefAt` + the shared formers ≈ 1610 lines | 9 constructors: `circIn`, `joinCirc`, `joinCircP`, `circNotIn`, `axIC`, `lift`, and the promise/fallible join pairs; the `Tag` index; `Covers`; `RefAt`/`KeptChain`; `classForce`/`vacZoneA` | intrinsic (rules), overhead (the `≐`/`Fin` plumbing) |
| **Soundness** (Thm 3.12 / `theo:soundFRJ`; Lemma 3.10 / `lemma:soundFRJ`; app. Lemma 16 / `app:lemma:soundFRJ`) | pp. 16–17 + appendix pp. 51–53 | `Model`+`Step`+`Extract`+`Sound` = 1637 lines | `StepW`+`ExtractW`+`SoundW` = 3167 lines (`SoundW` alone 1906 vs 515) | fallible worlds, the modal cone, `tag_cone`, `refAt_refutes_sf` and a second size-mutual induction inside the join case | intrinsic |
| **Completeness of the refutation calculus** | proved twice: §6 direct (Lemma 6.3 / `lemma:minMod`, Thm 5.13(i)) and via the duality (§4+§5) | direct route only: `Complete`+`Minimal` = 746 lines, unconditional | direct route **blocked**; `FRJ/Minimal.lean:483` keeps it only under a `◯`-freeness gate; the whole duality had to be built | the `(height, phase, size)` recursion has no consistent order for `◯` (documented argument, §4.3) | intrinsic, and the single largest cost |
| **The provability calculus** | Fig. `fig:GBU` (source 2960–3078): 14 rule schemas | `wip/gbu.lean` 523 lines, 16 constructors (10+6) | `wip/gbu_circ.lean` 2524 lines, 24 constructors (12+12) | `L◯`, `L◯ᵢ`, `R◯`, `R◯ᵢ`, `L⊃ᵢ` at a `◯` goal, plus `L⊥ᵢ`/`L∧ᵢ`/`L∨ᵢ` | intrinsic |
| **Termination of backward search** | Lemma 8 (`lemma:wggbu`) + Thm 7 (`theo:gbufin`), 1 page: `Wg(τ) = ⟨\|Sf^L(G)∖Cl(Ψ)\|, tp, \|τ\|⟩` | `wip/gbu.lean:433–501`, `wg_step`/`step_wf`, ~70 lines | REFUTED for the naive extension (`no_measure_stepC`), then re-won: `wip/gbu_measure.lean` 522 lines + `wgC` in the searcher | a two-cycle `Γ ⇒g Z ↦ Γ →g ◯Z ↦ Γ ⇒g Z` | intrinsic (the refutation is the point) |
| **Saturated databases** (§4: Lemma 5, Thm 4, Lemma 6, Thm 5) | pp. 21–23 | not attempted for IPC alone | `wip/gbu_frjw_closure.lean` 1803 + `wip/gbu_frjw_saturate.lean` 2434 = 4237 lines | derivation-carrying rows, `DBClosed` (21 clauses), canonical keying, the pigeonhole, choice-free skolemisation | mixed: intrinsic (the store is what buys termination) + heavy overhead |
| **The search procedure** (Thm 8 `theo:search`, Thm 9 `theo:GBU-FRJ`, Thm 10) | pp. 33–35 | `wip/gbu_search.lean` 602 lines (IPC `BSearch` correctness) | `wip/gbu_frjw_search.lean` 725 + `db` 569 + `circdb` 544 + `corner` 654 + `dichotomy` 132 + `exclusion` 47 = 2671 lines | the `◯Z`-corner and `totalityW`; `WUnrefutedBelow`; the inversion-lemma bank grows to 22 entries | intrinsic |
| **The crown** | Thm 10: completeness of both | not stated | `decideGbuW`, `frjw_complete`/`gbuw_complete`, `provableGbuC_iff_pll`, `decidePLL` (`wip/gbu_frjw_saturate.lean:2290–2340`) | the mechanised result is *stronger* than the paper's: it decides PLL | intrinsic |
| **Second completeness route** | none | none | `wip/gbu_ljfo*.lean` 1342 lines (`gbuC_complete` via LJF◯ focalisation) | deliberate redundancy, retained on the compaction's own verdict | residue (by choice) |
| **Superseded parallel calculi** | none | none | FRJ◯ line 9932 lines, FRJV line 6701 lines | the two earlier `◯` calculi, kept compiled | residue |
| **Retired search apparatus** | none | none | `wip/gbu_search_circ.lean` 1354 lines (`searchO`, `BigAnte`, `CleanReg`) | REFUTED supplies, kept for their live countermodels | residue |
| **TOTAL in the orbit** | 30 printed pages for §2–§5, plus 11 for §6 | 4837 lines | 39 567 lines, of which ≈ 34 730 are `◯`-attributable | ≈ 7.2× the IPC baseline | see §5 |

---

## 1. What is being compared, and the measuring rules

Three artefacts:

1. **The paper.** Camillo Fiorentini and Mauro Ferrari, *Duality between
   unprovability and provability in forward proof-search for
   Intuitionistic Propositional Logic*, ACM TOCL 21(3), 2020. Cited by
   journal number with the arXiv label in parentheses, per
   `docs/frj-fidelity.md`. Structure and page numbers below are read
   from the arXiv source `frj-corr.tex` and from
   `docs/frj-paper-skeleton.md`, whose numbers come from that source's
   compiled `.aux`.

2. **The IPC mechanisation here**, at `05994d5`: nine files under
   `FRJ/`, 3712 lines, soundness and completeness of FRJ(G) both PROVED.

3. **The `◯` development**, at `b2f2525`: `FRJ/` (24 573 lines) plus
   the `wip/gbu*` orbit (14 994 lines).

**Measuring rules.** Line counts are `wc -l` on the file as retrieved
by `git show <rev>:<path>`; they include docstrings and blank lines,
which in this repository are a large fraction (the calculus files are
about one-third docstring). Declaration counts are `grep` for
`theorem`/`lemma`/`def`/`abbrev`/`inductive`/`structure` at any
indentation; they undercount work badly in the soundness files, where a
single `theorem` can be 400 lines of case analysis, so for those I
quote lines. Nothing here was built; no Lean was run for this document.

---

## 2. The paper

### 2.1 Structure and size

`frj-corr.tex` is 6682 lines, of which 422 are preamble. Section spans
in source lines, and printed-page spans computed from consecutive
section start pages in `docs/frj-paper-skeleton.md`:

| Section | source lines | start page | span (pp.) |
|---|---|---|---|
| §1 Introduction | 240 | 1 | 4 |
| §2 Preliminaries | 99 | 5 | 1 |
| §3 The calculus FRJ(G) | 1890 | 6 | 15 |
| — §3.2 Countermodels and soundness | 233 | 16 | 2 |
| — §3.3 Termination | 395 | 19 | 2 |
| §4 Proof-search and saturated databases | 294 | 21 | 3 |
| §5 Gbu(G) and completeness of FRJ(G) | 1508 | 24 | 11 |
| §6 Minimality | 1355 | 35 | 11 |
| §7 Related and future work | 451 | 46 | 5 |
| §A Soundness of FRJ(G) (appendix) | 423 | 51 | 3+ |

The duality route proper is §2 + §3 + §4 + §5, i.e. **pp. 5–34, thirty
printed pages**, plus the three-page appendix that carries the actual
proof of the soundness lemma.

### 2.2 The numbered results

38 numbered items across 8 sections, 2 of them in the appendix
(`docs/frj-paper-skeleton.md`): 11 theorems, 17 lemmas, 10 examples.
On the duality route, 24 numbered items. Those the mechanisation cares
about:

| Item | Label | Statement |
|---|---|---|
| Thm 3.1 | `theo:FRJsound` | `⊢_FRJ(G) G` implies `G ∉ IPL` |
| Lemma 3.5 | `lemma:lhs` | (i) `σ₁ ↦ᴿ₀ σ₂`, `R ≠ ⊃∉` imply `Lhs(σ₂) ⊆ Lhs(σ₁)`; (ii) `σ₁ ↦₀ σ₂` implies `Lhs(σ₂) ⊆ Cl(Lhs(σ₁))`; (iii) same for `↦*` |
| Lemma 3.10 | `lemma:soundFRJ` | for every `σ` in `D`: (i) `σ = Γ ⇒ C` implies `φ(σ) ⊩ Γ` and `φ(σ) ⊮ C`; (ii) `σ = Σ;Θ → C`, `σ ↦ σ_p ∈ PS(D)`, `σ_p ⊩ Σ ∩ Sf⁻(C)` imply `σ_p ⊮ C` |
| Thm 3.12 | `theo:soundFRJ` | `Mod(D)` is a countermodel for `G` |
| Lemma 3.x | `lemma:wg` | `σ₁ ↦ σ₂` implies `⟨0,0,0⟩ ⪯ wg(σ₂) ≺ wg(σ₁)` |
| Lemma 4.x | `lemma:subsRules` | rules are monotone under `⊑` |
| Thm 4.x | `theo:fsearchAdequate` | `FSearch` is an adequate proof-search procedure |
| Thm 4.x | `theo:uniquetSatDB` | a unique compact (= minimum) saturated database exists |
| Lemma 5.x | `lemma:GBUsound` | `⊢_Gbu(G) τ` implies `τ` valid |
| Lemma 5.x | `lemma:wggbu` | every Gbu(G) rule strictly decreases `Wg` |
| Lemma 5.x | `lemma:gbuInv` | **nine** invertibility clauses for `▷` (counted: the `\item`s at tex 3828–3868; the in-repo ledger at `wip/gbu_circ.lean:15` says ten, which I could not reproduce) |
| Lemma 5.x | `lemma:gbuSuccAt`, `lemma:gbuSuccOr` | the two success lemmas |
| Thm 5.x | `theo:search` | `Search(τ, D_G)` computes a Gbu(G)-derivation of `τ` |
| Thm 5.x | `theo:GBU-FRJ` | `⊢_Gbu(G) G` iff `⊬_FRJ(G) G` |
| Thm 5.13 | (no own label) | (i) `G ∉ IPL` implies `⊢_FRJ(G) G`; (ii) `G ∈ IPL` implies `⊢_Gbu(G) G` |
| Lemma 6.3 | `lemma:minMod` | from a countermodel and a world, build an irregular and a regular FRJ(G)-derivation with rank bounds |
| Lemma 6.7 | `lemma:closure` | `Λ_α = Cl(Λ_α) = Cl(Λ*_α)` |

### 2.3 Rule counts and side conditions

**FRJ(G)** (Fig. `fig:FRJ`, source 1370–1500), ten rule schemas:
regular-conclusion `Ax^R`, `∧`, `⊃∈`, `⋈^At`, `⋈^∨`;
irregular-conclusion `Ax^I`, `∧`, `∨`, `⊃∈`, `⊃∉`. With `k ∈ {1,2}`
expanded, twelve rule instances. Blanket side condition on every
conclusion: `Rhs(σ) ∈ Sf^R(G)`.

The join rules' side conditions, verbatim from the figure:

    (J1)  Σᵢ ⊆ Σⱼ ∪ Θⱼ   for every i ≠ j
    (J2)  Y ⊃ Z ∈ Σ^⊃   implies  Y ∈ Υ
    ⋈^At extra:  F ∈ Prime ∖ Σ^at
    ⋈^∨  extra:  {C₁, C₂} ⊆ Υ

with the conclusion zones

    Σ^at = ⋃ⱼ Σⱼ^at    Θ^at = ⋂ⱼ Θⱼ^at    Σ^⊃ = ⋃ⱼ Σⱼ^⊃
    Θ^⊃  = (⋂ⱼ Θⱼ^⊃) / Υ        where  Γ^⊃/Υ = { Y ⊃ Z ∈ Γ^⊃ | Y ∈ Υ }

**Gbu(G)** (Fig. `fig:GBU`, source 2960–3078), fourteen rule schemas:
regular `Ax`, `L⊥`, `L∧`, `R∧`, `L∨`, `R∨ₖ`, `L⊃`, `⊃R_i`, `⊃R_ni`;
irregular (right-focused, no left rules) `Ax`, `R∧`, `R∨ₖ`, `⊃R_i`,
`⊃R_ni`. With `k` expanded, sixteen instances.

### 2.4 The two termination measures

The paper's forward measure for FRJ(G) (source 2292–2308):

    wg(σ) = ⟨ |Cl(Γ) ∩ Sf^L(G)| , tp(σ) , |G| − |C| ⟩,
    tp(σ) = 0 if σ regular, 1 otherwise,       lexicographic,

resting on three properties: `Cl` only shrinks along `↦`; `⊃∉` shrinks
it strictly; a non-join rule shrinks `|G| − |C|`.

The paper's backward measure for Gbu(G) (source 3196–3212):

    Wg(τ) = ⟨ |Sf^L(G) ∖ Cl(Ψ)| , tp(τ) , |τ| ⟩,
    tp(τ) = 1 if τ regular, 0 otherwise.

The middle component exists for exactly one step in each: the join
conclusion (irregular premise, regular conclusion) in FRJ(G), and
`L⊃`'s left premise plus `R∨ₖ`'s premise (regular conclusion,
irregular premise) in Gbu(G).

---

## 3. The IPC mechanisation, at `05994d5`

### 3.1 Scope and route

From `docs/frj-fidelity.md` ("Scope"): **in scope** are §2, §3 and
§3.2, and completeness of FRJ(G); **out of scope** are Gbu(G),
saturated databases, `Search`, §3.3's termination and complexity, and
§6's minimality beyond what completeness needs.

Completeness was taken by the **direct §6 route** (Lemma 6.3
`lemma:minMod`, giving Thm 5.13(i)) rather than through the duality,
for the reason the document gives: "It is equally published, it is a
fraction of the work, and it does not require formalising a second
calculus and a search procedure to obtain a theorem about the first."

### 3.2 Sizes

| File | lines | thm | def |
|---|---|---|---|
| `FRJ/Basic.lean` | 1044 | 61 | 29 |
| `FRJ/Calculus.lean` | 191 | 4 | 8 |
| `FRJ/Model.lean` | 219 | 6 | 2 |
| `FRJ/Step.lean` | 427 | 18 | 4 |
| `FRJ/Extract.lean` | 476 | 13 | 11 |
| `FRJ/Sound.lean` | 515 | 15 | 0 |
| `FRJ/Complete.lean` | 253 | 11 | 5 |
| `FRJ/Minimal.lean` | 493 | 7 | 10 |
| `FRJ/Audit.lean` | 94 | 0 | 0 |
| **total** | **3712** | **135** | **69** |

The calculus is 191 lines for the paper's ten rule schemas, twelve
Lean constructors (`FRJr`: `axR`, `andR1`, `andR2`, `impIn`, `joinAt`,
`joinOr`; `FRJi`: `axI`, `andI1`, `andI2`, `orI`, `impInI`,
`impNotIn`). Every side condition is a constructor field; the blanket
`Rhs(σ) ∈ Sf^R(G)` is the field `hgoal`.

Axiom pins at that commit (`FRJ/Audit.lean`, `#guard_msgs`-guarded):
`soundness`, `completeness`, `completenessData`, `frj_iff_countermodel`,
`minMod`, `modR_countermodel`, `lemma39R`, `lemma39I`,
`lhs_clo_of_steps`, `minEta` all at `[propext, Quot.sound]`;
`Kripke.decForce`, `Kripke.force_mono`, `not_IPL_of_countermodel`,
`maxOn`, `eq_nil_of_forall_not_mem` at no axioms at all; and
`frj_iff_not_IPL` at `[propext, Classical.choice, Quot.sound]`, the
choice being a property of the statement (`¬∀K` to `∃K`), not of the
proof.

### 3.3 The divergences, and what they cost

From `docs/frj-fidelity.md` "Divergences, in full", plus the later
corrections:

1. **Worlds of `Mod(D)` are p-sequent occurrences, not p-sequents.**
   The paper's `PS(D)` identifies two occurrences of the same sequent;
   we do not. `Mod(D)` is a countermodel iff its quotient is, so
   soundness is insensitive; the identification matters only for §6's
   minimal-height results, which are out of scope.

2. **The `⊃`-clause of forcing is written as an implication**, not the
   paper's disjunction. Writing the disjunction would put excluded
   middle into the definition.

3. **`k ∈ {1,2}` is two constructors.**

4. **Sequent well-formedness is a lemma, not a type index.** The paper
   defines the sequent set by `Γ ⊆ Ĝ`, `Σ ∪ Θ ⊆ Ĝ`, `C ∈ Sf^R(G)`; here
   the judgment is indexed by plain lists and the blanket goal
   condition is a field. The context constraints then have to be
   proved: `wf : FRJr G Γ C → Γ ⊆ gHat G`, which is what licenses
   `atPart`/`impPart` not silently dropping anything at the joins.

5. **Lists, not `Finset`s.** Traced, not guessed: mathlib's
   `Finset.instUnion`, `Finset.erase`, `Finset.image` and
   `Multiset.ndunion` are choice-tainted at the *definition* level, so
   a term merely mentioning `s ∪ t` carries `Classical.choice` however
   it is proved. Only `Finset.filter` is clean. The `List` API is
   axiom-free at definition level.

6. **`≐` (extensional context equality) replaced the normal form `nf`.**
   The first attempt normalised computed contexts (`nf G (St ++ Lam)`
   in a constructor index); that was green slime and it also
   strengthened `⊃∈`'s side condition from `A ∈ Cl(Σ ∪ Λ)` to
   `A ∈ Cl(nf G (Σ ∪ Λ))`, a genuine divergence. Deleting `nf` and
   stating the context equations as `CtxEq l m := ∀ x, x ∈ l ↔ x ∈ m`
   restored the paper's conditions and made the transport a theorem
   (`transportR`, `transportI`). Cost: the `≐` block in
   `FRJ/Basic.lean:1048–1108` (61 lines, replacing `nf`'s 57) plus
   about 55 lines of transport per calculus family.

7. **Joins are indexed by `Fin (n+1)`.** The paper's `n ≥ 1` premises
   become `prem : ∀ j : Fin (n+1), FRJi G (stab j) (th j) (rhs j)`, with
   `unionAll`/`interAll` defined over `List.finRange`. The archived
   parallel development `Archive/FRJLax-parallel/` used a nonempty
   vector instead and recorded that as a deliberate divergence; the
   `Fin` encoding is what the live line uses, and it is the source of
   the reindexing work in the saturation stage (§4.6).

8. **Completeness is Type-valued.** Lemma 6.3's two halves are records
   carrying the derivation (`IrrWit`, `RegWit`), because extracting a
   disproof from an existence proof needs `choose` or `Nonempty.some`.
   The payoff: `completenessData : (K : Kripke) → ¬ K.valid G →
   Derivation G` is an algorithm.

9. **A divergence found in the paper.** Lemma 6.7 (`lemma:closure`) as
   stated, `Λ_α = Cl(Λ_α) = Cl(Λ*_α)`, is FALSE in its first equality:
   `Cl` is generated by a grammar in which `A` ranges over all
   formulas, so `Cl(Λ_α)` contains `Z ⊃ C` for arbitrary `Z`, which
   need not lie in `Sf^L(G)`. Both directions the construction uses are
   true and are proved (`forces_clo_lamStar`, `mem_clo_lamStar`).

---

## 4. The modal extension, component by component

The modal line went through three calculi, in this order. Keeping them
apart is essential to reading the numbers.

* **FRJ◯** (`FRJ/Calculus.lean` and its `Model`/`Step`/`Extract`/
  `Sound`/`Complete`/`Minimal`/`Saturate`/`Modal`/`Fallible`/`Erase`/
  `Profile` companions, 9932 lines): the paper's FRJ(G) plus our W3/W4
  modal devices. Soundness PROVED; completeness **REFUTED** at the two
  witnesses #80/#81.
* **FRJV** (`FRJ/CalculusV.lean` and companions, 6701 lines): the
  `RefAt` repair of the #80/#81 gap. Soundness PROVED; completeness
  never established.
* **FRJW** (`FRJ/CalculusW.lean`, `StepW`, `ExtractW`, `SoundW`, 3541
  lines): FRJV plus `lift`, minus `⊃∉`. Soundness PROVED afresh;
  completeness PROVED, via the duality.

### 4.1 (a) What the `◯` rules add to the disproof calculus

`FRJ/CalculusW.lean:52–241`. The `#slime` pins at `:358–372` record the
shape: **13 regular constructors, 8 irregular, 0 carrying green slime**,
against the IPC family's 6 and 6.

The nine new constructors, and the semantic fact forcing each:

| Constructor | Rule | Why it exists |
|---|---|---|
| `circIn` (`◯∈`) | `Γ ⇒ Z` infers `Γ ⇒ ◯Z` when the root's whole modal cone refutes `Z` | the `◯`-clause quantifies over the `≤`-cone and asks for an `Rm`-successor of each of its worlds; the tag is the syntactic record making that decidable |
| `joinCirc` (`⋈^◯`) | from irregular premises with `Z ∈ Υ`, infer `Γ ⇒ ◯Z` at a barren root | `◯∈` cannot reach it: its regular premise `Γ ⇒ Z` for `Z = A ⊃ B` only exists at roots forcing `A`, while a `◯(A⊃B)`-refuting root may have its `A`-witness strictly above (cell `circ_circ_imp`, `wip/frj_sat.lean`) |
| `joinCircP` (`⋈^◯,p`) | the promise variant, cone = the promise family | there is no fallible variant: a fallible cone-member forces every body |
| `circNotIn` (`◯∉`) | from `Γ ⇒ Z` with a clean tag, infer `∅ ; Θ → ◯Z` | without it no derivable context contains an implication with a modal antecedent, since (J2) demands the antecedent among the premises' right formulas and nothing produced `rhs = ◯Z` (`docs/frj-w4.md` §1 (D2)) |
| `axIC` (`Ax^I◯`) | `∅ ; vacZone(ats) → ◯F` for a classically `F`-refuting valuation | `◯∉`'s zone is capped by `Cl` of a context, which cannot see vacuous forcing (`Cl(∅) = ∅` in an atom-free signature); that cap is what made `¬¬◯⊥` underivable |
| `lift` | `Γ ⇒ C`, `Θ ⊆ Ĝ ∩ Cl(Γ)` infers `∅ ; Θ → C` | the irregular duality has a hole at `◯(◯Z ⊃ Z)`; a regular disproof exists (`provableV_Gcc`) but is unusable where the join's *schema* reading is required |
| `joinAtP`, `joinOrP` | promise joins, `k+1` extra regular premises `Δᵢ ⇒ Dᵢ` becoming modal successors | a `◯`-goal needs modal successors that the paper's model construction never builds |
| `joinAtF`, `joinOrF` | fallible joins | `¬◯⊥` is IPL-valid but not PLL-valid, so a calculus whose models are all infallible is incomplete (`valid_neg_circ_bot_of_infallible`) |

`⊃∉` (`impNotIn`) is **deleted** in FRJW: it is `lift` composed with
`⊃∈`, and its extra condition `¬ Cl(Θ) ∋ A` is not needed
(`docs/frjw-plan.md` §1). `FRJ/CalculusW.lean:333–334` is the
reconstruction, and `disprovableW_of_provableV`
(`FRJ/CalculusW.lean:343–350`, `[propext, Quot.sound]`) is the
conservativity theorem.

The supporting apparatus, all of it new:

* **`Tag`** (`FRJ/Calculus.lean:311–319`): `barren | chain (D : Form) |
  blocked`. It records what the root's modal cone is. Its semantic
  content is the canonical model's `mfal` pledge component
  (`LaxLogic/PLLCompleteness.lean`), restricted to a single pledge.
* **`Covers`** (`FRJ/Calculus.lean:238–243`), five clauses: a chain
  certificate for `W` transfers to every `Z` reachable from `W` by
  `◯`, `∧`-superformula, and `⊃`-superformula with `Clo Γ A`. Needed
  because a single-formula tag cannot re-certify itself across `◯∈`
  nesting or the `∧`/`⊃` wraps of the completeness visit.
* **`RefAt`** (`FRJ/RefAt.lean:36–48`), seven clauses:

      C ∈ Υ                                  (the premise mechanism)
      ⊥                                      (the root is infallible)
      A ⊃ B   if A ∈ Cl(ctx), B ∈ RefAt      (the root is its own witness)
      ◯Z      if Z ∈ RefAt, cone = true      (barren roots only)
      Z₁ ∨ Z₂ if both;   Z₁ ∧ Z₂ if either

  with the semantic kill lemma `refAt_refutes` (`:442–465`) and its
  subformula-graded variant `refAt_refutes_sf` (`:471–509`).
* **`KeptChain`** (`FRJ/RefAt.lean:144–150`) and the greedy fixpoint
  `keptOf` (`:245–257`) with `keptOf_saturated` (`:374–386`). The
  stratification is load-bearing: a self-referential retention
  condition admits mutually-justifying kept pairs with no soundness
  argument, so each link may cite only the base context and the links
  before it.
* **The zone restrictions**: `restrictC` (`Θ^◯/Cl(Δ⃗)`, an existential
  over the promise family, `FRJ/Calculus.lean:67–84`) and `restrictP`
  ((J7) as a restriction, `:98–113`). Both are modelled on the paper's
  `Θ^⊃/Υ`.
* **`classForce`/`vacZoneA`** (`FRJ/Calculus.lean:186–206`): the
  classical theory of a final world, which `Ax^I◯` needs as a zone.

New join side conditions, beside the paper's (J1), (J2):

    (J5)  ◯Y ∈ ⋃ⱼ Σⱼ^◯  implies  ∃i, Y ∈ Cl(Δᵢ)
    (J7)  ∀ i j, ∀ X ∈ Σⱼ, X ∈ Cl(Δᵢ)
    hcirc (barren joins)  ⋃ⱼ Σⱼ^◯ = []
    htag  the pledge condition on the promise family
    hkc   the KeptChain certificate on the kept zone
    hJ2 on ⋈^◯, relaxed 2026-09-01 with Matthew's sign-off, from
         A ⊃ B ∈ ⋃ⱼ Σⱼ^⊃ → A ∈ Υ
      to A ⊃ B ∈ ⋃ⱼ Σⱼ^⊃ → RefAt true Υ (base ++ kept) A

### 4.2 (b) What the soundness proof needed that the paper's does not

The IPC soundness stack is `Model` + `Step` + `Extract` + `Sound` =
1637 lines. The FRJW stack is `StepW` + `ExtractW` + `SoundW` = 3167
lines, on top of a `FRJ/Model.lean` that itself grew from 219 to 249.
`SoundW` alone is 1906 lines against `Sound`'s 515: **3.7×**.

Where the extra 1391 lines go:

* **The models carry two more fields.** `Kripke` gains `Rm` (modal
  accessibility) and `Fal` (fallible worlds), i.e.
  Fairtlough–Mendler's constraint models. `FRJ/Basic.lean` grows a
  144-line block, "The two facts every modal rule needs"
  (`:439–582`), that does not exist in the IPC file.
* **`Mod(D)` is no longer barren.** In the IPC construction a join's
  conclusion is a fresh world below the disjoint union of the premises'
  posets. With `◯` there are three further world sources: promise
  components (mounted as modal successors), the declared fallible
  world, and the `Ax^I◯` leaf, which is the only axiom that
  *contributes* a world.
* **The join case runs a second size-mutual induction.** In the paper
  the join case carries one secondary induction on `size H`, proving
  (P2) `H ∈ Γ^⊃ ⟹ σ ⊩ H` and (P3) `H = A_j ⟹ σ ⊮ A_j` together. After
  the (J2) relaxation the base and kept implications share ONE such
  induction, founded by `refAt_refutes_sf`: both the `ups`-leaves and
  the `Clo`-leaves of a certificate are subformulas of its target.
  Without that subformula bound the induction is not founded.
* **`tag_cone`.** `◯∈` is sound exactly when every world of the root's
  modal cone refutes the body; the tag has to be shown to mean that.
  There is no IPC analogue at all.

`soundnessW : DisprovableW G → ¬ PLL G` is at
`FRJ/SoundW.lean:1875–1877`, pinned `[propext, Quot.sound]`.

### 4.3 (b) Why the paper's cheap completeness route is unavailable

This is the single most important fact in the comparison, and it
explains most of the size difference.

The paper's §6 route builds an FRJ(G)-derivation from an arbitrary
countermodel by a triple induction, realised here as the lexicographic
measure `(ht K a, t, C.size)`: the height of the world, the sequent type
(irregular before regular), and the size of the goal
(`docs/frj-fidelity.md`, §6 section). That is 746 lines for IPC and it
is unconditional.

For `◯` it does not work, and the reason is recorded as an argument in
`docs/frj-w4.md` §9 and §10 addendum:

* The `◯`-body edge `I(◯Z) → R(Z)` fires at a world `a` with
  `cone(a) = {a}`, `a ⊮ Z`, `∀v > a: v ⊩ ◯Z`. That configuration is
  Kripke-realisable, and there the premise anchor can only be `a`
  itself, so the irregular `◯Z`-visit calls the regular `Z`-visit **at
  the same world**. Under `(ht, t, |C|)` this edge *increases* `t`.
* Under size-priority `(ht, |C|, t)` the Υ-edge breaks instead: the
  (J2) cells for stable-implication antecedents `A` have `|A|`
  unbounded relative to the goal, and force irregular-before-regular
  phase priority at fixed height, which is the paper's own (IH2).
* The abstract call graph at a fixed world contains the cycle
  `I(◯Z) → R(Z) → I(Y)` with `◯Z` a subformula of `Y`, then back to
  `I(◯Z)` (realisable with `(◯Z ⊃ W) ∈ Λ*_a`, or with `Y = ◯Z ∨ W` as a
  goal disjunct).

The §10 addendum's conclusion: "No lexicographic combination of
(height, phase, size) satisfies both; the supply order that resolves a
given instance depends on the model … so the induction order must be
computed per instance, and this is precisely what saturation is."

**Status.** That is a documented argument with a Kripke-realisability
claim, not a kernel-checked theorem. It is the analogue of
`no_measure_stepC` (§4.4) for the completeness recipe rather than for
the search, and no such sharp form has been proved. Marked **UNCERTAIN**
as a formal claim. What would settle it: a theorem of the shape
`no_measure_stepC` for the visit's call relation, i.e. exhibit the cycle
as a two-cycle of an explicit relation and conclude that no measure into
any well-founded order can decrease along it.

What is PROVED on that route:

* `FRJ/Minimal.lean:483`: `completeness` survives, but under a
  `◯`-freeness gate `hcf : ∀ X ∈ sfR G ++ sfL G, X.isCirc = false`. The
  paper's theorem holds here only for `◯`-free goals.
* `FRJ/Complete.lean:621`: `provable_root_countermodel : Provable G →
  ∃ K, ¬ K.Fal K.root ∧ ¬ K.valid G`, the soundness half, with no
  `◯`-freeness hypothesis.
* `FRJ/Saturate.lean` (1565 lines): the replacement organisation, with
  conditional results only: `completeness_of_supply`,
  `completeness_of_allMet`, `completeness_of_endpoints`,
  `completeness_of_coneGrounded`, `completeness_of_rmFull`,
  `completeness_of_discrete`. Unconditional FRJ◯ completeness was never
  reached on that route.

And the calculus-level refutations that closed the FRJ◯ line
altogether:

    FRJ80.frj_incompleteness_80 : ¬ PLL G80 ∧ ¬ Provable G80   (wip/frj80_noprov.lean:188)
    FRJ81.frj_incompleteness_81 : ¬ PLL G81 ∧ ¬ Provable G81   (wip/frj81_noprov.lean:506)
    FRJ80.not_CompletenessFRJ   : ¬ Certified.CompletenessFRJ  (wip/frj80_noprov.lean:198)

with `G80 = ρ12 ⊃ ρ9`, `G81 = ρ13 ⊃ ρ6`, all `[propext, Quot.sound]`.
The mechanism, in one sentence from HANDOFF §2026-08-25c: join contexts
cannot retain an implication forced *vacuously* at the world being
created (its antecedent `ι = ¬¬◯⊥ ⊃ ◯⊥` is refuted with the new world
itself as witness), and both `Cl` and the Υ-restriction are blind to
that. `RefAt` is exactly the repair, and FRJV/FRJW carry it.

### 4.4 (b) Gbu◯ and the termination refutation

`wip/gbu.lean` transcribes Gbu(G) in 523 lines: 16 constructors, Lemma
7 (soundness, `:226–243`), Lemma 8 (`wg_step`, `:433–461`) and the
well-foundedness that Theorem 7 buys (`step_wf`, `:497–501`). Divergence
D5 is recorded: the `O(|τ|²)` height bound is not mechanised, because
what backward search needs is well-foundedness, and that is what is
proved.

`wip/gbu_circ.lean` (2524 lines) extends it. Measured constructor
counts at `:1266–1365`: **`GbuRC` 12, `GbuIC` 12**, against `GbuR` 10
and `GbuI` 6. Note a stale docstring: the header at `:1242` says "Six
new constructors"; the family as built carries **eight**
(`lcirc`, `rcirc` on the regular side; `lcircI`, `limpLI`, `lbotI`,
`landLI`, `lorLI`, `rcircI` on the irregular). The three
`◯`-goal-restricted left rules `lbotI`/`landLI`/`lorLI` are not in the
displayed rule figure of that docstring. This is a documentation defect,
not a soundness one: `soundIC` covers all twelve.

Two REFUTED statements shaped this calculus, both kernel-checked and
both pinned "does not depend on any axioms":

    not_wf_stepC (G : Form) :
      ¬ WellFounded (fun p q : Bool × List Form × Form => StepC G p q)
                                        (wip/gbu_measure.lean:87–93)

    no_measure_stepC (G : Form) {β : Type} (m : cell → β)
      {lt : β → β → Prop} (hwf : WellFounded lt)
      (hm : ∀ p q, StepC G p q → lt (m p) (m q)) : False
                                        (wip/gbu_measure.lean:103–107)

The witness is a two-cycle: with `Γ = ◯Z ⊃ B, Ψ`, the step `L⊃` on
`◯Z ⊃ B` takes `Γ ⇒g Z` to `Γ →g ◯Z`, and `R◯ₙᵢ` takes `Γ →g ◯Z` back
to `Γ ⇒g Z`. So the paper's `Wg` is not merely hard to repair for `◯`:
**no function of the sequent whatsoever can serve as a measure**, into
any well-founded order.

Two further kernel-checked refutations settled the rule design:

* `rcircNI_not_invertible` (`wip/gbu_circ.lean:746`,
  `[propext, Quot.sound]`) refutes the licence for `R◯ₙᵢ`;
* `not_gbuR_omegaNI` (`:1191`, `[propext]`) refutes its completeness,
  and is what forced admitting `L⊃ᵢ` in the irregular judgment: `Ω ⊢ ◯q`
  can need modus ponens on an implication of `Ω`, and no `◯` rule
  substitutes for it.

`L⊃ᵢ`'s own side condition then had to be adapted. It read
`A.hasCirc = false ∨ A.size < |◯C|`, and that makes the calculus
incomplete: the cell

    [◯((◯p ⊃ r) ∧ ◯p)] ⇒g ◯r ∨ z

is PLL-valid, but the `∨`-goal blocks `L◯`, `R∨ₖ` forces the irregular
`◯r`-goal, and there every route dies on `|◯p| < |◯r|` (2 < 2). The
licensed replacement (`wip/gbu_circ.lean:1338–1342`) is
`A.hasCirc = false ∨ A ∈ sfR G`: a modal antecedent is admitted whenever
it is a right-signed subformula of `G`, which is where every left
implication's antecedent lives. `soundIC` never used `hsz`, so soundness
is untouched.

Conservativity over the IPC calculus is a **gate, not a remark**:
`deCircR`/`deCircI` (`:1497–1527`) is a total translation of Gbu◯ into
Gbu for `◯`-free `G`, so a rule that could fire on `◯`-free input stops
that translation compiling. `provableGbuC_iff_provableGbu` at `:1558`.

`L◯`'s goal must be `◯`-shaped, and that is a theorem
(`lcirc_goal_must_be_circ`, `:248`), not a convention: unrestricted the
rule is unsound.

Finally, the header ledger of `wip/gbu_circ.lean:9–21` still records
Thm 8, Thm 9, Thm 10 as OPEN. That is a snapshot from 2026-08-30 and is
now stale: they were closed for FRJW (not for FRJ◯) on 2026-09-01.

### 4.5 (b) The searcher, the corner, and totality

The cell-level statement (`wip/gbu_frjw_dichotomy.lean:114–130`):

    WSearchOk G D (true, Ψ, C) =
      (∀ X ∈ Ψ, X ∈ Sf^L G) → C ∈ Sf^R G →
      ¬ WEvalR D Ψ C → GbuRC G Ψ C

    WSearchOk G D (false, Ω, C) =
      (∀ X ∈ Ω, X ∈ Sf^L G) →
      (C.isCirc = false → ∀ X ∈ Ω, X ∈ Ĝ) → C ∈ Sf^R G →
      WUnrefutedBelow G D Ω C → GbuIC G Ω C

Three things here have no IPC counterpart.

* **`WUnrefutedBelow`** (`:103–108`). In irregular mode the bare
  negative fact `¬ WEvalI D Ω C` is *vacuous* at a context outside `Ĝ`,
  because every irregular row has `Ĝ`-bounded zones, so nothing could
  answer. The invariant therefore carries a `Ĝ`-bounded ancestor `Ω₀`
  alongside. This is a strengthening of the paper's (BSr1).
* **The tag is explicit in the regular database sequent** (`WSeq.reg t
  Γ C`, `:58–60`) and `WSubsumes` is tag-aware through the retention
  order `tagLeB` (`blocked ≤ chain D ≤ barren`). The paper's `⊑` is
  plain zone inclusion.
* **The measure `wgC = (unclosed G Ψ, tpC reg C, seqSize Ψ C)`** where
  `tpC` is 2 for regular, else 1 if `◯` occurs in `C`, else 0. The
  paper's `tp` is a Boolean; here the goal's modality has to be graded
  as well, and by `hasCirc`, not `isCirc` (the `R∧ᵢ` step at
  `C₁ ∧ ◯C₂`).

**The corner.** One cell shape resists the rule-by-rule walk: irregular
mode, goal `◯Z`, context inside `Ĝ_at ∪ Ĝ_imp`, `Z` refuted. A
constructor sweep (PROVED, by cases on `FRJWi`) shows the only row
manufacture left is the barren `⋈^◯` join followed by `lift`. A join
retains a context implication in exactly one of three ways: its
antecedent has a row; its antecedent has a `RefAt` certificate; or its
consequent is `Clo`-available in the join context.

**`totalityW`** (`wip/gbu_frjw_search.lean:278–324`) closes it: at a
critical cell, every `X ∈ Sf^R(G)` is `RefAt`-refutable over `Z :: R₀`
(`R₀` = all refuted forms) **or** `Gbu◯`-derivable, by structural
induction on `X`, because `RefAt`'s clauses and the irregular
introduction rules are De Morgan duals:

    ∧ : one side refuted            vs  both sides derivable
    ∨ : both sides refuted          vs  one side derivable
    ◯ : body refuted (cone)         vs  body derivable (R◯ᵢ)
    ⊃ : Clo-antecedent + refuted body  vs  R⊃ / R⊃ₙ
    atom : absent (refuted)         vs  present (ax)

The atom clause is the pivot: an atom present in the context makes the
subgoal derivable by `ax`, and an atom absent from the context is always
refuted (`evalI_axI_gHat`: the `Ax^I` row covers every critical cell the
atom is not in). There is nothing to prove here for IPC, because there
is no `◯`-goal.

**The inversion-lemma bank** is the strategy that makes `searchW` a
walk rather than a search: for every Gbu◯ rule, a lemma saying that if
the store answers the premise query it answers the conclusion query.
Each is proved once, by opening `WSaturated` (`.1` extracts the premise
row's disproof, `.2` re-stores the FRJW constructor applied to it). The
bank has 22 entries with 39 consumption sites
(`docs/frjw-recursion-explainer-plan.md` §C.11). The paper's Lemma 9
(`lemma:gbuInv`) has nine clauses, mechanised as `gbuInv1`–`gbuInv10`
(`gbuInv3` splits by disjunct); ours adds `gbuInv11` (`L◯`),
`gbuInv14` (the `Ĝ`-ancestor step at a `◯` goal), `gbuInvLift`,
`evalI_axI_gHat`, `wEvalI_axIC`, `gbuSuccCirc`,
`refutedCleanly_circ_certs`, and the two `WUnrefutedBelow` wrappers.

### 4.6 (b) The closure and saturation stage

The paper gets its saturated database in three pages (§4): `FSearch` is
adequate (Thm 4), the compact saturated database is unique and minimum
(Thm 5), and the rows are *sequents*. Here the rows carry their
disproofs as data, and the whole stage is 4237 lines:

* **`DBClosed`** (`wip/gbu_frjw_closure.lean:1179–1339`), a
  **21-field** structure, one clause per FRJW rule, each saying: given
  stored premise sequents and the rule's side conditions, the store
  holds a subsumer of the conclusion.
* **T-A**: every `KeptChain` link lands in the greedy `keptOf`
  (`keptChain_sub_keptOf_of_le`, `closure:67–82`), in a
  parameter-growth form that absorbs zone growth under premise swap.
* **T-B**: monotonicity for all 21 rules. The eleven standalone `_mono`
  defs (`closure:235–869`, about 275 lines by span measurement) are
  **archived in place** with zero code consumers; the live content is
  the `_of_swap` transfer lemmas and the context-inclusion lemmas.
* **T-C**: the mutual induction `tCr`/`tCi` (`closure:1496–1677`), 13 +
  8 cases matching the 21 `DBClosed` fields one for one, giving
  `tC_of_closed` (`:1680`) and `decideGbuW_of_dbClosed` (`:1687`).
  Family premises are skolemised without choice by `irrPick`/`regPick`
  through `List.find?` over the decidable subsumption test.
* **The construction of the store** (`wip/gbu_frjw_saturate.lean`):
  19 emitters (`:1206–1213`) flattened into `stepAll` (`:1216`), the
  fuel recursion `sat` (`:1308`), `closureDB` (`:1368`) with fuel
  `(univList G).length + 1`, and the pigeonhole that says the fuel
  suffices. Canonical keying (`canonSeq`) is what makes the pigeonhole
  finite despite rows being stored in former-shaped contexts.

Three `Classical.choice` leaks were driven out at this stage with
`#choice_path`: the `finRange` `Ord` chain in the `Fin` deciders (hence
the hand-built `decForallFin`/`decExistsFin`), mathlib's `mem_dedup`
(hence `dedupF`), and a `simpa` through `Order.lt_add_one_iff`. This is
not fastidiousness: a decidability theorem that secretly used choice
would be worthless, and the standing rule is that a `Decidable`
hypothesis must not be discharged by `Classical.choice`.

### 4.7 (c) The crown, and sizes beside the IPC baseline

`wip/gbu_frjw_saturate.lean:2284–2340`, all sorry-free,
`#guard_msgs`-pinned `[propext, Quot.sound]`:

    dbClosed_exists (G) : ∃ db, DBClosed G db
    decideGbuW (G) : ProvableGbuC G ⊕' DisprovableW G
    frjw_complete : ¬ ProvableGbuC G → DisprovableW G
    gbuw_complete : ¬ DisprovableW G → ProvableGbuC G
    provableGbuC_iff_pll : ProvableGbuC G ↔ PLL G
    disprovableW_iff_not_pll : DisprovableW G ↔ ¬ PLL G
    decidePLL (G) : Decidable (PLL G)
    decideGbuWData (G) : GbuRC G [] G ⊕ (Σ' t Γ, FRJWr G t Γ G)   (:2388)

The last is the bare form: the proof object or the disproof object, no
truncation. The paper's Theorem 10 is the first two of these for IPC;
`decidePLL` has no counterpart in the paper at all, and is strictly more
than the paper claims.

**Sizes, side by side.**

| Layer | IPC (`05994d5`) | `◯` (`b2f2525`) | ratio |
|---|---|---|---|
| syntax, subformulas, closure, models | `Basic` 1044 | `Basic` 1298 + `RefAt` 510 | 1.7× |
| the disproof calculus | `Calculus` 191 | `CalculusW` 374 (definition closure ≈ 1610) | 2.0× (8.4×) |
| step relation and model extraction | `Model` 219 + `Step` 427 + `Extract` 476 = 1122 | `Model` 249 + `StepW` 758 + `ExtractW` 503 = 1510 | 1.3× |
| soundness | `Sound` 515 | `SoundW` 1906 | 3.7× |
| completeness of the disproof calculus | `Complete` 253 + `Minimal` 493 = 746 | the whole duality: 2671 (search) + 4237 (closure/saturation) + 3046 (Gbu◯) = 9954 | 13.3× |
| the provability calculus | (out of scope in the IPC snapshot; `wip/gbu.lean` 523 + `wip/gbu_search.lean` 602 later) | `gbu_circ` 2524 + `gbu_measure` 522 | 2.7× on the calculus file |
| **orbit total** | 4837 | 39 567 | 8.2× (7.2× on `◯`-attributable work) |

The 4837 figure is `05994d5`'s nine FRJ files (3712) plus the IPC
Gbu(G) files that came later but are `◯`-free (`wip/gbu.lean` 523,
`wip/gbu_search.lean` 602). The comparison is **not** like for like at
the top level, and I want that on the record: the `◯` side closed
Theorems 8, 9 and 10, which the IPC side here never attempted. The
per-layer ratios above are the meaningful ones.

---

## 5. The candid assessment

### 5.1 What is intrinsic to `◯`

These are the places where a mathematical fact, not a Lean fact, forces
the work. Each has a kernel-checked witness in the repository except
where noted.

| Driver | The fact that forces it | Witness | Cost |
|---|---|---|---|
| The direct §6 completeness route is unavailable | the `◯`-body edge and the Υ-edge demand opposite phase priorities at a fixed world; the resolving order depends on the model | `docs/frj-w4.md` §9, §10 addendum (**documented argument, UNCERTAIN as a formal claim**) | the entire duality: ≈ 9954 lines against 746 |
| The paper's `Wg` cannot be repaired | `L⊃` on `◯Z ⊃ B` and `R◯ₙᵢ` form a two-cycle | `not_wf_stepC`, `no_measure_stepC` (`gbu_measure.lean:87–107`), no axioms | the store-carrying measure (522 lines) and, permanently, the fact that search must consult the database |
| `R◯ₙᵢ` cannot be the modal right rule | its licence and its completeness both fail | `rcircNI_not_invertible` (`gbu_circ.lean:746`), `not_gbuR_omegaNI` (`:1191`) | `L⊃ᵢ` in the irregular judgment, and with it the `◯`-corner |
| `L⊃ᵢ`'s size condition makes Gbu◯ incomplete | `[◯((◯p ⊃ r) ∧ ◯p)] ⇒g ◯r ∨ z` is PLL-valid and blocked at `|◯p| < |◯r|` | documented at `gbu_circ.lean:1321–1337`; the cell is exhibited, its underivability under the old condition is argued rather than pinned as a named theorem (**UNCERTAIN**) | the `A ∈ Sf^R G` adaptation |
| The paper's FRJ(G) rules extended naively are incomplete | join contexts cannot retain a vacuously-forced implication | `frj_incompleteness_80/81`, `not_CompletenessFRJ` | `RefAt`, `KeptChain`, `keptOf` and its fixpoint theorem: `FRJ/RefAt.lean` 510 lines |
| The irregular duality has a hole | no FRJV irregular disproof of `◯(◯Z ⊃ Z)` exists, and Gbu◯ must not prove it | `no_irregular_circ_imp_self` (`wip/gbu_weakening.lean:211`), `not_gbuIC_Gcc` (`gbu_search_circ.lean:1299`), `provableV_Gcc` | the `lift` rule and the whole FRJW re-transcription (3541 lines) |
| Infallible models are not enough | `¬◯⊥` is IPL-valid, not PLL-valid | `valid_neg_circ_bot_of_infallible` (`FRJ/Fallible.lean:226`) | the fallible joins, `leafF`, `FRJ/Fallible.lean` 732 lines |
| `Cl` cannot see vacuous forcing | `Cl(∅) = ∅` in an atom-free signature, and `¬¬◯⊥` needs a world whose theory is classical | the `Ax^I◯` design note at `Calculus.lean:583–598` | `classForce`, `vacZoneA`, `axIC`, and the one axiom that contributes a world to `Mod(D)` |
| The `◯`-corner | no Gbu◯ rule applies to a `◯Z` goal at a critical cell | the constructor sweep, PROVED by cases on `FRJWi` | `totalityW` and the `refutedCleanly_circ_certs` manufacture |

**Rough size**: the calculus rules and their soundness (`CalculusW` +
`RefAt` + `SoundW` + `StepW` + `ExtractW` = 4051), Gbu◯ and its
measure work (3046), the searcher and its bank (2671), and the closure
and saturation stage (4237). Total **≈ 14 000 lines**, about **40%** of
the `◯`-attributable 34 730.

### 5.2 What is formalisation overhead

Not forced by `◯`; forced by mechanising in Lean 4 with the axiom
discipline this repository imposes. It is spread through every file
rather than sitting in one, so the numbers below are estimates from
measured blocks, and I say which.

| Source | What it costs | Measured or estimated |
|---|---|---|
| **Lists rather than `Finset`s**, to avoid choice at the definition level | the `≐` apparatus and its transports | `Basic.lean:1048–1108` (61 lines) + `transportR`/`transportI` (`Calculus.lean:606–686`, 81 lines) + `transportWr` (`CalculusW.lean:251–276`, 26) + `transportRC`/`transportIC` (`gbu_ljfo_transport.lean`, 202) = **370 lines measured** |
| **`Fin (n+1)`-indexed join families** | `unionAll`/`interAll` and their membership lemmas, `decForallFin`/`decExistsFin` written by hand because mathlib's `Fin` order instances drag in choice, and the reindexing of arbitrary families to stored sublists in the coverage layer | `Calculus.lean:24–40` (17) + `saturate:688–711` (24) + the coverage reindexing, which is the bulk of `saturate`'s 21 coverage lemmas: **estimated 400–600 lines**, not separately measurable because the reindexing is interleaved with the mathematics |
| **`Classical.choice` avoidance** generally | `maxOn` and its two specification lemmas replacing `List.argmax_mem`; `eq_nil_of_forall_not_mem` replacing `List.eq_nil_iff_forall_not_mem`; `dedupF` replacing `List.dedup`; `findNotT`, `splitOfMem`, `splitHatT`, `findCMT` as constructive scans; `findSub`/`irrPick`/`regPick` as choice-free skolemisation; `omega` instead of `simp` on order goals | `search:33–72` and `:197–208` (58 lines) + `closure:1393–1435` (43) + `saturate:76–78` (3) + the `Basic` replacements: **estimated 250–350 lines** |
| **Type-valued search** (`⊕'`, `Σ'`, `WSearchOk` into `Type`) rather than `∨`/`∃` | every clause has to be a `def` returning data; no `by_cases` on a `Prop` where a derivation must come out | pervasive, structural; not separately countable |
| **The blanket sequent-language condition as a field** (`hgoal`, and the `Sf^R`/`Sf^L` threading through every rule) | rather than an index, per divergence 4 | pervasive |
| **The `Clo` decision procedure**, needed to make the engine and the deciders run | `Basic.lean:1221–1298` (78 lines), absent from the IPC snapshot | **78 lines measured** |
| **Docstrings and the divergence log discipline** | roughly a third of the calculus files | not a defect; a deliberate cost |
| **Elaboration cost** | `searchW` needs `set_option maxHeartbeats 3200000` (`search:325`) | one line, but it is the symptom of a 450-line `def` with about thirty recursion sites |

**Rough size**: about **1500–2500 lines** are clearly attributable
overhead, i.e. **4–7%** of the `◯`-attributable total. That is smaller
than one might guess. The reason is that the axiom-hygiene work, once
done, is done once: `RefAt`'s decider, the `Fin` deciders, `dedupF` and
the constructive scans are each written once and consumed many times.
The pervasive costs (Type-valuedness, `hgoal` threading) inflate every
file by some percentage rather than adding files.

### 5.3 What is historical residue

Compiled, pinned, correct, and not part of the current argument.

| Item | Lines | Status |
|---|---|---|
| **The FRJ◯ line** (`Calculus`, `Model`, `Step`, `Extract`, `Sound`, `Complete`, `Minimal`, `Saturate`, `Modal`, `Fallible`, `Erase`, `Profile`, `Audit`, `Bridge`, `WitnessKit`) | 9932 | mixed. `Calculus.lean`'s *definitions* are consumed by FRJV and hence FRJW (the join formers, `Tag`, `Covers`, `classForce`). Its *theorems* are not: `Sound.lean` (2010) proves soundness of a calculus that FRJW replaced; `Saturate.lean` (1565) is the abandoned completeness organisation with conditional results only; `Erase.lean` (342) holds an OPEN transfer `(E)`; `Profile.lean` (458) is an engine optimisation. The line is deliberately retained as the subject of the #80/#81 incompleteness theorems, which must survive verbatim. |
| **The FRJV line** (`CalculusV`, `CalculusVLemmas`, `StepV`, `ExtractV`, `SoundV`, `SaturateV`, `CompleteV`, `CompleteV0`, `AuditV`, `BridgeV`, six `WitnessV*` files) | 6701 | mostly residue. FRJW re-proves everything, soundness included, by explicit policy (`docs/frjw-plan.md`: "no FRJV theorem migrates by renaming or aliasing; FRJV files stay byte-for-byte untouched"). What is still live: `CalculusV`'s definitions (imported by `CalculusW`), `SoundV` (imported by `gbu_search`), the `WitnessV*` files (kernel-checked banked results, including the ρ12⊬ρ15 cell). `SaturateV` (1598) has no consumer in the FRJW chain. |
| **`wip/gbu_search_circ.lean`** (`searchO`, `BigAnte`, `CleanReg`) | 1354 | retired: `residues_unsatisfiable` (`:1326`) shows the two supplies are jointly contradictory at `◯(◯p ⊃ p)`, so `searchO` is vacuous for any modal `G`. Retained for its live countermodels (`not_gbuIC_Gcc`, `provableV_Gcc`, `countermodel_Gcc`). |
| **`wip/gbu_measure.lean`'s store measure** (`Wg◯`, `stepU_wf`) | ~420 of 522 | superseded by `wgC`. Retained as the record of why `R◯ₙᵢ` was abandoned; the refutations `not_wf_stepC`/`no_measure_stepC` (about 100 lines) are live and load-bearing. |
| **The T-B `_mono` defs** | ~275 | archived in place, zero code consumers, marked in the module header (`closure:42–50`). **Measured discrepancy**: `docs/frjw-compaction.md` names *nine*; the file carries *eleven* (`joinAtF_mono` and `joinOrF_mono` are omitted from the archive note). |
| **The `RefAtG` kit and the pre-totality corner fast-paths** (`refutedCleanly_circ_kept` at `corner:92`, `refutedCleanly_circ_axI` at `:251`, `RefAtG` + its three lemmas at `:392–454`) | ~262 of `corner`'s 654 (40%) | pinned banked results whose consumer went with the pre-totality corner. `refutedCleanly_circ_certs` (`:470–654`) is live, consumed at `search:430`. |
| **The second GBUW completeness route** (`gbu_ljfo` 898 + `_support` 242 + `_transport` 202) | 1342 | deliberate redundancy, explicitly not retired: `docs/frjw-compaction.md` "Deferred" says "both stand, and their independence is itself evidence". `_transport` is genuinely shared (imported by `gbu_frjw_search`); `gbu_ljfo.lean` itself is the alternative route. Note also its external dependency `LJF/OBridge.lean` (548 lines) and the LJF◯ core, which belong to a different campaign. |
| **`wip/gbu_db.lean`** | 722 | the paper's §4 for the *V* family (divergence D6); the W-analogues are `gbu_frjw_db.lean` and `gbu_frjw_circdb.lean`. Still imported by `gbu_search` and `gbu_frjw_db`, so partly live. |
| **`FRJ/Search/`** (`Core`, `Engine`, `Fast`, `OpsV`, `OpsW`, `Pin`, `Profile`) | 2591 | live infrastructure, not residue: the engine functor is what discovers the cells the proofs are then built on. It has no IPC counterpart because the IPC snapshot needed no discovery. |

**Rough size**: taking the FRJ◯ line's dead theorems (`Sound` 2010 +
`Saturate` 1565 + `Erase` 342 + `Profile` 458 + `Complete`/`Minimal`
under the `◯`-freeness gate 1148, call it 5500 of the 9932), the FRJV
line's superseded part (about 5000 of 6701), `searchO` (1354), the
superseded measure (420), the `_mono` archive (275), the corner's dead
kit (262), and the second completeness route (1342): **≈ 14 150 lines**,
about **41%** of the `◯`-attributable total.

### 5.4 The split, and how I got it

| Bucket | Lines | Share of `◯`-attributable |
|---|---|---|
| Intrinsic to `◯` | ≈ 14 000 | ≈ 40% |
| Formalisation overhead | ≈ 2 000 | ≈ 6% |
| Historical residue | ≈ 14 150 | ≈ 41% |
| Unclassified (engine infrastructure, probes, `Basic`'s modal growth, the LJF◯ external dependency) | ≈ 4 600 | ≈ 13% |
| **Total `◯`-attributable** | **34 730** | 100% |

**Method.** Whole files were assigned to a bucket where a file has a
single role (`gbu_search_circ` → residue; `SoundW` → intrinsic). Where a
file is mixed I measured the block (the `_mono` defs by declaration
span; the corner file by declaration boundaries; `RefAt` by whole file)
or estimated and said so. The overhead figure is the weakest of the
three, because the pervasive costs (Type-valuedness, `hgoal` threading,
docstring discipline) are not separable from the mathematics by any
measurement I can make; I have counted only the blocks that exist purely
to avoid choice or to carry `≐`, and the true figure is certainly
higher. Treat 6% as a floor, not an estimate.

### 5.5 The answer to the question as asked

Matthew's observation is correct and the numbers support it: **about
41% of the modal development is material that the current argument does
not use.** That is not because the simplification effort failed. Stages
1–3 of the compaction plus the C-items cut the three core files from
5465 to 4962 lines, and the search file from 1189 to 725 (−39%),
verified with pins byte-identical. What those stages did *not* touch is
the larger residue: two superseded calculi (FRJ◯ and FRJV, together
16 633 lines), a retired search apparatus (1354), and a second
completeness route (1342). Each is retained for a stated reason, and
each reason is defensible:

* FRJ◯ must survive verbatim because the incompleteness theorems
  #80/#81 are theorems *about it*, and their `cases` are exhaustive over
  its constructors.
* FRJV must survive because the ρ12⊬ρ15 banked result and the
  `WitnessV*` files are FRJV objects, and because `SoundV` is imported
  by `gbu_search`.
* `searchO` must survive because `residues_unsatisfiable` is a theorem
  about it, and because it holds the `Gcc` countermodel.
* The LJF◯ route survives on the compaction's own verdict:
  independence is evidence.

So the residue is *justified* but it is still residue, and it is why the
development reads as extremely complex. The intrinsic part, at about
14 000 lines, is roughly **2.9×** the whole IPC baseline (4837) and
**19×** the IPC completeness proof (746). That ratio, not the 7.2×
headline, is the real answer to "what did `◯` cost": the modality forces
you off the cheap completeness route and onto the expensive one, and the
expensive one is where the paper itself spends 14 of its 30 duality
pages.

If the aim is to make the development *readable* rather than smaller,
the highest-value actions are, in order:

1. **Separate the lines physically.** Move the FRJ◯ and FRJV files into
   an `Archive/` subtree with their pins intact, leaving `FRJ/` holding
   `Basic`, `RefAt`, the W-family, and `Search/`. That is a ≈16 600-line
   reduction in what a reader must navigate, with no mathematical
   change. The constraint-supersession check would have to be run per
   file, and `SoundV`'s consumer in `gbu_search` re-pointed or the
   import kept.
2. **Promote the W-chain out of `wip/`.** The `wip` library is not in
   `defaultTargets`, so `lake build` proves nothing about the very
   files that carry the crown.
3. **Fix the four stale or inaccurate records found while writing
   this**: the "six new constructors" docstring at `gbu_circ.lean:1242`
   (there are eight), the Thm 8/9/10 "OPEN" ledger at
   `gbu_circ.lean:9–21`, the "Lemma 9 … 10 clauses" row in the same
   ledger (`gbu_circ.lean:15`; the arXiv source has nine), and the
   nine-vs-eleven `_mono` count in `docs/frjw-compaction.md`.
4. **Retire the corner's dead kit** (262 lines) and `SaturateV` (1598)
   after their supersession checks.

None of that touches the intrinsic 40%, which is the actual
mathematical content and is not compressible by tidying.

---

## 6. What I could not verify

* **The §6-route obstruction is an argument, not a theorem.** §4.3.
  Marked UNCERTAIN. Settled by proving a `no_measure_stepC`-shaped
  statement for the completeness visit's call relation.
* **The `L⊃ᵢ` incompleteness cell.** The cell
  `[◯((◯p ⊃ r) ∧ ◯p)] ⇒g ◯r ∨ z` is documented at
  `gbu_circ.lean:1321–1337` with its blocking analysis, but I found no
  named theorem pinning its underivability under the old size
  condition. Marked UNCERTAIN. Settled by a `¬ Nonempty (GbuRC …)`
  theorem against the pre-adaptation rule.
* **The overhead figure.** §5.2, §5.4. A floor, not an estimate.
* **Journal page numbers.** All page numbers here are from the arXiv
  compilation recorded in `docs/frj-paper-skeleton.md`; the ACM TOCL
  21(3) Article 22 pagination will differ. Item numbers are the
  journal's where `docs/frj-fidelity.md` supplies them and the arXiv's
  otherwise, with the label always given.
* **Nothing is attributed to the S4 paper** (Fiorentini–Ferrari, JLC
  31(3), 2021), which is unread here by Matthew's decision of
  2026-08-17. The promise-family shape is ours permanently.

---

## 7. Sources

**Paper**: `frj-corr.tex` (arXiv:1804.06689), read directly;
`docs/frj-paper-skeleton.md` for the label → number → page map.

**Repository record**, all at `b2f2525`: `docs/frj-fidelity.md`,
`docs/frjlax-fidelity.md`, `docs/frjw-plan.md`, `docs/refat-plan.md`,
`docs/frjw-compaction.md`, `docs/searchw-architecture.md`,
`docs/frjw-recursion-explainer-plan.md`, `docs/frj-w4.md`,
`docs/calculus-map.md`, `HANDOFF.md` §§2026-08-25c to 2026-09-02.

**Code**, all at `b2f2525` unless marked `05994d5`: `FRJ/Basic.lean`,
`FRJ/Calculus.lean`, `FRJ/CalculusV.lean`, `FRJ/CalculusW.lean`,
`FRJ/RefAt.lean`, `FRJ/SoundW.lean`, `FRJ/Complete.lean`,
`FRJ/Minimal.lean`, `FRJ/Saturate.lean`, `FRJ/Audit.lean`,
`wip/gbu.lean`, `wip/gbu_circ.lean`, `wip/gbu_measure.lean`,
`wip/gbu_search.lean`, `wip/gbu_search_circ.lean`, `wip/gbu_db.lean`,
`wip/gbu_ljfo.lean`, `wip/gbu_frjw_dichotomy.lean`,
`wip/gbu_frjw_search.lean`, `wip/gbu_frjw_closure.lean`,
`wip/gbu_frjw_saturate.lean`, `wip/gbu_frjw_corner.lean`,
`wip/frj80_noprov.lean`, `wip/frj81_noprov.lean`.

🕒 2026-09-02 15:57 BST
— Opus · effort unknown
