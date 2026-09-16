# FRJ◯ from scratch — the W0 plan

*Written 2026-08-16 on branch `claude/frj-redevelopment-69005f` (cut from
`frj-lax` at `cc6ed4b`).  This is the W0 deliverable of
`docs/frj-lax-handoff.md`: the source has been read at source, and this
document lists every numbered result to be reproduced, the module plan
that reproduces it, and the divergences already visible before any Lean
is written.*

Companions: `docs/frj-lax-handoff.md` (the brief), `docs/frj-fidelity.md`
(the fidelity record of the IPC base, whose numbering this document
corrects), `docs/calculus-formalisation-method.md` (the six-step method),
`docs/why-chain.md` (the goal chain), repo `CLAUDE.md`.

---

## 0. What was read, in full

| Source | Form | Read |
|---|---|---|
| **ACM TOCL 21(3), Article 22 (March 2020)**, Fiorentini–Ferrari, *Duality between Unprovability and Provability in Forward Refutation-search for IPL* | extracted text of the published PDF (`ff-tocl.txt`, 2 300 lines; `ff-tocl.pdf`) | §2, §3, §3.1, §6 in full; §4, §5 skimmed for statements only |
| **arXiv:1804.06689**, LaTeX source `frj-corr.tex`, 6 682 lines | LaTeX source | preamble, §2, §3, §3.1, §3.2, §6 and **Appendix A** in full; §4, §5 skimmed |
| arXiv:1804.06689 PDF | extracted text (`ff-arxiv.txt`) | numbering only |

Both are in this session's scratchpad.  Figure 1 of the journal version is
a raster image in the PDF and could not be read as text; the rule table was
therefore read from the **arXiv LaTeX figure** (`fig:FRJ`) and independently
cross-checked clause by clause against the **journal prose**, which states
every rule and every side condition in words.  The two agree.  This is
recorded here because the campaign's governing failure was formalising from
a paraphrase rather than the source.

---

## 1. The finding that changes the fidelity record: arXiv ≠ journal

`docs/frj-lax-handoff.md`, `docs/frj-fidelity.md` and `FRJ/Basic.lean` all
describe `frj-corr.tex` as "the arXiv LaTeX source … which is the full
journal version".  **It is not.**  It is a close variant that predates the
published article.  The differences inside the in-scope material are not
cosmetic:

1. **The journal adds Lemma 3.9**, absent from the arXiv source:

       ⊢_FRJ(G) Σ ; Θ → C   implies   ∀ H ∈ Σ. |H| < |C|

   proved by induction on height, and its ⊃∈ case **uses restriction
   (RS1)** (the minimality of `Λ`).

2. **The key soundness lemma has a different part (ii).**

   * arXiv: for every p-sequent `σ_p` with `σ ↦ σ_p` and
     `σ_p ⊩ Σ ∩ Sf⁻(C)`, we have `σ_p ⊮ C`.
   * journal (Lemma 3.10(ii)): for every p-sequent `σ_p` with `σ ⇢ σ_p`,
     `σ_p ⊩ Σ` implies `σ_p ⊮ C`.

   `Σ ∩ Sf⁻(C) ⊆ Σ`, so the **arXiv statement is the stronger lemma**
   (weaker hypothesis, same conclusion).  The journal recovers the size
   decrease its secondary induction needs from Lemma 3.9 instead of from
   `Sf⁻`; that is why Lemma 3.9 exists, and why the journal's soundness
   proof depends on (RS1) while the arXiv's depends on nothing.

3. **The journal introduces the relation `⇢`**: `σ₀ ⇢ σ_p` iff
   `σ₀ ↦₀ … ↦₀ σ_n ↦₀ σ_p` with `σ₀ … σ_n` all irregular and `σ_n` a
   premise of a join rule with conclusion `σ_p`.  Along `⇢` no `⊃∉` step
   occurs, so the journal can use Lemma 3.5(i) where the arXiv needs
   3.5(iii) together with (Cl5).

4. **(P2) and (P3) are swapped** between the two versions' join cases.

5. Renamings: `(RS1)–(RS4)` for `(PS1)–(PS4)`; "refutation" for
   "derivation"; the soundness properties are `(SREG)`/`(SIRR)` rather
   than `(S1)`/`(S2)`; the height bounds move from §3.2 to Theorem 6.1.

6. The journal names the join side conditions **(J3)** (`F ∈ Prime ∩ Sr(G)`,
   `F ∉ Σ^At`) and **(J4)** (`C₁ ∨ C₂ ∈ Sr(G)`, `{C₁,C₂} ⊆ Υ`), which the
   arXiv leaves inside the figure's blanket condition.

**Decision taken (mine, reversible, flagged in §9):** cite the **journal**
numbering, formalise the **arXiv form of Lemma 3.10(ii)**.  Reasons: the
journal is the version of record and the method document requires the
journal over the conference version; but the arXiv form of (ii) is the
stronger statement, and it makes soundness independent of (RS1)–(RS4), so
the calculus needs no minimality or maximality side conditions at all.
Those conditions quantify over all proper subsets of a context; carrying
them as decidable fields on constructors would be the single most
expensive thing in the rule table, and nothing in scope needs them.

### 1.1 Numbering: three systems, and the correction owed

| Result | **journal (cite this)** | arXiv PDF | arXiv label | `docs/frj-fidelity.md` says |
|---|---|---|---|---|
| Soundness of FRJ(G) | **Theorem 3.1** | Thm 1 | `theo:FRJsound` | Theorem 3.1 ✓ |
| `Lhs` under `↦` | **Lemma 3.5** | Lemma 1 | `lemma:lhs` | Lemma 3.4 ✗ |
| sizes in `Σ` | **Lemma 3.9** | — | *absent* | — |
| key soundness lemma | **Lemma 3.10** | Lemma 2 | `lemma:soundFRJ` | Lemma 3.9 ✗ |
| soundness property (SREG) | **Lemma 3.11** | Lemma 17 (part) | `lemma:soundnessProperties` | — |
| `Mod(D)` is a countermodel | **Theorem 3.12** | Theorem 2 | `theo:soundFRJ` | Theorem 3.10 ✗ |
| soundness property (SIRR) | **Theorem 3.14** | Lemma 17 (part) | `lemma:soundnessProperties` | — |
| weight decreases | **Lemma 3.16** | Lemma 3 | `lemma:wg` | — |
| branch bounds | **Lemma 3.17** | Lemma 4 | `lemma:branch` | — |
| height bounds | **Theorem 6.1** | Theorem 3 | `theo:height` | — |
| `Rn(D) = h(Mod(D))` | **Lemma 6.2** | Lemma 13 | `lemma:rnk` | — |
| the completeness construction | **Lemma 6.3** | Lemma 14 | `lemma:minMod` | Lemma 6.4 ✗ |
| minimal-height refutation | **Theorem 6.4** | Theorem 11 | `theo:minMod` | — |
| `Λ_α = Cl(Λ_α) = Cl(Λ*_α)` | **Lemma 6.7** | Lemma 15 | `lemma:closure` | Lemma 6.5 ✗ |
| completeness (via duality) | **Theorem 5.13** | Theorem 10 | — | Theorem 6.2(i) ✗ |

The five ✗ rows are numbers that exist in **neither** published version.
A fidelity table whose numbers cannot be looked up is not checkable
against the original, which is the one thing it is for.

**Applied 2026-08-16** (Matthew's call): `docs/frj-fidelity.md` has been
renumbered throughout to the journal numbering, with a dated note under
its Scope section recording the change.  Its section references are
corrected too — the journal's §3.1 is *Restrictions (RS1)–(RS4)*, its
§3.2 is *Countermodels and Soundness*, its §3.3 is *Termination*.  The
FRJ/ development itself is unaffected: only its citations were wrong,
never its mathematics.  Still uncorrected, and outside this campaign's
scope: `FRJ/Basic.lean`'s header repeats the claim that `frj-corr.tex`
"is the full journal version".

---

## 2. The results to be reproduced

Everything below is stated for FRJ(G) over IPC.  W5 asks the same
questions again with ◯ present, and nothing in W5 is settled here.

### In scope

| # | Journal | Statement | Stage |
|---|---|---|---|
| 1 | §2 | language, `size`, `Prime = PV ∪ {⊥}`, `Fm⊃`, `Sf`, `Sf⁻` | W1 |
| 2 | §2 | `Sf^L(G)`, `Sf^R(G)`: the four defining clauses | W1 |
| 3 | §2 | Kripke model; the five forcing clauses; monotonicity | W1 |
| 4 | §2 | validity, `IPL` = the valid formulas, countermodel | W1 |
| 5 | §2 | closure `Cl(Γ)` by the grammar `X ::= C \| X∧X \| A∨X \| X∨A \| A⊃X` | W1 |
| 6 | §2 | (Cl1)–(Cl6) | W1 |
| 7 | §3 | `Ĝ_at`, `Ĝ_imp`, `Ĝ`; regular and irregular sequents; `Lhs`, `Rhs` | W2 |
| 8 | Fig. 1 | the ten rules, with (J1)–(J4) and the blanket `Rhs(σ) ∈ Sf^R(G)` | W2 |
| 9 | §3 | `⊢_FRJ(G) σ`, `⊢_FRJ(G) G` | W2 |
| 10 | §3 | `↦₀`, `↦`, `↦*` | W3 |
| 11 | **Lemma 3.5** | (i) `σ₁ ↦₀^R σ₂`, `R ≠ ⊃∉` ⟹ `Lhs(σ₂) ⊆ Lhs(σ₁)`; (ii) `σ₁ ↦₀ σ₂` ⟹ `Lhs(σ₂) ⊆ Cl(Lhs(σ₁))`; (iii) same for `↦*` | W3 |
| 12 | §3.1 | p-sequents `P(D)`; `Mod(D) = ⟨P(D), ≤, ρ, V⟩` with `V(σ) = Lhs(σ) ∩ PV`; that it *is* a model | W3 |
| 13 | §3.1 | the map `φ`; its three stated properties | W3 |
| 14 | **Lemma 3.10** | (i) `σ = Γ ⇒ C` ⟹ `φ(σ) ⊩ Γ` and `φ(σ) ⊮ C`; (ii) arXiv form: `σ = Σ;Θ → C`, `σ ↦ σ_p ∈ P(D)`, `σ_p ⊩ Σ ∩ Sf⁻(C)` ⟹ `σ_p ⊮ C` | W3 |
| 15 | **Theorem 3.12** | `Mod(D)` is a countermodel for `G` | W3 |
| 16 | **Theorem 3.1** | `⊢_FRJ(G) G` ⟹ `G ∉ IPL` | W3 |
| 17 | **Lemma 3.11**, **Theorem 3.14** | the soundness properties (SREG), (SIRR) | W3 |
| 18 | §6 | `α ⊩* H`; `Λ_α`, `Λ*_α`, `Ω_α` | W4 |
| 19 | **Lemma 6.7** | `Λ_α = Cl(Λ_α) = Cl(Λ*_α)`, in the two directions that are true (see §4.2) | W4 |
| 20 | **Lemma 6.3** | the construction: `D^→_α(C)` with (ii), and `D^⇒_α(C)` with (iv) | W4 |
| 21 | §6 (K1) | from a countermodel `K` for `G`, an FRJ(G)-refutation of `G` | W4 |
| 22 | — | **completeness**: `G ∉ IPL` ⟹ `⊢_FRJ(G) G`, and `⊢_FRJ(G) G ↔ G ∉ IPL` | W4 |

### In scope, optional, decided at the W3/W4 boundary

| # | Journal | Statement | Note |
|---|---|---|---|
| 23 | **Lemma 3.16**, **Lemma 3.17**, **Theorem 6.1** | `wg` decreases; branch length `O(N²)`; `h(Mod(D)) ≤ N` | termination and the size bound the W6 searcher wants |
| 24 | **Lemma 6.2**, **Theorem 6.4** | `Rn(D) = h(Mod(D))`; a refutation whose model has minimal height | needs clauses (i) and (iii) of Lemma 6.3 to be carried; recommended **after** completeness closes, not before |

### Out of scope, and why

* **§4** (`FSearch`, saturated databases; Lemma 4.1, Theorem 4.2, Lemma 4.3, Theorem 4.4) and **§5** (Gbu(G); Lemmas 5.1–5.10, Theorems 5.2, 5.4, 5.11, 5.12, 5.13).  The journal derives completeness of FRJ(G) as a corollary of the duality `⊢_Gbu(G) G iff ⊬_FRJ(G) G`, which costs a second calculus and a search procedure.  §6 proves it directly.  Same theorem, a fraction of the work, equally published.
* **(RS1)–(RS4)**.  Refutation-search restrictions.  Dropping them strengthens soundness and costs completeness nothing: the construction of Lemma 6.3 happens to satisfy them, and takes `Λ := Λ*_α \ Σ₁`, `Θ := Λ*_α` without any minimality or maximality argument.
* **No IPC proof system is needed anywhere.**  The paper defines IPL semantically ("Intuitionistic Propositional Logic IPL coincides with the set of valid formulas"), so both theorems in scope are statements about Kripke semantics alone.

---

## 3. The module plan

`FRJLax/` gets one `[[lean_lib]]` entry and a root `FRJLax.lean`.
Namespace `FRJLax`.  Nothing is imported from `FRJ/`, `FRJO/`, `Reject/`
or `BiLax/`.

| Module | Content | Journal |
|---|---|---|
| `FRJLax/Core.lean` | `Form`, `size`, `isPV`/`isPrime`/`isImp` as `Bool`, list primitives (`rm`, `cap`, `≐`), `Sf`, `Sf⁻`, `Sf^L`/`Sf^R`, `Ĝ_at`/`Ĝ_imp`/`Ĝ`, `Cl`, (Cl1)–(Cl6) | §2 |
| `FRJLax/Model.lean` | `Kripke` with `elems`/`complete`/`decEq`/`decLe`/`decV`; `force`, `decForce`, monotonicity, `forces`, `valid`, `IPL`, `Countermodel` | §2 |
| `FRJLax/Calculus.lean` | `Sequent`, `Lhs`, `Rhs`, the mutual `FRJr`/`FRJi` families, `Provable` | §3, Fig. 1 |
| `FRJLax/Step.lean` | `↦₀` indexed by rule name, `↦`, `↦*`, occurrence, Lemma 3.5, well-formedness of contexts | §3 |
| `FRJLax/Extract.lean` | `P(D)`, `Mod(D)`, the map `φ` | §3.1 |
| `FRJLax/Sound.lean` | Lemma 3.10, Theorem 3.12, Theorem 3.1, Lemma 3.11, Theorem 3.14 | §3.1, App. A |
| `FRJLax/Complete.lean` | `Λ_α`, `Λ*_α`, `Ω_α`, Lemma 6.7, height, Lemma 6.3, (K1), completeness | §6 |
| `FRJLax/Emit.lean` (W6) | `Mod(D)` as `FinCM`; the `decide`-checkable certificate | — |

`Core.lean` is written with **zero imports**, on the model of
`LaxLogic/LJFOCore.lean`, so that no other calculus in the repo can carry
any part of the syntax or the closure.  Later modules may import Mathlib
if a proof genuinely needs it, but every module carries its own
`#guard_msgs`-pinned `#print axioms`.

### 3.1 The rule table, slime-free

The existing `FRJ/Calculus.lean` puts a computed term in almost every
constructor's return-type index (`FRJr G ((gAt G).erase F) F`,
`FRJi G (St₁ ∪ St₂) (Th₁ ∩ Th₂) (C₁ ∨ C₂)`, …), which is the concrete
reason its `Extract.lean` fights the kernel.  Here every index is a
variable and every computation moves into a hypothesis.  Write

    l ≐ m   for   l ⊆ m ∧ m ⊆ l          (equality up to membership)

which removes all order dependence and all need for `List.dedup` (which
is classical).  Then, with `Γ, Σ, Θ, Λ` variables throughout:

    axR       (hF : F.isPrime) (hg : F ∈ sfR G)
              (hΓ : Γ ≐ rm (gAt G) F)
              : FRJr G Γ F

    axI       (hF : F.isPrime) (hg : F ∈ sfR G)
              (hΣ : Σ ≐ []) (hΘ : Θ ≐ rm (gAt G) F ++ gImp G)
              : FRJi G Σ Θ F

    andR k    (d : FRJr G Γ Aₖ) (hg : and A₁ A₂ ∈ sfR G)
              : FRJr G Γ (and A₁ A₂)                       (k = 1, 2)

    andI k    (d : FRJi G Σ Θ Aₖ) (hg : and A₁ A₂ ∈ sfR G)
              : FRJi G Σ Θ (and A₁ A₂)                     (k = 1, 2)

    orI       (d₁ : FRJi G Σ₁ Θ₁ C₁) (d₂ : FRJi G Σ₂ Θ₂ C₂)
              (j₁ : Σ₁ ⊆ Σ₂ ++ Θ₂) (j₂ : Σ₂ ⊆ Σ₁ ++ Θ₁)
              (hΣ : Σ ≐ Σ₁ ++ Σ₂) (hΘ : Θ ≐ cap Θ₁ Θ₂) (hg : …)
              : FRJi G Σ Θ (or C₁ C₂)

    impInR    (d : FRJr G Γ B) (hA : Clo Γ A) (hg : …)
              : FRJr G Γ (imp A B)

    impInI    (d : FRJi G Σ₁ Θ' B) (hΘ' : Θ' ≐ Θ ++ Λ)
              (hdisj : ∀ x ∈ Θ, x ∉ Λ) (hA : Clo (Σ₁ ++ Λ) A)
              (hΣ : Σ ≐ Σ₁ ++ Λ) (hg : …)
              : FRJi G Σ Θ (imp A B)

    impNotIn  (d : FRJr G Γ B) (hΘ : ∀ x ∈ Θ, Clo Γ x ∧ x ∈ gHat G)
              (hA : Clo Γ A) (hnA : ¬ Clo Θ A) (hΣ : Σ ≐ []) (hg : …)
              : FRJi G Σ Θ (imp A B)

    joinAt    {n} (d : ∀ j : Fin (n+1), FRJi G (Σf j) (Θf j) (Af j))
              (J1 : ∀ i j, i ≠ j → Σf i ⊆ Σf j ++ Θf j)
              (J2 : ∀ Y Z, imp Y Z ∈ ⋃ⱼ impPart (Σf j) → Y ∈ Υ)
              (hF : F.isPrime) (J3 : F ∉ ⋃ⱼ atPart (Σf j)) (hg : F ∈ sfR G)
              (hΓ : Γ ≐ joinCtxAt Σf Θf Af F)
              : FRJr G Γ F

    joinOr    {n} (d : ∀ j …) (J1) (J2)
              (J4 : C₁ ∈ Υ ∧ C₂ ∈ Υ) (hg : or C₁ C₂ ∈ sfR G)
              (hΓ : Γ ≐ joinCtxOr Σf Θf Af)
              : FRJr G Γ (or C₁ C₂)

with `Υ = { Af j | j }`, and the join conclusion contexts factored out
once as

    joinCtxAt Σf Θf Af F = Σ^at ++ rm Θ^at F ++ Σ^⊃ ++ Θ^⊃
    joinCtxOr Σf Θf Af   = Σ^at ++ Θ^at ++ Σ^⊃ ++ Θ^⊃
    Σ^at = ⋃ⱼ atPart (Σf j)      Θ^at = ⋂ⱼ atPart (Θf j)
    Σ^⊃  = ⋃ⱼ impPart (Σf j)     Θ^⊃  = (⋂ⱼ impPart (Θf j)) / Υ

so that `↦` refers to the same functions as the rules and cannot drift
from them.  `Υ` nonempty is guaranteed by indexing the premises with
`Fin (n+1)`.

Two constraints this table must satisfy, and both are checkable
mechanically before any proof is attempted:

* **every return-type index is a variable** (`Γ`, `Σ`, `Θ`, and the goal
  a constructor form) — the McBride test;
* **the blanket condition `Rhs(σ) ∈ Sf^R(G)` is a field on every
  constructor** (`hg`), as in the figure's own header.  The context
  constraints `Γ ⊆ Ĝ` and `Σ ∪ Θ ⊆ Ĝ` are **not** indices: they are a
  lemma (`wf`), proved in `Step.lean`, and they are what justifies the
  `atPart`/`impPart` split in the joins.  That obligation is discharged
  before soundness, not after.

### 3.2 Choice-free budget

Target: **`[propext, Quot.sound]`** at worst, no axioms where attainable,
`Classical.choice` absent.  Pinned with `#guard_msgs` in each module, so a
regression is a build failure.

* `List` only; never `Finset`.  `Finset.instUnion`, `Finset.erase`,
  `Finset.image`, `Multiset.ndunion` report `Classical.choice` **at the
  definition level**, so a term that merely mentions `s ∪ t` carries
  choice however it is proved.  Only `Finset.filter` is clean.
* Avoid `List.dedup` and `List.erase` (both classical); filter instead —
  `rm`, `cap` as in `git show frj-choicefree:FRJ/Basic.lean`.
* Shape predicates as `Bool`, never `Prop`.
* `Kripke` carries `elems : List W`, `complete`, `decEq`, `decLe`, `decV`
  instead of a `Finite` instance (eliminating `Finite` needs
  `Fintype.ofFinite`, which costs choice).  This makes `force`
  **decidable** (`decForce`, the `⊃` clause by `List.decidableBAll` over
  `elems`), which is what lets `Λ*_α` be a `List.filter`.
* Never `tauto`, never `Classical.propDecidable`, never `native_decide`.
* Height of a world by `List.countP` over `elems`, with `countP_mono` /
  `countP_lt_countP` in place of `Finset.card_lt_card`; `List.argmax` in
  place of `Finset.exists_max_image`.
* **Type-valued from line one.**  `FRJr`/`FRJi` land in `Type`, and
  Lemma 6.3 **returns a refutation**.  `choose` and `Nonempty.some` are
  themselves choice, and an existence proof yields no procedure.  This is
  the step that turns completeness into an algorithm from countermodel to
  refutation, which is the point of the campaign.

Reusable, verified at `frj-choicefree` (2026-08-16): no axioms at all for
`clo_forces`, `clo_trans`, `clo_pv`, `force_mono`,
`not_IPL_of_countermodel`; `[propext]` for `sfPos_closed`, `sfR_imp`,
`clo_sf`; `[propext, Quot.sound]` for the `Step` layer.

---

## 4. Divergences already identified, before any Lean

Recorded now so they are interventions and not accidents.  Numbers 1–4
are inherited from the IPC pass and re-checked at source; 5–7 are new.

1. **Worlds of `Mod(D)` are p-sequent occurrences, not p-sequents.**  The
   paper takes `P(D)` to be the *set* of p-sequents in `D`, identifying
   two occurrences of the same sequent.  Both are finite posets with a
   minimum and a monotone valuation, and `Mod(D)` is a countermodel for
   `G` iff its quotient is, so soundness is insensitive.  The
   identification matters only for the minimal-height results.
2. **The ⊃-clause of forcing is written as an implication**, not as the
   paper's disjunction "`K,β ⊮ A` or `K,β ⊩ B`".  Equivalent, and the
   disjunction would put excluded middle into the definition.
3. **`k ∈ {1,2}` in the ∧ rules becomes two constructors.**  Same rule
   instances.
4. **Lemma 6.7 as stated is false, in the first equality.**  The paper
   states `Λ_α = Cl(Λ_α) = Cl(Λ*_α)`.  `Cl` is generated by a grammar in
   which `A` ranges over *all* formulas, so `Cl(Λ_α)` contains `Z ⊃ C`
   for arbitrary `Z`, which need not lie in `Sf^L(G)` and hence not in
   `Λ_α`; and the proof's step "`α ⊩ A ∧ B`, hence `A ∧ B ∈ Λ_α`"
   silently needs `A ∧ B ∈ Sf^L(G)`.  The two directions the
   construction actually uses are true and get proved:

       α ⊩ Cl(Λ*_α)          and          A ∈ Λ_α ⟹ A ∈ Cl(Λ*_α)

5. **`Rhs(G)` in the join rules is read as `Sf^R(G)`.**  Both versions
   write `F ∈ Prime ∩ Rhs(G)` and `C₁ ∨ C₂ ∈ Rhs(G)`, but `Rhs` is
   defined only on sequents.  The figure's blanket condition
   `Rhs(σ) ∈ Sf^R(G)` gives the intended reading, and the sequent
   definition forces it.
6. **Lemma 3.10(ii) is taken in the arXiv form**, not the journal form
   (§1 above).  It is the stronger statement, and it removes the
   dependence of soundness on (RS1).
7. **In the `C = C₁ ∧ C₂` regular case of Lemma 6.3, the paper cites
   (IH2) where the call is regular-to-regular at the same world** and so
   must be (IH3).  The measure decreases either way.

---

## 5. Staging, with exit criteria

Unchanged from the handoff except that W0 is now closed and the optional
items of §2 are placed.

| Stage | Content | Exit |
|---|---|---|
| **W0** | read the source; this document | **done** |
| **W1** | `Core.lean`, `Model.lean` — §2, with ◯ in the syntax iff decision 1 says so | builds; (Cl1)–(Cl6) proved; axioms pinned |
| **W2** | `Calculus.lean` — Fig. 1, ◯-free rules only | builds; every return-type index a variable; `Provable` defined |
| **W3** | `Step.lean`, `Extract.lean`, `Sound.lean` — items 10–17, plus `wf` | sorry-free; pinned; no `Classical.choice` |
| **W4** | `Complete.lean` — items 18–22 | sorry-free; pinned; the construction **computes** |
| **W3b/W4b** | items 23, 24, if wanted | optional, after W4 |
| **W5** | the ◯ rules: screen, then Matthew signs off, then extend W2–W4 | screens recorded; rules signed off; results re-proved |
| **W6** | the searcher, plus a `decide`-checkable certificate | runs as a `lean_exe`; corpus recorded |

Bank at every boundary: commit, push, append a dated section to
`HANDOFF.md`.

---

## 6. The screens

Per `CLAUDE.md`, every quantified candidate statement gets an extensional
attack before a proof build is scoped, in four directions.  Two rounds
are already scheduled:

**Round A (W2, before any soundness proof).**  The target is the ◯-free
rule table itself.  The screen is: *no derivable regular sequent
`Γ ⇒ C` has `Γ ⊨ C` valid*.  Cells:

* corpus replay: the paper's own worked refutations — `S` and `T` of
  Example 3.7 (Scott and anti-Scott, Nishimura `N₁₀`, `N₉`, both of
  height 2), `K` the Kreisel–Putnam instance of Example 3.8 (height 1),
  and the `G = (p ∧ H) ⊃ (q₁ ∨ q₂)` of Example 3.6 with
  `H = p ⊃ q₁ ∨ q₂`, whose irregular refutation of a **valid** goal is
  exactly the trap that (SIRR) exists to close;
* boundary: `⊥` as goal, empty `Γ`, `Σ` empty, `n = 1` joins;
* frontier: the three cells that killed FRJ◯ v3 — `[⊥] ⇒ p`,
  `[p ∧ q] ⇒ p`, `[p, p ⊃ q] ⇒ q` — which must be **underivable** here;
* branch coverage: one admissible cell per constructor, including both
  `∧` arms and both joins.

**Round B (W5, before any modal rule is proposed for sign-off).**  Same
four directions, against each candidate ◯ rule, with the PLL corpus
substituted: the G4iLL blocker `◯((◯p→r)→◯p), ◯p→r ⇒ r`, the g4ill gap
sequent, the φ★/φ♦ ladder.  Every candidate is surfaced as a displayed
inference figure with its side conditions **and its screen results**, and
waits.

Discipline for both: three-valued verdicts (`pass`/`fail`/`flag`), `fail`
only ever on a certificate, `flag` a frontier marker never dropped
silently; run compiled as a `lean_exe`, one appended line per cell.

---

## 7. What W5 will have to decide, stated now so it is not discovered late

The handoff's §8 says ◯ in the syntax from W1 is cheaper.  It is worth
being precise about what that commits us to, because it is more than one
constructor.

The repo's PLL semantics is the Fairtlough–Mendler **constraint model**
(`LaxLogic/PLLKripke.lean`): two relations and a set of fallible worlds,

    C = ⟨W, Rᵢ, Rₘ, F, V⟩,     Rₘ ⊆ Rᵢ,   both reflexive and transitive,
    w ⊩ ⊥      iff  w ∈ F
    w ⊩ ◯φ     iff  ∀v. Rᵢ w v → ∃u. Rₘ v u ∧ u ⊩ φ

whereas FRJ's models are single-relation finite posets in which `⊥` is
forced nowhere.  So carrying ◯ from W1 means carrying **constraint
models** from W1, and Theorem 3.12 becomes "`Mod(D)` is a constraint
model and a countermodel for `G`" — `Mod(D)` must then produce `Rₘ` and
`F` as well as `Rᵢ`.  That is a genuine design question about the
extraction, not a syntactic one, and it is the place where the previous
attempt's `worldOK` went wrong.

There is a concrete target that settles the shape: `FinCM` and `checkB`
in `LaxLogic/PLLCountermodelEmit.lean`, with
`FinCM.not_provable_of_check`.  That is the repo's **certified** finite
constraint-model checker, and it is what makes a discovered countermodel
replayable by `decide`.  W6 should emit `Mod(D)` as a `FinCM`; stating
that at W1 means the extracted model is built in the shape the checker
already accepts, rather than translated into it afterwards.

Nothing here proposes a modal rule.  That is W5 and it is Matthew's.

---

## 8. Corpus, banked now

From the paper, for W2's screen and W6's timings.  The first three are
non-valid and must therefore be FRJ-refutable; the fourth is valid and
must not be:

    S = ((¬¬p ⊃ p) ⊃ ¬p ∨ p) ⊃ ¬¬p ∨ ¬p                    h(S) = 2
    T = S ⊃ (¬¬p ⊃ p) ∨ ¬¬p                                h(T) = 2
    K = K₀ ⊃ K₁,  K₀ = ¬a ⊃ b ∨ c,  K₁ = (¬a ⊃ b) ∨ (¬a ⊃ c)   h(K) = 1
        (the Kreisel–Putnam instance of Example 3.8)
    G = (p ∧ H) ⊃ (q₁ ∨ q₂),  H = p ⊃ q₁ ∨ q₂              VALID: must NOT be refutable

`G` is the discriminating cell: an irregular sequent with `G` on the
right **is** derivable (Example 3.15), and only the fact that it cannot
be used to derive a regular sequent keeps the calculus sound.  Any
formalisation that makes `G` refutable has mis-stated (SIRR).

---

## 9. Open decisions for Matthew

1. **Syntax staging** (handoff §8.1), refined by §7 above — **SETTLED
   2026-08-16: ◯ and constraint models from W1**, with `FinCM` as the
   extraction target.  The ◯-free results are therefore proved once, in
   the structure the modal case needs, and the price is that the
   extraction must decide infallibility of worlds from the start.  That
   is exactly where `FRJO/`'s `worldOK` failed, so it is screened, never
   assumed: the three refuting cells `[⊥] ⇒ p`, `[p ∧ q] ⇒ p`,
   `[p, p ⊃ q] ⇒ q` are in round A.
2. **The arXiv-vs-journal decision of §1** — cite the journal, prove the
   arXiv form of Lemma 3.10(ii), drop (RS1)–(RS4).  Taken; reversible;
   stated here rather than buried, because it changes which side
   conditions the rule table carries.
3. **Item 24** (rank, Lemma 6.2, Theorem 6.4): worth it?  It buys
   minimal-height countermodels, which is a real gain for a disproof
   engine, at the cost of `Rn` and one more clause in each case of
   Lemma 6.3.  Recommendation: after W4 closes, not before.
4. ~~The correction note to `docs/frj-fidelity.md`~~ — **SETTLED
   2026-08-16: renumbered throughout**, done.
5. **The saturation half of the v4 repair** (handoff §8.2) and **every
   modal rule statement** (handoff §8.3) remain open and untouched.
