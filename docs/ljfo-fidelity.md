# LJF◯ — the calculus-fidelity table

*Round 3 deliverable, 2026-08-12. Branch `ljf-pll`.*

**What this document is.** For every clause of the interpolant `interp`, it
records four things: the move the clause makes, the rule of LJF◯ that move
inverts or answers, whether the soundness and minimality proofs discharge
that clause on **raw rules** or through a **named toolkit lemma**, and
whether Pitts or Dyckhoff make the corresponding move on paper. It is the
skeleton a paper version of the proof would follow, and it is the map for
deciding where the mechanisation is a transcription and where it is an
extension.

**What it is not.** The right-hand column is an *expository* claim about
correspondence to the literature, not a theorem. Nothing in it is
machine-checked and nothing in it may be cited as one. The status of every
Lean result named here is in §5, and only §5 carries the PROVED /
conditional / OPEN discipline.

**Standing claim discipline.** Uniform interpolation for PLL is **OPEN**.
This document describes a construction and what is proved about it; it does
not claim the theorem.

---

## 1. The calculus

`LaxLogic/LJFOCore.lean` (frozen, zero imports). Four mutually inductive
judgments over a context `Γ : List Neg`, a pending list `Ω : List Pos`, a
flag `j : JD ::= tru | lax`, and polarised formulas

    Pos ∋ P ::= a | ⊥ | P ∨ P | ↓N          Neg ∋ N ::= ↑P | P ⊃ N | N ∧ N | ◯P

| judgment | meaning | rules |
|---|---|---|
| `Inv Γ Ω j N` | inversion (right rules + pending-list processing) | `impR`, `andR`, `circR`, `stable`, `orL`, `flsL`, `downL`, `atomL` |
| `Stab Γ j P` | stable sequent (no invertible rule applies) | `rfoc`, `lfoc`, `laxOf` |
| `RFocus Γ j P` | right focus on the goal | `init`, `or1`, `or2`, `rel` |
| `LFoc Γ N j P` | left focus on a hypothesis | `rel`, `impL`, `and1`, `and2`, `circL` |

**Provenance.** The polarised skeleton and the four judgments follow the
LJF style of focusing (the name is Liang–Miller's). The IPC calculus this
extends, `LaxLogic/LJF.lean`, is **not a port**: its header records that it
is built from its own rules and imports nothing, deliberately, "so that the
technique is what is under test" (Matthew, 2026-08-08). LJF◯ inherits that
discipline — zero imports, no other calculus carries any of the proof. The
◯-extension is ours and is exactly three rules plus one coercion:

* `circ : Pos → Neg` in the syntax, nothing else;
* `circR : Inv Γ Ω .lax (↑P) → Inv Γ Ω j (◯P)` — *sets* its premise to lax
  from either flag;
* `circL : Inv Γ [Q] .lax (↑P) → LFoc Γ (◯Q) .lax P` — the only rule with
  modal content, and lax-only. This is F&M's `SC` side condition "the
  succedent must be `◯`-shaped" recast as a phase condition;
* `laxOf : Stab Γ .tru P → Stab Γ .lax P` — the truth-to-lax coercion at the
  stable judgment. `PLLFocused.lean` lacked it and thereby missed `◯φ` for
  provable implicational `φ`; found by the identity port (plan §3-results
  (f)).

`impR`/`andR` are tru-only: at lax they would assert the converse of K.

---

## 2. The interpolant

`interp p todo done goal : Neg`, structurally recursive on a weight measure,
in two phases.

**Processing phase** — consume the head of `todo`, one clause per shape of
hypothesis. Thirteen clauses; nothing modal happens except that boxes and
◯-implications *park*.

**Aggregate phase** — `todo` exhausted, `done` saturated (`findFire = none`).
Two modes:

* `goal = none` (∃p): a conjunction over the station, `eConjRows`.
* `goal = some G` (∀p): dispatch on the shape of `G`. Shifted goals `↑G` use
  `truStationRows`; the ◯-goal is box-wrapped and uses
  `laxRows = laxPrefix ++ circStationRows`.

Both station maps and all nine aggregate equations are in
`LaxLogic/LJFORows.lean` (rounds 2 and 3). Before those rounds each map was
spelled out verbatim at every statement about it — seven times on the lax
side, four on the tru side.

---

## 3. The fidelity table

Legend for the apparatus columns: **raw** = the clause is discharged by
constructors of the four judgments alone; a **name** = it goes through that
toolkit lemma. Legend for the paper column: **Pitts** / **Dyckhoff** = the
same move is made on paper; **ours** = no counterpart, introduced by the
polarisation or by ◯; **—** = no move (bookkeeping).

### 3.1 Processing phase

| # | `todo` head | move | soundness (`eSound`/`aSound`) | minimality (`eMinF`/`aMinF`) | paper |
|---|---|---|---|---|---|
| 1 | `↑a` | park the atom | raw / raw | raw / raw | Pitts (atoms accumulate) |
| 2 | `↑⊥` | absurd: `⊥` in ∃p, `⊤` in ∀p | raw / `invertPos` | `nBotElimJ` / raw | Pitts |
| 3 | `↑(P∨Q)` | split the context | `nOrAllIntro` / `simHyp`, `lfocAndAll` | `invUp`, `nOrAllElimJ` / `invUp`, `nAndAllIntro` | Pitts |
| 4 | `↑↓M` | shift into the context | `invertPos` / `invertPos` | `invUp` / `invUp` | ours (polarity) |
| 5 | `M∧N` | split the conjunction | `simHyp` / `simHyp` | `invAndHyp` / `invAndHyp` | Pitts |
| 6 | `⊥⊃N` | inert, drop | raw / raw | `invImpFls` / `invImpFls` | Dyckhoff (L⊥⊃) |
| 7 | `a⊃N` | park until the atom arrives | raw / raw | raw / raw | Dyckhoff (La⊃) |
| 8 | `(Q₁∨Q₂)⊃N` | split the antecedent | `simHyp` / `simHyp` | `invImpOr` / `invImpOr` | Dyckhoff (L∨⊃) |
| 9 | `↓↑P′⊃N` | strip the double shift | `simHyp` / `simHyp` | `invStrip` / `invStrip` | ours (polarity) |
| 10 | `↓(M₁∧M₂)⊃N` | curry | `simHyp` / `simHyp` | `invCurry` / `invCurry` | Dyckhoff (L∧⊃) |
| 11 | `↓(Q′⊃N′)⊃N` | park — the Dyckhoff shape | raw / raw | raw / raw | **Dyckhoff (L⊃⊃), the hard rule** |
| 12 | `◯Q` | park — not left-invertible | raw / raw | raw / raw | **ours** |
| 13 | `↓◯Q′⊃N` | park — the modal Dyckhoff shape | raw / raw | raw / raw | **ours** |

Clauses 11–13 are the whole difficulty. On paper Dyckhoff's `L⊃⊃` is where
Pitts' induction needs its weight argument; clauses 12 and 13 are the modal
analogues we had to invent, and 13 is where `CimpAnt` sits (§5).

### 3.2 Aggregate phase, ∃p (`goal = none`)

One clause. The value is `nAndAll (eConjRows p done)`: one conjunct per
split of the station.

| station member | conjunct | apparatus |
|---|---|---|
| `↑a` (surviving atom) | `pGuard p a ⊤ (↑a)` | `atomConjMem`, `atomAssemble` |
| `a⊃N` | `pGuard p a ⊤ (a ⊃ E(N,rest))` | `qimpConjMem`, `qAssembleN` |
| `↓(Q′⊃N′)⊃N` | `(↓A(…) ⊃ E(N,rest)) ∧ E(…)` | `dykConjMem`, `dykAssembleN` |
| `◯Q` | `◯↓E([↑Q],rest)` | `boxConjMem`, `boxAssembleN` |
| `↓◯Q′⊃N` | `(↓A(rest ⇒ ↑↓◯Q′) ⊃ E(N,rest)) ∧ E(rest)` | `cimpConjMem`, `cimpAssembleN` |

`pGuard p a` is the elimination guard: a member mentioning `p` contributes
`⊤`. Rows 4 and 5 are ours; rows 1–3 are Pitts' hypothesis cases.

### 3.3 Aggregate phase, ∀p (`goal = some G`)

Dispatch on `G`. The station rows are shared — `truStationRows` for shifted
goals, `circStationRows` for the ◯-goal — and only the goal-inversion prefix
varies.

| goal | prefix | station map | equation | paper |
|---|---|---|---|---|
| `Q ⊃ N` | — (guarded branch conjunction) | none | `interpA_imp_eq` | Pitts, **with our guard** (see §4.1) |
| `M ∧ N` | — | none | `interpA_and_eq` | Pitts |
| `↑a`, `a ∈ done` | — | none (value `⊤`) | `interpA_atomT_eq` | Pitts |
| `↑a`, `a ∉ done` | `atomHead p a` | `truStationRows` | `interpA_atom_eq` | Pitts |
| `↑⊥` | — | `truStationRows` | `interpA_fls_eq` | Pitts |
| `↑(P₁∨P₂)` | the two disjuncts' ∀p | `truStationRows` | `interpA_or_eq` | Pitts |
| `↑↓M` | `A(M)` | `truStationRows` | `interpA_down_eq` | ours (polarity) |
| `◯Q`, seven shapes of `Q` | `laxPrefix p done Q` | `circStationRows` | `interp_circ_laxRows` | **ours** |

`circStationRows` is `truStationRows` plus one row — the `circL` row, which
exists only at a lax goal because only a lax sequent may focus left on a
box. That one row is the entire modal content of the aggregate.

The seven-way split on the shape of `Q` under the `◯` is **irreducible**:
`interp`'s ∀p dispatch matches on the positive *under* the modality, so no
tactic can cross the wrapper at an abstract `Q`. Round 2 reduced it from
seven restated lemmas to seven branches of one lemma; it cannot be reduced
below that without changing `interp`.

### 3.4 The traversal families

The minimality side is a mega-mutual of eighteen functions. They pair up:

| ∃p side | ∀p side | what it traverses |
|---|---|---|
| `eMinF` | `aMinF` | the processing phase, clause for clause with §3.1 |
| `TInv` | `UInvG` | inversion at a saturated station |
| `TStab` | `UStab` | the stable sequent (attack emission) |
| `TRF` | `URF` | right focus |
| `TLF` | `ULF` | left focus on a kept hypothesis |
| `TpElim` | `UpElim` | the `p`-fire eliminator |
| `TpLF` | `UpLF` | left focus after a `p`-fire |
| `TpInv` | `UpInvG` | inversion after a `p`-fire |

The `Tp*`/`Up*` triple has no counterpart in Pitts: it exists because the
eliminated atom `p` can be *fired* by a parked `p⊃N`, and the interpolant
must survive that fire. This is the mechanisation's largest structural
addition to the paper argument.

---

## 4. Where the mechanisation departs from paper practice

Four departures, all forced, all recorded with the failure that forced them.

**4.1 The guarded implication goal (forced change #1).** At a `Q ⊃ N` goal
the ∀p value conjoins, per branch `b`, `↓E(b) ⊃ A(b ⇒ N)` — the branch's
∀p **guarded by the branch's ∃p**. Without the guard, minimality demands
`E(Γ) ⊢ E(Γ+b)`, which is false. Soundness still closes because `eSound`
supplies the guard. The same guard reappears at the `↑(P∨Q)` context split.

**4.2 The box-wrapped ◯-goal aggregate (forced change #3).** The ◯-goal
value is `◯↓(⋁ rows)`, not `⋁ rows`. Refuted in the unwrapped form by a
two-line countermodel before any proof was attempted — the flag discipline
turned a design error into a refutable statement.

**4.3 The goal-inversion prefix (forced change #2).** Each ◯-goal aggregate
carries a prefix of goal-specific disjuncts before the station rows;
`laxPrefix` names it. At `↑(P₁∨P₂)` under a box the prefix has three entries,
which is why `URF`'s `or1`/`or2` arms select prefix rows 1 and 2 and stay
per-shape.

**4.4 `laxOf`.** The truth-to-lax coercion at the stable judgment, absent
from `PLLFocused.lean` and from the obvious reading of F&M's `SC`. Without
it the calculus misses `◯φ` for provable implicational `φ`.

---

## 5. Status ledger — PROVED / conditional / OPEN

| result | statement | status |
|---|---|---|
| `eSound` (E1) | the ∃p interpolant is sound | **PROVED**, `[propext, Classical.choice, Quot.sound]` |
| `aSound` (A1) | the ∀p interpolant is sound | **PROVED**, same pin |
| `interp_pfree` | the interpolant is `p`-free | **PROVED**, same pin |
| `idNeg` | identity expansion | **PROVED**, `[propext, Quot.sound]` |
| `BlockerTest.blocker` | the G4iLL blocker is derivable in LJF◯ | **PROVED**, no axioms |
| `satE2` (E2) | minimality of ∃p | **CONDITIONAL on `CimpAnt`**, sorry-free, same pin |
| `satA2` (A2) | minimality of ∀p | **CONDITIONAL on `CimpAnt`**, sorry-free, same pin |
| `CimpAnt` | the ◯-implication antecedent miner (clause 13) | **OPEN** |
| uniform interpolation for LJF◯ | — | **OPEN** (needs `CimpAnt`) |
| `focalizeSCO` / `FocalizationPLL` | focalization completeness for PLL | **PROVED** 2026-08-14, `[propext, Quot.sound]` (`LaxLogic/LJFOBridge.lean`) |
| `Stab.sound` / `sound_tru` | LJF◯ soundness for PLL (the erasure) | **PROVED**, same pin |
| `bridge_iff` | **LJF◯ ⊢ ⟺ PLL ⊢** | **PROVED**, same pin |
| uniform interpolation for PLL | — | **OPEN** (needs `CimpAnt` only; focalization for PLL is now PROVED) |

**Update 2026-08-14.** The row "focalization for PLL" has moved from
OPEN to PROVED. `LaxLogic/LJFOBridge.lean` supplies the ◯-preserving
polarisation `posOfO`/`negOfO` (`LJFComplete`'s `posOf`/`negOf` discard
the modality, since that development targets IPC through
`PLLND.erase`), the erasure and its soundness, and `focalizeSCO` — the
port of `LJFComplete.focalizeSC`, whose only new content is the two
modal cases (`laxR` ↦ `circR`/`laxOf`, `laxL` ↦ `circR`/`lfoc`/`circL`),
those being trivial in `LJFComplete` only because `negOf` erases `◯`.
Every other helper already existed in `LJFOCore` with the flag
threaded. So the remaining obstacle to uniform interpolation for PLL is
`CimpAnt` alone.

`CimpAnt` is isolated as a typed hypothesis exactly as `DykAnt` was for
clause 11. **`DykAnt` is no longer open**: `dykAnt : DykAnt p` exists
(LJFO.lean:2079). Note carefully what that does and does not mean — `dykAnt`
is `dykAntC cAnt …`, defined inside the section parameterised by
`variable (cAnt : CimpAnt p)`, so its Lean term takes `cAnt` like everything
else in the mega-mutual. It introduces no *new* assumption; `CimpAnt` is the
single open obligation of the whole development, and the intuitionistic
clause-11 analogue is discharged relative to it. Its discharge fails for
every consumed-implication
architecture at χ-uses inside crossed-station material (Howe's ①/②
duplication, MSCS 2001 §5). The frontier attack on its *statement* produced
zero certified failures.

---

## 6. What this feeds

* **`docs/calculus-map.md` has no LJF◯ entry.** It should gain one: LJF◯ is
  a further system in this repository, ours, the ◯-extension of the
  self-contained focused calculus in `LaxLogic/LJF.lean`. What depends on it:
  `LJFORows`, `LJFO`, `LJFOHeight`, `LJFOUniverse`, `LJFOSearch`, `LJFOFuel`,
  and the four `wip/ljfo_*` probes (`_eval`, `_attack`, `_attack_weights`,
  `_crosscheck`) — nothing else. Until that entry exists the map is incomplete —
  flagged here rather than edited, because that file is the provenance
  reference and its revision is a separate decision.
* **The paper skeleton.** §3.1 is the case list of a paper proof, in order;
  §4 is the "what is new" section; §5 is the theorem list with its honest
  status.
* **Layer 4.** `interpF` mirrors `interp` clause for clause with the
  retention guard at all twelve modal sites. §3.2/§3.3 say which row
  families it will grow, and round 3's lesson says to name them from the
  start rather than restate them per shape.
