# Horn clauses and Herbrand models for QLL: plan

Dated 2026-09-11.  A new stage **H**, inserted after stage 2 of
`docs/qll-clp-implementation-plan.md` and before stage 3; stage 5 (§7 of the
draft) builds on it.  Nothing below is built yet: every statement is **OPEN**
unless marked otherwise.

## 1. What the repository has, and what it lacks

Has: Def 5.1 (`IsSigma`, `Clause`, `Program`) and the five Fig. 3 rules
(`QLL/LLP.lean`); the Kripke semantics `KModel`, `force`, `force_openAt`,
`force_of_fallible` (`Kripke.lean`); the consequence relation `Γ ⊫ A` and
`Prv.sound` (`Prov.lean`); completeness by a saturated Lindenbaum construction,
`completeness1`, `prv_iff_consequence` (`Complete1.lean`, uses
`Classical.choice`); the paper's models `CModel`, `CModel.toKModel`, `thm_3_6`
(`PaperSemantics.lean`); `Derives.erase`, `Derives.weakenCons`, `Kit.freshFor`.

Lacks: any notion of Horn clause, ground term, Herbrand interpretation, least
model or fixpoint operator.  The Horn clauses are implicit in Def 5.1: a
`Clause` is `∀x̃. S ⊃ H` with `S` a Σ-formula, and a Σ-body is a finite
disjunction of Horn bodies (the draft's `ind(S)`, `S♯g`, §6.2).

## 2. Vocabulary (standard)

* **Primitive positive (pp) formula**: built from `⊤`, atoms, `∧`, `∃` (the
  *regular* formulas of categorical logic).
* **Positive existential formula**: pp plus `∨`.  These are exactly the draft's
  Σ-formulas.
* **Horn clause** (Lloyd's *definite clause*): `∀x̃. B₁ ∧ … ∧ Bₖ ⊃ H`, `Bᵢ`,
  `H` atoms with arbitrary terms.  A variable occurring only in the body may
  equally be read existentially in the body, since
  `∀ỹ(B ⊃ H) ⊣⊢ (∃ỹ.B) ⊃ H` for `ỹ` not in `H`; so a Horn clause is
  `∀x̃. φ ⊃ H` with `φ` pp, up to prenexing.
* **Modal Horn clause**: the same with head `◯_q H`.
* **Herbrand universe** `𝓗`: ground terms.  **Herbrand interpretation**: a set of
  ground atoms.  **Least Herbrand model** `M_P`, **immediate consequence
  operator** `T_P` (van Emden and Kowalski 1976; Lloyd, *Foundations of Logic
  Programming*, 2nd ed. 1987, §6, where `M_P = lfp T_P = T_P↑ω` and `M_P` is the
  set of ground atoms that are logical consequences of `P`; section numbering
  from memory, the book is not on this machine).
* **Lloyd–Topor transformation** (Lloyd and Topor 1984): rewriting clause bodies
  with `∨`, `∃` into definite clauses.  Its positive part is what `ind(S)` does.
* For §7's world 2, least models **relative to built-in relations** (Jaffar and
  Lassez, *Constraint logic programming*, POPL 1987): the constraint predicates
  keep a fixed interpretation `R_c`.

## 3. Design decisions

**D1. A Horn body is a pp formula, not a list of atoms.**  From Def 5.1 to Horn
clauses only disjunctions must be split, and splitting `∨` leaves every de Bruijn
index where it was.  Prenexing does not: `A ∧ ∃y.B ⊣⊢ ∃y.(A↑ ∧ B)` shifts the
indices of `A`, which needs a lift operation the syntax does not have.  Lloyd's
list-of-atoms form is the prenex form of a pp body; it is recovered in stage 4,
where the draft's Table 1 computes `S♯g = ∃ỹ. ⋀ᵢ Dᵢ` already prenexed and so
needs the lift anyway.  Nothing in stage H or in §7 needs the prenex form.

**D2. Heads carry arbitrary terms**, as in Lloyd.  Def 5.1's heads
`P(x₁, …, xₘ)` are the special case `args = headVars m`.

**D3. The Herbrand universe is over the full signature**: every `String` is a
function symbol of every arity, as `Tm` already has it.  Lloyd uses the
program's own symbols and adds a constant when there is none.  The difference
is harmless: his theorem holds for any language containing the program's
symbols, and a ground term always exists.

**D4. The least model is an inductive predicate, not `OrderHom.lfp`.**  Checked
in a scratch file this session: for `T := insert 0` on `Set ℕ`, Mathlib's
`OrderHom.lfp_le` and `OrderHom.map_lfp` give
`[propext, Classical.choice, Quot.sound]`, while the same facts for an inductive
predicate depend on no axioms.  An inductive predicate also gives the induction
principle that proof extraction is (induction on the stage at which an atom
enters the model).  The equation with `OrderHom.lfp` is kept as a side theorem,
with its choice pinned.

**D5. Modal results are for single-modality programs**, as in the draft, which
has one `◯`: T1 below assumes every modal clause carries the query's `q`.  T0
needs no restriction.

**D6. Extraction goes to `Prv` first.**  Theorem 7.5 speaks of LLP derivations
with proof terms, needed only at world 2, where the constraint `|q|` is read off
the term.  At the `Derives` level the same recursion needs `Derives.weakenCons`
with names from `Kit.freshFor` and no cut theorem, since derivations are built
bottom-up; it is scheduled with stage 5, where `|q|` exists.

## 4. The definitions (Lean sketches; names may change)

```lean
inductive IsPP : Form → Prop
  | top | pred (P ts) | and : IsPP A → IsPP B → IsPP (.and A B)
  | ex : IsPP A → IsPP (.exists_ A)

structure Horn where
  arity : Nat
  body  : Form          -- IsPP; loose indices < arity
  body_pp : IsPP body
  head  : String
  args  : List Tm       -- loose indices < arity
  modal : Bool
  q     : Q

def Horn.form (h : Horn) : Form := Form.foralls h.arity (.imp h.body h.headForm)

-- the draft's ind(S) and the ∨-selection part of S♯g
inductive Idx | leaf | pair (g₁ g₂ : Idx) | inl (g : Idx) | inr (g : Idx) | ex (g : Idx)
def ind : Form → List Idx
def sel : Form → Idx → Form
def Clause.toHorn (c : Clause) : List Horn   -- one Horn clause per g ∈ ind c.body

def Tm.Ground (t : Tm) : Prop := Tm.lcAt 0 t ∧ t.fv = []

-- the least Herbrand model, relative to built-in relations R, together with
-- truth of pp formulas in it (one inductive, so the clause premise is positive)
inductive Holds (R : String → List Tm → Prop) (P : List Horn) : Form → Prop
  | base  : R p ts → (∀ t ∈ ts, t.Ground) → Holds R P (.pred p ts)
  | top   : Holds R P .top
  | and   : Holds R P A → Holds R P B → Holds R P (.and A B)
  | ex    (t : Tm) : t.Ground → Holds R P (A.openAt 0 t) → Holds R P (.exists_ A)
  | fire  : h ∈ P → h.modal = false → ts.length = h.arity → (∀ t ∈ ts, t.Ground) →
            Holds R P (Form.instAll ts h.body) → Holds R P (Form.instAll ts h.headAtom)

def LHM (R) (P) (p : String) (ts : List Tm) : Prop := Holds R P (.pred p ts)
```

The Herbrand models are ordinary `KModel`s; no new semantics is introduced.

```lean
-- one world: Lloyd's Herbrand interpretation
def herbrand1 (I : String → List Tm → Prop) : KModel where
  S := Unit; D := Tm; Dom _ t := t.Ground
  Ri _ _ := True; RA _ _ := True; RE _ _ := True; Fl _ := False
  fn f ds := .fn f ds; I _ := I; d₀ := .fn "c" []   -- …proof fields

-- truth of a closed formula in a Herbrand interpretation *is* forcing there
def HTrue (I) (A : Form) : Prop := (herbrand1 I).force A () (fun _ => .fn "c" []) []

-- two worlds 0 ≤ 1, constant domain 𝓗, Rm = Ri = ≤, nothing fallible:
-- §7's frame restricted to the worlds {0, 1}
def herbrand2 (I₀ I₁ : String → List Tm → Prop) (h : I₀ ≤ I₁) : CModel
```

## 5. The theorems

`Γ ⊫ A` is the existing Kripke consequence, `Γ ⊢q A` the existing `Prv`.
Throughout, programs and queries are closed, `S` is a Σ-formula, and
`P.forms`, `Θ.forms` are the clause formulas.

### 5.1 Horn clauses made explicit (file H1)

    (N1)  IsSigma S → g ∈ ind S → IsPP (sel S g)
    (N2)  [S] ⊢q ⋁_{g ∈ ind S} sel S g      and     [sel S g] ⊢q S   (g ∈ ind S)
    (N3)  [c.form] ⊢q h.form  (h ∈ c.toHorn)   and   (c.toHorn).forms ⊢q c.form

(N2) is the draft's `S ≡ ⋁_g S♯g` of Example 6.4, before prenexing.  (N3) says
a Def 5.1 program and its Horn normal form prove the same formulas.

### 5.2 Lloyd's theory, ◯-free (file H2; the IPC instance, rule 8)

For a modal-free Horn program `P`, with `T_P` the immediate consequence operator
on Herbrand interpretations:

    (L1)  T_P (LHM R P) = LHM R P                       -- a fixpoint; in particular a model
    (L2)  R ≤ I → T_P I ≤ I → LHM R P ≤ I               -- the least one
    (L3)  LHM R P p ts ↔ ∃ n, (T_P^[n] R) p ts          -- T_P↑ω
    (L4)  LHM R P = OrderHom.lfp T_P                    -- side theorem, choice pinned

and the interface with the Kripke semantics:

    (K1)  evTm of a ground term is that term, in herbrand1 and herbrand2
    (K2)  HTrue I (.circ q A) ↔ HTrue I A ;  HTrue I (.imp A B) ↔ (HTrue I A → HTrue I B)
    (K3)  HTrue I (.exists_ A) ↔ ∃ t, t.Ground ∧ HTrue I (A.openAt 0 t)   -- by force_openAt
    (K4)  HTrue I h.form ↔ I is closed under the ground instances of h
    (K5)  IsPP φ → (Holds R P φ ↔ HTrue (LHM R P) φ)

Lloyd's theorem, over our consequence relation (`R = ⊥`):

    (LL)  P.forms ⊢q S   ↔   HTrue (LHM ⊥ P) S   ↔   P.forms ⊫ S

Proof plan.  `⊢q → ⊫` is `Prv.sound`.  `⊫ → HTrue` instantiates `⊫` at
`herbrand1 (LHM ⊥ P)`, which forces `P.forms` by (L1) and (K4).
`HTrue → ⊢q` is induction on `Holds` (atoms) and on `IsSigma` (the query),
using only `Prv.var`, `allE` (via a `Prv` twin of `Derives.allEs`), `impE`,
`andI`, `orI`, `exI` with a ground witness, and `topI`.  This is the draft's
remark that existentials are handled "by witnesses".

For ground atoms, (LL) is van Emden and Kowalski's `M_P = {A | P ⊨ A}`, with
`⊨` read as Kripke consequence.  The `⊫ → ⊢q` half is completeness for this
fragment proved without a Lindenbaum construction, which is Lloyd's route.
Whether its pinned axiom set is free of choice is the question deferred on
2026-09-11: the route is built not to need it (inductive least model,
instantiation, structural induction), the pins will report the outcome, and no
further effort goes into it now.

### 5.3 The LLP Herbrand model: §7 for worlds 0 and 1 (file H3)

For an LLP program `Θ` (Def 5.1, closed, one modality `q`), normalised by
`toHorn`:

* `Θ⁰`: the modal clauses dropped (the draft's `Π⁰`, `◯P ↦ true`);
* `Θ¹`: `◯` stripped from every head (the draft's `Π¹`, `◯P ↦ P`);
* `I₀ := LHM ⊥ Θ⁰ ≤ I₁ := LHM ⊥ Θ¹`, by (L2), since every clause of `Θ⁰` is one of `Θ¹`;
* `𝓜(Θ) := herbrand2 I₀ I₁`.

    (M1)  every clause of Θ is forced at world 0 of 𝓜(Θ)          -- Lemma 7.2 on {0,1}
    (M2)  0 ⊨ S ↔ HTrue I₀ S ;   0 ⊨ ◯_q S ↔ 1 ⊨ S ↔ HTrue I₁ S

(M1): a non-modal clause holds because `I₀` and `I₁` are both closed under it; a
modal clause `∀x̃. S ⊃ ◯P` holds at 0 because `S` true in `I₀ ≤ I₁` puts `P` in
`I₁`, and world 1 is `Rm`-reachable from 0 and from itself.  (M2): world 1 is
`Rm`-maximal and not fallible, so `◯` collapses there; Σ-formulas are forced
locally.

Theorem 7.5 for `i = 0, 1`, at the level of provability:

    (T0)  Θ.forms ⊢q S       ↔   HTrue (LHM ⊥ Θ⁰) S   ↔   Θ.forms ⊫ S
    (T1)  Θ.forms ⊢q ◯_q S   ↔   HTrue (LHM ⊥ Θ¹) S   ↔   Θ.forms ⊫ ◯_q S

The extraction half of (T1) is induction on `Holds` for `Θ¹`, producing
`Θ.forms ⊢q ◯_q A` for every atom `A` of the model.  Its steps are exactly
the stage 2 rules: `∧◯`, `∃◯`, and `◯⊤ = val(⋆)` assemble `◯` of a clause body
from `◯` of its atoms (plus `∨◯` for a Σ-query); then `⊃◯` fires a modal clause,
and CLP.lean's `impCirc` fires a non-modal one under `◯`.  So this proves that
the Fig. 3 calculus is complete for `◯`-queries against Def 5.1 programs, which
is what §5 presents it for.  The draft's own proof sketch ("a least fixedpoint
construction … using witnesses") is followed in outline; its details are not
used.

Theorem 7.5 is stated for closed atoms in `llp-mod.tex` and for closed
Σ-formulas in `temp.pdf`; (T0) and (T1) are the Σ version.

### 5.4 Four worlds: the canonical constraint model (stage 5, not stage H)

The frame, from the rendered page 17 of `temp.pdf` (the TeX source's
`model.eepic` is not on the drive): `0 ⇢ 1`, `0 ⇢ 2 ⇢ 3`, all arrows `Rm`,
`3` fallible.  World 2 is `LHM R_c Θ²` with `Θ² = (Θ : Ξ)♭`, the refinement by
the constraint table, and the constraint relations as the built-in `R`.  This
needs stage 3 (`|·|`, constraint tables) and stage 4 (refinement, prenex
`S♯g`).  Stage H supplies: `Holds` with a base `R`; a `CModel` built from a
finite frame and hereditary interpretations; the locality lemmas; (M1) for
worlds 0 and 1; and `force_of_fallible` covers world 3 (every formula is forced
at a fallible world).  What remains for stage 5: `I₀ ≤ I₂`; world 2 forces `Θ²`
(Def 7.1(3)); Theorem 7.5 at `i = 2`, where solvability enters.

## 6. How stage H connects to the existing model theory

| existing | role in stage H |
| :-- | :-- |
| `KModel`, `force` | `herbrand1`, `herbrand2` are instances; no new semantics |
| `force_openAt` | ground instances of quantifiers, (K3), (K4) |
| `force_of_fallible` | world 3 in stage 5 |
| `Γ ⊫ A` | completeness by instantiating it at a Herbrand model |
| `Prv.sound` | the soundness halves of (LL), (T0), (T1) |
| `completeness1`, `prv_iff_consequence` | not used; stage H reproves their Horn/LLP instance independently, without Lindenbaum, which also cross-checks them |
| `CModel`, `CModel.toKModel`, `thm_3_6` | `herbrand2` and the §7 model are `CModel`s with `Rm = Ri`; Def 7.1 becomes a predicate on `CModel`s |
| Fig. 3 rules (`LLP.lean`), `CLP.impCirc` | the proof steps of the extraction in (T1) |
| `Derives.erase`, `Derives.weakenCons`, `Kit.freshFor` | `Derives`-level extraction in stage 5 |
| `IsSigma`, `Clause`, `Program` | normalised to `Horn` by `Clause.toHorn` |

## 7. Work breakdown

| file | contents | depends on |
| :-- | :-- | :-- |
| H1 `QLL/Horn.lean` | `IsPP`, `Horn`, `Horn.form`, `Idx`, `ind`, `sel`, `Clause.toHorn`, (N1)–(N3) | `LLP.lean` |
| H2 `QLL/Herbrand.lean` | `Tm.Ground`, `Holds`, `T_P`, (L1)–(L4), `herbrand1`, `HTrue`, (K1)–(K5), (LL) | H1, `Prov.lean` |
| H3 `QLL/HerbrandLLP.lean` | `Θ⁰`, `Θ¹`, `herbrand2` as `KModel` and `CModel`, (M1), (M2), (T0), (T1) | H2, `PaperSemantics.lean` |

Order H1 → H2 → H3: H2 is the `◯`-free instance, H3 the modal one (CLAUDE.md
rule 8).  Refutation stage (rule 9), designed cells only:

* Why queries must be Σ: `P ∨ (P ⊃ ⊥)` is true in `herbrand1 ∅` but `[] ⊬q` it
  (two-state countermodel, `P` at the top state only).  To be checked in H2.
* Why programs must be Horn: `[P ∨ Q]` has no least Herbrand model, since
  `{P}` and `{Q}` are minimal models of it and neither contains the other.  To be
  checked in H2.

## 8. Decisions for Matthew

1. **D1** pp bodies now, prenex (Lloyd's exact form) in stage 4.  Recommended.
2. **D3** Herbrand universe over the full signature.  Recommended.
3. **Order**: stage H before stage 3.  Recommended: it depends on neither 3 nor
   4, stage 5 needs it, and it gives a second, independent completeness proof
   for the fragment.

## 9. Status, 2026-09-11: stage H built

Decisions D1–D3 and the order H → 3 were approved by Matthew on 2026-09-11.
Every item of §5 is PROVED, sorry-free, with pinned axioms, except the
`Derives`-level extraction, which D6 already assigned to stage 5.

| file | commit | what is proved | axioms |
| :-- | :-- | :-- | :-- |
| `QLL/Size.lean` | `4a4e526` | `Form.size`, hoisted from `Complete1.lean`; `size_openAt` | none |
| `QLL/Horn.lean` | `4a4e526` | (N1) `IsSigma.pp_sel`; (N2) `Prv.of_sel`, `Prv.disj_sel`, `KModel.force_iff_sel`; (N3) `Clause.prv_toHorn`, `Clause.prv_of_toHorn`; `Prv.foralls_congr` | `[propext, Quot.sound]` or less |
| `QLL/Herbrand.lean` | `d51cb21` | (L1) `Tp_LHM`; (L2) `LHM_least`; `HTrue_LHM_form`; (K1)–(K5) as `HFrame.evTm_lc`, `HTrue_*`, `Holds.toHTrue`, `Holds.of_HTrue`; (LL) `lloyd_completeness` | `[propext, Quot.sound]` |
| | | (LL) `lloyd_prv_iff`, `lloyd_consequence_iff`, `vanEmden_Kowalski` | `[propext, Quot.sound]` (see the note on choice) |
| `QLL/HerbrandLLP.lean` | `f395180` | (M1) `llpModel_clause`; (M2) `llpModel_sigma`, `llpModel_circ`; `llp_completeness0/1`; `llpCModel_force_iff` | `[propext, Quot.sound]` |
| | | (T0) `thm_7_5_world0`, (T1) `thm_7_5_world1` | `[propext, Quot.sound]` (see the note on choice) |
| `QLL/HerbrandFix.lean` | this commit's parent | (L3) `LHM_iff_Tpow` | `[propext, Quot.sound]` |
| | | (L4) `LHM_eq_lfp` | `+ Classical.choice` (Mathlib's `lfp`) |

The two designed cells of §7 are kernel-checked in the repository:
`lem_HTrue` with `lem_not_prv`, and `or_no_least_model` (`Herbrand.lean`).

Changes from the text above, all minor:

* **D3, extended.**  The Herbrand universe is the locally closed terms, with
  free names counted as constants.  Under `ρ = Tm.fvar` every such term
  evaluates to itself, so free names need no bookkeeping.  This is the device
  of the canonical model in `Complete1.lean`.
* **The Herbrand models are one construction.**  `HFrame.model` builds a
  `KModel` on any preorder of worlds.  `herbrand1` is the one-world case, and
  `herbrand2` (`HFrame.two`) the two-world one; stage 5 adds worlds 2 and 3
  to the same construction.
* **`Holds` ignores the modal flag.**  So `LHM` of all the Horn clauses of `Θ`
  is `Π¹`'s least model, with no separate stripping of `◯`.  `Π⁰` is the
  sub-program of non-modal clauses, `Program.horn0`.
* **Theorem 7.5 is stated against forcing.**  At worlds `0 = false` and
  `1 = true` of `llpModel Θ`, as in the draft.  The Herbrand-truth form
  follows by `llpModel_sigma`.

On choice (updated later on 2026-09-11): stage H uses none, except through
Mathlib's `lfp` in L4.  The soundness theorem `Prv.sound` used to carry it.
The source was Lean's core `String` library, not the logic: in this toolchain
`String.length` and `String.toList` depend on `Classical.choice`, and
`Kit.freshFor_notMem`, the fresh-name lemma behind `∀I` and `∃E`, was proved
by counting characters.  It is now proved by UTF-8 byte size instead
(`String.utf8ByteSize` depends on no axioms), with `freshFor` itself
unchanged.  `Prv.sound` and `Prv.soundT` are now `[propext, Quot.sound]`, and
ten pins across the QLL files lost choice.  What still uses choice in QLL:
the Lindenbaum completeness (`truth_lemma1`, `completeness1`,
`prv_iff_consequence`, and so `thm_3_6`), `refinement_not_complete`,
`CompleteTests.and_comm_prv`, and `LHM_eq_lfp`.

Still open for §2's citations: Lloyd's section and theorem numbers are from
memory.  The full text Matthew provided on 2026-09-11 (a claude.ai artifact)
could not be read from the session: the public link returns only the page
shell, and the `code/artifact` form of the same id reports it as not shared.
