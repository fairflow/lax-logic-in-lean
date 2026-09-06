# A Pitts-style uniform-interpolant clause table for LJF◯

Drafted 2026-09-04, worktree branch `worktree-agent-a4ac0cff1695042a1`,
base `a6ea18a` (the `LJF/` tree is byte-identical to `origin/frjw-dev`).

**Status of this document.  Nothing in it is machine-checked.**  It is a
paper reconstruction: the clause table, the termination analysis and the
two hand-computations of §4 were done by hand and are asserted at the
strength of a hand argument, which under `CLAUDE.md` rule 1 is OPEN, not
PROVED.  Three kinds of external support are cited, and each citation
says which kind it is:

* **PROVED**: a sorry-free Lean result with a `#print axioms` pin.  Used
  for `LJFO.eSound`, `LJFO.aSound`, `LJFIPC.uniform_interpolation_IPC`,
  the totality of `LJFO.interp`, and `PLLND.box_right_not_invertible`.
* **CONDITIONAL**: sorry-free but parameterised by an undischarged typed
  obligation.  Used for `LJFO.satE2` / `LJFO.satA2`, both conditional on
  `LJFO.CimpAnt`, for which no term exists anywhere in the repository.
* **ORACLE-CHECKED**: a verdict of the G4c decision procedure
  (`PLLND.Search.settle`, run through `lake exe pllbench --engine=g4c`),
  which returns a derivation on `valid` and a countermodel on `invalid`
  but is compiled code, not a kernel-checked theorem.  Eight such
  verdicts are used, listed in §4.0.

Nothing here is a `sorry`; no declaration is added anywhere; the open
items are recorded as data in §5, per rule 1.

---

## 0 · Scope, sources, and two corrections to the brief

### 0.1 What the document is for

The uniform interpolants for a logic with entailment ⊢, an atom `p` and a
formula `φ` are the `p`-free formulas `∃p.φ` and `∀p.φ` satisfying, for
every `p`-free ψ,

        φ ⊢ ψ   ⟺   ∃p.φ ⊢ ψ                    ψ ⊢ φ   ⟺   ψ ⊢ ∀p.φ

Pitts (JSL 57(1), 1992) constructs them by a simultaneous recursion over
backward proof search in Dyckhoff's contraction-free G4ip: a formula
`E_p(Γ)` recursing on left rules only, and `A_p(Γ ⇒ φ)` recursing on
(Γ, φ) jointly, one clause per rule, with an outer conjunction (for `E`)
or disjunction (for `A`) over all applicable rule instances.  The method
needs the calculus to be (R1) terminating in backward search, (R2)
complete, (R3) with the applicable rule instances determined by the
sequent alone, and (R4) closed enough that each clause is provable.

This document does that for LJF◯, the lax-flagged focused calculus of
`LJF/OCore.lean`.

### 0.2 The record this builds on (searched first, per `METHOD.md` §0)

The clause table below is **not new**.  A mechanised version of it exists
and has existed since August 2026:

| object | where | status |
|---|---|---|
| `LJFO.interp p todo done goal` | `LJF/OCore.lean:768–1104` | total, `termination_by 2 * sum3 todo + sum3 done + goalW goal` |
| `LJFO.eSound` (E1) | `LJF/OCore.lean:2519` | **PROVED**, pinned `[propext, Classical.choice, Quot.sound]` |
| `LJFO.aSound` (A1) | `LJF/OCore.lean:2731` | **PROVED**, pinned, same axioms |
| `LJFO.satE2` (E2), `LJFO.satA2` (A2) | `LJF/O.lean:2068`, `:2074` | **CONDITIONAL** on `LJFO.CimpAnt` |
| `LJFO.CimpAnt` | `LJF/O.lean:904–920` | **undischarged**; no term of that type in the repository |
| `LJFO.interpF` (the retaining variant) | `LJF/OFuel.lean:17` | definition only, nothing proved about it |
| the station row maps | `LJF/ORows.lean:81`, `:168`, `:262` | the read-off rows, factored |
| the IPC baseline `LJF.interp` | `LJF/Base.lean:710` | its UI theorem `LJFIPC.uniform_interpolation_IPC` **PROVED**, `LJF/Complete.lean:591`, pinned |

So the value of a fresh paper table is not the clauses.  It is (i) the
provenance marking of §2, which says of each clause whether it is
Pitts's, Pitts's modified, or ours, (ii) the termination analysis of §3
written out at the one place the mechanised measure does not reach, and
(iii) the two hand-computations of §4, which are the first worked
evaluations of the ◯-rows on the calculus's own separating sequents.

`docs/ljfo-fidelity.md` §§3–4 is the nearest existing prose table and
should be read beside this one; where they differ, that file is about
the mechanised `interp` and this one is about the paper reconstruction.

### 0.3 Uniform interpolation for PLL is OPEN

Standing claim discipline, repeated in `docs/ljfo-fidelity.md`,
`docs/ljfo-plan.md`, `docs/ui-two-routes.md` and `HANDOFF.md` §8:
**uniform interpolation for PLL is OPEN**, in neither direction settled,
and nothing in this document changes that.  Iemhoff's published proof
rests on G4iLL, which is REFUTED in this repository
(`PLLND.sep_not_G4`, `[propext]`), so no external proof stands either.

### 0.4 Correction 1: the multiplicity claim in the brief is not established

The brief states that

        ◯((◯p ⊃ r) ⊃ ◯((◯p ⊃ r) ⊃ ◯p)),  ◯p ⊃ r  ⇒  r

"needs three decides on `◯p ⊃ r`, and the pattern iterates, so there is
NO constant bound on decides".  Two separate things must be said.

* **The iteration claim is REFUTED as stated, for the calculus in which
  it was measured.**  The family is `wip/multiplicity.lean`'s
  `K 0 = ◯p`, `K (n+1) = ◯(F ⊃ K n)` with `F = ◯p ⊃ r`.  Its conjecture
  ("the least number of copies is `n+1`") was refuted by computation:
  `docs/ui-two-routes.md` §3.1 records the measured least copy count as
  `K 0 ↦ 1`, `K 1 ↦ 2`, `K 2 ↦ 2`, `K 3 ↦ 2`.  The reason given there:
  once inside the modal phase the goal stays ◯-shaped, so no further
  goal conversion is demanded, and the copies inside are shared across
  layers.
* **But those numbers are about `G4`, not LJF◯**, as `docs/ui-two-routes.md`
  §3.1a insists: `PLLDecide` decides `G4`, Iemhoff's naive and
  *incomplete* calculus, and in the retention-repaired `G4c` contraction
  is already admissible, so "how many copies" is not the right question
  there at all.  In LJF◯ the context is persistent (`Stab.lfoc` selects
  by membership), so "copies" is likewise the wrong quantity; the right
  one is **the number of `lfoc` decides on the hypothesis along one
  branch**.  Those are different numbers and there is no contradiction.

My own hand derivation in LJF◯ (§4.2) uses **three** decides on
`↓◯p ⊃ ↑r` for the nested sequent and **two** for the single one.
Whether fewer suffice in LJF◯ is **OPEN**: I did not machine-check
minimality of either derivation, and no such measurement exists in the
record.  The brief's "no constant bound on decides" is therefore
recorded here as OPEN for LJF◯ and REFUTED for `G4`'s copy count on the
`K n` family.

### 0.5 Correction 2: "retention is forced" needs splitting in two

The brief says retention is forced.  That is right at the level of the
**rule** and needs care at the level of the **clause**.

* At the rule: the antecedent premise of the derived ◯-implication left
  rule is `Γ ⊢_lax Q'` over the *full* Γ, and the G4ip residual `Q' ⊃ N`
  does not serve, because the hypothesis the inner subproof has is `◯Q'`,
  not `Q'`.  §1.3 gives the derivation; the diagnosis is not new
  (`docs/iemhoff-note.md` §2, `docs/lax-logic-interpolation-handoff.md`).
* At the clause: the drafted non-retaining ◯-implication rows survive
  both hand-checks of §4 on the E side, because the outer conjunction
  over the station repairs what the row drops.  On the A side the
  non-retaining row is strictly weaker than the retaining one, by exactly
  the formula `◯r` at the first frontier sequent.  §4.4 measures that
  gap, and §4.5 shows the retaining row closes it.

So retention is forced on the A row for the *unrelativised* ∀-equation,
and is not demonstrated to be needed on the E row.

---

## 1 · LJF◯ restated on paper

Transcribed from `LJF/OCore.lean:46–117`.  Lean constructor names appear
after each rule in a comment so the paper form cannot drift from the
mechanised one.

### 1.1 Syntax and judgments

        Positive   P, Q  ::=  a  |  ⊥  |  P ∨ Q  |  ↓N
        Negative   M, N  ::=  ↑P  |  Q ⊃ N  |  M ∧ N  |  ◯P
        Flag       j     ::=  tru  |  lax

`◯` is **negative with a positive body**; implication has a positive
antecedent and a negative consequent.  Contexts Γ are lists of negatives
and are **persistent**: no rule removes a hypothesis.  Ω is the list of
positives under inversion.

Four judgment forms:

        Γ ⊢_j P            stable                 (Stab Γ j P)
        Γ ⊢_j [P]          right focus            (RFocus Γ j P)
        Γ ; [N] ⊢_j P      left focus on N        (LFoc Γ N j P)
        Γ ; Ω ⊢_j N        inversion              (Inv Γ Ω j N)

### 1.2 The rules

Stable:

        Γ ⊢_j [P]  ⟹  Γ ⊢_j P                                          -- Stab.rfoc
        N ∈ Γ,  Γ ; [N] ⊢_j P  ⟹  Γ ⊢_j P                              -- Stab.lfoc     (DECIDE)
        Γ ⊢_tru P  ⟹  Γ ⊢_lax P                                        -- Stab.laxOf

Right focus:

        ↑a ∈ Γ  ⟹  Γ ⊢_j [a]                                           -- RFocus.init
        Γ ⊢_j [P]  ⟹  Γ ⊢_j [P ∨ Q]                                    -- RFocus.or1
        Γ ⊢_j [Q]  ⟹  Γ ⊢_j [P ∨ Q]                                    -- RFocus.or2
        Γ ; · ⊢_j N  ⟹  Γ ⊢_j [↓N]                                     -- RFocus.rel

Left focus:

        Γ ; Q ⊢_j ↑P  ⟹  Γ ; [↑Q] ⊢_j P                                -- LFoc.rel
        Γ ⊢_tru Q,  Γ ; [N] ⊢_j P  ⟹  Γ ; [Q ⊃ N] ⊢_j P                -- LFoc.impL
        Γ ; [M] ⊢_j P  ⟹  Γ ; [M ∧ N] ⊢_j P                            -- LFoc.and1
        Γ ; [N] ⊢_j P  ⟹  Γ ; [M ∧ N] ⊢_j P                            -- LFoc.and2
        Γ ; Q ⊢_lax ↑P  ⟹  Γ ; [◯Q] ⊢_lax P                            -- LFoc.circL

Inversion:

        Γ ; Q, Ω ⊢_tru N  ⟹  Γ ; Ω ⊢_tru Q ⊃ N                         -- Inv.impR
        Γ ; Ω ⊢_tru M,  Γ ; Ω ⊢_tru N  ⟹  Γ ; Ω ⊢_tru M ∧ N            -- Inv.andR
        Γ ; Ω ⊢_lax ↑P  ⟹  Γ ; Ω ⊢_j ◯P                                -- Inv.circR
        Γ ⊢_j P  ⟹  Γ ; · ⊢_j ↑P                                       -- Inv.stable
        Γ ; P, Ω ⊢_j N,  Γ ; Q, Ω ⊢_j N  ⟹  Γ ; P ∨ Q, Ω ⊢_j N         -- Inv.orL
        Γ ; ⊥, Ω ⊢_j N                                                 -- Inv.flsL
        M, Γ ; Ω ⊢_j N  ⟹  Γ ; ↓M, Ω ⊢_j N                             -- Inv.downL
        ↑a, Γ ; Ω ⊢_j N  ⟹  Γ ; a, Ω ⊢_j N                             -- Inv.atomL

Four facts about the flag carry the whole modal content.

1. `circL` is **lax only**.  A box hypothesis is unusable at a `tru`
   goal.  This is F&M's `SC` side condition ("the succedent must be
   ◯-shaped") recast as a phase condition.
2. `circR` fires at **either** flag and sets its premise to `lax`.  So
   the ◯-right rule is invertible here, which the single-judgment
   calculus cannot have: `PLLND.box_right_not_invertible : [◯p] ⊬ p`,
   PROVED, `wip/polarity.lean:68`, pinned `[propext, Quot.sound]`.
3. `impL` proves its antecedent at **tru** whatever the ambient flag.
   This is the only rule that switches `lax` back to `tru`.
4. `impR` and `andR` are **tru only**; at `lax` they would assert the
   converse of K.

### 1.3 The derived ◯-implication left rule, and why the residual trick fails

Composing `lfoc`, `impL`, `rfoc`, `RFocus.rel`, `circR` and `Inv.stable`
gives, for `↓◯Q' ⊃ N ∈ Γ`,

        Γ ⊢_lax Q'          Γ ; [N] ⊢_j P
        ─────────────────────────────────────  (L◯⊃)
                    Γ ⊢_j P

**Both premises see the full Γ**, including the principal formula, since
`lfoc` selects by membership.  The left premise is the site of the whole
difficulty.

In G4ip the corresponding rule `L⊃⊃` lightens its left premise: from
`Γ, D⊃B, C ⇒ D` and `Γ, B ⇒ E` infer `Γ, (C⊃D)⊃B ⇒ E`, justified by the
identity `C ⊢ ((C⊃D)⊃B) ↔ (D⊃B)`.  The lightening is licensed by the
premise's *assumption* `C`.

(L◯⊃) has no such assumption.  Its left premise is a **mode switch**, not
a context extension: nothing is added to Γ, only `j` moves to `lax`.
There is therefore nothing for a Dyckhoff-style identity to bite on, and
the residual is forced to be the principal formula itself.  Concretely,
with `Q' = p` and `N = ↑r` the naive residual would be `p ⊃ r`, and

        ◯((◯p ⊃ r) ⊃ ◯p),  p ⊃ r  ⊬_lax  p

because the hypothesis reached inside the box is `◯p`, not `p`, and
`p ⊃ r` does not yield `◯p ⊃ r`.  (Hand argument; the rule-level
diagnosis is the one recorded at `docs/iemhoff-note.md` §2, where the
same phenomenon refutes contraction-admissibility for G4iLL.)

---

## 2 · The clause table

### 2.1 The recursion's state

Following the mechanised design, the recursion carries a context split
into an unprocessed part Θ and a **station** Σ of parked hypotheses, plus
an optional goal:

        E(Θ | Σ)             the ∃p mode:  the strongest p-free consequence of Θ ++ Σ
        A(Θ | Σ ⇒ G)         the ∀p mode:  the weakest p-free hypothesis that,
                             beside Θ ++ Σ, suffices for G

with `E(Σ)` and `A(Σ ⇒ G)` abbreviating the Θ = · cases.  `p` is fixed
throughout and suppressed.

**The recursion carries no flag.**  This is load-bearing and is the
design's own decision (`LJF/OCore.lean:35–37`): the lax judgment is
definable, `Γ ⊢_lax P` iff `Γ ⊢_tru ↓◯P`, so the interpolant of a lax
sequent is the interpolant at the ◯-goal, and only the derivation
traversals carry `j`.  A flag-indexed clause table would be a different
(and larger) object.

Interpolant connectives, all inside the same syntax:

        ⊤ := ⊥ ⊃ ↑⊥        ⊥ := ↑⊥        M ∧ N        M ∨ N := ↑(↓M ∨ ↓N)

with ⋀ and ⋁ their finite folds (units ⊤ and ⊥).  `inv(Q)` is the list
of branches of the full left inversion of a positive:

        inv(a) = [[↑a]]      inv(⊥) = []      inv(P ∨ Q) = inv P ++ inv Q      inv(↓M) = [[M]]

**Provenance convention.**  A clause is marked

* **TRANSCRIBED** when it is clause-for-clause the corresponding clause
  of `LJF.interp` (`LJF/Base.lean:710`), the ◯-free interpolant whose
  uniform-interpolation theorem `LJFIPC.uniform_interpolation_IPC` is
  PROVED and pinned.  That is a checkable statement about this
  repository; I did not re-read Pitts 1992 while drafting, so the
  attribution to Pitts is through that file's own attribution and
  through Iemhoff (APAL 170(11), 2019), and is flagged where the
  rendering is disputable.
* **ADAPTED** when it is a Pitts clause modified for polarisation or for
  the two judgments, with the modification named.
* **NEW** when it has no ◯-free counterpart.

### 2.2 Processing clauses: consume the head of Θ

Both modes unless the modes are displayed separately.

| # | head of Θ | E and A | mark |
|---|---|---|---|
| P1 | `↑a` | `E/A(Θ \| ↑a, Σ)` | ADAPTED: bookkeeping.  Pitts classifies Γ by inspection; the Θ/Σ split makes the classification a recursion step. |
| P2 | `↑⊥` | `E = ⊥`, `A = ⊤` | TRANSCRIBED (L⊥: the sequent is an axiom; ⋁ over no branches is ⊥, ⋀ over none is ⊤). |
| P3 | `↑(P ∨ Q)` | `E = ⋁_{b ∈ inv(P∨Q)} E(b·Θ \| Σ)`;  `A = ⋀_b ( ↓E(b·Θ \| Σ) ⊃ A(b·Θ \| Σ ⇒ G) )` | E TRANSCRIBED (L∨).  A ADAPTED: each branch conjunct is **E-guarded**.  Without the guard minimality would demand `E(Γ) ⊢ E(Γ + b)`, which is false. |
| P4 | `↑↓M` | `E/A(M, Θ \| Σ)` | ADAPTED: pure shift bookkeeping, no ◯-free counterpart because IPC is unpolarised. |
| P5 | `M ∧ N` | `E/A(M, N, Θ \| Σ)` | TRANSCRIBED (L∧). |
| P6 | `⊥ ⊃ N` | `E/A(Θ \| Σ)` | TRANSCRIBED (the hypothesis is inert). |
| P7 | `a ⊃ N` | `E/A(Θ \| a ⊃ N, Σ)` | ADAPTED: bookkeeping; parks until its atom arrives. |
| P8 | `(Q₁ ∨ Q₂) ⊃ N` | `E/A(Q₁⊃N, Q₂⊃N, Θ \| Σ)` | TRANSCRIBED (L⊃∨). |
| P9 | `↓↑P' ⊃ N` | `E/A(P'⊃N, Θ \| Σ)` | ADAPTED: shift-strip, polarisation only. |
| P10 | `↓(M₁ ∧ M₂) ⊃ N` | `E/A(↓M₁ ⊃ (↓M₂ ⊃ N), Θ \| Σ)` | TRANSCRIBED (L⊃∧, currying). |
| P11 | `↓(Q' ⊃ N') ⊃ N` | `E/A(Θ \| ↓(Q'⊃N')⊃N, Σ)` | ADAPTED: bookkeeping; the Dyckhoff implication parks. |
| P12 | `◯Q` | `E/A(Θ \| ◯Q, Σ)` | **NEW.**  A box is not left-invertible: `circL` needs a lax goal, so nothing can be done with `◯Q` until the goal is known.  Parking is the only option. |
| P13 | `↓◯Q' ⊃ N` | `E/A(Θ \| ↓◯Q'⊃N, Σ)` | **NEW.**  The modal Dyckhoff shape.  Its left rule is (L◯⊃), whose left premise is goal-independent but whose right premise is not, so it too must wait. |

The thirteen clauses are exhaustive over `Neg` once P8–P13 have split
`Q ⊃ N` by the shape of `Q` (P8: `Q = Q₁∨Q₂`; P9/P10/P11/P13: `Q = ↓M`
by the shape of `M`; P7: `Q = a`; P6: `Q = ⊥`).

### 2.3 Firing and saturation

With Θ exhausted, a parked `a ⊃ N` whose atom has arrived fires:

        if  ↑a ∈ Σ  and  (a ⊃ N) ∈ Σ:      E/A(· | Σ)  =  E/A(N | Σ ∖ (a⊃N))

TRANSCRIBED (G4ip's `L⊃atom`).  Σ is **saturated** when no such pair
exists.  A saturated station holds exactly five shapes:

        ↑a          a ⊃ N (a absent)          ↓(Q'⊃N') ⊃ N          ◯Q          ↓◯Q' ⊃ N

the last two NEW.  (`LJFO.ParkedN`, `LJF/O.lean:241–246`.  Note that the
docstrings of both `LJF/OCore.lean:752` and `LJF/O.lean:236` still say
"exactly three shapes", prose left over from the ◯-free development; the
inductive says five.  A documentation defect, not a code defect.)

### 2.4 The E read-off at a saturated station

        E(Σ)  =  ⋀_{X ∈ Σ}  e(X, Σ ∖ X)

| # | X | `e(X, Σ∖X)` | mark |
|---|---|---|---|
| E1 | `↑a` | `↑a` if `a ≠ p`, else `⊤` | TRANSCRIBED. |
| E2 | `a ⊃ N` | `a ⊃ E(N \| Σ∖X)` if `a ≠ p`, else `⊤` | TRANSCRIBED. |
| E3 | `↓(Q'⊃N') ⊃ N` | `( ↓A(↓N'⊃N \| Σ∖X ⇒ Q'⊃N') ⊃ E(N \| Σ∖X) ) ∧ E(↓N'⊃N \| Σ∖X)` | TRANSCRIBED (Pitts's `L⊃⊃` clause: what the implication yields, guarded by what its antecedent demands, paired with the ∃p of the residual station).  The residual `↓N' ⊃ N` is the G4ip `D ⊃ B`. |
| E4 | `◯Q` | `◯ ↓ E(↑Q \| Σ∖X)` | **NEW.** |
| E5 | `↓◯Q' ⊃ N` | `( ↓A(· \| Σ∖X ⇒ ↑↓◯Q') ⊃ E(N \| Σ∖X) ) ∧ E(· \| Σ∖X)` | **NEW.** |

**E4, the reasoning.**  A box hypothesis `◯Q` is usable only under a lax
goal, and under a lax goal `circL` puts `Q` into the context.  So
everything the *opened* station yields is available, but only inside the
modality.  Hence: take the ∃p interpolant of the opened station
`↑Q, Σ∖X` and box it.  The clause is exactly the ◯-monotonicity of PLL
composed with the induction hypothesis, `Γ ⊢ ψ ⟹ ◯Γ ⊢ ◯ψ`.  What I am
unsure of: whether `◯↓E(↑Q | Σ∖X)` is the *strongest* p-free
consequence, i.e. whether all p-free content extractable from a box is
boxed.  It is not obviously so, since PLL has p-free theorems mixing
boxed and unboxed material; but I found no candidate for extra content
and the clause is the one the mechanised development uses.

**E5, the reasoning, and the contested part.**  The left rule (L◯⊃) has
two premises, and the clause mirrors them: the second premise's
contribution is `E(N | Σ∖X)`, and it is available only once the first
premise is discharged, so it is *guarded* by whatever the first premise
demands.  The first premise demands `⊢_lax Q'`, i.e. `⊢_tru ↓◯Q'`, so
its demand is the ∀p interpolant at that goal, and the guard reads
`A(· | ? ⇒ ↑↓◯Q')`.  The third component `E(· | Σ∖X)` is the analogue of
E3's residual component, forced there by the same induction.

The contested part is `?`.  Two candidates:

        (E5-r)  ? = Σ ∖ X       the residual station.  Terminating; what LJF◯ has.
        (E5-f)  ? = Σ           the full station.  Faithful to (L◯⊃); what
                                `LJF/OFuel.lean`'s `interpF` has; not terminating
                                on the additive measure (§3.4).

I draft (E5-r) as the table's clause, following the mechanised design,
and record (E5-f) as its repair.  §4 evaluates both.

Two shapes contribute nothing to `E(Σ)`: a `↑a` with `a = p` (E1) and a
`a ⊃ N` with `a = p` (E2), both ⊤ under the `p`-guard.

### 2.5 The A read-off, by the shape of the goal

Write `atk(Σ, G)` for the **station attacks**, the ways a saturated
station can advance a non-invertible goal:

| # | X ∈ Σ | disjunct of `atk(Σ, G)` | mark |
|---|---|---|---|
| C1 | `a ⊃ N` | `↑a ∧ A(N \| Σ∖X ⇒ G)` if `a ≠ p`, else `⊥` | TRANSCRIBED. |
| C2 | `↓(Q'⊃N') ⊃ N` | `A(↓N'⊃N \| Σ∖X ⇒ Q'⊃N') ∧ A(N \| Σ∖X ⇒ G)` | TRANSCRIBED (`L⊃⊃`). |
| C3 | `↓◯Q' ⊃ N` | `A(· \| Σ∖X ⇒ ↑↓◯Q') ∧ A(N \| Σ∖X ⇒ G)` | **NEW**; carries the same contested `?` as E5, drafted at `Σ ∖ X`. |
| C4 | `↑a`, `◯Q` | `⊥` | `↑a` TRANSCRIBED (an atom is not a left rule).  `◯Q` **NEW**: a box cannot be decided at a non-lax goal, so it contributes no attack here.  Its attack exists only at a ◯-goal, A7. |

The goal clauses:

| # | G | `A(Σ ⇒ G)` | mark |
|---|---|---|---|
| A1 | `Q ⊃ N` | `⋀_{b ∈ inv Q} ( ↓E(b \| Σ) ⊃ A(b \| Σ ⇒ N) )` | ADAPTED: **E-guarded**, as P3.  Pitts's `R⊃` clause is the unguarded `A(Γ, Q ⇒ N)`; the guard is needed because minimality would otherwise demand `E(Γ) ⊢ E(Γ+b)`.  This is the departure `docs/ljfo-fidelity.md` §4.1 calls forced change #1. |
| A2 | `M ∧ N` | `A(Σ ⇒ M) ∧ A(Σ ⇒ N)` | TRANSCRIBED (`R∧`). |
| A3 | `↑a` | `⊤` if `↑a ∈ Σ`; else `⋁ ( head(a) ∪ atk(Σ, ↑a) )`, where `head(a) = {↑a}` if `a ≠ p` and `∅` if `a = p` | TRANSCRIBED.  `head` is the axiom/right disjunct; it is dropped when `a = p` because the interpolant must be p-free. |
| A4 | `↑⊥` | `⋁ atk(Σ, ↑⊥)` | TRANSCRIBED. |
| A5 | `↑(P₁ ∨ P₂)` | `⋁ ( {A(Σ ⇒ ↑P₁), A(Σ ⇒ ↑P₂)} ∪ atk(Σ, ↑(P₁∨P₂)) )` | TRANSCRIBED (`R∨`, non-invertible, so both disjuncts appear). |
| A6 | `↑↓M` | `⋁ ( {A(Σ ⇒ M)} ∪ atk(Σ, ↑↓M) )` | ADAPTED: shift. |
| A7 | `◯P` | `◯ ↓ ⋁ ( pre(Σ, P) ∪ atk(Σ, ◯P) ∪ box(Σ, ◯P) )` | **NEW**, three separate departures, below. |

with

        box(Σ, ◯P)  =  { ↓E(↑R | Σ∖X) ⊃ A(↑R | Σ∖X ⇒ ◯P)   :   X = ◯R ∈ Σ }

and `pre(Σ, P)` the **goal-inversion prefix**, one family per shape of
the body, because `◯` does not distribute over `∨`:

        P = a          pre = { A(Σ ⇒ ↑a) }
        P = ⊥          pre = { A(Σ ⇒ ↑⊥) }
        P = P₁ ∨ P₂    pre = { A(Σ ⇒ ◯P₁), A(Σ ⇒ ◯P₂), A(Σ ⇒ ↑(P₁∨P₂)) }
        P = ↓↑P'       pre = { A(Σ ⇒ ◯P') }
        P = ↓◯P'       pre = { A(Σ ⇒ ◯P') }
        P = ↓(M₁∧M₂)   pre = { A(Σ ⇒ ↑↓(M₁∧M₂)) }
        P = ↓(Q₀⊃N₀)   pre = { A(Σ ⇒ ↑↓(Q₀⊃N₀)) }

**A7, the three departures, and the reasoning for each.**

1. *Box-wrapping.*  The aggregate is `◯↓(⋁ rows)`, not `⋁ rows`.
   Reason: the interpolant must be a `tru`-usable formula, but the rows
   are the ways of establishing a *lax* goal, and lax content is only
   recoverable under `◯`.  The countermodel that forces this is on
   record (`docs/ljfo-plan.md`, forced change #3): with `Σ = ·`,
   `Δ = [◯q]` and goal `↑q` at lax, `◯q ⊢_lax q` holds while
   `◯q ⊬_tru q`, so an unwrapped `A(· ⇒ ◯q) ≈ ↑q` would be wrong.
2. *The goal-inversion prefix.*  Since `◯` does not distribute over `∨`,
   the ways of proving `◯(P₁ ∨ P₂)` are not the union of the ways of
   proving `◯P₁` and `◯P₂`; the disjunctive body itself must appear as a
   row.  Hence the seven-way family.  `docs/ljfo-fidelity.md` §3.3
   records that this split is irreducible in the mechanisation.
3. *The box attacks.*  `box(Σ, ◯P)` is the entire modal content of the A
   aggregate: it is the only place `circL` can fire, and it is present
   only at a ◯-goal.  Each row opens one box and is **E-guarded** for the
   same reason as A1: the opened station is strictly larger, so its ∀p
   may legitimately depend on its own ∃p.

What I am unsure of in A7: whether `pre` is complete for every body
shape.  I checked `a`, `⊥`, `P₁∨P₂` and `↓◯P'` by hand and found no
missing row, but the `↓(Q₀⊃N₀)` case, where the body is an implication
under a box, is the one where a missing row would be hardest to notice,
and I did not check it.  Recorded as OPEN.

### 2.6 What is NEW, in one list

Six clauses have no ◯-free counterpart: **P12** (park a box), **P13**
(park a ◯-implication), **E4** (the box E-row), **E5** (the
◯-implication E-row), **C3** (the ◯-implication attack), **A7** (the
◯-goal, with its box-wrapping, its prefix family and `box(Σ, ◯P)`).
Two further clauses, **P3-A** and **A1**, are ADAPTED in the same
direction (E-guarding) and are the mechanised development's own
documented departures from Pitts.

`docs/ljfo-fidelity.md` §3.1 puts it the same way: clauses 11 to 13 are
the whole difficulty, and 13 is where `CimpAnt` sits.

---

## 3 · The termination measure

### 3.1 Weights

        w(a) = w(⊥) = 1            w(P ∨ Q) = w P + w Q + 1        w(↓N) = w N + 1
        w(↑P) = w P                w(Q ⊃ N) = w Q + w N + 1
        w(M ∧ N) = w M + w N + 3   w(◯P)    = w P + 1

The `+3` on `∧` is not decoration: it is exactly what pays for currying
(P10), where `w(↓M₁ ⊃ (↓M₂ ⊃ N)) = wM₁ + wM₂ + wN + 4` must be strictly
below `w(↓(M₁∧M₂) ⊃ N) = wM₁ + wM₂ + wN + 5`.  The `+1` on `◯` is what
pays for opening a box, below.

        Σ₃(Γ) = Σ_{N ∈ Γ} 3^{w N}        g(none) = 0        g(some G) = 3^{w G}

        μ(Θ, Σ, γ)  =  2·Σ₃(Θ)  +  Σ₃(Σ)  +  g(γ)

This is a well-founded order on the recursion's state (a single natural
number, no lexicographic product).  It is **PROVED** to work for the
table of §2 as drafted: `LJFO.interp` is total, `LJF/OCore.lean:1059`,
with the thirty descent lemmas `dec_*` at `LJF/OCore.lean:548–739`
discharging every clause.

The doubling of Θ is what makes parking strict: a park moves `3^{w X}`
from the doubled side to the single side, so `μ` drops by `3^{w X}` even
though nothing was consumed.

### 3.2 The case analysis

Base inequalities, all instances of `3^a + 3^b < 3^c` for `a, b < c`
(`p3_add`), `2·3^a < 3^c` for `a < c` (`p3_2`), and `2·3^a + 3^b < 3^c`
for `a+2 ≤ c`, `b+1 ≤ c` (`p3_21`).

| clause | why the premises are smaller | lemma |
|---|---|---|
| P1, P7, P11, P12, P13 (park) | `2Σ₃Θ + (3^{wX} + Σ₃Σ) < 2(3^{wX} + Σ₃Θ) + Σ₃Σ` | `dec_park` |
| P2 | no premise | — |
| P3 (context split) | `Σ₃(b) < 3^{w(P∨Q)}` for every branch `b` | `invertPos_lt`, `dec_orctx`, `dec_orA` |
| P4 (shift in) | `3^{wM} < 3^{wM + 1}` | `dec_shift1` |
| P5 (∧ split) | `3^{wM} + 3^{wN} < 3^{wM+wN+3}` | `dec_and` |
| P6 (drop) | `Σ₃Θ < 3^{wX} + Σ₃Θ` | `dec_drop` |
| P8 (⊃∨ split) | `3^{wQ₁+wN+1} + 3^{wQ₂+wN+1} < 3^{wQ₁+wQ₂+1+wN+1}`, using `wQᵢ ≥ 1` | `dec_impor` |
| P9 (strip) | `3^{wP'+wN+1} < 3^{wP'+1+wN+1}` | `dec_stripshift` |
| P10 (curry) | the `∧`-cost inequality above | `dec_curry` |
| fire | `2·3^{wN} < 3^{1+wN+1}` | `dec_fire` |
| E2 | `2·3^{wN} < 3^{w(a⊃N)}` | `dec_qimp` |
| E3 / C2 | `2·3^{w(↓N'⊃N)} + 3^{w(Q'⊃N')} < 3^{w X}` and `2·3^{wN} < 3^{wX}` | `dec_dyk0/1/2` |
| **E4 / box(Σ,·)** | `2·3^{wQ} < 3^{wQ+1} = 3^{w(◯Q)}` | `dec_boxE`, `dec_boxA_g`, `dec_boxE_g` |
| **E5 / C3** guard | `3^{w(↑↓◯Q')} = 3^{wQ'+2} < 3^{wQ'+2+wN+1} = 3^{w X}` | `dec_cimp1`, `dec_cimp1_g` |
| **E5 / C3** fire | `2·3^{wN} < 3^{w X}` | `dec_cimp2`, `dec_cimp2_g` |
| **E5 / C3** residual | `Σ₃(Σ∖X) < Σ₃(Σ)` | `dec_cimp3` |
| A1 | `2·Σ₃(b) + 3^{wN} < 3^{wQ+wN+1}`; guard component with `g = 0` | `dec_ainv`, `dec_ainv0` |
| A7 direct row | `3^{wP} < 3^{wP+1}` | `dec_circDirect` |

Two entries deserve emphasis, because §3.4 turns on their margins.

* **The box row has margin exactly `3^{w R}`.**  Opening `◯R ∈ Σ`
  removes `3^{wR+1}` from the station and puts `↑R` on the doubled side
  at cost `2·3^{wR}`.  The drop is `3^{wR+1} − 2·3^{wR} = 3^{wR}`, and
  not one unit more.  This is the same inequality that pays for the atom
  fire, one level up, which is exactly why `w(◯P) = w P + 1` and not more.
* **The E5/C3 guard is affordable only because the principal formula is
  consumed.**  The goal `↑↓◯Q'` weighs `3^{wQ'+2}`; the principal `X`
  weighs `3^{wQ'+2+wN+1}`, at least `3^2 = 9` times more.  The guard is
  paid for out of `X`.  If `X` stays in the station, nothing pays.

### 3.3 The retained-formula case: what retention would be

The clause faithful to (L◯⊃) computes its guard at the **full** station:

        (E5-f)   e(X, Σ∖X) = ( ↓A(· | Σ ⇒ ↑↓◯Q') ⊃ E(N | Σ∖X) ) ∧ E(· | Σ∖X)
        (C3-f)   disjunct  =   A(· | Σ ⇒ ↑↓◯Q') ∧ A(N | Σ∖X ⇒ G)

for `X = ↓◯Q' ⊃ N ∈ Σ`.  This is exactly `LJF/OFuel.lean`'s `interpF`,
whose module header calls it "the `L◯→″` retention discipline that
dissolves the crossed-station obstruction"; `interpF` is founded on
structural fuel and nothing is proved about it.

Under `μ` the retained call is not a descent:

        μ(·, Σ, ↑↓◯Q')  =  Σ₃(Σ) + 3^{wQ'+2}     vs     μ(·, Σ, γ₀)  =  Σ₃(Σ) + g(γ₀)

which increases whenever `3^{wQ'+2} > g(γ₀)`, and in particular in the E
mode where `g(none) = 0`.  Worse, the retaining table is not a definition
at all without a further device: `A(· | Σ ⇒ ↑↓◯Q')` unfolds by A6 to a
disjunction containing `A(Σ ⇒ ◯Q')`, whose A7 row set contains
`atk(Σ, ◯Q')`, which contains (C3-f) at the same `X`, whose first
component is `A(· | Σ ⇒ ↑↓◯Q')` again.  The retained formula loops on
itself immediately.

### 3.4 The mode-switch financing argument, and where it stops

The loop above is not a real proof-search loop, and saying why is the
financing argument.

**The loop cut (claim, OPEN).**  Suppose a derivation of `Γ' ⊢_lax Q'`
contains a decide on `X = ↓◯Q' ⊃ N` whose `impL` antecedent premise is
`Γ' ⊢_tru ↓◯Q'`.  By definability that premise is the sequent being
derived, so the decide can be pruned and completeness is not lost.  The
same argument applies to an ancestor: within a derivation of
`Σ ⊢_tru ↓◯Q'`, a nested demand for `Σ ⊢_tru ↓◯Q'` at the same station
is redundant.

**What a genuine second use costs.**  A use of `X` that is *not*
redundant must have changed the goal in between, and the only rule that
returns from `lax` to `tru` is `impL`, whose principal formula must
itself be decomposed.  So every genuine re-use of `X` is separated by
the consumption of a *different* station member.  §4.2's derivation
exhibits this: the second decide on `↓◯p ⊃ ↑r` happens only after
`◯((◯p⊃r)⊃◯p)` has been opened by `circL` and the resulting
`(◯p⊃r) ⊃ ◯p` has been decided, and it happens at goal `↑r`, not at
goal `◯p`.  Each mode switch consumes Γ-structure.

**The candidate order.**  Index the recursion by a visited set
`V ⊆ M(Σ)`, where `M(Σ)` is the set of ◯-implications in the station;
let (E5-f)/(C3-f) be available only for `X ∈ M(Σ) ∖ V`, passing
`V ∪ {X}`; let every clause that changes the station reset `V` to ∅.
Discount the visited members from the station:

        μᵥ(Θ, Σ, γ, V)  =  2·Σ₃(Θ)  +  Σ₃(Σ ∖ V)  +  g(γ)

*The retained call descends.*  Before: `Σ₃(Σ∖V) + g(γ₀)`.  After:
`Σ₃(Σ∖V) − 3^{w X} + 3^{wQ'+2}`.  Since `w X = wQ' + 2 + w N + 1 > wQ' + 2`,

        3^{wQ'+2}  <  3^{w X}

so `μᵥ` strictly drops, whatever `γ₀` was.  This is the same inequality
`dec_cimp1` already spends; the only change is that the visited set,
rather than the sub-call's context, is what records the spending.

*Where it stops: the reset.*  When a clause consumes a station member,
`V` must be reset, or the discipline is incomplete.  §4.5 shows it must:
in the repaired computation of `A(Γ₁ ⇒ ↑r)` the hypothesis `↓◯p ⊃ ↑r` is
selected again after the station has changed to `◯p, r ⊃ ◯p, ↓◯p ⊃ ↑r`,
and with `V` still holding it the value drops from ⊤ to a strictly
weaker formula.  But the reset restores `Σ₃(V)` to the measure, so a
station-consuming step descends only if its own margin exceeds `Σ₃(V)`.
The tightest margin is the box row, computed in §3.2 as exactly
`3^{w R}`.  So `μᵥ` is well-founded if and only if

        Σ₃(V)  <  3^{w R}     at every box opening of `◯R` after visiting `V`

which is **false in general**: take `R` an atom, so `3^{wR} = 3`, and any
visited `X = ↓◯s ⊃ N`, whose weight is at least 5.

This lands on the place the record already names.  `docs/ljfo-plan.md`'s
terminus (I) says the same-station reference is "unpayable at the
box-row's crossing (the box's weight is spent exactly, `2·3^{wR}` vs
`3^{wR+1}`, leaving no margin)".  Reached from a different direction, the
discounted-station order fails at exactly that crossing.  I take the
agreement as confirmation rather than as a new finding.

### 3.5 Status of §3

* The measure `μ` for the table **as drafted** (with E5-r, C3-r):
  **PROVED**, `LJF/OCore.lean:1059`.
* The loop cut: **OPEN**, a claim with a plausibility argument, not a
  proof.
* The discounted-station order `μᵥ`: **REFUTED as a well-founded order**
  by the box-row margin computation above (hand argument), unless the
  reset can be avoided, which §4.5 says it cannot.
* Options on record for founding the retaining table: fuel
  (`LJF/OFuel.lean`, built, nothing proved), a non-additive order (route
  A′ of `docs/ljfo-plan.md`, research), or the finite-space and history
  discipline (route B, `LJF/OHeight.lean`, `LJF/OUniverse.lean`,
  `LJF/OSearch.lean`, all green, Matthew's chosen route).

---

## 4 · Hand-checks on the two frontier sequents

### 4.0 The instances, the eliminated variable, and the oracle checks

Abbreviations, all in LJF◯'s polarised syntax:

        H   :=  ↓◯p ⊃ ↑r                          the ◯-implication      ( ◯p ⊃ r )
        K   :=  ↓H ⊃ ◯p                                                  ( (◯p ⊃ r) ⊃ ◯p )
        G₁  :=  ◯↓K                                                      ( ◯((◯p ⊃ r) ⊃ ◯p) )
        K₂  :=  ↓H ⊃ ◯↓K
        G₂  :=  ◯↓K₂                                                     ( ◯((◯p⊃r) ⊃ ◯((◯p⊃r) ⊃ ◯p)) )
        D   :=  r ⊃ ◯p                            the Dyckhoff residual of K under H

`K` and `K₂` are ordinary Dyckhoff implications (`↓(Q'⊃N') ⊃ N` with
`Q' = ↓◯p`, `N' = ↑r`), so their residual `↓N' ⊃ N = ↓↑r ⊃ ◯p` strips by
P9 to `D`.  `H` is the modal Dyckhoff shape.  The two sequents are

        Γ₁  =  G₁, H  ⊢_tru  r                    Γ₂  =  G₂, H  ⊢_tru  r

**Which variable to eliminate, and why `p`.**  Take `p`, the atom under
the box.  Then (i) every hypothesis in play is `p`-carrying, so E4, E5,
C3 and A7 all fire, which is where the checks must bite; (ii) `r` is
`p`-free and `Γᵢ ⊢ r`, so the two UI equations both reduce to a single
test formula, and it is the goal of the frontier sequents themselves,
i.e. the derivation that forces the repeated decides on `H`.  Eliminating
`r` instead would leave the sharpest available test formula as `◯p`,
whose derivation does not exercise the outer decide on `H` at all, so it
is a weaker probe.

**Oracle checks.**  Eight PLL validity questions used below were put to
the G4c oracle, `lake exe pllbench --engine=g4c`, from
`docs/ui-ljfo-clause-table-cells.tsv`.  All eight settled in seconds;
none returned don't-know.  (`c1` and `c2` were independently returned
`invalid` by the certificate-carrying FRJW engine as well.)

| id | formula | verdict |
|---|---|---|
| c1 | `◯r` | **invalid** |
| c2 | `◯((◯p ⊃ r) ⊃ ◯p) ⊃ ◯p` | **invalid** |
| c3 | `(◯((◯p ⊃ r) ⊃ ◯p) ∧ ◯r) ⊃ ◯p` | valid |
| c4 | `(◯((◯p ⊃ r) ⊃ ◯p) ∧ (◯p ⊃ r)) ⊃ (◯r ∧ (◯r ⊃ r))` | valid |
| c5 | `((◯r ⊃ r) ∧ ◯r) ⊃ r` | valid |
| c6 | `◯((◯p ⊃ r) ⊃ ◯p) ⊃ ((◯p ⊃ r) ⊃ r)` | valid |
| c7 | `◯((◯p⊃r) ⊃ ◯((◯p⊃r) ⊃ ◯p)) ⊃ ((◯p ⊃ r) ⊃ r)` | valid |
| c8 | `(◯((◯p⊃r) ⊃ ◯((◯p⊃r) ⊃ ◯p)) ∧ (◯p ⊃ r)) ⊃ (◯r ∧ (◯r ⊃ r))` | valid |

c6 and c7 are the two frontier sequents; c1 is what the A-side check
turns on; c4, c5 and c8 are the E-side answers computed below, checked
against the sequents they must interpolate.

### 4.1 The two UI equations, stated exactly

For a station Σ and a `p`-free ψ:

        (∃-eq)      Σ ⊢ ψ            ⟺   E(Σ) ⊢ ψ
        (∀-eq)      Σ, ψ ⊢ φ         ⟹   ψ ⊢ A(Σ ⇒ φ)
        (∀-eq-E)    Σ, ψ ⊢ φ         ⟹   E(Σ), ψ ⊢ A(Σ ⇒ φ)

(∀-eq-E) is the statement the construction actually targets, both in the
proved IPC theorem and in the LJF◯ development.  `LJF/Complete.lean:578–585`
says so in as many words, and calls (∀-eq) "a different (and false)
statement, since a `p`-free Δ need not prove `exI p Γ`"; the
corresponding LJF◯ statement is `LJFO.SatA2`, `LJF/O.lean:339–344`, whose
conclusion carries `interp p [] done none` on the left.  At the top
level, where `∀p.φ := A(· ⇒ φ)` is read off, `Σ = ·` and `E(·) = ⊤`, so
the two coincide and the theorem is unaffected.

I check (∃-eq) and both A-statements.

### 4.2 The derivation being interpolated

For Γ₁ ⊢_tru r (oracle: c6 valid), a derivation with **two** decides on
`H`:

1. `lfoc` on `H`, `impL`.  Right premise: `Γ₁ ; [↑r] ⊢_tru r`, closed by
   `LFoc.rel`, `atomL`, `stable`, `init`.  Left premise: `Γ₁ ⊢_tru ↓◯p`,
   i.e. by `rfoc`/`rel`/`circR`/`stable`, `Γ₁ ⊢_lax p`.
2. `lfoc` on `G₁`, `circL` (legal: the flag is `lax`), then `downL`:
   `K, Γ₁ ⊢_lax p`.
3. `lfoc` on `K`, `impL`.  Right premise: `K, Γ₁ ; [◯p] ⊢_lax p`, closed
   by `circL`.  Left premise: `K, Γ₁ ⊢_tru ↓H`, i.e. by
   `rel`/`impR`/`downL`, `◯p, K, Γ₁ ⊢_tru r`.
4. **`lfoc` on `H` again**, at station `◯p, K, G₁, H` and goal `r`.  Its
   left premise `⊢_tru ↓◯p` is now immediate from the hypothesis `◯p`.

The second decide on `H` is at a `tru` goal reached *through* the lax
phase, in a context holding `◯p` and not `p`, which is what kills the
lighter residual (§1.3).  For Γ₂ the same shape with one more layer gives
**three** decides on `H`.  Whether two (resp. three) is least is OPEN,
per §0.4.

### 4.3 Check 1, the ∃ side

Both hypotheses park (P12, P13), giving the saturated station
`Σ₁ = [H, G₁]`, which does not fire.  So

        E(Σ₁)  =  e(H, [G₁])  ∧  e(G₁, [H])

**The `G₁` conjunct** is E4: `◯↓ E(↑↓K | H)`.  Processing `↑↓K` by P4 and
parking `K` by P11 gives the station `[K, H]`, so

        E(↑↓K | H)  =  e(K, [H])  ∧  e(H, [K])

`e(K, [H])` is E3 with residual `D`:

        ( ↓A(D | H ⇒ H)  ⊃  E(◯p | H) )  ∧  E(D | H)

sub-values, each computed by the same clauses:

* `E(◯p | H)`: `◯p` parks; the station is `[◯p, H]`; E4 gives
  `◯↓E(↑p | H)` and E5 gives, at `Σ∖X = [◯p]`,
  `( ↓A(· | [◯p] ⇒ ↑↓◯p) ⊃ E(↑r | [◯p]) ) ∧ E(· | [◯p])`.
  Now `A(· | [◯p] ⇒ ↑↓◯p) = A([◯p] ⇒ ◯p) ∨ ⊥` by A6 and C4, and
  `A([◯p] ⇒ ◯p) = ◯↓( A([◯p] ⇒ ↑p) ∨ box-row )` by A7 with
  `A([◯p] ⇒ ↑p) = ⊥` (A3, `head(p) = ∅`, `atk` empty by C4) and the box
  row `↓E(↑p | ·) ⊃ A(↑p | · ⇒ ◯p) = ⊤ ⊃ ◯⊤ ≡ ⊤`; so the guard is ⊤.
  And `E(↑r | [◯p]) ≡ r ∧ ◯r ≡ r`, `E(· | [◯p]) = ◯↓E(↑p | ·) = ◯⊤ ≡ ⊤`.
  Also `E(↑p | H) ≡ r` by the same E5 row.  Hence

        E(◯p | H)  ≡  ◯r ∧ r  ≡  r

* `E(D | H)`: `D = r ⊃ ◯p` parks (P7), the station is `[D, H]`, no fire
  (`r` absent).  E2 gives `r ⊃ E(◯p | H) = r ⊃ r ≡ ⊤`, and E5 at
  `Σ∖X = [D]` gives `( ↓A(· | [D] ⇒ ↑↓◯p) ⊃ E(↑r | [D]) ) ∧ E(· | [D])`.
  Here `A(· | [D] ⇒ ↑↓◯p) ≡ ◯r ∨ r ≡ ◯r` (A6, then A7 whose only row is
  the C1 attack `r ∧ A(◯p | · ⇒ ◯p) ≡ r`), `E(↑r | [D]) ≡ r` (the atom
  `r` arrives, `D` fires, `E(◯p | [↑r]) ≡ ◯r ∧ r ≡ r`), and
  `E(· | [D]) = r ⊃ ◯⊤ ≡ ⊤`.  Hence

        E(D | H)  ≡  ◯r ⊃ r

* `A(D | H ⇒ H)`: parks `D`, no fire; goal `H = ↓◯p ⊃ ↑r` is A1 with the
  single branch `b = [◯p]`, giving `↓E(◯p | D, H) ⊃ A(◯p | D, H ⇒ ↑r)`,
  and the second component is ⊤ by the C3 attack on `H` at
  `Σ∖X = [◯p, D]`, whose guard `A(· | [◯p, D] ⇒ ↑↓◯p) ≡ ⊤` and whose
  fire component `A(↑r | [◯p, D] ⇒ ↑r) ≡ ⊤` (the atom is present, A3).
  Hence `A(D | H ⇒ H) ≡ ⊤`.

So `e(K, [H]) ≡ (⊤ ⊃ r) ∧ (◯r ⊃ r) ≡ r`, and `e(H, [K])`, computed the
same way, is `(A([K] ⇒ ↑↓◯p) ⊃ E(↑r | K)) ∧ E(· | K) ≡ (◯r ⊃ r) ∧ ⊤`.
Therefore

        E(↑↓K | H)  ≡  r ∧ (◯r ⊃ r)  ≡  r          and      e(G₁, [H])  ≡  ◯r

**The `H` conjunct** is E5 at `Σ∖X = [G₁]`:

        ( ↓A(· | [G₁] ⇒ ↑↓◯p)  ⊃  E(↑r | [G₁]) )  ∧  E(· | [G₁])

The guard `A(· | [G₁] ⇒ ↑↓◯p)` is A6 followed by A7.  `atk([G₁], ·)` is
⊥ by C4 (a box gives no attack at a `↑`-goal), `pre([G₁], p)` is
`A([G₁] ⇒ ↑p) = ⊥` (A3: `head(p) = ∅` and again no attack), and the one
surviving row is the box attack on `G₁`:

        ↓E(↑↓K | ·)  ⊃  A(↑↓K | · ⇒ ◯p)

whose two components are computed at the empty residual station:

* `E({K})`: the only row is E3, giving
  `(↓A(D | · ⇒ H) ⊃ E(◯p | ·)) ∧ E(D | ·)` with `E(◯p | ·) = ◯↓E(↑p | ·) = ◯⊤`,
  `E(D | ·) = r ⊃ ◯⊤`, and `A(D | · ⇒ H) ≡ ◯⊤ ⊃ r ≡ r`.  Since `⊢ ◯⊤`,
  both conjuncts are provable, so `E({K}) ≡ ⊤`.  (Cross-check by
  substitution: `K[⊤/p] = (◯⊤ → r) → ◯⊤` is provable, so `K` has no
  non-trivial `p`-free consequence.)
* `A({K} ⇒ ◯p)`: A7 with `pre = { A({K} ⇒ ↑p) }` and `atk` the C2 attack
  on `K`.  `A({K} ⇒ ↑p) = ⊥` (its C2 attack has second component
  `A(◯p | · ⇒ ↑p) = ⊥`, a box at a `↑`-goal).  The C2 attack at the
  ◯-goal is `A(D | · ⇒ H) ∧ A(◯p | · ⇒ ◯p) ≡ r ∧ ⊤ ≡ r`.  So
  `A({K} ⇒ ◯p) = ◯↓(⊥ ∨ r) ≡ ◯r`.  (Sanity: `◯r` does suffice,
  oracle c3 valid; and ⊤ does not, oracle c2 invalid.)

So the box attack is `⊤ ⊃ ◯r ≡ ◯r`, giving `A(· | [G₁] ⇒ ↑↓◯p) ≡ ◯r`.
With `E(↑r | [G₁]) ≡ r ∧ ◯r ≡ r` and
`E(· | [G₁]) = ◯↓E({K}) ≡ ⊤`, the `H` conjunct is `◯r ⊃ r`, and

        **E(Σ₁)  ≡  ◯r  ∧  (◯r ⊃ r)  ≡  r**

**Verdict.**  (∃-eq) is satisfied on this instance: `Γ₁ ⊢ E(Σ₁)` is c4
(valid) and `E(Σ₁) ⊢ r` is c5 (valid), and `r` is `p`-free, so the test
formula ψ = r passes both directions.  Independently: substituting
`p := ⊤` turns Γ₁ into `◯((◯⊤→r)→◯⊤), ◯⊤→r`, which is `⊣⊢ r` since
`⊢ ◯⊤`, so every `p`-free consequence of Γ₁ follows from `r` and `E(Σ₁)`
is not merely sufficient but exactly right.  **PASSES.**

**The mechanism, and why it is worth banking.**  The `H` row dropped `H`
from its own guard and paid for it: the guard came out `◯r` rather than
⊤, and `◯((◯p⊃r)⊃◯p) ⊬ ◯p` (oracle c2), so the demand is real.  What
discharged it was the *sibling* conjunct `e(G₁, [H])`, which retains `H`
and yields exactly `◯r`.  The outer conjunction over the station repairs
what the row loses.

That is precisely the shape of the undischarged obligation.
`LJFO.CimpAnt` (`LJF/O.lean:904–920`) asks, for a station `done`
containing `X = ↓◯Q' ⊃ N` with residual `rest`, that

        E(done),  K   ⊢   A(· | rest ⇒ ↑↓◯Q')

whenever the mixed context proves `↓◯Q'`.  At this instance, with
`K = ·`, that reads `r ⊢ ◯r`, which holds.  **So Γ₁ and Γ₂ are
validating instances of `CimpAnt`**, and they are validating instances of
exactly the configuration the obligation exists for.  Banked as
validation in the sense of `METHOD.md` §3; they are not evidence that
`CimpAnt` is provable.

### 4.3b The same check on the nested sequent

`Σ₂ = [H, G₂]` is saturated for the same reason, and
`E(Σ₂) = e(H, [G₂]) ∧ e(G₂, [H])`.  The computation has the shape of
§4.3 with one extra layer, and the extra layer changes nothing, which is
the point.

**The `G₂` conjunct**, E4, is `◯↓E(↑↓K₂ | H)`, at station `[K₂, H]`.
The `K₂` row is E3 with residual `r ⊃ ◯↓K` (the same P9 strip, one
`◯↓K` in place of `◯p`):

        ( ↓A(r ⊃ ◯↓K | H ⇒ H)  ⊃  E(◯↓K | H) )  ∧  E(r ⊃ ◯↓K | H)

* `E(◯↓K | H)`: station `[◯↓K, H]`.  E4 gives `◯↓E(↑↓K | H) ≡ ◯r` by
  §4.3's inner computation, unchanged.  E5 on `H` at `Σ∖X = [◯↓K]` gives
  `(↓A(· | [◯↓K] ⇒ ↑↓◯p) ⊃ E(↑r | [◯↓K])) ∧ E(· | [◯↓K])`, whose guard
  is `◯r` (the box attack on `◯↓K` opens it, and the opened station's
  `A({K} ⇒ ◯p)` is `◯r` again), whose fire component is `r`, and whose
  residual component is ⊤.  So `E(◯↓K | H) ≡ ◯r ∧ (◯r ⊃ r) ≡ r`.
* `A(r ⊃ ◯↓K | H ⇒ H) ≡ ⊤`, by A1's single branch `[◯p]` and then the
  C3 attack on `H` at the deeper station, exactly as in §4.3.
* `E(r ⊃ ◯↓K | H) ≡ ⊤ ∧ (◯r ⊃ r) ≡ ◯r ⊃ r`, the atom row giving
  `r ⊃ E(◯↓K | H) = r ⊃ r ≡ ⊤` and the E5 row on `H` giving `◯r ⊃ r`.

So the `K₂` row is `(⊤ ⊃ r) ∧ (◯r ⊃ r) ≡ r`; the `H` row at
`Σ∖X = [K₂]` is again of the form `(… ⊃ r) ∧ …`; and
`E(↑↓K₂ | H) ≡ r`, so `e(G₂, [H]) ≡ ◯r`.

**The `H` conjunct**, E5 at `Σ∖X = [G₂]`, is
`(↓A(· | [G₂] ⇒ ↑↓◯p) ⊃ E(↑r | [G₂])) ∧ E(· | [G₂])` with guard `◯r`
(the box attack on `G₂` opens it and reduces, one layer down, to
`A({K} ⇒ ◯p) ≡ ◯r`), fire component `r`, residual ⊤.  Hence

        **E(Σ₂)  ≡  ◯r  ∧  (◯r ⊃ r)  ≡  r**

the same value as for Σ₁.  (∃-eq) holds: `Γ₂ ⊢ E(Σ₂)` is oracle c8
(valid), `E(Σ₂) ⊢ r` is oracle c5 (valid).  **PASSES.**

The nesting is absorbed because the extra layer is consumed by the box
row, not by the ◯-implication row: opening `G₂` yields `K₂`, whose
Dyckhoff residual carries `◯↓K`, whose own box row opens to the §4.3
computation.  Each layer costs one box opening, which the measure pays
for, and none of them costs an extra guard.  This is the interpolant-side
counterpart of the observation in `docs/ui-two-routes.md` §3.1 that once
inside the modal phase the goal stays ◯-shaped and the layers share
their uses.

### 4.4 Check 2, the ∀ side, and where the drafted clause stops

The station is again `Σ₁ = [H, G₁]`, saturated; the goal is `↑r` with
`r ≠ p` and `↑r ∉ Σ₁`, so A3 applies:

        A(Σ₁ ⇒ ↑r)  =  ↑r  ∨  atk(H, [G₁])  ∨  atk(G₁, [H])

* `atk(G₁, [H]) = ⊥` by C4: `G₁` is a box and the goal is not a ◯-goal,
  so `circL` cannot fire.  There is no row here at all.
* `atk(H, [G₁])` is C3: `A(· | [G₁] ⇒ ↑↓◯p) ∧ A(↑r | [G₁] ⇒ ↑r)`.  The
  second component is ⊤ (the atom parks and A3's `↑a ∈ Σ` case fires).
  The first is `◯r`, computed in §4.3.

Hence

        **A(Σ₁ ⇒ ↑r)  ≡  r ∨ ◯r  ≡  ◯r**

**Verdict against (∀-eq): REFUTED as drafted.**  Take ψ = ⊤, which is
`p`-free.  `Γ₁, ⊤ ⊢ r` holds (c6, valid).  (∀-eq) demands
`⊤ ⊢ A(Σ₁ ⇒ ↑r)`, i.e. `⊢ ◯r`, and `◯r` is **invalid** (c1).  So the
drafted C3 does not support (∀-eq) at a non-empty station.

**Verdict against (∀-eq-E): PASSES.**  `E(Σ₁) ≡ r` and `r ⊢ ◯r`, so
`E(Σ₁), ⊤ ⊢ A(Σ₁ ⇒ ↑r)`.  The same holds at `j = lax`, where
`jGoal lax ↑r = ◯r` and `A(Σ₁ ⇒ ◯r) ≡ ⊤` because A7's box row opens `G₁`
and the opened station settles the goal.

**The nested sequent behaves identically.**  `Σ₂ = [H, G₂]` gives
`A(Σ₂ ⇒ ↑r) = ↑r ∨ atk(H, [G₂]) ∨ ⊥`, and `atk(H, [G₂])` is C3 with
guard `A(· | [G₂] ⇒ ↑↓◯p) ≡ ◯r` (§4.3b) and fire component ⊤, so
`A(Σ₂ ⇒ ↑r) ≡ ◯r` as well.  Same refutation of (∀-eq), same pass of
(∀-eq-E) since `E(Σ₂) ≡ r`.  The extra layer neither helps nor hurts:
the gap is created at the outermost C3 row and is one `◯` deep however
deep the nesting is.

**What the check therefore establishes.**  Not a defect in the
development: (∀-eq-E) is what `SatA2` and the proved IPC theorem state,
and (∀-eq) is known to be false in general, for the ◯-free calculus
already.  What is new is the *measurement*: at a station whose only
non-modal hypothesis is a ◯-implication, the gap between (∀-eq) and
(∀-eq-E) is exactly the retention gap of §1.3, and it is the formula
`◯r`.  The E-relativisation is doing the work that retention would
otherwise do, and it is doing it at the ◯-implication row specifically.
Two consequences worth recording:

1. The E-guard is **not optional** in the modal case.  If a future
   variant of the table drops the relativisation anywhere on a path to a
   C3 row, this instance refutes it.
2. Because `E(·) = ⊤`, the top-level read-off `∀p.φ = A(· ⇒ φ)` is not
   touched.  The gap is an artefact of nonempty stations, that is, of
   the induction, not of the theorem.

### 4.5 The repair, and what it costs

Replace C3 by (C3-f) of §3.3, retaining the station in the guard, with
the visited-set discipline of §3.4.  Recomputing:

        A(Σ₁ ⇒ ↑r)  =  ↑r  ∨  ( A^{H}(· | Σ₁ ⇒ ↑↓◯p)  ∧  ⊤ )  ∨  ⊥

`A^{H}(· | Σ₁ ⇒ ↑↓◯p)` is A6 to A7 at station `Σ₁` with `H` visited.  The
C3 row for `H` is now forbidden (⊥), the A3 row `A^{H}(Σ₁ ⇒ ↑p)` is ⊥,
and the box row for `G₁` fires, resetting the visited set because the
station changes:

        ↓E(↑↓K | H)  ⊃  A(↑↓K | H ⇒ ◯p)      ≡   r ⊃ A([K, H] ⇒ ◯p)

and `A([K, H] ⇒ ◯p) ≡ ⊤`: its A7 row set contains the C2 attack on `K`,
whose components are `A(D | H ⇒ H) ≡ ⊤` (§4.3) and
`A(◯p | H ⇒ ◯p) ≡ ⊤` (A7's box row on `◯p` at station `[◯p, H]`, whose
guard `E(↑p | H) ≡ r` and whose body `A(↑p | H ⇒ ◯p) ≡ ⊤` because the
atom `p` is now present).  So the box row is `r ⊃ ⊤ ≡ ⊤` and

        **A(Σ₁ ⇒ ↑r)  ≡  ⊤**       under (C3-f)

which satisfies (∀-eq).  The same computation on Γ₂ gives ⊤ as well, via
`A^{H}(· | Σ₂ ⇒ ↑↓◯p)`'s box row on `G₂`, whose body reduces through the
two-layer Dyckhoff attack to ⊤.  And on the E side the repair only
improves matters: with the guard at the full station, `A(· | Σ₁ ⇒ ↑↓◯p)`
becomes ⊤ and `e(H, [G₁])` becomes `⊤ ⊃ r ≡ r`, so `E(Σ₁) ≡ r` directly
rather than through the sibling conjunct.

**The reset is not optional.**  The *genuine* second decide on `H`, step
4 of §4.2, appears in the interpolant as the C3 row on `H` at the deeper
station `[◯p, D, H]`, reached after `G₁` has been opened and `K`
decomposed.  At that station the row's guard is ⊤ (the hypothesis `◯p`
is present, so the box goal is immediate) and the row delivers
`A(◯p | D, H ⇒ ↑r) ≡ ⊤`, which is what carries ⊤ up the chain through
`A(D | H ⇒ H)` to the root.  If `H` were still marked visited from the
root, that row is ⊥, the value falls to `r`, and the root value falls
back below ⊤, losing (∀-eq) again.  I checked the same thing for the
variant that gates only C3 and leaves E5 ungated: it fails too, at the
same node.

So the visited set must be reset when the station changes, and §3.4's
measure then fails at the box row.  **This is the cost of the repair,
and it is unpaid.**  Restated as the sharpest form of the obstruction
this document reaches: *the discipline that makes retention definable
must forget its history exactly when the station changes, and the
station's cheapest change, opening a box, has margin `3^{w R}` and no
more.*

### 4.6 Summary of the checks

| check | instance | statement | verdict |
|---|---|---|---|
| ∃, sequent 1 | `E([H, G₁]) ≡ ◯r ∧ (◯r ⊃ r) ≡ r` | (∃-eq) at ψ = r | **PASSES** |
| ∃, sequent 2 | `E([H, G₂]) ≡ ◯r ∧ (◯r ⊃ r) ≡ r` | (∃-eq) at ψ = r | **PASSES** |
| ∀, sequent 1, drafted C3 | `A([H, G₁] ⇒ ↑r) ≡ ◯r` | (∀-eq) at ψ = ⊤ | **REFUTED as drafted** |
| ∀, sequent 1, drafted C3 | same | (∀-eq-E) at ψ = ⊤ | **PASSES** |
| ∀, sequent 2, drafted C3 | `A([H, G₂] ⇒ ↑r) ≡ ◯r` | (∀-eq) / (∀-eq-E) | **REFUTED / PASSES** |
| ∀, both, repaired C3-f | `≡ ⊤` | (∀-eq) | **PASSES**, at the cost of §3.4 |
| `CimpAnt` at both instances | `r ⊢ ◯r` | the obligation's conclusion | **holds** (validation, not proof) |

No clause was refuted against the statement the construction targets.
One clause, C3, is refuted against the stronger unrelativised statement,
and that refutation is the measurement of the retention gap.

### 4.7 Machine check of §4.3–4.4 (O10, settled 2026-09-04)

The hand values above were checked against the mechanised construction.
`wip/ui_o10_interp.lean` evaluates `LJFO.interp "p" Σ [] none` (the ∃
side) and `LJFO.interp "p" Σ [] (some ↑r)` (the ∀ side) on the polarised
Γ₁ = [G₁, H] and Γ₂ = [G₂, H] of §4.0, erases to `PLLFormula` by
`eraseNeg`, and normalises with the certified simpset
(`Rewrite.simplifyWith Rewrite.fullSetC 200`, interderivability-preserving
by `simplifyWith_interd`).  Run: `lake env lean wip/ui_o10_interp.lean`.

| value | raw `interp` size | normal form (size) |
|---|---|---|
| `E([G₁, H])` | 3406 nodes | `((◯r ⊃ (r ∧ ◯(r ∧ (r ∧ (r ∧ ◯r))))) ∧ ◯(((r ∨ ◯r) ⊃ (r ∧ (r ∧ (r ∧ ◯r)))) ∧ (((r ∨ ◯r) ⊃ (r ∧ ◯r)) ∧ ((r ⊃ (r ∧ ◯r)) ∧ (r ∧ ◯r)))))` (51) |
| `A([G₁, H] ⇒ ↑r)` | 407 | `(r ∨ ◯r)` (4) |
| `E([G₂, H])` | 76049 | 181 nodes; printed by the eval file |
| `A([G₂, H] ⇒ ↑r)` | 4642 | `(r ∨ ◯(r ∧ ◯r))` (7) |

Each normal form was then put to the G4c oracle against the hand value
in both directions (`docs/ui-ljfo-clause-table-o10.tsv`, eight cells,
`lake exe pllbench --engine=g4c --cells=…`, 5 s wall):

| computed ⊣⊢ hand value | fwd | bwd |
|---|---|---|
| `E([G₁, H]) ⊣⊢ r` | valid | valid |
| `A([G₁, H] ⇒ ↑r) ⊣⊢ ◯r` | valid | valid |
| `E([G₂, H]) ⊣⊢ r` | valid | valid |
| `A([G₂, H] ⇒ ↑r) ⊣⊢ ◯r` | valid | valid |

So every displayed value of §4.3, §4.3b and §4.4 is the mechanised
interpolant up to provable equivalence.  Status, stated exactly: the
normalisation is kernel-certified; the eight equivalences are
engine-certified (G4c `.proved`, proof objects behind each verdict), not
kernel-pinned theorems.  Two things the check adds beyond confirmation:
the raw interpolants are large (`E` on the nested station is 76,049
nodes before normalising to 181), which any future `#guard` against
`interp` must budget for; and `A([G₁, H] ⇒ ↑r)` computes to
`r ∨ ◯r ≡ ◯r` on the mechanised object too, so §4.4's measurement of the
retention gap is a fact about `LJFO.interp`, not about the paper
reconstruction.

### 4.8 The fuel-founded chains, measured against known limits (2026-09-04)

`LJFO.interpF` (`LJF/OFuel.lean`, route (B)'s retaining interpolant,
definition only, no theorems) was evaluated on two stations with the
same pipeline as §4.7 (`wip/ui_fuelchain_interpF.lean`,
`wip/ui_gz_fuelchain_interpF.lean`: erase, then the certified simpset,
then the G4c oracle).  Every fuel level is sound by construction — `A`
ascends from `⊥`, `E` descends from `⊤` — so what is measured is
convergence, and the new element is that on the first station the
LIMIT IS KNOWN, so distance-to-target can be measured rather than only
consecutive-level equality (the method of `wip/ljfo_stab.lean`).
Hypotheses were fed through `todo`, and each parking step costs one
unit, so "station fuel" below is the eval's fuel minus 2.

**Station [G₁, H] (the separating sequent; true `∀p = ⊤` since Γ₁ ⊢ r,
true `∃p = r` by §4.7):**

| station fuel | `A` normal form | ⊢ A ? | ◯r ⊢ A ? | `E` normal form | E ⊣⊢ r ? |
|---|---|---|---|---|---|
| 2 | `r` | no | no | `⊤` | no |
| 6 | `r ∨ ◯⊥` | no | no | 13 nodes | no |
| 14 | 1058 nodes (raw 119,015) | **no** | **yes** | 1314 nodes (raw 159,115) | unsettled at the oracle's cap |
| 18 | **`⊤`** (raw 2,290,162) | **yes** | yes | 528 nodes (raw 3,064,714) | **yes** |

So the retaining chain passes `interp`'s value `◯r` (§4.7) at station
fuel 14 and reaches the true `∀p` at 18; `E` reaches the true `∃p` at
18.  On the ①/② double-use station, the plan's statement W holds with
the limit identified.  The cost: raw sizes grow about ×20 per four fuel
units; the simplifier recovers the small answer only after the fact.

**Station [◯p ⊃ r, ◯q], goal ◯p:** the normal forms do not collapse.
*CORRECTED 2026-09-04 22:00.*  This paragraph originally called the
cell "the GZ-candidate cell" with its `∀p` "unknown".  Both are wrong
against the record: `docs/ljfo-plan.md` named it a candidate on the
morning of 2026-08-11 and RESOLVED it that afternoon from both prongs
— its `∀p` is `θmax = ((◯⊥ ⊃ r) ∧ ◯q) ⊃ ◯⊥` (the station's
⊥-instance ⊃ `◯⊥`, maximal because `◯⊥ ⊢ ◯p` re-derives the goal),
and the chain of that day was proved logically stationary from f = 6
(`A₆ ⟛ A₇ ⟛ A₈ ⟛ θmax` on the raw values).  The record's own warning:
"stabilisation testing must be LOGICAL, never syntactic".  What the
table below measures is the syntactic size of the new `interpF`
chain; §4.10 does the logical test by the reduction the record's
mechanism gives.

| station fuel | `E` (nodes) | `A`, goal `◯p` | `A`, goal `↑↓◯p` (the plan's form) |
|---|---|---|---|
| 2 | 3 | `◯⊥` | `◯⊥` |
| 6 | 43 | 44 | 64 |
| 10 | 378 | 379 | 599 |
| 14 | 2653 | 2654 | 4279 |
| 18 | 18,243 (raw 1.5 M) | 18,244 (raw 2.5 M) | 29,504 (raw 2.7 M) |

Growth after the certified simplifier is about ×7 per four fuel units
on every chain, and every element still carries `◯⊥` blocks — the
fuel-exhaustion default under a box, replaced level by level.  This
reproduces the plan's certified strict ascent (station fuels 3→4, 5→6)
and extends the non-collapse to station fuel 18.

**Interderivability on the GZ chains: UNSETTLED at the G4c oracle's
reach.**  Twenty-six cells were put to `pllbench --engine=g4c`:
consecutive-level interderivability at station fuels 6↔10, 10↔14, 14↔18
for all three chains (both directions), and sufficiency
`A_f ∧ (◯p ⊃ r) ∧ ◯q ⊢ ◯p` for both `A` chains at 6, 10, 14, 18 —
formulas of 43 to 29,504 nodes.  The oracle settled NONE of them; the
first cell (`E` at fuel 6 versus fuel 10, 43 and 378 nodes) ran
46 min 14 s without a verdict and was killed.  The 1314-node `E` cell
of the separating station at station fuel 14 was likewise unsettled
after more than ten minutes.  This is the reach limit
`docs/ljfo-review-2026-08-11.md` §5c recorded ("the unfocused prover
cannot practically decide the box-wrapped aggregates at p-carrying
stations"), reproduced on the chain elements themselves.  So the
statement W on the GZ cell — strict ascent or eventual stabilisation up
to interderivability — is OPEN past station fuel 6, where
`wip/ljfo_stab.lean`'s kernel search certified strict steps at 3→4 and
5→6.  Two tools would reach further, and both are prerequisites for the
refutation prong: the kernel-search engine (`LJF/OSearch.lean`) applied
to the chain elements, and a certified simplifier inside the `interpF`
iteration so the elements stay small enough to search.  What the
measurement DOES establish is the contrast with the separating station:
same pipeline, same fuels, one cell collapses to its known limit and
the other grows ×7 per level with `◯⊥` blocks persisting.

**A tooling defect found on the way, with its fix.**  Bounding a run by
`perl -e 'alarm N; exec @ARGV' -- lake exe X …` bounds `lake`, not the
binary `X` it spawns: on SIGALRM `lake` dies and `X` is orphaned and
runs on.  That is what the "19 min 32 s" `pll` run of
`docs/engine-profile.md` §9 was (under a 60 s alarm), and what held an
oracle job open past its cap here.  `batch/run.sh` and
`batch/bench-run.sh` were already right — they exec `.lake/build/bin/…`
directly; ad-hoc checks must do the same.

### 4.9 The certified simplifier inside the iteration (2026-09-04)

§4.8 named an in-iteration simplifier as a prerequisite; this section
builds it and reports what it does and does not change.
`wip/ui_interpFS.lean` is `interpF` with every clause's return wrapped
in `simpN X := negOfO (Rewrite.simplifyWith Rewrite.fullSetC 40 (eraseNeg X))`
(the certified pipeline, so every level is still interderivable with
`interpF`'s), evaluated natively by `lake exe uifs`
(`wip/ui_interpFS_run.lean`); eval fuel 8, 12, 16, 20, 24 = station fuel
6, 10, 14, 18, 22 in §4.8's convention.  Node counts of the normal forms:

| station fuel | `[G₁,H]` E | `[G₁,H]` A, goal r | GZ E | GZ A, goal `↑↓◯p` |
|---|---|---|---|---|
| 6 | 13 | 4 | 25 | 38 |
| 10 | 83 | 53 | 226 | 339 |
| 14 | 620 | 553 | 1475 | 2355 |
| 18 | **45** | **`⊤`** | 9,989 | 16,126 |
| 22 | **45** (same form) | **`⊤`** | 68,298 | 110,467 |

Three findings, in the order they were forced.

**(i) Placement changes nothing; the rule set is the limit.**  With the
simpset as it stood, the in-iteration normal forms were node-for-node
the sizes of §4.8's after-the-fact ones (GZ `A` 64 / 599 / 4279 /
29,504) — wrapping each level buys speed (the whole sweep runs in 9 s
against minutes of raw evaluation) and not one node of size.  The
surviving blocks were `◯⊥ ∨ ◯((q ⊃ ◯⊥) ∨ ◯⊥)`: an inner box under a
box, which `fullSetC` folds only when the two boxes are adjacent.

**(ii) The absorption family, refuted before it was built.**  The
candidate laws were put to the G4c oracle first
(`pllbench --engine=g4c`, eight cells, all settled):

| under an outer `◯` | → | ← |
|---|---|---|
| `◯(a ∨ ◯b)` vs `◯(a ∨ b)` | valid | valid |
| `◯(a ∧ ◯b)` vs `◯(a ∧ b)` | valid | valid |
| `◯(a ⊃ ◯b)` vs `◯(a ⊃ b)` | **invalid** | valid |
| `◯(◯a ⊃ b)` vs `◯(a ⊃ b)` | valid | **invalid** |

So an inner box absorbs through `∧`/`∨` and through neither position of
`⊃`: an implication goal under a box is proved in true mode, where the
inner box cannot be opened.  What went into `Rewrite/Canon.lean`, each
with its `Interd` certificate (`canon_interd`, `simplifyWith_interd`
still pinned at `[propext, Classical.choice, Quot.sound]`): `stripBox`
— under a box, delete every `◯` reachable through `∧`/`∨`
(`box_strip`, one induction; subsumes `◯◯φ = ◯φ`); `◯⊥ ∨ ◯ψ = ◯ψ` and
`◯⊥ ∧ ◯ψ = ◯⊥` through the syntactic absorber test `absorbsBoxBot`
(`boxBot_deriv`, `dropBoxBot_interd`, `collapseBoxBotAnd_interd`);
`simpRounds` 4 → 32, because each round strips one box level and folds
the constants it exposes, so the fixpoint needs about the box-nesting
depth.  And a defect in the pre-existing chain machinery, found because
the output showed `r ∨ (r ∨ (r ∨ …`: `insOr`/`insAnd` compared the new
element with the whole chain and never with its head, so a duplicate
head survived; fixed with `or_head_idem`/`and_head_idem`.

**(iii) What the strengthened simplifier settles and what it does not.**
On the separating station both chains now reach a SYNTACTIC fixpoint at
station fuel 18 and hold it at 22: `A` is `⊤`, `E` is one 45-node form
(provably `r` by §4.7, not syntactically).  On the GZ cell the `◯⊥`
blocks are gone and the sizes fall by about a third, but the growth
rate does not move: ×6.8 per four fuel units through station fuel 22.
The residue is an `∧`/`∨` ladder of boxed implications,
`((◯A ∧ ◯B) ∨ ◯((A ∧ B) ∨ C)) ∧ ◯D) ∨ …`, built by the aggregate
clauses level by level.  The laws that would act on it are not modal
absorption but `◯A ∧ ◯B = ◯(A ∧ B)` (the strength; a three-line
certificate) and monotone absorption `◯X ∨ ◯Y = ◯Y` when `X` is a
sub-conjunction of `Y` (a syntactic entailment test); whether they
collapse the ladder or only thin it is untested, and no oracle can
answer for the raw elements: the FRJW control on the fuel-6/10 `E`
cells was unsettled at 600 s, and `LSeq.search` at search fuel 16, 24
and 32 returned `false` in both directions, which certifies nothing.
*Addendum 22:00: §4.10 shows the logical question at this cell never
needed those oracles — the record's ⊥-instance mechanism reduces it to
two small facts.*

### 4.10 The cofinality refutation attempt on `{◯p ⊃ r, ◯q} ⇒ ◯p` — VALIDATED, not refuted (2026-09-04)

The two route-(B) cofinality statements (`wip/ui_routeB_statements.lean`),
instantiated at the cell with `done` the parked station and `Γ` its
formulas:

    ACofinalF:  ∀ p-free Δ,  Δ, Γ ⊢ ◯p  →  ∃ f.  E_f, Δ ⊢ A_f
    ECofinalF:  ∀ p-free Δ ψ,  Δ, Γ ⊢ ψ  →  ∃ f.  E_f, Δ ⊢ ψ

**The reduction (the record's mechanism, `docs/ljfo-plan.md` "closed
from the proof side").**  Substituting `p := ⊥` in a derivation of
`Δ, Γ ⊢ ◯p` gives `Δ, Γ[⊥] ⊢ ◯⊥`, i.e. `Δ ⊢ θmax` with
`θmax = ((◯⊥ ⊃ r) ∧ ◯q) ⊃ ◯⊥`; and `Δ, Γ ⊢ ψ` gives `Δ, Γ[⊥] ⊢ ψ`.  So
both statements hold at fuel `f` as soon as

    (b)  E_f ⊢ (◯⊥ ⊃ r) ∧ ◯q          (E_f is at least the ⊥-instance)
    (d)  ◯⊥ ⊢ A_f                     (A_f is ◯⊥-absorbing)

since `(◯⊥ ⊃ r) ∧ ◯q ∧ θmax ⊢ ◯⊥`.  (b) and (d) are properties of the
chain elements alone, so they can be tested at every fuel.

**Syntactic prong (`lake exe uifs`, sufficient tests, every station
fuel 6–22):** `E_f` has `◯q` as a conjunct and a conjunct `X ⊃ Y` with
`X` ◯⊥-absorbing and `r` a conjunct of `Y` — true at 6, 10, 14, 18,
22; `A_f` is ◯⊥-absorbing (`Rewrite.absorbsBoxBot`, whose certificate
`boxBot_deriv` is a `LaxND` derivation of `◯⊥ ⊢ A_f`) — true at every
fuel for BOTH goal forms, `◯p` and `↑↓◯p`.

**Oracle prong (`pllbench --engine=g4c`, seven cells, 7 s in all):**

| cell | verdict |
|---|---|
| `(◯⊥ ⊃ r) ∧ ◯q ∧ θmax ⊢ ◯⊥` | valid |
| `θmax ∧ Γ ⊢ ◯p` (θmax sufficient) | valid |
| `Γ ⊢ ◯p` (control: the cell is not trivial) | **invalid** |
| (b) at station fuel 6 (`E` 25 nodes) and 10 (226 nodes) | valid, valid |
| (d) at station fuel 6 (`A` 38 nodes) and 10 (339 nodes) | valid, valid |

**Verdict.**  Neither cofinality statement can be refuted at this cell:
for every p-free `Δ` the derivation goes `E_f, Δ ⊢ ◯⊥ ⊢ A_f` at every
measured fuel.  Read with soundness (§O8: `A_f, Γ ⊢ ◯p`, hence
`A_f ⊢ θmax` by the same substitution), the new `interpF` chain is
LOGICALLY STATIONARY modulo `E_f` from station fuel 6 — `E_f ∧ A_f ⟛
E_f ∧ θmax` — while its syntax grows ×6.8 per four fuel units.  This is
the record's 2026-08-11 finding reproduced on the retaining chain, and
its filter confirmed: a cell whose goal is settled by `◯⊥` cannot be a
Ghilardi–Zawadowski witness.  What is NOT certified here: substitution
admissibility (`Deriv Γ C → Deriv Γ[p:=χ] C[p:=χ]`, the plan's named
adjunct, still without a term), and the per-fuel `absorbsBoxBot A_f =
true` as kernel `decide`s rather than native evaluation.

**The next stratum**, per the record's double filter (crank with no
X-free disjunct; goal not settled by `◯⊥`): the goal must be unboxed
and `p` must occur with both polarities on the hypothesis side, so
that neither the `⊥`- nor the `⊤`-instance is extremal.  The smallest
such shape is `{◯p ⊃ r, s ⊃ ◯p} ⇒ r`, and it was screened the same
night (`pllbench --engine=g4c`, every cell settled in seconds unless
marked):

| claim | verdict |
|---|---|
| `ψ₀ = ((◯⊥ ⊃ r) ∧ (s ⊃ ◯⊥)) ⊃ r` sufficient (the ⊥-instance closes the cell) | **invalid** |
| `s ∨ r` sufficient | valid |
| `ψ₀ ⊢ s ∨ r` | invalid |
| `Γ ⊢ ◯s ⊃ r` | valid |
| `T := (◯s ⊃ r) ⊃ r` sufficient (the s-instance closes the cell) | **valid** |
| `T ⊢ r ∨ ◯s` | invalid |
| `A₆ ⊢ T`, `A₁₀ ⊢ T` (soundness + substitution `p := s`) | valid, valid |
| `A₁₀ ⟛ r ∨ ◯s` (both directions) | valid |
| cofinality instance `E₆ ∧ T ⊢ A₆` | **invalid** |
| cofinality instance `E₁₀ ∧ T ⊢ A₁₀` | **valid** |

So the ⊥-instance does not close this cell (the first cell of the
campaign where that mechanism fails), but the `s`-instance does:
`Γ ⊢ Γ[s] = {◯s ⊃ r, s ⊃ ◯s}` and `Γ[s] ⊃ r ⟛ T` is sufficient, so
`T` is the cell's `∀p` by the same substitution argument.  The chain
climbs to `r ∨ ◯s` at station fuel 10, strictly below `T` as formulas;
but `E₁₀ ⟛ ◯s ⊃ r`, under which `T`, `r ∨ ◯s` and `r` coincide, so the
cofinality instance holds at fuel 10, and with it cofinality for every
sufficient `Δ` (each has `Δ ⊢ T`).  VALIDATED again.  The instance
`E₁₄ ∧ T ⊢ A₁₄` (201 + 187 nodes) was UNSETTLED at the 300 s bound —
a frontier marker (re-run at a raised budget, or decompose as the
record did for θmax: the `∧`/`∨` structure splits it into
engine-sized leaves), not a failure.  Likewise `A₁₀ ⊢ θmax` on the
first cell (339-node hypothesis) was unsettled at 300 s; its fuel-6
twin is valid and the substitution argument covers every fuel.

**The filter, sharpened by these two cells.**  A cell is closed by the
instance `p := χ` (χ p-free) whenever `Γ[χ] ⊃ G[χ]` is sufficient —
then it is the `∀p` outright, and cofinality reduces to `E_f ⊢ Γ[χ]`
plus the chain reaching `G[χ]` modulo `E_f`.  Both cells so far are
instance-closed (`χ = ⊥`, `χ = s`).  A candidate that can refute
cofinality — or be a Ghilardi–Zawadowski witness — must have NO
sufficient instance, which is the situation in which a uniform
interpolant, if it exists, is not a substitution instance (in IPC:
`∀p.((p ⊃ q) ∨ (q ⊃ p)) = q ∨ ¬q`).  The plan's substitution-
admissibility lemma makes this instance screen a certificate; until
then it is an oracle screen, run before any chain is measured.

**The instance screen is now a certificate (2026-09-05,
`LaxLogic/PLLInstanceBound.lean`, admitted to the `LaxLogic` root and
`Production`).**  With `substND` (the substitution admissibility of
`PLLSemUICtx.lean`) and `substP_of_not_mem`:

    instanceBound  :  p ∉ atoms Δ  →  LaxND [Δ, Γ] G  →  LaxND [Δ] (Γ[χ] ⊃ G[χ])
    instanceClosed :  p ∉ atoms χ  →  LaxND [Γ[χ] ⊃ G[χ], Γ] G
                      →  IsWeakestSufficient p Γ G (Γ[χ] ⊃ G[χ])

where `IsWeakestSufficient p Γ G ψ` packages `p ∉ atoms ψ`, `ψ, Γ ⊢ G`,
and `∀ Δ p-free, (Δ, Γ ⊢ G) → (Δ ⊢ ψ)` — the cell's `∀p`, Pitts's sense.
The two cells above are certified: `cell1_forall_p` (θmax, literally the
`⊥`-instance bound, sufficiency by a hand `LaxND` derivation:
`◯⊥ ⊃ r` from `◯p ⊃ r` since a box of `⊥` yields a box of anything;
`◯q` from `Γ`; hence `◯⊥`, hence `◯p`) and `cell2_forall_p`
(`Ts = ((◯s ⊃ r) ∧ (s ⊃ ◯s)) ⊃ r`, the literal `s`-instance bound, equal
to the record's `T` up to the provable conjunct `s ⊃ ◯s`; sufficiency:
open `◯s` under the lax goal `◯p`, fire `s ⊃ ◯p`, then `◯p ⊃ r`).
Pins, measured: `instanceBound`, `instanceClosed`, both cells
`[propext, Quot.sound]`; the two sufficiency derivations `θmax_suff`,
`Ts_suff` are closed terms with **no axioms**.  The gate was watched
failing on two controls (a bound omitting `propext`; a sorried twin).
The IPC contrast stands as the filter's justification: a candidate with
a sufficient p-free instance is settled by `instanceClosed` before any
chain is measured; only a candidate with none can refute cofinality or
be a Ghilardi–Zawadowski witness.

### 4.11 The cofinality proof build — STOPPED at the founding of the recursion (2026-09-04, late)

Matthew's direction: stop refuting, prove cofinality in general; if
the proof does not go through, the stopping point defines the next
candidates.  An Opus agent templated the weight-founded minimality
family (`TInv`/`UEntry` and auxiliaries, `LJF/O.lean`, conditional on
`CimpAnt`) onto `interpF`.  Result, all in `LJF/OFuelMin.lean`
(755 lines, no `sorry`, merged as `10ffa22`):

* **PROVED**: the ten aggregate equations and nine row memberships at
  fuel `f+1` (`[propext]`); the processing phase `eMinFF`/`aMinFF` —
  cofinality at a saturated station implies cofinality at every
  station (`[propext, Classical.choice, Quot.sound]`); the reductions
  `ecofinalF_of_satE2F`, `acofinalF_of_satA2F` from the saturated
  forms `SatE2F`/`SatA2F` to the approved statements.
* **The obligation, and what it is**: `CimpAntF` (the retention form of
  `CimpAnt`, `rest` replaced by `done`) and
  `cimpAntF_of_satA2F : SatA2F p → CimpAntF p` — every one of the four
  `cAnt` sites type-checks as the predicted native call of `∀p`-
  cofinality at the FULL station on the antecedent's subderivation.
  So the obligation is an instance of the statement being proved; a
  conditional port would be near-vacuous.
* **STOPPED**: `TInvF`/`UEntryF` themselves, hence `ecofinalF`/
  `acofinalF`.  The reason is the founding.  The weight-founded family
  is ordered lexicographically by (station-and-goal weight, derivation
  size).  Taking the retention discharge as a recursive call adds the
  edge `E@done → A@done(↑↓◯Q′)`, which raises the goal weight; but the
  family already has the opposite cross-edge `A@done(c) → E@done` (the
  `↑c` conjunct of the `c ⊃ N` attack row, `LJF/O.lean:1580`).  Round
  the cycle

      A@done(↑c) → A@done c → E@done → A@done(↑↓◯c) → A@done(↓◯c)
        → A@done(◯c) → A@done(↑c)

  every edge is a strict subderivation, so a station-first measure must
  be constant round it, hence goal-blind at `done`; a goal-blind
  measure cannot pay for goal inversion `A@done(Q ⊃ N) → A@(b ++ done)(N)`
  (derivation rebuilt by `extract`, station grown), and iterating that
  edge from the retention goal `↑↓◯(↓(↑d ⊃ ↑c))` gives stations
  `done, ↑d :: done, ↑d :: ↑d :: done, …` each carrying the cycle.  The
  agent checked the arithmetic escapes (inflating the `∃p` side by
  `max` over the ◯-goals, by `σ`, by `Σ 3^goal`; three-component
  orders; scaling): all fail on `μ_A(done, small goal) ≥ μ_E(done) ≥
  μ_A(done, large ◯-goal)`.
* **The cell** (`wip/ui_retention_cell.lean`, kernel-checked at every
  fuel): station `[↓◯c ⊃ ↑a, c ⊃ ↑a]` with `p ≠ c, a`; its `∃p` row
  of the ◯-implication carries the retained guard at `done`, its `∀p`
  attack row at goal `↑c` carries `↑c` — the two cross-edges, in the
  aggregates themselves.

**What survives, and the question it opens.**  The opposite order —
derivation height first, station weight second — drops on every cycle
edge; the station-changing edges use rebuilt derivations, so it needs
height bounds for `wk`, `simInv`/`simHyp`/`simStab`, `routeStabT`,
`extract`, `invBranches`, `relStab`, `negOfDownStab`, `dykCommute`.
The last two raise the height by the size of the formula they rewrite,
and that is not bookkeeping only: on a path that alternates a
retention edge (height down by one) with a Dyckhoff fire (height up by
`|φ|`), derivation-founded recursion is not obviously well-founded
either.  Whether the fuel a derivation needs is finite is then a
mathematical question, and it defines the refined candidate family:

    a saturated station holding a ◯-implication `↓◯Q′ ⊃ N` whose
    antecedent `Q′` contains a Dyckhoff implication, together with an
    atom-implication `c ⊃ N′`, with `p` occurring in both polarities
    (no instance `Γ[χ] ⊃ G[χ]` sufficient) and an unboxed goal.

Screen it as §4.10 did — instance screen first, then the chain probe
and the cofinality instances at station fuels 6/10/14 — before any
height-founded refactor is scoped.  OPEN, both ways: no refutation, no
proof; the obstruction is exact.

### 4.12 The candidate family screened (2026-09-04/05, Matthew's (i))

**The grid** (`wip/ui_screen/gen.py`, seven stations, not a
sweep): the base cell `S1 = [◯(d ⊃ p) ⊃ a, c ⊃ ◯p] ⇒ a` — the box on
`◯p` is what stops the composite `c ⊃ … ⊃ a` from being derivable,
which had closed every earlier cell — with its unboxed twin `S2`
(control), the box moved to the atom-implication's antecedent `S3`, the
disjunctive goal `S5 = [◯(d ⊃ c) ⊃ p, c ⊃ p] ⇒ (p ⊃ q) ∨ (q ⊃ p)`, a
Dyckhoff hypothesis added `S6 = S1 + (d ⊃ c) ⊃ e`, the goal `a ∨ c`
`S7`, and `p` only positive `S8` (control).  Instance screen: fourteen
`χ` (`⊥`, `⊤`, the atoms, their boxes, `¬d`, `◯¬d`, `¬c`, `¬q`), one
G4c process per cell under a 60 s alarm, 105 cells in one minute.

| station | `Γ ⊢ G` | closing instance | survivors |
|---|---|---|---|
| S1 | invalid | none of 14 | **survives** |
| S2 | invalid | `χ = c` (as designed) | — |
| S3 | invalid | `χ = ◯c` | — |
| S5 | invalid | none of 10; four "don't-know" (engine budget) | survives, unsettled |
| S6 | invalid | none of 14 | **survives** |
| S7 | invalid | none of 14 | **survives** |
| S8 | invalid | `χ = ⊤` (as designed) | — |

At S1 the conjunction of eight instance bounds is not sufficient
either.  So S1 is the first cell of the campaign whose `∀p` is neither
an instance nor a finite conjunction of instances.

**S1's interpolants, by hand and oracle.**  Sufficient p-free formulas:
`a`, `c` (through `c → ◯p → ◯(d ⊃ p)`, monotonicity), `◯c`, `◯⊥`,
`◯¬d`, `X := ◯(c ∨ ¬d)`; not sufficient: `◯(d ⊃ c)`, `◯(d ⊃ ◯⊥)`.
For a p-free goal the `∀p` is `(∃p.Γ) ⊃ a` (a sufficient `Δ` has
`Δ, E ⊢ a` by E-minimality, and conversely), and the weakest sufficient
formula in hand is

    T := (X ⊃ a) ⊃ a,    X = ◯(c ∨ ¬d),

with `Γ ⊢ X ⊃ a` valid, `T` sufficient, and `T` strictly weaker than
`a ∨ X` (both oracle-settled).  Whether `T` is the `∀p` is whether
`∃p.Γ ⟛ X ⊃ a`.

**The chains** (`lake exe uifs cand`, station fuels 6/10/14/18): S1
`E` 20 / 290 / 2987 / 37,632, `A` 16 / 274 / 2973 / 37,618, growth ×12
per four units; S6 `E` up to 176,412, S3 up to 861,870.  `A₆ ⟛ a ∨ ◯⊥`
up to absorption.  The retained guard's own chain (`S1g`, goal
`↑↓◯(d ⊃ p)`): `(c ∧ ◯⊥) ∨ ◯¬d` at 6, then 454 / 5687 / 70,575.

**Cofinality instances at S1 (G4c, 300 s each):**

| instance | fuel 6 | fuel 10 | fuel 14 |
|---|---|---|---|
| `E_f ∧ c ⊢ a` (E-side, Δ = c) | invalid | invalid | unsettled |
| `E_f ∧ X ⊢ a` (E-side, Δ = X) | invalid | invalid | unsettled |
| `E_f ∧ T ⊢ A_f` | invalid | invalid | unsettled |
| `E_f ∧ (a ∨ X) ⊢ A_f` | invalid | invalid | unsettled |
| `E_f ∧ c ⊢ A_f` | invalid | invalid | unsettled |
| `A_f ⊢ T` (fails only if `T` is not the `∀p`) | valid | unsettled | unsettled |
| `A_f ⊢ a ∨ X` | valid | invalid | invalid |

S6 and S7 show the same pattern (all invalid at 6 and 10, unsettled at
14; at S6 `A₁₀ ⊬ T`, so `T` is not S6's `∀p`, as expected with the
extra hypothesis).

**What the forms say.**  `E₁₀` at S1 is
`(G ⊃ ((c ⊃ a ∧ ◯a) ∧ a)) ∧ (c ⊃ ((G′ ⊃ a ∧ ◯a) ∧ ◯(◯⊥ ⊃ a)))` with
`G`, `G′` the retained guards, and every disjunct of `G′` pairs `c`
with a BOXED residue — the guard is the `∀p` of a ◯-goal, computed as
`◯(…)` by the ◯-goal rows, and its inner box row `↓E([↑p] rest) ⊃ A(…)`
collapses to `⊤` only once the sub-station's `E` has itself reached
`a`: one nesting level per parked box, about ten fuel units.  So the
four-step consequence `c ⊃ a` is expected to appear in `E_f` at station
fuel 12–14, exactly where the G4c oracle's reach ends.  The escalation
is the focused kernel search (`LJFO.search`, sound by `search_sound`)
on `E_f, ↑c ⊢ ↑a` — `lake exe uifs esearch <evalfuel> <sfuel>` — whose
result is recorded below.

**The focused search settles it — E-cofinality at S1 VALIDATED at
station fuel 14.**  `LJFO.LSeq.search` on `E_f, ↑c ⊢ ↑a` (native
evaluation of a search that is sound by `search_sound`; a `true` is a
derivation):

| station fuel | search fuel 16 | 24 | 32 |
|---|---|---|---|
| 10 (`E` 290 nodes) | false | false | false |
| 14 (`E` 2987 nodes) | **true** | true | true |
| 18 (`E` 37,632 nodes) | **true** | true | true |

So the consequence `c ⊃ a` (derivation height about 4) enters the
E-chain at station fuel 14, where the row analysis put it, and stays.
The fuel is about 3.5 times the derivation height — the shape the
proof's fuel function must have (a nesting level per parked box, not a
step per rule).  This is evidence FOR cofinality on the first cell that
no instance closes, and against the §4.11 family as a refutation
candidate; the kernel pin of the fuel-14 derivation (a `decide` on a
2987-node context) is not attempted here.

**The other instances by the same engine** (`wip/ui_screen/esearch-run.sh`,
search fuels 16 and 32 agree in every cell; `false` certifies nothing):

| instance | station fuel 10 | 14 | 18 |
|---|---|---|---|
| `E_f ∧ c ⊢ a` (E-side, Δ = c) | false | **true** | true |
| `E_f ∧ c ⊢ A_f` (A-side, Δ = c) | false | **true** | true |
| `E_f ∧ X ⊢ a` (E-side, Δ = X = ◯(c ∨ ¬d)) | false | false | false |
| `E_f ∧ T ⊢ A_f` (A-side, Δ = T) | false | false | false |

So cofinality holds for the sufficient formula `c` on both sides from
station fuel 14, and for the weaker `X` and `T` at no fuel through 18
(37,632-node `E`).  The row analysis says why, with a number: `X ⊢
guard` must go through the boxed disjunct `A(done ⇒ ◯↓(d ⊃ p))`, whose
`c`-branch sits one parked-box level deeper than the outer `c`-branch
that Δ = c uses, so the `X` instances are predicted about ten fuel
units later, station fuel 22–24.  What the `X`/`T` instances test is
the E-chain's convergence to `∃p.Γ` itself (the `∀p` is `(∃p.Γ) ⊃ a`,
and `T = (X ⊃ a) ⊃ a` is the `∀p` iff `∃p.Γ ⟛ X ⊃ a`).

**Station fuel 22 confirms the prediction: `E₂₂ ∧ X ⊢ a` is TRUE**
(search fuel 48; false at 16 and 32).  The depth needed exposes a
posing defect in the searches above: `E_f` entered the context as one
`∧`-chain, and the canonical chain is right-nested and sorted, so left
focusing on the k-th conjunct costs k steps — the Δ = c derivations
were found because their conjunct sorts near the front, and every
`false` above at search fuel ≤ 32 is a depth artefact, not evidence.
The searches are re-posed with the conjuncts of `E_f` as separate
hypotheses (∧-left inversion, equivalent; `uifs esearch` now does
this); their verdicts follow.  What stands regardless: the weaker
consequence `◯(c ∨ ¬d) ⊃ a` enters the E-chain by station fuel 22,
inside the predicted window, about three times its derivation height.

**The other survivors** (`wip/ui_screen/esearch-stations.sh`, Δ = c,
search fuel 16): at S6 — the cell WITH the Dyckhoff hypothesis, the
closest match to the §4.11 family — and at S7, both cofinality
instances are TRUE at station fuels 14 and 18, E-side and A-side.  The
Dyckhoff hypothesis does not delay the chain.

**Re-posed verdicts and the frontier (2026-09-05, 01:34).**  With the
conjuncts of `E_f` as separate hypotheses: Δ = c reproduces (false at
10, true at 14); Δ = X is false at 10/14/18 through depth 32 and TRUE
at 22 at depth 48 (reproducing the chain-posed verdict — the derivation
is 33–48 steps deep, a box opened, a case split, the inner rows); so
`◯(c ∨ ¬d) ⊃ a` enters the E-chain at station fuel 22 exactly, the
predicted window.  The A-side instance for the conjectured `∀p`,
`E_f ∧ T ⊢ A_f`, is false through depth 32 at every fuel and UNSETTLED
at depth 48 (fuels 18, 22) and 64 (fuel 22), 30 min each: the goal is
`A_f` itself (37,632 and about 450,000 nodes), which the search has to
construct.  A frontier marker, not a failure — the next tool is a
certified simplifier for the A-side or a kernel-side decision on the
sub-goal `E_f ⊢ ∃p.Γ`.

**Verdict of the screen.**  No cell of the §4.11 family refutes
cofinality.  Every instance the tools could decide was VALIDATED, at
the fuel the row analysis predicted: Δ = c on both sides from station
fuel 14 at S1, S6, S7; Δ = X on the E-side at station fuel 22 at S1.
The chain is slow — a consequence enters about three times its
derivation height later, one parked-box nesting level per ~10 fuel
units — and that number is the constraint on the proof's fuel
function, not a counterexample.  Runners: `wip/ui_screen/`.

### 4.13 The height-first founding — STOPPED, and the obstruction is now exact on both sides (2026-09-05, 09:03)

Matthew's direction: no more testing, refound the family on derivation
height first.  An Opus agent did Step 0 — height bounds for every
derivation transformer the family uses — and the table decides the
route.  `LJF/OFuelHeight.lean` (873 lines, every bound pinned at
`[propext, Classical.choice, Quot.sound]`, merged as `45dce44`):

| transformer | height |
|---|---|
| `wk` (all four judgments) | **equal** |
| forced-shape extractors | strictly smaller |
| `extract` | ≤ |
| `invBranches` | ≤ max + `sizePos R` |
| `routeStab`/`routeStabT`, `relStab`, `simStab`/`simLFoc`/`simInv`, `simRFocus`, `simHyp` | ≤ (with the stated budgets) |
| `invAndHyp`, `invImpFls`, `invUp`, `invFireHyp`, `fireClean`, `boxClean` | ≤ |
| `negOfDownStab` at `↑P` / `◯P` | ≤ `szS s + 1` / `+ 2` |
| `stabOr1`/`stabOr2` | **rises** (per right-focus leaf; 11 → 13) |
| **`invImpOr`, `invStrip`, `invCurry`** | **rise** (21 → 26, 25 → 26, 29 → 40), kernel-checked cells `ceOrD`, `ceStD`, `ceCyD` |
| `negOfDownStab` at `M₁ ∧ M₂`, `dykCommute` | rise **unboundedly** (`szI = 10n + 25` on a measured family; proved as an equation) |
| the max-based height | fails on the same three clauses (`dpD`: 13 → 18) |

**Verdict.**  The order (derivation height, station weight) does not
found the family, and not because of the Dyckhoff transformers: those
rise unboundedly but LEAVE the family — Part 9 proves drop-in
replacements for their two release sites (`laxReleaseUp`,
`laxReleaseCirc`, height ≤ `szS (laxOf s)`, landing on the same `∀p`
row), and the `interpR` retention removes the third.  The binding
obstruction is in the PROCESSING phase: the three clauses that RESHAPE a
parked implication's antecedent — `(Q₁∨Q₂) ⊃ N` into two implications,
`↓↑P′ ⊃ N` into `P′ ⊃ N`, `↓(M₁∧M₂) ⊃ N` curried — rebuild every use of
the implication as a nest of constructors at the depth of the
antecedent proof's focus leaves, so their derivation transformers raise
the height while the station weight drops, and height is the first
component.  The `interpR` fallback of the brief does not touch the
processing phase, so it dies on the same three cells; the agent
rightly did not build it.  Both natural derivation measures are
refuted; the weight order of `LJF/O.lean` remains the only one that
runs the processing phase, and §4.11's cycle remains the reason it
cannot take the retention discharge.  The obstruction is exact on
both sides.

**What the table forces (Part 9).**  Every other processing clause
either PARKS (weakening only, height exact) or is one of the six
non-increasing transformers.  A height-founded family must therefore
park those three shapes too — extend `ParkedN` by `(Q₁∨Q₂) ⊃ N`,
`↓↑P′ ⊃ N`, `↓(M₁∧M₂) ⊃ N`, each with an aggregate row whose fire is
guarded by the retained `∀p` of its antecedent at the full station,
exactly as the ◯-implication rows already are — instead of reshaping
them.  Read as a principle: *no rewriting of hypotheses; every
non-atomic implication fires through a retained guard.*  That is a
definition change to `interpF` of a different order from `interpR`
(new parked shapes, new rows in both aggregates, new soundness cases
by weakening, new minimality clauses as native calls), and it is a
decision on what the interpolant IS — Matthew's.  Blueprint node N0e
(`docs/ui-routeB-blueprint.md`).

### 4.14 `interpP` built: soundness PROVED, the founding PROVED, the family is re-authoring (2026-09-05, 09:52)

Matthew's decision (09:10): go ahead with the parking definition;
soundness must be preserved.  One Opus run, merged as `e0f7ee2`
(`LJF/OFuelP.lean` 601, `OFuelPSound.lean` 1894, `OFuelPMin.lean` 642,
`OFuelPCof.lean` 369, `OFuelHeight.lean` +309 lines; `lake build LJF
wipshared Production` exit 0; no `sorry` anywhere):

* **The definition.**  `interpP` = `interpF` with exactly these changes:
  the three reshaping clauses park their shape instead (`(Q₁∨Q₂) ⊃ N`,
  `↓↑P′ ⊃ N`, `↓(M₁∧M₂) ⊃ N` → `done`); each parked shape has an ∃p row
  and an attack row in all eleven ∀p blocks, of the ◯-implication row's
  form with the antecedent as the guard goal; the Dyckhoff rows carry
  their guard at the full station.  Everything else byte-identical
  (mechanical diff).  Principle: no rewriting of hypotheses — every
  non-atomic implication parks and fires through the retained `∀p` of
  its antecedent at the full station.
* **Soundness PROVED, first**: `eSoundP`/`aSoundP` at
  `[propext, Quot.sound]` (the `interpF` pair's set), pinned at both
  bounds, gate watched failing (`[propext]` → error naming
  `Quot.sound`).  The three new parking clauses are plain weakenings
  (the simulation blocks of the reshaped hypotheses vanish); the new
  rows go through as the twelve modal rows did (`atkPark`, the
  antecedent-generic form of `atkCimp`, equal to it at `↓◯Q′` by `rfl`).
* **Sanity, kernel-level**: `interpP = interpF` on the S1 station of
  §4.12 (no changed shape) at every fuel 0–8 in ∃p mode and at a shifted
  ∀p goal, 0–7 at a ◯-goal, by `decide` (`[propext]`); negative
  controls — one station per changed clause — where the two DIFFER at
  fuels 2–5, also kernel-checked, so the agreement is not vacuous.
* **Rows, processing phase, reductions PROVED** (`OFuelPMin.lean`):
  nine aggregate equations, twelve row memberships, `SatE2P`/`SatA2P`,
  `eMinPP`/`aMinPP` unconditional on the station weight (`dec_park`
  where the reshaping clauses used `dec_impor`/`dec_stripshift`/
  `dec_curry`), `ECofinalP`/`ACofinalP` and their reductions in
  `wip/ui_routeB_statements.lean`.
* **The founding PROVED** (`OFuelHeight.lean` Part 10): one
  phase-neutral height `hgt` (`hgtI d = szI d`, `hgtS s = szS s + 1`,
  `hgtL = szL + 2`, `hgtR = szR + 2`, so that phase changes are `rfl`),
  and the measure `μ = (hgt, station weight with the `LJF/O.lean`
  offsets, sizeOf)`.  Every edge class: structural descent `<`;
  antecedent dispatch for ALL FIVE parked shapes `<` (`hgt_antDispatch`);
  fire continuation `<`; box row `=` with the station dropping; the two
  release sites via `laxReleaseUp`/`laxReleaseCirc` `<`; goal inversion
  `<` (`hgt_goalInv`); parking of all eight shapes exact with the
  station dropping; `↑(P∨Q)`, `↑↓M`, `M∧N`, `⊥⊃N`, the fire scan `≤` with
  the station dropping.  `invImpOr`/`invStrip`/`invCurry` do not occur;
  `negOfDownStab`/`dykCommute` are never called.  Gate watched failing
  (`hgt_boxRow` cannot be strengthened to `<`: opening a box is
  height-neutral).
* **Beneath the family, PROVED**: `parkAntP_of_satA2P` — the antecedent
  dispatch is an instance of ∀p-cofinality at the same station, ONE
  statement for all five shapes; `parkFireE` and its five instances —
  the retention row's use in the two-fuel form (aggregate at `f+1`,
  guard and continuation at `f`, thresholds by `max`), which `CimpAntF`
  could only state; the chain `TInvP → SatE2P → ECofinalP`,
  `UEntryP → SatA2P → ACofinalP`.
* **Open, and now purely re-authoring**: the family itself — the
  18-definition mutual of `LJF/O.lean` (lines 927–2062) in fuel-carrying
  form, returning `UpFrom`/`UpFrom2` witnesses, thresholds combined by
  `max`, `UStab`'s row-list block fuel-indexed, about seventy
  `decreasing_by` sites fed from Part 10.  Typed obligations `TInvP`,
  `UEntryP` (verbatim in `OFuelPCof.lean`); the agent judged it beyond
  one run and did not leave it broken.  Exercising cell: S1 with
  `K = [↑c]`, goal `↑e`, a focus on the ◯-implication forcing the
  dispatch edge.  Next run: this re-authoring, group by group.

### 4.15 The family BUILT on `interpP`, conditional on two antecedent dispatches; the Dyckhoff row's guard has the wrong polarity (2026-09-05, 12:20)

**What landed** (`LJF/OFuelPFam.lean`, 2048 lines, one agent run of
2 h 24 min; merged at 40446bc with the instance-bound commit; `lake build
LJF wipshared Production` clean, 8949 jobs).  `LJF/O.lean`'s minimality
family re-authored in fuel-carrying form over `interpP`: 17 definitions
(O.lean's `dykAntC` is replaced by an obligation, see below) in TWO
`mutual` blocks — the `∃p` side (`eMinQ`, `TInvQ`, `TStabQ`, `TRFQ`,
`TLFQ`, `TpElimQ`, `TpLFQ`, `TpInvQ`) and the `∀p` side (`aMinQ`,
`UEntryQ`, `UStabQ`, `URFQ`, `ULFQ`, `UInvGQ`, `UpElimQ`, `UpLFQ`,
`UpInvGQ`) — each founded on `LJF/O.lean`'s lexicographic PAIR (station
weight, `sizeOf`), NOT the height-first triple.  The split is possible
because with the antecedent guards as parameters the `∃p` side calls
nothing on the `∀p` side, so `LJF/O.lean`'s strongly connected component
breaks in two; every one of the ~70 `decreasing_by` sites is discharged
by `ljf_dec_e`/`ljf_dec_a` or five new alternatives (`dec_parkT`,
`dec_parkS`, `dec_restT`, `dec_parkG`, `dec_parkG2`), so **no Part 11
was needed** and `OFuelHeight.lean` is unchanged.  Entry points
`tinvP_of`, `uentryP_of`, `satE2P_of`, `satA2P_of`; the chain in
`wip/ui_routeB_statements.lean`:

    tinvP, uentryP, satE2P, satA2P, ecofinalP, acofinalP
      :  ParkAntP p → DykAntP p → ⟨the statement⟩

No `sorry`, `admit`, `native_decide` or `partial` anywhere (swept).
Pins, measured: the family and the chain `[propext, Classical.choice,
Quot.sound]` (the choice from well-founded recursion, as in `LJF/O.lean`);
the kit (`qAssembleP`, `boxAssembleP`, `parkFireA`, `qFireA`,
`boxFireA`, `dec_parkT/S`, `dec_restT`) `[propext, Quot.sound]`;
`dykCell_saturated`, `dykCell_parked` `[propext]`.  Three gates watched
failing, one of them instructive: `Saturated dykCell` by `decide` left
a `sorryAx` silently (no `DecidableEq` at the option type) and was
caught only by the pin; `rfl` proves it.

**Status: CONDITIONAL**, in the `CimpAnt` idiom — two typed obligations
passed as parameters, never assumed.  `ECofinalP`/`ACofinalP` are NOT
claimed.

**(a) `ParkAntP p`** (`OFuelPCof.lean`, pre-existing) — the antecedent
guard of the parked implications whose antecedent is a positive `Q`:

    ParkAntP p := ∀ done K Γ′ Q N,  Saturated done → ParkedCtxP done →
      (Q ⊃ N) ∈ done → Γ′ ⊆ done ∪ K → done ⊆ Γ′ → K p-free →
      Stab Γ′ tru Q →
      UpFrom2 (e f ↦ E_e :: K ⊢ A_f(done ⇒ ↑Q))

A fixpoint requirement, not a gap: `parkAntP_of` (new) derives it from
the family itself (`satA2P_of_uentryP` + `parkAntP_of_satA2P`), and
Part 8 settles the two facts a native discharge needs — `nativeParkAnt`:
at the dispatch site the family already holds `hm`, `hm2`, `hK` and
`s_d : Stab Γ′ tru Q`, so the guard is literally
`UEntryQ done … (.up Q) (Inv.stable s_d)`, no weakening, no reshaping,
at exactly `parkAntGuard`'s type; and `nativeParkAnt_edge`:
`hgtI (Inv.stable s_d) < hgtS (Stab.lfoc h (.impL s_d lf′))`, strict with
the station unchanged (`hgt_antDispatch` + `hgt_wk`).  What stands
between the family and an unconditional `ParkAntP` is the MEASURE: the
family must be re-founded on `μ = (hgt, station weight, sizeOf)`, and at
the many height-equal sites (every parking, every phase change, every
`wk`) the equality is propositional (`hgt_wk`), so `Prod.Lex.right` does
not apply syntactically — each such site needs its named Part-10 bound
and a `lex_of_le_of_lt` helper.  About seventy sites, ~9 min per build;
the agent did not start it inside its run.  Next run's work.

**(b) `DykAntP p`** (`OFuelPFam.lean` Part 4, new) — the finding of the
run.  The same obligation for the Dyckhoff shape `↓(Q′ ⊃ N′) ⊃ N`, with
the guard goal `Q′ ⊃ N′` (a NEGATIVE) in place of `↑Q`:

    DykAntP p := ∀ done K Γ′ Q′ N′ N,  Saturated done → ParkedCtxP done →
      (↓(Q′ ⊃ N′) ⊃ N) ∈ done → Γ′ ⊆ done ∪ K → done ⊆ Γ′ → K p-free →
      Stab Γ′ tru ↓(Q′ ⊃ N′) →
      UpFrom2 (e f ↦ E_e :: K ⊢ A_f(done ⇒ Q′ ⊃ N′))

This is NOT an instance of `ParkAntP`, and the height-first re-founding
does not reach it.  `interpP`'s Dyckhoff row (§4.14 (c), carried over
from `interpF`) is

    ∃p:  ( ↓A(done ⇒ Q′ ⊃ N′) ⊃ E(N :: rest) )  ∧  E(↓N′ ⊃ N :: rest)
    ∀p:    A(done ⇒ Q′ ⊃ N′)  ∧  A(N :: rest ⇒ goal)

while the generic dispatch (`hgt_antDispatch`, §10.4) is generic in an
antecedent POSITIVE and at `Q = ↓(Q′ ⊃ N′)` supplies
`A(done ⇒ ↑↓(Q′ ⊃ N′))`.  By `interpPA_down_eq` that aggregate is a
DISJUNCTION whose head disjunct is the wanted `A(done ⇒ Q′ ⊃ N′)`, so
the implication runs the wrong way; the only transformer that bridges
the two, `negOfDownStab` at an implication body, rises unboundedly
(§7.3, `ceCyD` 29 → 40, `szI = 10n + 25`); and `dykCommute` lands at the
RESIDUAL station where `interpP` retains the guard at the FULL one.
Exercising cell, mechanised (`dykCell`, saturated by `rfl`, parked by
construction):

    done = [ ↓(c ⊃ ↑a) ⊃ ↑e ],   goal ↑e,
    single ∃p row  ( A(done ⇒ c ⊃ ↑a) ⊃ E(↑e) ) ∧ E(↓↑a ⊃ ↑e)

**Diagnosis.**  The Dyckhoff row is the ONE row of `interpP` that
violates `interpP`'s own principle (§4.14: no rewriting of hypotheses —
every non-atomic implication fires through the retained `∀p` of its
antecedent).  The antecedent of `↓(Q′ ⊃ N′) ⊃ N` is the positive
`↓(Q′ ⊃ N′)`, whose retained `∀p` is `A(done ⇒ ↑↓(Q′ ⊃ N′))`; the row
guards by the BODY `Q′ ⊃ N′` instead, the `interpF` form.  The other
four parked shapes and the ◯-implication all guard by `A(done ⇒ ↑Q)`
(`OFuelP.lean` lines 196–209, 249–252 and the attack rows), and
`ParkAntP` is already stated for every positive `Q`.

**The fix, proposed (not built):** guard the Dyckhoff row by the
antecedent's own goal, exactly as the ◯-implication row does with
`↑↓◯Q′`:

    ∃p:  ( ↓A(done ⇒ ↑↓(Q′ ⊃ N′)) ⊃ E(N :: rest) )  ∧  E(↓N′ ⊃ N :: rest)
    ∀p:    A(done ⇒ ↑↓(Q′ ⊃ N′))  ∧  A(N :: rest ⇒ goal)

In the Lean: `some (.imp Q' N')` → `some (.up (.down (.imp Q' N')))` at
the twelve sites of `LJF/OFuelP.lean` (one `∃p` aggregate, eleven `∀p`
attack rows), nothing else in the definition; the residual conjunct
`E(↓N′ ⊃ N :: rest)` stays (sound by `resSim`).  Then `DykAntP` IS
`ParkAntP` at `Q = ↓(Q′ ⊃ N′)`, the Dyckhoff arms of the family become
parked arms, and the obligation is deleted.  Soundness, which must be
re-proved for the row first: the new guard is WEAKER than the old
(`interpPA_down_eq`: old ⊢ new), and the ◯-implication row is the
template with `◯Q′` replaced by `Q′ ⊃ N′` — from `A, done ⊢ ↑↓(Q′ ⊃ N′)`
the goal inverts to `Stab (A :: done) tru ↓(Q′ ⊃ N′)`, which is exactly
the antecedent premise of `impL`, so the fire is immediate.  The
kernel-checked agreement `interpP = interpF` on S1 (§4.14) is
unaffected (S1 has no Dyckhoff hypothesis); `dykCell` is the cell on
which the changed row must differ from the old (the negative control).
Work: `OFuelP.lean` (12 sites), `OFuelPSound.lean` (Dyckhoff row cases
by the ◯-implication template), `OFuelPMin.lean` (rows),
`OFuelPCof.lean` (a `parkFireE` instance for `dyk`, already the shape
`parkAntP_of_satA2P` covers), `OFuelPFam.lean` (four Dyckhoff arms →
parked arms, `DykAntP` removed).  One run, soundness first; then the
μ-re-founding run for `ParkAntP`.

**Three mechanisation points from the run**, for the next one: a
combinator argument does not fix a recursive call's indices the way a
constructor application does (`circR` needed `pfreeCircUp`, three more
sites needed `show`); a `let` before an anonymous constructor duplicated
a match arm's binders so the termination goal compared `sizeOf` of two
distinct fvars (`UpFrom2.map`); a `rw` inside an anonymous constructor
cannot see through the un-β-reduced `UpFrom2` family (`UpFrom2.mk1`);
and a ◯-goal clause that opens the aggregate AND rewrites one of its
prefix rows spends two fuel units (`UpFrom2.mk2`), because the prefix
sits one fuel below the aggregate.

### 4.16 The Dyckhoff row fixed, soundness re-proved first; `DykAntP` WITHDRAWN — the family is conditional on `ParkAntP` alone (2026-09-05, 13:10)

Built exactly as proposed in §4.15, in one agent run of 36 minutes,
three commits (definition + soundness; rows + the `parkFireE` instance;
the family), merged at 392949b and verified here (`lake build LJF
wipshared Production`, exit 0; `LJF.OFuelPFam` 522 s).

**The definition.**  `some (.imp Q' N')` → `some (.up (.down (.imp Q' N')))`
at the twelve sites of `LJF/OFuelP.lean`, header (c) rewritten.  The
brief's count was short by two: `OFuelPFam.lean` Part 3 carried the old
guard in `dykFireA` (`hmemA`/`want`) and in the ∀p row-block record's
field `dmem` — a SECOND COPY of the row specification, which must move
whenever `interpP`'s ∀p rows move, and where a partial edit hides.  The
first build failed on them and the `#axioms_within` pins caught the
cascade as `sorryAx`, a gate firing unasked.

**Soundness, first and unchanged.**  `eSoundP`, `aSoundP` at
`[propext, Quot.sound]` as before.  The ∃p case is now the ◯-implication
case verbatim (`aSoundP` at the goal `↑↓(Q′ ⊃ N′)`, then `unStable`,
with `resSim` surviving only in the unchanged residual conjunct); the
eleven ∀p rows lost their re-shift `.stable (.rfoc (.rel …))` and are
plain `atkPark`.  The kernel agreement `interpP = interpF` on S1 and its
three `≠` controls still pass.  The negative control on the exercising
cell, by `rfl`, pinned `[propext]`, watched failing with the old guard
`c ⊃ ↑a` in the expected formula:

    interpP "p" 3 [] [↓(c ⊃ ↑a) ⊃ ↑e] none
      = ⋀ [ ( ↓A₂([↓(c ⊃ ↑a) ⊃ ↑e] ⇒ ↑↓(c ⊃ ↑a)) ⊃ E₂(↑e) ) ∧ E₂(↓↑a ⊃ ↑e) ]

**The family.**  The four Dyckhoff arms (`TStabQ`, `TpElimQ`, `UStabQ`,
`UpElimQ`) are parked arms at `Q := ↓(Q′ ⊃ N′)`; `DykAntP` and every
`dant` parameter are gone (Part 4 records the withdrawal); no measure
work anywhere — every `decreasing_by` site in the converted arms goes
through on `LJF/O.lean`'s (station weight, `sizeOf`) pair, and
`OFuelHeight.lean` is untouched.  The chain now reads

    tinvP, uentryP, satE2P, satA2P, ecofinalP, acofinalP  :  ParkAntP p → ⟨statement⟩

and `ECofinalP`/`ACofinalP` are STILL NOT claimed.  Pins measured,
unchanged: the family and chain `[propext, Classical.choice, Quot.sound]`;
new `dykConjMemP`, `laxRowsP_dykMem`, `dykFireE`, `dykFireA`
`[propext, Quot.sound]`; `parkAntP_of_satA2P` `[propext]`.  Five gates
watched failing: the control with the old guard ("not a definitional
equality"); the fold `example` at the end of `OFuelPCof.lean` with the
pre-change `want` type (an elaboration-time gate that the fold stays
exact); three new pin lines at `[propext]` (each "depends on
Quot.sound").

**What remains for N0c is one obligation and one job.**  `ParkAntP` is
the single dispatch shape, and Part 8's `nativeParkAnt` and
`nativeParkAnt_edge` already cover all five parked shapes, the Dyckhoff
one now genuinely an instance (`hgt_antDispatch` is generic in the
antecedent positive).  WP1b: re-found the family on
`μ = (hgt, station weight, sizeOf)` so that the guard is a native
recursive call — about seventy sites, the height-equal ones through a
`lex_of_le_of_lt` helper on the Part-10 bounds — after which
`ecofinalP`/`acofinalP` are unconditional and N0c/N0d are PROVED.

### 4.17 The family re-founded on the height; the guard NATIVE; `ecofinalP`/`acofinalP` UNCONDITIONAL — N0c and N0d PROVED (2026-09-05, WP1b)

Built in one agent run.  `LJF/OFuelPFamKit.lean` (new, 264 lines),
`LJF/OFuelPFam.lean` (1910 lines after the split), `LJF/OFuelPCofinal.lean`
(new), `wip/hgt_probe.lean` (new bench), `wip/ui_routeB_statements.lean`,
`lakefile.toml`, `Audit/Production.lean`.

**The call graph, first — it did not halve the job.**  The brief's
hypothesis was that with the guard native the `∃p` side calls the `∀p`
side but not conversely, so that only the `∀p` block would need the new
measure.  REFUTED, and in the opposite direction: the `∃p` block calls no
`∀p` name, but the `∀p` block calls `TStabQ` — the `∃p` stable traversal
— at FOUR sites (`UStabQ`'s and `UpElimQ`'s fired `q`-implication arms,
through `qFireA`'s `∃p` witness; `ULFQ`'s and `UpLFQ`'s `.impL` arms).
The two blocks were separable only while the guard was a parameter;
native, the `∃p` side calls `UEntryQ` at ten sites and the strongly
connected component is whole again.  The family is now ONE `mutual` of
seventeen definitions, as `LJF/O.lean`'s is, and all of it takes μ.

**The measure.**

    μ  =  (normalised derivation height, station weight, `sizeOf`)

lexicographic, the height of Part 10 and the second and third components
exactly the pair the family already had — so no station obligation moves
and `ljf_dec_e` / `ljf_dec_a` / `ljf_dec_p` discharge them unchanged,
reached through `lex3_of_le` (height `≤`, pair pays) or bypassed by
`Prod.Lex.left` (height strict).  176 recursive-call occurrences across
the seventeen definitions; the strict class is every structural descent,
the antecedent dispatch, the fire continuation, goal inversion and the
two release sites, and the `≤` class is every parking, every phase change
and every `wk`, where the equality is only propositional.

**Two facts Part 10 does not state, and the run had to.**

* **The `p`-eliminators need `lfP` in the measure.**  `TpElimQ`, `TpLFQ`,
  `TpInvQ`, `UpElimQ`, `UpLFQ`, `UpInvGQ` carry an EXTRA derivation
  `lfP : LFoc Γ′ M j P₀` beside the one they recurse on and SPLICE it into
  the argument of their fire call,
  `fireClean … (.stable (.lfoc h′ (.impL X (lfP.wk S))))`, so that
  argument's height contains `szL lfP`, which the recursion argument does
  not bound — `hgt_fireCont` is stated for a single `lf′` and does not
  reach it.  Their first component is the SUM
  `hgt(recursion argument) + hgtL lfP`.  Under it the fire edge is strict
  (`szS s_b ≥ 1` pays), the entry edge from `TStabQ`/`UStabQ` is exact
  with the station unchanged and `sizeOf` dropping, and the six edges
  inside the group are strict.  This is a fact about the family's
  argument lists, not about a transformer, which is why Part 10 has no
  place for it.
* **The cast on the refired atom.**  The two `p`-eliminators hold
  `ha : a = p`, `hb : b = p` and must present `Stab _ .tru (↑a)` where
  they hold `Stab _ .tru (↑b)`, by `(hb.trans ha.symm) ▸ …` at twelve
  sites.  Under the `Eq.ndrec` the height is opaque to `simp`, so `szS X`
  was an unbounded atom and the fire edge unprovable.  `stabAtomCast`
  names the cast and `szS_stabAtomCast` makes its height a rewrite.

**The kit, split out — the method point of the run.**  `LJF.OFuelPFam`
costs 27 min to elaborate merged (522 s split), which is not a loop one
can found a family in.  Part 1 (station-descent lemmas, `ljf_dec_p`) and
the new Part 4b (the height side: `lex3_of_le`, `lex3_or_of_le`,
`stabAtomCast`, `hgt_antDispatchN`, and the farms `hgt_close`,
`hgt_body`, `hgt_dec`, `ljf_dec_pair`, `ljf_dec_h`) are now
`LJF/OFuelPFamKit.lean`, which elaborates in seconds, and
`wip/hgt_probe.lean` is the bench: one `example` per edge class, stated
exactly as the `decreasing_by` goal presents it, checked in 3.7 s.  Two
defects were found there in minutes that had each already cost a full
family build:

* `simp_wf` leaves the goal as `Prod.Lex … (h′,w′,s′) (h,w,s)`, and a `by`
  block inside `refine lex3_of_le (by …) ?_` runs before the second
  component is assigned — the height goal arrives as `szI d ≤ ?m`.  Two
  `?_` and bullets fix it.
* `szI_extract`'s `d` is typed at `Inv Γ (Ω₁ ++ R :: Ω₂) j C`, so with
  `Ω₁ := []` its conclusion's `szI d` is a DIFFERENT atom from the goal's
  `szI d` until `List.nil_append` normalises: `omega` reported two atoms
  both printed `↑(szI d₁)`.  This is why `hgt_goalInv`'s own proof carries
  a `simp only [List.nil_append]`.

**Result.**  `parkAntGuard pant …` is replaced at all twenty parked arms
by the native `UEntryQ done hsat hP hm hm2 hK (.up _) (Inv.stable s_d)`,
the `pant` parameter is gone, and

    tinvP, uentryP, parkAntP, satE2P, satA2P, ecofinalP, acofinalP
      :  ⟨the statement⟩          — no parameter

in `LJF/OFuelPCofinal.lean`, all at `[propext, Classical.choice,
Quot.sound]` (the choice from the well-founded recursion, as in
`LJF/O.lean`).  `ParkAntP` survives as a consequence
(`parkAntP_of_satA2P (satA2P_of_uentryP uentryP)`), not a hypothesis.
The module is imported by `Audit/Production.lean` and `LJF` is added to
the `#axiom_sweep` roots, so the whole LJF◯ estate is now swept for
`sorryAx`.  **N0c and N0d are PROVED.**


**Verified in the session worktree (2026-09-05, 18:43), independently of
the run's own report.**  The run itself was killed by an expired OAuth
token while restoring its first gate injection (the height component
of μ set to 0, which it reports fired); its clean HEAD 578ead2 was merged
at 776b162 and `lake build LJF wipshared Production` exits 0 here, 8952
jobs — `LJF.OFuelPFam` 1749 s (the one 17-way well-founded `mutual`;
see §4.18), `LJF.OFuelPCofinal` 1.1 s — and the production axiom sweep,
now with `LJF` among its roots, reports 12 480 declarations within
`[propext, Classical.choice, Quot.sound]`.  Pins measured here with
`#axioms_within_pin`: `tinvP`, `uentryP`, `parkAntP`, `satE2P`, `satA2P`,
`ecofinalP`, `acofinalP`, each `[propext, Classical.choice, Quot.sound]`;
the gate watched failing here on `ecofinalP` at `[propext, Quot.sound]`
("depends on Classical.choice, which the bound does not allow").  Sorry
sweep of `OFuelPFam.lean`, `OFuelPFamKit.lean`, `OFuelPCofinal.lean`,
`wip/ui_routeB_statements.lean`: clean.  The two statements, as the
kernel holds them (`#print`):

    ECofinalP p := ∀ done Δ ψ,  Saturated done → ParkedCtxP done →
                     Δ p-free → ψ p-free → ∀ j,  done ++ Δ ⊢ⱼ ψ  →
                     Σ f,  E_f :: Δ ⊢ⱼ ψ
    ACofinalP p := ∀ done Δ G,  Saturated done → ParkedCtxP done →
                     Δ p-free → ∀ j,  done ++ Δ ⊢ⱼ G  →
                     Σ f,  E_f :: Δ ⊢ A_f(jGoal j G)

with `E_f = interpP p f [] done none`, `A_f(G) = interpP p f [] done (some G)`.
Note the witness is a single fuel `Σ f`, not the upward-closed `UpFrom`
form; the upward-closed statements (N0d's `ECofinalUp`/`ACofinalUp`) are
projections of the family's `UpFrom2` witnesses and are still DRAFTED —
N3's backward direction is what needs them.  **N0c and N0d for `interpP`
are PROVED.**

### 4.18 Build time, and the budget refactor (WP1c) — 2026-09-05, 18:45

The 17-way `mutual` by well-founded recursion costs Lean 1749 s to
elaborate (176 `decreasing_by` sites, then the packing of the mutual and
its equation lemmas); no proof search and no `decide` is involved.  That
is a maintenance liability, and N3 will need to UNFOLD the family.
Matthew's suggestion (18:35): assert a termination bound, use it, refine
it — make the recursion structural on explicit budgets bounding the
components of μ, with the derivation's bound carried as a hypothesis, so
that each site's descent proof becomes a stand-alone lemma that can be
assumed first (a typed parameter) and discharged later, and the entry
points instantiate the budgets at the actual μ.  Expected: elaboration in
seconds, definitional unfolding for N3, and `Classical.choice` leaving
the pins (no `WellFounded.fix`).  The statements `ECofinalP`/`ACofinalP`
do not change.  Launched as WP1c.

### 4.19 WP2: N1, N2 stated; N3 forward PROVED without cut; N3 backward and N6 PROVED relative to `CutInv` — over the cofinality statements as variables (2026-09-05, 20:40)

Built in one agent run of 66 minutes on Matthew's direction ("state it
in a variable and continue"), in a NEW module `wip/ui_routeB_n3.lean`
(863 lines) that imports only `OFuelP`, `OFuelPSound`, `OFuelPMin`,
`OBridge` — not the family — and takes `(s2 : SatE2P p) (a2 : SatA2P p)`
as arguments; instantiating them with `LJFO.satE2P`/`satA2P` is one
line for later.  Merged at 37fd8ca; verified here: `lake build
wipshared` exit 0, pins measured, gate watched failing (`hasUI_of_stabEq`
at `[propext]` → "depends on Quot.sound"), sorry sweep clean.
**No `Classical.choice` anywhere**: every declaration is at
`[propext, Quot.sound]` or below.

**N1, literal and interderivable.**  `interpP` uses its fuel only as a
bound, so stabilisation can be stated as the chain being constant AS A
FORMULA:

    EStabEq p done    := Σ′ f₀, ∀ f ≥ f₀,  E_f = E_{f₀}
    AStabEq p done G  := Σ′ f₀, ∀ f ≥ f₀,  A_f(G) = A_{f₀}(G)

(`Σ′` because the second component is a `Prop`).  The approved
interderivable forms `EStabilises`/`AStabilises` (now over `interpP`) are
derived from them by `idNeg` after the rewrite.

**N2.**  `IsUIPair p done G E A`: `E`, `A` p-free; `done ⊢ E`;
`minE : ∀ Δ ψ p-free, ∀ j, done ++ Δ ⊢ⱼ ψ → E :: Δ ⊢ⱼ ψ` (every
judgment, since `SatE2P` carries `∀ j`); `A :: done ⊢ G`;
`minA : ∀ Δ p-free, done ++ Δ ⊢ G → E :: Δ ⊢ A` at `tru` only — at
`lax` the ∀p approximant of `jGoal j G` is the different formula
`A(◯P)`, so the lax cell is the cell `done ⇒ ◯P`, covered by the same
statement.  `HasUI p done G := Σ E A, IsUIPair p done G E A`.

**N3 forward — PROVED, no cut:**

    hasUI_of_stabEq : SatE2P p → SatA2P p → Saturated done → ParkedCtxP done →
                      EStabEq p done → AStabEq p done G → HasUI p done G

with `E := E_{f₀}`, `A := A_{f₁}`; soundness from `eSoundP`/`aSoundP` at
the stabilisation fuel; minimality by reading the `UpFrom`/`UpFrom2`
witness above both thresholds and rewriting with the literal
stabilisation.  (Mechanisation point: destructure the witness before
rewriting, or the motive fails.)  `interpP_pfree : ∀ f todo done g,
PFreeN p (interpP p f todo done g)` PROVED (16 aggregate cases by
`fun_induction`; the `interp_pfree` farm of `OCore.lean` does not
transfer — refuting an alternative on an aggregate goal exhausts
8 000 000 heartbeats).

**N3 backward — PROVED relative to ONE obligation:**

    CutInv := ∀ Γ Δ j N ψ,  Γ ⊢ N  →  N :: Δ ⊢ⱼ ψ  →  Γ ++ Δ ⊢ⱼ ψ
    stabilises_of_hasUI : CutInv → SatE2P p → SatA2P p → Saturated done →
                          ParkedCtxP done → HasUI p done G →
                          EStabilises p done × AStabilises p done G

Contraction and permutation come free from `Inv.wk`; the proof uses
`CutInv` at `j = tru` only.  Where the two independent fuels of
`UpFrom2` pay: `E_f, A_f ⊢ A_{f₀}` must read the cofinality instance at
∃p-fuel `f` and ∀p-fuel `f₀`.  Cut admissibility for LJF◯ was not
attempted; it is a work package of its own (review theme 4).

**N6 — PROVED relative to `CutInv` and the per-cell pairs.**  The
anticipated polarisation obstacle dissolved: `pfree_roundTripN :
PFreeN p N → PFreeN p (negOfO (eraseNeg N))` (the round trip is not the
identity on `Neg` but preserves atoms).  Then

    IsUIPairPLL p φ E A := E, A p-free; [φ] ⊢ E; (∀ ψ p-free, [φ] ⊢ ψ → [E] ⊢ ψ);
                           [A] ⊢ φ; (∀ ψ p-free, [ψ] ⊢ φ → [ψ] ⊢ A)      (in LaxND)
    PLL_UI := ∀ p φ, Σ E A, IsUIPairPLL p φ E A
    CellsFor p := ∀ φ, HasUI p [negOfO φ] (negOfO φ) × HasUI p [] (negOfO φ)
    pll_ui_of_ljfo : CutInv → (∀ p, CellsFor p) → PLL_UI

Two cells per formula, not one: the station `[negOfO φ]` supplies
`∃p.φ`, the cell `[] ⇒ negOfO φ` supplies `∀p.φ`.  `CutInv` enters once,
on the ∀p side, to discharge the `E₀` that the E-relativised `minA`
leaves beside the candidate.  `CellsFor` is what N4 owes through N3
forward: the second component is N3 at the empty station, the first is
N3 at the SATURATION of `[negOfO φ]` plus `eMinPP`/`aMinPP` to move the
pair back through the processing phase (that transfer is WP4's content).

**Fuel irrelevance — a typed obligation, on N4's path, not N3's:**

    FuelIrrelevance p := ∀ f todo done g,
        interpP p (f+1) todo done g = interpP p f todo done g →
        ∀ f′ ≥ f, interpP p f′ todo done g = interpP p f todo done g

needs a `Defined` predicate mirroring interpP's thirty clauses; not
built.  With it, ONE equality check at a station is literal
stabilisation (`eStabEq_of_fuelStep`, `aStabEq_of_fuelStep`, proved).

**What this does to N4.**  The literal form suggests stating the open
theorem as TERMINATION OF `interpP`'S RECURSION at every saturated
parked station — "there is a fuel `f` with `interpP p (f+1) [] done g =
interpP p f [] done g`" — plus `FuelIrrelevance`.  Both are statements
about the recursion, which is where WP3's loop-elimination argument
lives, and N3 forward consumes exactly the literal form, so nothing is
lost by strengthening.  That is the standing OPEN item O8 (termination
of the retaining table) with its object made precise.  The refutation
prong is unaffected: an A-chain ascending without bound refutes the
literal form and, through N3 backward (relative to `CutInv`), `HasUI`
for that cell.

**The theorem chain, as it now stands** (every arrow machine-checked):

    N4 (OPEN: stabilisation at every saturated station, literal form)
      ─N3 forward─▶ CellsFor p (with WP4's transfer through the processing phase)
      ─N6─▶ PLL_UI,   given CutInv (OPEN) and cofinality (PROVED, §4.17)

### 4.20 WP1c: the budget refactor's premise REFUTED by measurement; where the 25 minutes and the choice axiom actually come from (2026-09-05, 23:50)

One agent run of 3 h 25 min.  The family and `OFuelPCofinal.lean` are
byte-identical to 776b162; committed are `OFuelPFamKit.lean` Part 4c
(the budget transposition as groundwork, 181 lines, 1.5 s) and
`wip/hgt_probe.lean` benching BOTH foundings (50 examples, 5.8 s).
Merged with PR #19 at the same time; the verification build follows.

**The measurement** (the same seventeen-definition block, same bodies,
same tactic blocks, CPU on the agent's machine):

    as `unsafe def` (no well-founded packing)               3.0 s
    μ-founded, `debug.skipKernelTC := true`                 510 s
    μ-founded, as committed (clean olean)                  1463 s

So the 176 `decreasing_by` proofs are a minor part; the
`WellFounded.fix` TRANSLATION costs ~507 s to elaborate and the KERNEL
~950 s to check the packed term.  Section 4.18's diagnosis ("the
packing of the mutual and its equation lemmas") was half right about
the where and wrong about the what: the budget design (A), built in
full — 108 arms patched, 17 signatures, bounds discharged by
`autoParam` so no call site changed — still goes through
`WellFounded.fix` (`termination_by (n, w, sizeOf)`), lengthens every
telescope, makes every match motive dependent, and measured SLOWER
(bodies-only probes ≥ 2084 s against ≥ 1393 s, both killed under
contention).  Not installed.  Gates: a wrong budget class at a
weakening site fails to elaborate; `ecofinalP` at `[propext]` fails on
`Classical.choice, Quot.sound`.

**Where `Classical.choice` comes from — not the recursion.**  A toy
mutual well-founded definition pins at `[propext, Quot.sound]`.  The
path is

    eMinQ → eMinQ._mutual._proof_488 → atomMem_of_mem (LJF/O.lean)
      → String.instTransOrd → String.le_antisymm → List.le_antisymm
      → Classical.propDecidable → Classical.choice

i.e. one membership lemma in `LJF/O.lean` proved through the string
ORDER's antisymmetry instead of decidable equality.  Replacing that
proof makes the whole route-(B) chain choice-free (review theme 7,
now located).

**The design that would elaborate in seconds** — recorded, not built.
The family must not go through `WellFounded.fix` at all: an outer
`Nat.rec` on the height budget, an inner `Nat.rec` on the station
budget, and STRUCTURAL recursion on the derivation for the phase
changes.  The enabling fact, established by the run: every edge between
the `∃p` side and the `∀p` side is height-STRICT, so at a fixed height
budget the two sides do not call each other and §4.17's strongly
connected component breaks — the two-block form returns, one budget
level down.  With review themes 1–2 (one parked shape; `attackRows`)
the block to re-author is half the size.  Method for any development
loop on the family, from the run: never re-elaborate `LJF.OFuelPFam`
to test a body — check bodies as an `unsafe def` copy (3 s), the edge
goals in the bench (5.8 s), and pay the real build once.

**Verified after the two merges (PR #19 at ee8a0a5, WP1c at 6ee92a9):**
full rebuild of `LJF`, `wipshared`, `Production` from the root module
down, exit 0, 8953 jobs, 32 min wall (23:51–00:24); production axiom
sweep 12 492 declarations within `[propext, Classical.choice,
Quot.sound]`, the four `except`-held modules unchanged.

### 4.21 `CutInv`, refutation stage — from the rules, 26 designed cells; `PolInv` as first stated REFUTED at the lax judgment (a judgment-form fact), restated; the ◯-free block a result in its own right (2026-09-06, 00:55)

Matthew's two standing orders of tonight (rules 8 and 9 of `CLAUDE.md`)
applied: a first run that began enumerating small polarised sequents was
stopped; the replacement read the case list off the completeness proof
and wrote two or three designed cells per step, ◯-free steps first.  One
agent run of 20 minutes; `docs/cutinv-cases.md` (new), `wip/cutinv_cells.lean`
(new, leaf module, builds in 12 s); merged at 7731ba3; sorry sweep clean;
every cell kernel-checked at `[]` (closed terms of the inductive), the
refutation certificates likewise; the pin gate watched failing on the
boundary pin `Inv.sound` at `[]`, and a wrong-rule cell caught by
elaboration and by its own pin (`sorryAx`).

**The invariant and the case list.**  The canonical polarisation never
writes `↑` around a `↓` or `↓` around an `↑`, so exactly two shapes lie
outside the bridge's image: the positive delay `↓↑P` and the negative
delay `↑↓N` — both written by route (B) (`↓↑P′ ⊃ N`, `↑↓(Q′ ⊃ N′)`,
`↑↓◯Q′`, `◯↓(…)`).  Fourteen steps read off `focalizeSCO`: S1 `init`,
S2 `botL`, S3 `andR`, S4 `andL`, S5 `orR`, S6 `orL`, S7 `impR`, S8 `impL`,
S9 the positive delay, S10 the negative delay (the ◯-free block); S11
`circR`, S12 `circL`, S13 `laxOf`, S14 the `lax` judgment itself.

**The ◯-free block (rule 8): 17 cells, all PASS at `[]`.**  Liang–Miller's
"delays are inert" for the ◯-free part of LJF◯, confirmed cell by cell.
Every derivation is one of two moves — left delay elimination
(`lfoc`/`rel`/`downL` on `↑↓M`; `downL` on a queued `↓↑P`) and right
delay introduction (`stable`/`rfoc`/`rel`) — with `routeStab`/`stableFire`
supplying them under a focus.  The cell with content is
`⇒ ↓↑(a ∨ b) ⊃ ↑(b ∨ a)`: the delay pushes the case split out of the
inversion phase and left focus recovers it (`stableFire` in miniature,
since `invertPos (↓↑P) = [[↑P]]`).

**The ◯ block: 9 cells PASS** (`↑a ⇒ ◯↓↑a`, `◯a ⇒ ◯↓↑a`, `↑↓◯a ⇒ ◯a`,
the ◯-implication shape, `◯↓⊤`, …).  **S14 REFUTES `PolInv` as stated in
§4.19**, with certificates: at `Ω = []`, `j = lax`, no constructor
concludes an `imp` or an `and` goal (`impR`/`andR` write `tru`; `circR`
and `stable` conclude `◯`/`↑`; the Ω-rules need a non-empty queue), so

    Inv Γ [] lax (Q ⊃ N)   and   Inv Γ [] lax (M ∧ N)   are EMPTY
    (lax_imp_empty, lax_and_empty: exhaustive cases)

while `⊢ ◯(⊥ ⊃ ⊥)` is PLL-derivable (`s14_refute_nTop_erasure`, a `LaxND`
term); hence `not_polInv : ¬ PolInv`.  Two qualifications, both
certified: the failure is about the JUDGMENT FORM, not provability — the
same erasure is derived at `lax` once the goal carries its shift,
`↑↓(↑⊥ ⊃ ↑⊥)`; and it does not touch `CutInv`, whose premise and
conclusion carry the same `j` and `ψ`, so those cases are vacuous
(`cutinv_lax_imp`, `cutinv_lax_and`).  The underlying fact was already in
the repository (`upMergeJ`'s docstring, `LJF/OCore.lean`) and is cited,
not claimed.

**The obligation, correctly stated:**

    PolInvT := ∀ Γ ψ,  ⊢_ND (⌊Γ⌋ ⇒ ⌊ψ⌋)        →  Inv Γ [] tru ψ
    PolInvL := ∀ Γ P,  ⊢_ND (⌊Γ⌋ ⇒ ◯⌊P⌋)       →  Inv Γ [] lax (↑P)

and `CutInv` follows from them by erase (`Inv.sound`), compose
(`subst1`), split on `j` (`laxAdm` for the two vacuous shapes),
re-focalise.  No evidence against either; positive evidence at every
step including the three modal ones, where the Liang–Miller argument
had not been checked.

**Route (a), recommended, with its lemma list** (`docs/cutinv-cases.md`
§5 keys each case to the cell that does it by hand): eight transfer
lemmas between `N` and its canonical form `⟦N⟧ = negOfO (eraseNeg N)`, one
mutual block on the formula —

    (A) Inv Γ Ω j ⟦N⟧ → Inv Γ Ω j N         (A′) the converse        goal
    (B) Inv (⟦N⟧ :: Γ) Ω j C → Inv (N :: Γ) Ω j C   (B′)              hypothesis
    (C) Inv Γ (⟦P⟧ :: Ω) j C → Inv Γ (P :: Ω) j C   (C′)              pending positive
    (D) Stab Γ j ⟦P⟧ → Stab Γ j P           (D′)                      focused positive

with the delay cases by `routeStab`, `invBranches`/`extract`/`stableFire`,
`lfoc`/`rel`/`downL`, `stable`/`rfoc`/`rel`, and `circR` into `lax`; then
`laxAdm`, `PolInvT`/`PolInvL` from `FocalizationPLL`, and `CutInv`.  The
traversals needed (`routeStab`/`routeLFoc`/`routeInv`, `simHyp`, `extract`,
`invBranches`, `stableFire`, `upMerge`/`upMergeJ`) all exist, proved and
flag-threaded, in `LJF/OCore.lean`; direct cut admissibility (route b)
would re-prove them under a cut measure and handle the lax flag's
asymmetry besides.  WP6 in the blueprint; ◯-free steps first.

### 4.22 WP6: `CutInv` PROVED by polarisation invariance; the ◯-free block first; `(A′)` refuted; N3 backward and N6 lose their obligation (2026-09-06, 01:35)

One agent run of 32 minutes, three commits, merged at f7d361e and
verified here: `lake build LJF wipshared Production` exit 0 (the family
replayed; `LJF.OPolInv` 13 s), pins measured, the gate watched failing
(`cutInv` at `[propext, Quot.sound]` → "depends on Classical.choice"),
sorry sweep clean.  New production module `LJF/OPolInv.lean` (675
lines; imports `OCore`, `OBridge`, `Meta.Audit` only) and the consumer
`wip/ui_routeB_n3_cut.lean`.  **No typed obligation left**: `CutInv` is
discharged, not parked.

**The ◯-free block, first, as its own result (rule 8).**  Writing
`⟦N⟧ = negOfO (eraseNeg N)`, `⟦P⟧ = posOfO (erasePos P)` for the
canonical polarisation, the transfer block — one mutual recursion ON THE
FORMULA, no derivation height anywhere, all in `Type` — is

    bLL : ∀ N,  LFoc Δ ⟦N⟧ j P → LFoc Δ N j P
    gA  : ∀ N,  Inv Γ [] j ⟦N⟧ → Inv Γ [] j N
    sD  : ∀ P,  Stab Γ j ⟦P⟧ → Stab Γ j P
    fT  : ∀ R b, b ∈ invertPos R → b ⊆ Δ → (∀ b′ ∈ invertPos ⟦R⟧, Inv (b′ ++ Δ) [] tru G) → Inv Δ [] tru G
    fS  : the same for Stab
    bCtx : Inv (Γ.map ⟦·⟧) [] j C → Inv Γ [] j C

each delay case exactly as the cells of §4.21 do it (`routeStab`;
`invBranches`/`extract`/`stableFire`/`upMerge`; `rel`/`downL`;
`stable`/`rfoc`/`rel`).  Then, for ◯-free Γ, Δ, N, ψ at judgment `tru`:

    polInvT_circFree : ⊢_ND (⌊Γ⌋ ⇒ ⌊ψ⌋) → Nonempty (Inv Γ [] tru ψ)         [propext, Quot.sound]
    cutInv_circFree  : Inv Γ [] tru N → Inv (N :: Δ) [] tru ψ → Inv (Γ ++ Δ) [] tru ψ

This is Liang–Miller's "delays are inert" for the ◯-free part of LJF◯,
committed on its own (4a0d57e) before any modal step.  A finding: the
◯-free restriction buys NOTHING in the transfer block — `◯` is handled
in `bLL`/`gA`/`sD` exactly as `↑` and `∨` are — so the ◯-free statements
are the general ones with inert hypotheses; the file records them that
way.

**The modal steps and the theorem.**

    polInvT  : ∀ Γ ψ,  ⊢_ND (⌊Γ⌋ ⇒ ⌊ψ⌋)  → Nonempty (Inv Γ [] tru ψ)         [propext, Quot.sound]
    polInvL  : ∀ Γ P,  ⊢_ND (⌊Γ⌋ ⇒ ◯⌊P⌋) → Nonempty (Inv Γ [] lax (↑P))       [propext, Quot.sound]
    cutInvNE : Inv Γ [] tru N → Inv (N :: Δ) [] j ψ → Nonempty (Inv (Γ ++ Δ) [] j ψ)   [propext, Quot.sound]
    cutInv   : Inv Γ [] tru N → Inv (N :: Δ) [] j ψ → Inv (Γ ++ Δ) [] j ψ     [propext, Classical.choice, Quot.sound]

At `lax`, a `⊃` or `∧` goal empties the SECOND premise (`laxImpEmpty`,
`laxAndEmpty` — S14 of §4.21, used exactly as predicted); the shift goal
is `polInvL`; the box goal is `polInvL` under `circR` after the ◯◯
collapse.  `polInvT` is the bridge's converse at EVERY polarised sequent,
so route (B)'s parked shapes and rows all cross to PLL and back — the
reusable half of the work.

**Where the choice axiom enters, exactly once, and why it stays.**
`FocalizationPLL` factors through `PLLND.ND_to_SC` into the sequent
calculus `SCh`, which is a `Prop`; so every re-focalisation in this
development returns `Nonempty`, and `cutInv : … → Inv …` (data, which
its consumers destructure) is `cutInvNE … |>.some`.  The mathematics is
at `[propext, Quot.sound]` (`cutInvNE`); the `Type`-valued packaging costs
the choice.  Removing it needs a `Type`-valued cut elimination for PLL
(route b), not this package.

**Refuted along the way: `(A′)`.**  The converse transfer
`Inv Γ Ω j N → Nonempty (Inv Γ Ω j ⟦N⟧)` is FALSE (`notCanGoalConverse`,
axiom-free), by cell 14.3: `Inv [] [] lax ↑↓(↑⊥ ⊃ ↑⊥)` is inhabited,
its canonical form is `↑⊥ ⊃ ↑⊥`, and `Inv Γ [] lax (Q ⊃ N)` is empty.
The block is one-way by design; `(B′)`, `(C′)`, `(D′)` were not needed.

**Consumers.**  `cutInvOb : CutInv := cutInv` (definitional), and

    stabilises_of_hasUI′ : SatE2P p → SatA2P p → Saturated done → ParkedCtxP done →
                           HasUI p done G → EStabilises p done × AStabilises p done G
    pll_ui_of_ljfo′      : (∀ p, CellsFor p) → PLL_UI

both `[propext, Classical.choice, Quot.sound]`; the statements are
literally the specified ones (`example : LJFO.CutInv := LJFO.cutInv`
elaborates).  **N3 is PROVED in both directions** over the cofinality
statements as variables; **N6 is PROVED relative to `CellsFor` alone.**
What stands between the file and `PLL_UI` is now N4 (through N3 forward)
and WP4's transfer through the processing phase.

Gates watched failing: the two pins above; the negative-delay transfer
dropped from `bLL`'s `↑↓M` arm (type mismatch + `sorryAx` in the pin);
`polInvT` put where S14 forces `polInvL` (type mismatch).  Method trap
recorded by the run: `lake env lean` and `lake build` differ on
`autoImplicit`; verify with `lake build`.

### 4.23 N4 on ◯-free stations: the literal form REFUTED, N3 forward re-derived through cut, the ◯-free instance PROVED by transport from `uniform_interpolation_IPC`; the bounded form OPEN (2026-09-06, 02:30)

One agent run of 45 minutes, four commits, merged at cb18196 and verified
here (`lake build LJF wipshared Production` exit 0; the three new leaf
modules 12 s, 3 s, 24 s; pins measured; gate watched failing; sorry sweep
clean).  Files: `wip/ui_routeB_n4_lit.lean`, `wip/ui_routeB_n4.lean`,
`wip/ui_routeB_n4_cells.lean`, `docs/n4-circfree-cases.md`.  Rules 8 and 9
applied: six designed cells, no enumeration; the ◯-free instance first.

**Stage 1 — the LITERAL form of N1 is REFUTED, by design and in the
kernel.**  The ∀p attack row of a parked `Q ⊃ N ∈ done` at the goal `↑Q` is
`A_f(done ⇒ ↑Q) ∧ A_f(N :: rest ⇒ ↑Q)`, the same call one fuel down, so
`A_{f+1}(done ⇒ ↑Q)` contains `A_f(done ⇒ ↑Q)` as a proper subterm and the
chain is strictly size-ascending; the ∃p row carries the same guard, so
`E_{f+1}` determines `A_f`.  Cells and size lemmas, all `∀ f`, kernel-checked:

    (i)   done = [(a ∨ b) ⊃ ↑c],                       goal ↑(a ∨ b)   (the self-attack)
    (ii)  done = [(a ∨ b) ⊃ ↑c, (c ∨ d) ⊃ ↑a],         goal ↑(a ∨ b)   (a 2-cycle: through the cross guards alone)
    (iii) done = [↓(a ⊃ ↑b) ⊃ ↑c],                     goal ↑↓(a ⊃ ↑b) (the Dyckhoff shape)
    (iv)  done = [↓↑a ⊃ ↑b],                           goal ↑↓↑a       (the shift shape)
    (vi)  done = [(a ∨ b) ⊃ ↑c, ↓↑c ⊃ ↑d],             goal ↑d         (through a NESTED guard alone)

    not_aStabEq1 : AStabEq p cell1 goal1 → False        not_eStabEq1 : EStabEq p cell1 → False
    (and likewise 2, 2cd, 3, 4, 6)                       [propext, Quot.sound]
    not_fuelStep1A/E : ¬ FuelStep p [] cell1 g f, every f

So `EStabEq`/`AStabEq` have no instances at any saturated station with a
parked compound implication, `FuelIrrelevance` is moot (its consumer's
hypothesis is unsatisfiable there), and the "termination of the
recursion" reading of N4 (§4.19) is DEAD: the fuel is essential.  The
sixth cell is the control: (v) `done = [p ⊃ ↑c, ↑p]`, goal `↑c`, UNSATURATED,
is literally constant from fuel 3 (`aStabEq5`, `eStabEq5`, `[propext]`).
`literal_N1_dividing_line` packages all six: the dividing line is
SATURATION with a retained compound implication, not weight — which is
exactly `hasUI_of_stabEq`'s own hypothesis, so that theorem has no
instances.  Growth ratios of the chains at fuels 0–5, by `decide +kernel`:
2.2×, 2.1×, 1.8×, 1.8×, 3.3×; constant for (v).

**Stage 2 — N3 forward, interderivably, through cut** (`cutInv`, §4.22):

    hasUI_of_stabilises : SatE2P p → SatA2P p → Saturated done → ParkedCtxP done →
                          EStabilises p done → AStabilises p done G → HasUI p done G
                          [propext, Classical.choice, Quot.sound]

`cutInv` enters four times: once in `minE` (compose `E_{f₀} ⊢ E_k` with
cofinality's `E_k, Δ ⊢ⱼ ψ`), three times in `minA`.  N3 now consumes the
interderivable form in both directions; `hasUI_of_stabEq` stays as a
theorem with no instances.

**Stage 4 — N4 on ◯-free stations, PROVED by transport** (rule 8, from
`LJFIPC.uniform_interpolation_IPC`, `LJF/Complete.lean`):

    n4_circFree_uncond : SatE2P p → SatA2P p → Saturated done → ParkedCtxP done →
                         CircFreeCtx done → CircFreeN G →
                         EStabilises p done × AStabilises p done G
                         [propext, Classical.choice, Quot.sound]

Pair `E := negOfO (∃p ⌊done⌋)`, `A := negOfO (∀p (⌊done⌋ ⇒ ⌊G⌋))`; erase with
`Inv.sound`, apply the IPC property, re-focalise with `polInvT`/`polInvL`.
The judgment restriction was NOT needed: at `lax` a ◯-free goal must be a
shift, its erasure lands on `◯⌊P⌋`, and `LaxND.erased` brings it down since
context and goal are IPL.  **A restriction that IS needed, and is not an
artefact:** `IsUIPair.minE`/`minA` quantify over p-free test data `Δ`, `ψ`
that may carry `◯`, and Pitts's theorem cannot supply those (`exI_min`
needs `isIPL` of the test formula).  A pair against ◯-carrying test data at
a ◯-free station IS uniform interpolation for PLL on ◯-free cells, the
thing route (B) is built to prove.  So the transported pair is
`IsUIPairCF` (test data also ◯-free), N3 backward is re-derived for it
(`stabilises_of_hasUICF`), and nothing is lost because

    interpP_circFreeN : CircFreeCtx todo → CircFreeCtx done → OptCircFree g →
                        CircFreeN (interpP p f todo done g)          [propext, Quot.sound]

certifies that the only test data the backward direction uses — the
chain's own formulas — is ◯-free.  `Classical.choice` comes only from
`cutInv`'s data packaging and from the IPC theorem.  Gates: three helper
pins at `[propext]` fail on `Quot.sound`; `n4_circFree_uncond` at
`[propext, Quot.sound]` fails on `Classical.choice`.

**Stage 3 — the bounded form: OPEN, with three candidate shapes for the
bound refuted.**  No cell can refute N4 on ◯-free stations now that it is
proved; the cells refute three shapes for a fuel bound `W`: (v) refutes any
plain sum over `done` (adding `↑p` makes the station heavier and the
threshold smaller); (vi) refutes any `W′` built from the goal's
subformulas; (ii) refutes a recursion on the guard's guard, since the
guard graph cycles.  `docs/n4-circfree-cases.md` names the lemma the
bounded proof needs first — the self-attack disjunct is REDUNDANT up to
interderivability, which is exactly why the interderivable chain
stabilises while the literal one does not — and the measure it should
run on.  That lemma, and the bound, are the technique the modal case
needs; N4 for PLL remains OPEN both ways.

**Consequences for the blueprint.**  N1: the literal statements are
withdrawn as candidates (REFUTED at every saturated station of interest);
the interderivable forms stand.  N3: PROVED both ways in the interderivable
form.  N4: the ◯-free instance PROVED (by transport); the PLL instance
OPEN both ways.  N6's `CellsFor` is now inhabited on ◯-free cells through
`hasUI_of_stabilises ∘ n4_circFree_uncond`, up to WP4's transfer through
the processing phase, which is the next mechanical package.
---

### 4.24 WP4: the transfer through the processing phase PROVED — stabilisation and N3 restated at a generalised station; the ◯-free instance of `CellsFor` PROVED and shown to AGREE with `uniform_interpolation_IPC`; N5 a theorem; `PLL_UI` reduced to N4 alone (2026-09-06, 03:25)

One agent run of 38 minutes, two commits, merged at 61c9812 and verified
here (`lake build wipshared` exit 0; pins measured; gate watched failing;
sorry sweep clean).  File: `wip/ui_routeB_wp4.lean` (892 lines), registered
in `wipshared`.  Nothing under `LJF/` or `docs/` was touched by the run.

**There is no branch-station lemma.**  The plan (§4.23: "the transfer of a
pair from the saturation of `[negOfO φ]` back through the processing
phase") began by enumerating the saturated stations that processing
reaches from `[negOfO φ]`.  That enumeration is not needed and would be
the wrong object: every input N3 consumes is already stated at a
*generalised station* `(todo, done)` — soundness `eSoundP`/`aSoundP`
(`LJF/OFuelPSound.lean`); the processing-phase cofinality `eMinPP`/`aMinPP`
(`LJF/OFuelPMin.lean`), which take `SatE2P`/`SatA2P` at the saturated
stations and run the fire scan and the whole processing phase themselves;
and `interpP_circFreeN`.  The branch stations are named by `interpP`'s own
recursion.  So WP4 is N1 and N3 restated over `(todo, done)`:

    EStabilisesP p todo done   := Σ f₀, ∀ f ≥ f₀,  E_f ⟛ E_{f₀}                 (at (todo, done))
    AStabilisesP p todo done G := Σ f₀, ∀ f ≥ f₀,  E_f ∧ A_f ⟛ E_f ∧ A_{f₀}     (goal G)
    estabilisesP_nil : EStabilisesP p [] done = EStabilises p done := rfl   (astabilisesP_nil likewise)

**Stage 1 (rule 8) — the ◯-free instance of `CellsFor`, PROVED.**

    isUIPair_of_stabilisesP : SatE2P p → SatA2P p → ParkedCtxP done →
        (E-chain constant from f₀) → (A-chain constant from f₁) →
        IsUIPair p (todo ++ done) G (interpP p f₀ todo done none)
                                    (interpP p f₁ todo done (some G))
    stabilises_of_hasUICFP : SatE2P p → SatA2P p → ParkedCtxP done →
        CircFreeCtx todo → CircFreeCtx done → CircFreeN G →
        HasUICF p (todo ++ done) G → EStabilisesP p todo done × AStabilisesP p todo done G
    cellsFor_circFree : SatE2P p → SatA2P p → ∀ φ, isIPL φ →
        HasUI p [negOfO φ] (negOfO φ) × HasUI p [] (negOfO φ)
    IPC_UI_routeB := ∀ p φ, isIPL φ → Σ E A, IsUIPairPLL p φ E A
    ipc_ui_routeB : (∀ p, SatE2P p) → (∀ p, SatA2P p) → IPC_UI_routeB
                                                  [propext, Classical.choice, Quot.sound]

Saturation is never assumed: the two cells are the generalised stations
`([negOfO φ], [])` and `([], [])`.  The ◯-free restriction of the test
data (§4.23's `IsUIPairCF`) does NOT propagate: `HasUICF` is the input
(Pitts's theorem cannot reach ◯-carrying test data), the output is
unrestricted `HasUI`, because `eMinPP`/`aMinPP` are cofinal for every
p-free test datum, `◯` included.  So `IPC_UI_routeB` is uniform
interpolation for PLL at every IPC formula, tested against every p-free
PLL formula.  `cutInv` enters as in `hasUI_of_stabilises`: once in `minE`,
three times in `minA`; four more times in the backward direction.

**The check against `uniform_interpolation_IPC` — the two constructions
AGREE.**

    routeB_agrees_IPC : isIPL φ → (w : IPCPairRouteB p φ) →
        (Nonempty (LaxND [w.E] (exI p [φ]))  ∧ Nonempty (LaxND [exI p [φ]] w.E)) ∧
        (Nonempty (LaxND [w.A] (allI p [] φ)) ∧ Nonempty (LaxND [allI p [] φ] w.A))

Comparable because route (B)'s interpolants at an IPC formula are values
of `interpP` at a ◯-free generalised station, hence ◯-free
(`interpP_circFreeN`) and IPL after erasure (`isIPL_eraseNeg`), which is
what Pitts's minimality demands of a test formula.  The two cells are the
ones N6 uses (`∃p` at the station `[φ]`, `∀p` at the empty station with
goal `φ`); the E-relativisation of `allI_min` is discharged outright,
`exI p []` being a theorem.  Route (B) therefore computes Pitts's
interpolants, up to interderivability, wherever both are defined.

**Stage 2 — the transfer in general; N5 a theorem; `PLL_UI` from N4
alone.**

    StabilisationAllP p := ∀ done G, Saturated done → ParkedCtxP done →
                           EStabilises p done × AStabilises p done G        (N4, OPEN)
    stabP : StabilisationAllP p → ∀ todo done G, ParkedCtxP done → StabP p todo done G
    hasUI_of_stab : SatE2P p → SatA2P p → StabilisationAllP p →
        ∀ todo done G, ParkedCtxP done → HasUI p (todo ++ done) G            (N5)
    cellsFor_of_stab : SatE2P p → SatA2P p → StabilisationAllP p → CellsFor p
    pll_ui_of_stabilisationAll :
        (∀ p, SatE2P p) → (∀ p, SatA2P p) → (∀ p, StabilisationAllP p) → PLL_UI
                                                  [propext, Classical.choice, Quot.sound]

`stabP` runs `eMinPP`'s clause list on `eMinPP`'s measure
`2·sum3 todo + sum3 done`.  Eleven of the thirteen processing clauses and
the fire step satisfy `interpP p (f+1) todo done g = interpP p f todo′ done′ g`
for EVERY goal slot, so stabilisation transfers by rewriting, no
derivation touched (`StabP.step`; the fire step through
`interpPFire_eq`).  `↑⊥` is constant from fuel 1 (`stabP_fls`).
`↑(P ∨ Q)` is the only clause that builds a derivation (`stabP_or_at`),
and its one focused step is

    andAllImpUse : (↓E ⊃ A) ∈ l → Inv [E, nAndAll l] [] .tru A

`cutInv` enters Stage 2 only in threshold merging: the `∀p` chain is
E-relativised and the branching clause guards each row by that branch's
`∃p` at the SAME fuel, so the two chains must stabilise from a common
threshold (`StabAt.raiseTo`; `stabP_of_stabilises` at the leaf; two cuts
per `∀p` row of `stabP_or_at`).  The `∃p` half of the branching clause,
`StabP.step`, `stabP_fls` and `andAllImpUse` spend no cut.

**Pins** (measured with `#axioms_within_pin`, asserted with
`#axioms_within`): the chain statements, `StabAt`/`StabP`/
`StabilisationAllP`, `swapInv2` and the two `_nil` equations `[propext]`;
`circFree_posOfO`/`circFree_negOfO`/`IPC_UI_routeB`/`IPCPairRouteB` `[]`;
`StabAt.mk1`, `StabP.step`, `stabP_fls`, `andAllImpUse`
`[propext, Quot.sound]`; everything downstream of a cut at
`[propext, Classical.choice, Quot.sound]`, the choice from `cutInv` and
from `uniform_interpolation_IPC` and nowhere else.  Gates watched failing:
`cellsFor_circFree` and `stabP` at `[propext, Quot.sound]` each fail on
`Classical.choice` (both in the run; `stabP` re-watched here).

**Method note.**  `decreasing_by ljf_dec_e` is unusable in a module that
sees both `LJF/OCore.lean` and `LJF/Base.lean` (this one does, through
`LJF.Complete`): the token is ambiguous, the wrong expansion elaborates,
and every decreasing goal is left open with no diagnostic pointing at the
cause.  The six alternatives needed are spelled out in the module's
`decreasing_by`, with a comment.

**Consequences for the blueprint.**  N5: PROVED relative to N4
(`hasUI_of_stab`).  N6: `CellsFor` inhabited outright on IPC formulas
(`cellsFor_circFree`, hence `ipc_ui_routeB`), and in general from N4
(`cellsFor_of_stab`).  Uniform interpolation for PLL now rests on N4
alone, over `SatE2P`/`SatA2P` as variables (instantiated by
`LJFO.satE2P`/`satA2P` in one line, deferred with the 25-minute module).
Everything Matthew's overnight goal names after N4 — "then go ahead with
WP4, ◯-free, then complete WP4" — is done; WP8 (N4 for PLL through the
loop-checked recursion) is the one thing left in flight.

---

### 4.25 WP8: N4 for PLL through the loop-checked recursion `interpQ` — NOT proved; the route built, eighteen designed cells all bottom out (no refutation), two blueprint design decisions REFUTED and repaired, N4 reduced to the two typed obligations `QBound` and `PQEquiv` (2026-09-06, 03:35)

One agent run of 46 minutes, six commits, merged at 8654b8b and verified
here (`lake build wipshared` exit 0; pins measured; gate watched failing;
sorry sweep clean).  Files: `wip/ui_routeB_n4q.lean` (the definition and
p-freeness), `wip/ui_routeB_n4q_cells.lean` (the eighteen designed cells),
`wip/ui_routeB_n4q_thm.lean` (the theorems and the two obligations),
`docs/n4-loopcheck.md` (the design record).  Rules 8 and 9 applied: the
◯-free cells first; designed cells only, no enumeration.

**The definition.**  `interpQ` is `interpP` with the self-attack loop cut
in the definition: it carries `seen : List Pos`, the antecedents whose own
goal has already been attacked, and the two clauses that differ are

    parkRowE prev done Q′ N rest res seen =
        (if Q′ ∈ seen then ⊤
         else ↓A_prev(done ⇒ ↑Q′ | Q′ :: seen) ⊃ E_prev(N :: rest | seen))
      ∧ E_prev(res ++ rest | seen)
    parkRowA prev done Q′ N rest goal seen =
        if Q′ ∈ seen then ⊥
        else A_prev(done ⇒ ↑Q′ | Q′ :: seen)  ∧  A_prev(N :: rest ⇒ goal | seen)

(`res = [↓N′ ⊃ N]` for the Dyckhoff row, `[]` for the other four compound
shapes; every other clause of `interpP` transcribed with `seen` threaded).
Written in STEP form, `interpG rst p (f+1) = stepQ rst p (interpG rst p f)`,
so structural in the fuel: 11 s to elaborate, against the family's 25
minutes.  Calibration, kernel-checked: `interpQ = interpP` wherever no
compound implication is reached (the six `↑`/`∧`/`⊃` goal shapes, the
seven ◯-goal shapes, every processing clause, the five compound rows at
fuel 1), and `interpQ ≠ interpP` at cell (i) from fuel 2.  `interpG_pfree`
PROVED, `[propext, Quot.sound]`.

**REFUTED (1): the blueprint's per-station reset** (WP3's loop elimination,
§4.19: "`seen` grows within a fixed station and the antecedents of a
station are finitely many").  The recursion is parameterised by a reset
map: `interpQ0 = interpG (fun _ => [])` per-station, `interpQ = interpG id`
global.  The per-station policy does not terminate, and the counterexample
is ◯-FREE: cell (iii) `[↓(a ⊃ ↑b) ⊃ ↑c] ⇒ ↑↓(a ⊃ ↑b)`.  The surviving loop
runs through the ∀p goal inversion at an implication goal, where
`invertPos` moves `↑a` INTO the station and `seen` is reset, the station
one `↑a` longer each time round, so a per-station `seen` never sees the
same station twice.

    q0_3_not_const : ∀ f ∈ [12,13,14,15], interpQ0 "p" f [] cell3 (some goal3) [] ≠ interpQ0 "p" (f+1) …
    q_3_const_there : ∀ f ∈ [12,13,14,15], interpQ  "p" f [] cell3 (some goal3) [] = interpQ  "p" (f+1) …
                                                                                    [propext]

**REFUTED (2): recording at the aggregate.**  Putting the goal's positive
on `seen` when a ∀p aggregate sits at `↑Q` gives smaller interpolants
(cell (iii) threshold 8 against 12) but `seen` must then be read as
`seenOf(goal, seen)`, which DROPS at the ∃p companion of a disjunctive
hypothesis in ∀p mode (`↑(P₁∨P₂) :: todo, done, some ↑Q ⟶ b ++ todo, done,
none`), so the lexicographic measure does not close.  Committed: recording
at the guard CALL SITE, which makes `seen` monotone along every edge.  A
third finding from the first draft: the check must be SYMMETRIC (`⊥` for
the ∀p disjunct, `⊤` for the ∃p conjunct) or cell (iii) still loops; that
draft's chain plateaus at fuels 2–3 and resumes climbing — a false
fixpoint — which is why every certificate below checks two or three fuels
above its threshold and never one.

**The cells: every one bottoms out; the refutation candidate did not
fire.**  Literal constancy by `decide +kernel`, `[propext]`, forty
decisions in 16 s; thresholds:

    ◯-free (interpP literally REFUTED on five of these, §4.23):
        (i) 4   (ii) 6   (iii) 12   (iv) 4   (v) 3   (vi) 5
    modal:      (m1) 4   (m2) 6   (m3) 7   (m4) 6   (m5) 7
    GZ shapes:  (m6) 10  (m7) 10  (m8) 10  (m9) 9   (m10) 16  (m11) 10
    S1:         12 at ↑e, 13 at ◯g, 12 for ∃p

(m6)–(m11) are the shapes that reach the Ghilardi–Zawadowski pattern: a
◯-implication guarded through a box, a box whose opening makes a
◯-implication, a fire that re-creates one under a box, two nested boxes,
and the S1 variant whose fire re-creates the guard's own antecedent.
`qm10_false_fixpoint`: (m10)'s ∃p chain repeats at fuel 12 and moves again
at 14, kernel-checked — a single repeated level is not stabilisation for
this recursion, a second and independent reason `FuelIrrelevance` (N0i)
is unusable.

**Stage 2 — N4 over two obligations.**  (a) PROVED, `[propext, Quot.sound]`
(measured here; the run's report said "axiom-free", which the file's own
pins never claimed):

    QFounded rst p μ := ∀ prev₁ prev₂ s, (∀ t, μ t < μ s → prev₁ t = prev₂ t) →
                        stepQ rst p prev₁ s = stepQ rst p prev₂ s
    interpG_stab_of_founded : QFounded rst p μ → ∀ s f, μ s + 1 ≤ f →
                              interpG rst p f s = interpG rst p (μ s + 1) s
    qStabLitE_of_bound / qStabLitA_of_bound : QBound p → literal stabilisation at EVERY station

OPEN — `QBound p := Σ′ μ, QFounded id p μ`.  For `interpP` no such `μ`
exists (`not_fuelStep1A`); for `interpQ` its shape is forced by the edge
table: `μ = (K − |seen|, ν)` with `ν = 2·sum3 todo + sum3 done + 3^(wNeg goal)`
(`eMinPP`'s measure); the guard edges strictly decrease the first
component (the row fires only when `Q′ ∉ seen`, the call is made at
`Q′ :: seen`), every other edge carries `seen` and strictly decreases `ν`.
Two components remain: the subformula-closure invariant bounding `K`
(over the ORIGINAL cell's closure, since `invertPos` grows the station at
the ∀p implication goal), and the per-clause `ν` descent (every inequality
already in `LJF/OFuelPMin.lean`: `ljf_dec_e`/`ljf_dec_a`, `p3_2`, `p3_21`).

OPEN — `PQEquiv p := ∀ f done g, IDeriv (interpP p f [] done g) (interpQ p f [] done g [])`,
the redundancy lemma of `docs/n4-circfree-cases.md` §3.3 as data.  The
easy halves are `interpQ ⊢ interpP` on the ∀p side (the dropped disjunct
is `⊥`) and `interpP ⊢ interpQ` on the ∃p side (the dropped conjunct is
`⊤`); the hard halves are the redundancy claim.  One interderivability,
not two implications: the polarity table makes the four halves a single
simultaneous induction (`A^Q ⊢ A^P` needs `A^P ⊢ A^Q` under `parkRowE`'s
`↓A ⊃ E′`).

PROVED over them, `[propext, Classical.choice, Quot.sound]` (the choice
from `cutInv`'s data packaging alone):

    n4_of_interpQ    : PQEquiv p → QBound p → ∀ done G, EStabilises p done × AStabilises p done G
    hasUI_of_interpQ : SatE2P p → SatA2P p → PQEquiv p → QBound p →
                       Saturated done → ParkedCtxP done → HasUI p done G
    n4_circFree_intrinsic  (the ◯-free instance of the route)
    n4_circFree_byPitts    (cross-check by elaboration: the same conclusion is already
                            inhabited unconditionally by n4_circFree_uncond, so the two
                            obligations cannot contradict a machine-checked theorem there)

The conclusion needs no saturation, no parking, no ◯-freeness: both
obligations are statements about the recursion, not about a cell, so N4
comes out at every cell at once.  Soundness of `interpQ` is NOT built
(the polarity argument of `docs/n4-loopcheck.md` §3 is an argument, not a
proof); it is not needed on this route, which inherits `interpP`'s
soundness through `PQEquiv`.

**Gates watched failing** (quoted in the run): `qS1_A` at `[]` fails on
`propext`; `n4_of_interpQ` at `[propext, Quot.sound]` fails on
`Classical.choice`; a calibration defect (the lax prefix `◯↓◯P′` inverting
to `↑P′`) was caught by `decide` proving the proposition false and the
cell then depending on `sorryAx`.  Re-watched here: `n4_of_interpQ` at
`[propext, Quot.sound]`.

**Status of N4 for PLL: OPEN, in neither direction; no designed cell
refutes it.**  Launched in parallel at 03:40: **WP9** (`QBound`, the
measure — Stage 0 checks the candidate measure on the designed cells in
the kernel before any proof; the founding generalised to a well-founded
lexicographic order; the closure invariant and the `ν` descent) and
**WP10** (`PQEquiv` — refute-first at fuels 1–4 on six designed cells with
the certified decider, since the per-fuel form may hold only up to a fuel
shift; the cofinal restatement ready if it fails; then the easy halves by
the polarity induction, the hard halves ◯-free first).

---

## 5 · OPEN list

Everything in this document that is not established, in one place.  Each
item says what would settle it.  **Standing note (2026-09-06, §4.25):**
this list was written for the retaining table of §2–§3 and route A′; the
live state is route (B)'s, and it is one line — uniform interpolation for
PLL rests on N4 alone (§4.24), N4 rests on `QBound` and `PQEquiv` (§4.25),
both OPEN.  O2 (`CimpAnt`) is superseded by the unconditional cofinality
of §4.17; O7 (the loop cut) is now a definition, `interpQ`, with its
literal termination the `QBound` obligation; O8 (termination of the
retaining table) is answered for route (B) by the height-first founding
of §4.17.

**O1.  Uniform interpolation for PLL.**  OPEN, in neither direction.
Unchanged by this document.  (Standing claim discipline,
`docs/ljfo-fidelity.md`, `HANDOFF.md` §8.)

**O2.  `LJFO.CimpAnt`.**  Undischarged; no term of that type exists in
the repository.  `LJFO.satE2` and `LJFO.satA2` are sorry-free but
conditional on it, so **E2/A2 minimality for LJF◯ is not claimed**.
§4.3 adds two validating instances; that is validation, not discharge.

**O3.  The clause table of §2 is unverified as a paper object.**  It is
a reconstruction, believed to agree clause for clause with
`LJFO.interp`, but I did not machine-check the agreement.  A `#guard`
comparing the two on a corpus of stations would settle it.

**O4.  The provenance marks.**  TRANSCRIBED is checkable (it means
"identical to the corresponding clause of `LJF.interp`") and I did check
it by reading `LJF/Base.lean:710–824`, which covers the processing
clauses, the fire scan, the whole ∃p read-off and the ∀p clauses through
the `↑⊥` goal; I did not read the remaining ∀p goal shapes there, so the
marks on A5 and A6 are by pattern, not by inspection.  The attribution of those clauses
to *Pitts 1992* is second-hand: I did not read the 1992 paper while
drafting.  Anyone using this table in a paper must verify the
attribution against the source, in particular for E3/C2 (the `L⊃⊃`
clause) and for A3's `head` disjunct.

**O5.  Whether `pre(Σ, P)` in A7 is complete** for the body shape
`↓(Q₀ ⊃ N₀)`, an implication under a box.  I checked `a`, `⊥`,
`P₁ ∨ P₂` and `↓◯P'` by hand; I did not check that one, and it is where
a missing row would be hardest to see.

**O6.  Whether E4 is the strongest box row**, i.e. whether all `p`-free
content extractable from a box hypothesis is itself boxed.  I found no
candidate for extra content and no argument that none exists.

**O7.  The loop cut** of §3.4 ("a decide on `X` whose antecedent premise
is the sequent being derived can be pruned").  Stated with a
plausibility argument; not proved.  It is what would make the retaining
table a definition at all.

**O8.  Termination of the retaining table.**  §3.4's discounted-station
order `μᵥ` is refuted at the box row by a hand computation, and §4.5
shows the reset that breaks it is required.  Whether *some* well-founded
order founds the retaining table is OPEN; the record's route A′.  The
fuel-founded variant `LJFO.interpF` (`LJF/OFuel.lean`) is route (B),
and its soundness pair is PROVED (2026-09-04, `LJF/OFuelSound.lean`,
`eSoundF`/`aSoundF`, `[propext, Quot.sound]` — below the originals,
which take `Classical.choice` from the weight-founded recursion):

    eSoundF p : ∀ f todo done,   Inv (todo ++ done) [] tru (interpF p f todo done none)
    aSoundF p : ∀ f todo done G, Inv (interpF p f todo done (some G) :: (todo ++ done)) [] tru G

The twelve modal rows went through by weakening (`atkCimp` at
`rest := done`), the `∃p` aggregate row easier than its original.  What
remains OPEN for route (B) is cofinality (`ECofinalF`/`ACofinalF` in
`wip/ui_routeB_statements.lean`, typed statements with no declaration):
the proof build STOPPED at the founding of the recursion, with the
obstruction exact and a candidate family defined — §4.11.

**O9.  The decide counts of §4.2.**  Two decides on `H` for Γ₁ and three
for Γ₂ are the counts of the derivations I wrote down; **minimality of
either count is not established**, and the brief's "no constant bound on
decides" is not established for LJF◯.  For `G4` the analogous copy count
on the `K n` family is REFUTED as unbounded (measured 1, 2, 2, 2), but
that is a different quantity in a different, incomplete calculus.

**O10.  The hand computations of §4** — SETTLED at oracle level on
2026-09-04, §4.7: `LJFO.interp` evaluated on the polarised Γ₁, Γ₂,
normalised by the certified simpset, agrees with every displayed value
up to provable equivalence (eight G4c cells, all valid).  What remains
OPEN is only the last rung: the eight equivalences are engine-certified,
not kernel-pinned.

**O11.  Two stale docstrings observed in passing**, worth a one-line fix
in some later commit: `LJF/OCore.lean:752` and `LJF/O.lean:236` both say
the station has "exactly three shapes" where `LJFO.ParkedN` has five
(the two modal ones were added later); and `LJF/OCore.lean:4096` and
`LJF/O.lean:2087` point at `LaxLogic/LJFOAudit.lean`, a path that no
longer exists (the pins are in `LJF/OAudit.lean` after the 2026-08-22
split).
