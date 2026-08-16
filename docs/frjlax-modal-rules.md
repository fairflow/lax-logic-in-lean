# FRJ◯ — the modal rules: candidates, screens, and what soundness still needs

*2026-08-16, branch `claude/frj-redevelopment-69005f`.  W5, first half.
The rules below are **candidates**: their semantic obligations are each
PROVED in `FRJLax/Modal.lean`, and the cells that decide the design are
computed in concrete models.  The rule statements are Matthew's call;
this document is what he is being asked to sign off.*

Companions: `docs/frj-lax-plan.md` (the campaign plan),
`docs/frjlax-fidelity.md` (the fidelity table), `FRJLax/Modal.lean` (the
proofs and the screens).

---

## 1. The semantics, and where the difficulty is

    M,w ⊩ ◯A   iff   for every v with R_i w v there is u with R_m v u
                     and M,u ⊩ A

FRJ's join rule creates a world `β` below the premises' worlds, and the
whole calculus turns on being able to say what `β` forces.  For `⊃` the
mechanism is negative: `β ⊩ A ⊃ B` because **`A` fails at `β`**, so the
implication holds there vacuously, and above `β` it holds by the closure
argument.  That is all the support condition (J2) has to arrange — it
names `A` as some premise's right formula.

For `◯` the obligation at `β` is **positive**: a modal witness must
exist.  Nothing in FRJ's data supplies one, and that is the entire
content of the extension.  Stated as the two lemmas a rule may use:

**PROVED** (`Model.circ_intro`).  A witness at `w`, plus `◯A` forced
strictly above `w`, force `◯A` at `w`:

    (∃u. R_m w u ∧ u ⊩ A)  ∧  (∀v. R_i w v → v ≠ w → v ⊩ ◯A)
    ⟹  w ⊩ ◯A

**PROVED** (`Model.not_force_circ`).  No modal successor forcing `A`
refutes `◯A`:

    (∀u. R_m w u → u ⊮ A)  ⟹  w ⊮ ◯A

---

## 2. Three screens, and what each settled

All three run by `decide` against concrete constraint models, using the
decidable forcing of W1.

**Screen 1 — a selective witness is required.**  The two-world model
`lo < hi` with `p` true only at `hi` and `R_m = R_i` gives

    two ⊩_lo ◯p    and    two ⊮_lo p

so `◯p ⇒ p` is semantically refutable.  A rule able to witness `◯` only
by a fallible world could not build this model, because —

**Screen 2 — a fallible witness is all-or-nothing** (`circ_of_fallible_cone`).
A fallible world forces every formula, so a fallible modal successor
witnesses every `◯B` at once.  It is therefore the right mechanism for
`◯⊥` and the wrong one for `◯p`.

*A correction the screen produced.*  The first form written down here was

    R_m w u → Fal u → w ⊩ ◯A

and it is **false**: `u` is a modal successor of `w` and says nothing
about the modal successors of a world strictly above `w`.  What holds is
the cone form, `∀v ≥ᵢ w. ∃u. R_m v u ∧ Fal u`.  Caught before any rule
was written, which is the point of screening first.

**Screen 3 — the witness is per-world, not per-derivation.**  `◯(p ∨ q) ⊃
◯p ∨ ◯q` is not a PLL theorem, and the three-world model with root `bot`
below incomparable `l`, `r` (with `p` at `l`, `q` at `r`) gives

    branch ⊩_bot ◯(p ∨ q),    branch ⊮_bot ◯p,    branch ⊮_bot ◯q

Refuting it needs two successors of the root carrying *different* modal
witnesses.  So a single global promise world will not do: the modal data
belongs to the world a join creates.

---

## 3. The zones

**Ĝ gains a third zone**, and this is settled rather than proposed:

    Ĝ_at = Sf^L(G) ∩ PV      Ĝ_imp = Sf^L(G) ∩ Fm⊃
    Ĝ_◯  = Sf^L(G) ∩ {◯-formulas}
    Ĝ    = Ĝ_at ∪ Ĝ_imp ∪ Ĝ_◯

Two independent derivations of the same conclusion:

* *semantic*: `Cl` absorbs `∧` and `∨` on the left, which is why FRJ's two
  zones are exhaustive for IPC.  `◯` is absorbed by neither — `◯A` can be
  forced where `A` is not, exactly as `A ⊃ B` can be forced where `B` is
  not — so `◯`-formulas are determining data and must be carried;
* *empirical*, from the screen recorded in `docs/frj-lifting.md` §7:
  determining part = atoms + `⊥` + implications gives **32 certified
  failures** over 156 cells; adding `◯`-formulas gives **0**.

Implemented (`FRJLax/Core.lean`), with the three-way split proved:

    zone_split :  Γ ⊆ Ĝ  →  Γ ≐ Γ^at ++ Γ^⊃ ++ Γ^◯

On a `◯`-free goal `Ĝ_◯` is empty and this is the paper's `Ĝ`; the whole
`◯`-free development, including the replayed refutations of the paper's
Examples 3.6, 3.7 and 3.15, builds unchanged over the three-zone `Ĝ`.
That is the control on the generalisation.

---

## 4. The candidate rules

### 4.1 `◯∈` — regular `◯`-introduction

    Γ ⇒ Z
    ─────────  ◯∈        barren(D),   ◯Z ∈ Sf^R(G)
    Γ ⇒ ◯Z

where `barren(D)` holds when the p-sequent at the root of `D` declared no
promise, i.e. its world has no proper modal successor.

**Obligation, PROVED** (`Model.not_force_circ_of_no_promise`):

    (∀u. R_m w u → u = w)  ∧  w ⊮ Z   ⟹   w ⊮ ◯Z

`barren` is a decidable property of the derivation — follow it down to
the p-sequent at the root and read off whether that join carried a
promise.  It is the minimal form of the "modal zone" the earlier design
note (`docs/frjo-calculus-plan.md` §2) proposed as `μ`; the screens do not
justify a full zone, only this one bit.

### 4.2 `⋈^p` — the promise join

A join `⋈^At` or `⋈^∨` may carry one additional **promise premise**, a
regular derivation `Δ ⇒ D`, whose world becomes the modal successor of
the new world:

    σ₁ … σₙ            Δ ⇒ D
    ────────────────────────────────────────────────  ⋈^At,p
    Σ^at, Θ^at\{F}, Σ^⊃, Θ^⊃, Σ^◯, Θ^◯  ⇒  F

with (J1), (J2), (J3) unchanged and three new side conditions:

    (J5)   ◯Y ∈ Σ^◯ ∪ Θ^◯   implies   Y ∈ Cl(Δ)
    (J6)   Σ^◯ ∪ Θ^◯ ⊆ Cl(Δ)
    (J7)   Γ ⊆ Cl(Δ)

**Obligation, PROVED** (`Model.circ_intro`).  (J5) supplies the witness at
the new world; (J6) and (J7) supply the "strictly above" half at the
promise world; at the irregular premises' worlds it comes from the same
closure argument that (P2) already uses for `⊃`, needing no new lemma.

A join carrying **no** promise has `Σ^◯ = Θ^◯ = ∅` and its world is
barren — that is what makes `◯∈` applicable above it.

### 4.3 What is deliberately NOT proposed

* **No `◯` clause in `Cl`.**  `α ⊩ X` does imply `α ⊩ ◯X`
  (`Model.circ_of_force`), so (Cl1) would survive the clause; but `Cl`
  occurs in the side conditions of `⊃∈` and `⊃∉`, so adding it changes
  those rules, and nothing above needs it.
* **No fallible-witness rule for selective `◯`.**  Screen 2.  A fallible
  witness earns its place only for `◯⊥`, and is a separate rule if wanted.
* **No `◯` left rule.**  FRJ has none for any connective.

### 4.4 The standing test cells

    A ⇒ ◯A          must stay UNDERIVABLE   (Model.circ_of_force: the unit)
    ◯p ⇒ p          must be derivable       (Screen 1)
    ◯(p∨q) ⇒ ◯p∨◯q  must be derivable       (Screen 3)
    ◯⊥             refutable only via a fallible witness (Screen 2)
    [⊥] ⇒ p,  [p∧q] ⇒ p,  [p,p⊃q] ⇒ q       must stay UNDERIVABLE
                    (the three cells that refuted FRJO/ v3)

---

## 5. Soundness: what is proved, and what is not

**PROVED, and pinned with no axioms at all** — the six semantic
obligations, in `FRJLax/Modal.lean`:

| lemma | content |
|---|---|
| `circ_intro` | witness + above ⟹ `◯A` forced — the obligation of `⋈^p` |
| `not_force_circ` | no modal successor forces `A` ⟹ `◯A` fails |
| `not_force_circ_of_no_promise` | barren + `A` fails ⟹ `◯A` fails — the obligation of `◯∈` |
| `not_force_circ_of_above` | refutation of `◯A` descends along `R_i` |
| `circ_of_force` | the unit: `A` forces `◯A` |
| `circ_of_fallible_cone` | a fallible cone forces every `◯`-formula |

**NOT PROVED — OPEN.**  Theorem 3.1 for FRJ◯, `⊢_FRJ◯(G) G ⟹ G ∉ PLL`,
is **not** proved and must not be reported as proved.  What stands
between here and it is the whole soundness development, none of which is
built in `FRJLax/` yet:

1. `↦₀`, `↦`, `↦*` and **Lemma 3.5**, over the three-zone `Ĝ`;
2. the well-formedness lemma `Γ ⊆ Ĝ` (`zone_split` is its consumer and is
   proved; the lemma itself is not);
3. `Mod(D)` — the p-sequents-as-worlds construction, now also supplying
   `R_m` from the promise declarations and `Fal` from the fallible
   witnesses, with the poset, transitivity and `R_m ⊆ R_i` obligations;
4. **Lemma 3.10** — the main induction on height with the secondary
   induction on `|H|`, extended with (P4): `◯Y ∈ Γ^◯ ⟹ σ ⊩ ◯Y`, whose
   proof is `circ_intro` with the witness from (J5) and the above-half
   from the same closure argument (P2) uses;
5. **Theorem 3.12** and **Theorem 3.1**.

Item 3 is the bulk, and item 4 is where a mis-designed rule would show
up.  The rule-local obligations above are exactly the leaves that item 4
consumes, which is why they were proved first.

---

## 6. What is asked of Matthew

1. **Sign off, amend or reject `◯∈` and `⋈^p`** as stated in §4, with
   their side conditions.  Nothing is implemented in the rule table yet:
   `FRJLax/Calculus.lean` still has the ten `◯`-free rules only.
2. The three-zone `Ĝ` is already implemented, since it is settled by two
   independent screens and the `◯`-free layer is unaffected.  Say if that
   was premature.
3. Whether `◯⊥` and fallible witnesses are wanted in this pass at all, or
   deferred: they are a separate rule and the `◯`-free corpus does not
   exercise them.
