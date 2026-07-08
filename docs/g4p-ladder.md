# The G4iLL′ admissibility ladder: state and design (2026-07-08)

Target: contraction and cut admissible in `G4p`, then completeness
`SC → G4p` by plain induction on `SCh` — all structural, no
well-founded sequent order.

## Proven (sorry-free)

| brick | file | method |
|---|---|---|
| exchange, weakening, `G4 ⊆ G4p`, `toSC` | `PLLG4P` | structural |
| master inversion (9 inversions), `impR_inv` | `PLLG4PInv` | one traversal |
| identity `A, Γ ⊢ A`, telescoped MP | `PLLG4PAdm` | weight induction |
| `Spine` + lifts | `PLLG4PStr` | trivial |
| **`weak_Imp`** (D–N 4.1, *all* antecedents incl. `◯`) | `PLLG4PStr` | induction on the first derivation; each ending feeds one L⊃-rule |
| **`impLImp_dup`** (D–N 4.2, folded form) | `PLLG4PStr` | structural; principal case closed by `weak_Imp` |

## Remaining bricks and their true dependency graph

Notation: `S(F)` = self-absorbing weak implication for `F = ◯D→B`
(`Γ,F ⇒ ◯D` and `Γ,B ⇒ E` give `Γ,F ⇒ E`); `C(A)` = contraction;
`K(A)` = additive cut; `ABS(◯X)`/`OStr` = absorb/strengthen a boxed
hypothesis (`◯X ⇒ X` in context).

Verified case analyses (on paper, twice):

* `S(F)`: all cases close *structurally* — the kept implication is
  exactly what the `L◯→′`/`laxL` cases need — **except** a right rule
  at the spine's non-`◯` bottom `b`, which closes via `K(b)` with
  `w(b) < w(F)` (right premise manufactured from `identity` +
  `Spine.lift` + `weak_Imp`).  So `S(F) ⇐ K(<w F)`.
* `C(A)`: IPC-principal cases via inversions + `impLImp_dup` +
  smaller `C` (Dyckhoff–Negri verbatim).  Both `◯`-principal cases and
  both `F`-principal-with-spectator cases close via `S(w A)` and
  `K(w A)` — same weight, so `C(w) ⇐ S(w), K(w), C(<w)`.
* `K(A)`: principal ∧/∨/⊃/`R◯→` cases: smaller cuts only (additive —
  no context merging, no contraction except an easy standalone
  atom-contraction at the `init` case).  **The knot**: cut formula
  principal-right in `L◯→′`, and more generally pushing a cut into
  `L◯→′`'s first premise, requires transporting the *left* derivation
  across a box-opening (`Γ ∋ ◯X` versus premise context `∋ X`) — i.e.
  `OStr` applied to the left derivation.  And `OStr`'s own `L◯→′` case
  *is* an instance of `S(F₂)` for a context implication `F₂` of
  **unrelated weight**.  So the naive stratification
  `K(w) ⇐ C(<w), OStr ⇐ S(arbitrary) ⇐ K(<arbitrary)` is not obviously
  well-founded: the `F₂`-population comes from contexts, which the kept
  implication keeps re-supplying.

## Candidate resolutions (in preference order)

1. **Height-index the calculus** (`G4pH : Nat → …`, the `SCh` pattern
   already used in this repo): port perm/weaken/inversions
   height-preservingly, then run the classical
   (weight, height/level)-lexicographic inductions.  This gives the
   parametric cut cases for free, but the `OStr`-inside-cut transport
   is *still* not height-preserving (its `S`-uses go through `K`), so
   heights alone do not cut the knot — they only clean up the
   push-cases.  Worth doing regardless if 2 fails.
2. **Subformula-bounded joint induction**: all formulas ever passed to
   `S`/`C`/`K`/`OStr` in a ladder run lie in the subformula closure of
   the original inputs; the `F₂`-chains consumed by `S` strictly
   descend in `K`-weight *within each branch* (`S(F₂)` only spawns
   `K(b)` for `b` a proper subformula of `F₂`).  A candidate global
   measure: the *multiset of weights of all cut/self/contraction
   obligations*, under Dershowitz–Manna — each ladder step replaces an
   obligation by finitely many strictly lighter ones **except** the
   `K → OStr → S(F₂)` step, which must be shown to consume something
   else (the box `◯X` that `OStr` opens — a Bílková-flavoured
   component).  This is where the remaining design work is.
3. **Avoid `OStr` inside `K`** by changing the cut statement to build
   in box-transport ("cut under a stack of openings":
   from `Γ ⊢ A` and `A :: openings(Γ) ⊢ C` conclude `openings(Γ) ⊢ C`)
   — a `⊗`-flavoured strengthening imitating G4iSLt's `open_boxes_R`,
   which is what made *their* cut go through.  Needs care to state so
   that it is provable for single-box openings.

The incompleteness discovery means none of this has a published
blueprint — G4iSLt's escape (⊗-opening + Löb diagonal) is structurally
unavailable for lax.  Next session: attempt 2, falling back to 3+1.

## After the ladder

Completeness `SC → G4p` is then a plain induction on `SCh` (`impL` via
`K` + MP; `laxL` via `ABS`/`C`; the rest via inversions/identity), and
`G4p ≡ SC ≡ PLL` follows with `toSC`.  Termination of `G4p`
(decidability, F&M Thm 2.8) is a separate question: every rule premise
except `L◯→′`'s first is DM-decreasing; that premise strictly decreases
the *boxed-antecedent multiset* while trading the succedent for `◯φ` —
a lex/Bílková combination or a strategy-completeness argument is
needed, and weak termination + a complete strategy suffices.
