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

## Design revision 2 (2026-07-08, evening): the knot dissolves

Re-deriving the `K`-cases exposed that every appeal to `OStr`/`S`
inside cut has the same root: a rule premise whose context has *lost*
material (`◯χ` traded for `χ`) that the transported derivation still
needs.  The fix is to stop consuming boxes altogether — make **both**
box rules keep their box:

    Γ, ◯χ, χ ⇒ ◯B                            Γ, ◯χ, ◯φ→ψ, χ ⇒ ◯φ    Γ, ◯χ, ψ ⇒ Δ
    -------------- laxL″                     ------------------------------------- L◯→″
    Γ, ◯χ ⇒ ◯B                                        Γ, ◯χ, ◯φ→ψ ⇒ Δ

(`laxL″` is *exactly* G3iLL's `L◯`; `L◯→″` keeps both the implication
and the box in its first premise.)  Consequences, each checked at the
case level:

1. boxed-vs-unboxed absorption never arises: contraction's
   `◯`-principal cases are purely structural (the two copies always
   travel together — the minimal form of the iSL `⊗`-insight);
2. `OStr`/`ABS` drop out of the ladder entirely (the completeness
   simulation of `SC.laxL` becomes a direct `laxL″` rebuild);
3. every rule's premise context now contains the conclusion context
   minus at most a *decomposed* principal — so cut's parametric
   transports are inversions (for decomposed principals) or pure
   weakenings (box rules only add), never a box-crossing;
4. the dependency graph is acyclic by weight levels:
   `atomC → K_w (⇐ K_{<w}) → S_w (⇐ K_{<w}) → C_w (⇐ S_w, C_{<w})`;
5. remaining cost: `K`'s principal-left recursions transport the right
   derivation by weakening, which a `Prop`-valued structural induction
   cannot absorb — so the calculus gets a **height index**
   (`G4h : Nat → …` with `G4p″ := ∃ n, G4h n …`, the repo's own
   `SCh`/`SC` pattern) and height-preserving `perm`/`weaken`/`Inv`,
   after which `K` and `C` run on the classical
   (weight, height)-lexicographic measures.

`G4p″` has a tidy description: **G3iLL plus Dyckhoff's implication
splitting, with maximal retention in the two lax-implication rules.**
Termination is unaffected as a deferral (naive search now loops even
more freely, but decidability was always a separate discipline —
Bílková order or strategy-bounded search on the cut-free system).

## Superseded candidate resolutions (kept for the record)

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

## Design revision 3 (2026-07-09): `R◯→` keeps its context — contraction lands, cut-free

Writing the general-contraction case table *in Lean* exposed a case the
revision-2 paper analysis had missed: a doubled `◯φ→ψ` whose visible
copy is fired by `R◯→` (old premise 1 `Δ ⇒ φ` — the rule *consumes*
the implication).  The inverted premises `ψ,Γ ⇒ φ` and `ψ,Γ ⇒ E` do
**not** suffice to rebuild `◯φ→ψ,Γ ⇒ E`: with `j = id`, `φ := p`,
`ψ := p∧q`, `E := q` the required inference fails in a Heyting algebra
with nucleus — no proof was being overlooked, the rule shape itself was
the obstacle (with the consuming rule, this case genuinely needs the
self-absorption lemma `S`, as the pre-revision analysis had said).

Fix, same medicine as revision 2: `R◯→″`'s first premise keeps the
whole conclusion context — G3's `L⊃` premise-1 discipline:

    Γ, ◯φ→ψ ⇒ φ    Γ, ψ ⇒ Δ
    ------------------------ R◯→″
    Γ, ◯φ→ψ ⇒ Δ

Sound (a weakening of the old premise), `toSC` *simplifies* (premise 1
is already G3-shaped), and the whole `G4h` tower re-compiled after six
one-line edits.  With it:

* **Contraction is proved, cut-free** (`PLLG4HCtr.lean`,
  `G4c.contract`): outer weight induction, inner structural induction.
  Principal cases: inversion of the surviving copy + strictly lighter
  contractions (∧, ∨, `p⊃`, `⊥⊃`, `∧⊃`, `∨⊃`); `⊃⊃` by the
  Dyckhoff–Negri recipe (`impLImp_dup`, three lighter contractions,
  re-abstraction); all three lax rules close by the *inner* induction
  because their premises now carry both copies.  `S` has dropped out of
  contraction entirely.
* The ladder reorders to the classical Dyckhoff–Negri shape:
  `atomC → C (cut-free) → K(w) (⇐ K(<w), C, exfalso, cut_atom) →
  completeness`.
* `K`'s case table after re-tabulation under revision 3 — two former
  hard spots and one still open:
  1. `⊃⊃` parametric-right, premise-1 transport (the residue `B→D` is
     not an inversion piece) — **solved**: cut at the enlarged context,
     then `impR_inv` + `impLImp_dup` + `C` (now closed) + `impR`
     re-abstraction.
  2. cut formula principal-right in `R◯→″` — **now classical**:
     premise 1 keeps the cut formula, so a structural cut cleans it,
     then two strictly-smaller-weight cuts finish.
  3. **open**: cut formula `◯X` serving as the *box witness* `hX` of an
     `L◯→″` instance whose implication `F₂` has unrelated weight — the
     self-absorption flavour survives exactly here and nowhere else.
     Candidate escapes: (a) an `S`-interleave under a
     subformula-bounded measure; (b) generalising `L◯→″`'s witness side
     condition (derived box instead of present box); (c) a cut
     statement carrying a box-witness oracle.  Next design session.

## After the ladder

Completeness `SC → G4p` is then a plain induction on `SCh` (`impL` via
`K` + MP; `laxL` via `ABS`/`C`; the rest via inversions/identity), and
`G4p ≡ SC ≡ PLL` follows with `toSC`.  Termination of `G4p`
(decidability, F&M Thm 2.8) is a separate question: every rule premise
except `L◯→′`'s first is DM-decreasing; that premise strictly decreases
the *boxed-antecedent multiset* while trading the succedent for `◯φ` —
a lex/Bílková combination or a strategy-completeness argument is
needed, and weak termination + a complete strategy suffices.
