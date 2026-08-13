# (b) The rejection-calculus literature, read properly — and the first screen

*2026-08-13.  Follows (a) (`BiLax/Internal.lean`).  Literature research
by a dedicated agent with explicit VERIFIED/REPORTED confidence marks;
screen: `wip/reject_screen.lean`, `lean_exe rejscreen`, output
`wip/reject_screen_out.txt`.*

## 0. The headline: my proposed target was also wrong, twice over

I proposed "read Skura's IPC refutation system properly and screen
whether its rules extend to `◯` via `◯∃`".  The reading kills both
halves of that:

1. **Skura's system is NOT analytic**, so it is the wrong template.
   Verbatim, the IPC system is: one refutation axiom `⊣ p`; `r_sb`
   (reverse substitution); `r_mp` (`⊢ α→β, ⊣ β / ⊣ α`); and the
   infinite family `r_n` reversing the generalized disjunction
   property.  `r_mp` requires *guessing* `β` and *proving* `α→β` in
   IPC; `r_sb` requires guessing a substitution.  Goranko–Skura say of
   the generic modal version, in their own words, that deriving `⊣φ`
   "requires guessing the falsifying substitution σ, which amounts to
   finding a refuting valuation for φ" — i.e. **the Łukasiewicz-style
   route hides model search inside a side condition.**  It yields a
   certificate, not a search procedure.  That is no better than
   `refute?`, which we already have.
2. **Nothing in the literature bases a rejection calculus on
   co-implication.**  The semantic fact (`A ⤙ B` satisfiable iff
   `A ⊬ B`) is immediate from Rauszer's clause and is exactly (a), but
   the agent found no source using it as the *basis* of a rejection
   system.  The closest is Goré–Postniece's combined derivation /
   antisequent calculus for BiInt, where the antisequent judgement
   `σ(S Γ ⊳ ∆ P) = ⊭ τ(…)` *is* a falsifiability judgement — an
   architecture, not a rejection calculus driven by `⤙`.

So the bi-lax route's original motivation does not survive contact
with the literature in the form I gave it.  What survives is the
*architecture* claim (§3) and the internalisation (a).

## 1. The right template (VERIFIED)

The analytic tradition, not the Łukasiewicz one:

* **`FRJ(G)`** — Fiorentini & Ferrari, *ACM TOCL* 21(3) art. 22, 2020
  (TABLEAUX 2017, LNCS 10501).  An unprovability calculus for IPC,
  **parametrised by the goal `G`**: all sequents are built from
  left/right subformulas of `G`, so the sequent set is FINITE; only
  right-introduction rules (left rules absorbed into a closure
  operator); the Finite Rule Property; refutation heights quadratic in
  `|G|`; and a Kripke countermodel of minimal height is EXTRACTED from
  the refutation.  This is the "positive derivation object plus
  certificate extraction" shape, and it is finitely presentable in
  Lean.
* **`CRIP`** — Pinto & Dyckhoff 1995, over the contraction-free `LJT`:
  for any `Γ, φ`, either `Γ ⇒ φ` is derivable in `LJT` or `Γ ⇏ φ` is
  refutable in `CRIP`.
* **Modal layer**: Goranko's MIX rules (*Studia Logica* 53(2), 1994)
  — the only template for adding a modality to an analytic anti-sequent
  calculus — and **Fiorentini's `RS4`** (*JLC* 25(1), 2015), a
  refutation calculus for S4 **with the subformula property**, built by
  complementing a contraction-free `GS4`.  That last is the existence
  proof that the combination is achievable for a transitive modality,
  and its method — *start from your own contraction-free calculus and
  complement it* — is directly available to us, since we have the
  G4-family calculi and `LJF◯`.

## 2. The gap (a genuine negative finding)

**No refutation calculus exists for ANY intuitionistic modal logic** —
not `IK`, not `CK`, not intuitionistic S4, not monotone modal logics —
and none for lax logic.  The most recent comprehensive survey
(Goranko–Pulcini–Skura, ~90 references) has a section on "refutation
systems for intuitionistic and modal logics" in which every entry is
either intuitionistic-without-modality or modal-over-classical.  The
nearest recent work, Gao–Girlando–Olivetti 2025 on intuitionistic K,
is countermodel extraction from a FAILED derivation — precisely the
thing this project is trying to move away from.

So a rejection calculus for PLL is **research, not porting**.

## 3. The screen (the empirical half of (b))

The literature's own warning is the Kreisel–Putnam trap: a rejection
rule must be Ł-sound for `L` **and Ł-UNSOUND for every proper
extension** — Łukasiewicz's Disjunction Rule for IPC failed exactly
here (it is sound for Kreisel–Putnam logic ⊋ IPC).  That is testable
today by this repo's own method, so I tested it.

`lean_exe rejscreen`: 36,296 well-formed confluent frames (≤ 3
worlds) as the refuting battery, 22 corpus formulas (the catalogue's
crank-≤6 representatives plus p-carrying cells), 13 of them certified
non-theorems.  Verdicts certificate-only: KILL = every premise refuted
by a battery model while the conclusion is PROVED by the searcher.

| rule | shape | Ł-soundness for PLL | discriminates PCLL? |
|---|---|---|---|
| R1 | `⊣φ / ⊣◯φ` | no violation (13 cells) | **NO WITNESS** |
| R2 | `⊣◯φ / ⊣φ` | no violation (13 cells) | **NO WITNESS** |
| R3 | `⊣φ / ⊣(◯φ ⊃ φ)` | **6 CERTIFIED VIOLATIONS — DEAD** | 1 witness |
| R4 | `⊣φ / ⊣¬¬◯φ` | **5 CERTIFIED VIOLATIONS — DEAD** | NO WITNESS |
| R5 | `⊣φ,⊣ψ / ⊣◯(φ∨ψ)` | no violation (13 cells) | **NO WITNESS** |

**R3 and R4 are dead** — certified: e.g. `◯p` is a non-theorem while
`◯◯p ⊃ ◯p` is provable, and `w1` is a non-theorem while `¬¬◯w1` is
provable.  Two of five natural candidates fall to the first screen,
which is the point of screening first.

**R1, R2, R5 survive Ł-soundness but show no PCLL-discrimination
witness** — the Kreisel–Putnam danger sign, reported as such and not
passed.  R5 is the lax analogue of the very rule that killed
Łukasiewicz's conjecture, so its silence here is the expected shape of
trouble rather than a surprise.

**A methodological finding from the screen's own failure — with a
CORRECTION (2026-08-13, Matthew).**  The first run used only the
closed corpus and reported "NO WITNESS" for *every* rule including the
dead ones.  My first diagnosis said this was because "on the closed
fragment PCLL ≈ PLL".  **That is false, and this repo refutes it**:
distribution's four merges at crank ≤ 7 (`q12 ≡ q9`, `◯q9 ≡ q9`,
`◯q11 ≡ q11`, `w15 ≡ w16 ≡ w17 ≡ w18`) are each a STRICT separation —
pairs interderivable in PCLL and provably not in PLL, kernel-pinned.
So PLL ⊊ PCLL on the closed fragment, witnessed.  The merges are
SPARSE (four out of 680 classification cells), which is a different
claim entirely.

The true reason for the empty discrimination column: the rule
INSTANCES generated from my corpus (`◯φ`, `φ`, `◯φ ⊃ φ`, `¬¬◯φ`)
essentially never land on a distribution-sensitive formula — the four
merge sites are specific `∨`-shaped classes, and none of the rule
shapes maps the corpus onto them.  The screen was under-powered
because of the INSTANTIATION, not because of the fragment.  Adding
p-carrying cells fixed it incidentally (R3's witness is
`◯p ∨ ◯q`) but the principled fix is to instantiate rules AT the known
merge sites.  Any future extension screening should do both.

## 4. What to do next, if this thread continues

1. **Do not build on Skura.**  Build on `FRJ(G)` + Fiorentini's `RS4`
   method: complement one of our own contraction-free calculi.
2. **Expect a hybrid rule for `◯`.**  PLL's clause is `w ⊩ ◯A` iff
   `∀v ≥ w ∃u: v Rm u ∧ u ⊩ A`.  Refuting `◯A` needs a `v` with NO
   successor forcing `A` — an ∃∀ pattern whose inner universal is a
   *validity* statement, which no single antisequent premise expresses.
   So the `◯`-right rule will need a derivation-shaped premise
   alongside a refutation premise (Goranko's hybrid
   deduction–refutation systems; Goré–Postniece's `⊲/⊳`
   architecture).  A purely refutational calculus is unlikely to close.
3. **A concrete route worth checking** (the agent's own observation,
   not from the literature, and unverified): F&M's context-completeness
   gives `PLL ⊢ φ` iff `IPL ⊢ φ^C` for every standard constraint `C`.
   Negated: **`PLL ⊬ φ` iff there is a SINGLE constraint `C` with
   `IPL ⊬ φ^C`** — a rejection statement with a finite witness that
   composes with `FRJ(G)` (certificate = a constraint plus an IPC
   refutation).  We have that theorem mechanised.  The effective bound
   on `C` needs checking.
4. **Every candidate `◯`-rule goes through `rejscreen` first**, with
   p-carrying cells, before any proof is scoped.
5. **Idempotence puts PLL in the "transitive" class**, where the
   field's own experience is that refutation rules need normal forms
   and a rank measure (same shape as the DM-order obligation in
   `CimpAnt`); and Goranko's `Alt_n` argument shows rule arity cannot
   be bounded, so the calculus will be a rule schema over lists of
   premises rather than a fixed finite inductive.

## 5. Honest bottom line on the bi-lax investment

The internalisation (a) is real and now machine-checked, and it is the
correct statement of what `⤙` buys.  But the literature says
co-implication is **not** the vehicle anyone has used to build a
rejection calculus, and (a)'s ∃ is still over *models* — a model is
not a syntactic object.  So the bi-lax development is, at present,
justified as: the semantics against which a future rejection calculus
would be proved complete, plus one clean internalisation theorem.  It
is **not** justified as the disproof engine, and rounds 1–2 are
corrected accordingly.  Whether to continue is a judgement call about
appetite for genuinely new proof theory (item 4.2's hybrid rule is the
crux), and it should be made explicitly rather than by momentum.
