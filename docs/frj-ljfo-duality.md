# What the FRJ◯/LJF◯ "duality" is, and whether it can carry completeness

Investigation, 2026-08-29, at Matthew's request.  Claims are graded:
PROVED = in the repo, kernel-checked; OBSERVED = read off the two rule
tables, not mechanised; OPEN = neither.

## 1. What the source actually says

`docs/frjo-calculus-plan.md` §0 records the CEUR abstract
(Fiorentini–Ferrari, Vol-2756 paper 27) as: *"a FAILED refutation-search's
saturated database is a proof certificate for the goal, read back through
a backtracking-free backward calculus `Gbu(G)`"*, and
`docs/frj-lax-plan.md` states the theorem as

    ⊢_Gbu(G) G   iff   ⊬_FRJ(G) G                          (Theorem 5.13)

**The direction that does the work is `⊬_FRJ G → ⊢_Gbu G`**: run the
REFUTATION search to saturation; if the goal never appears, read a PROOF
off the database.  Contraposed against completeness of `Gbu` for IPC this
is completeness of FRJ.  The other direction is just soundness of FRJ.

This corrects the 2026-08-29 audit, which proposed the opposite traffic
(failed LJF◯ proof-search ⟹ FRJ derivation).  Both directions yield
FRJ-completeness; the paper's is the one with a mechanised engine already
in this repo (`saturateO`, `V.vOps`, forward subsumption).

**`Gbu(G)` is not LJF◯.**  It is a purpose-built backtracking-free
backward calculus.  LJF◯ is a *focused* calculus, and focusing is also a
backtracking-reduction discipline, so LJF◯ is a plausible substitute —
but that is an assumption to discharge, not a fact.  (OPEN.)

## 2. The duality as CALCULI — what really corresponds

The two rule tables line up De Morgan-wise on every connective.
(OBSERVED, from `LaxLogic/LJFOCore.lean` and `FRJ/CalculusV.lean`.)

| | LJF◯ (proof) | FRJ(V) (refutation) |
|---|---|---|
| atom | `init`: `↑a ∈ Γ` | `axR a`: context is `Ĝ_at \ {a}` — `a ∉ Γ` |
| `∧` right | `andR`: prove BOTH conjuncts | `andR1`/`andR2`: refute ONE |
| `∨` right | `or1`/`or2`: prove ONE disjunct | `orI`: refute BOTH |
| `⊃` right | `impR`: move `Q` into `Ω` | `impIn` (`Clo Γ A`) / `impNotIn` |
| `∨` left | `orL`: both branches | the `Υ` zone of the joins |
| `◯` right | `circR`: switch the judgment to `.lax` | `circIn` with the TAG |
| `◯` left | `circL`: lax-only (F&M's SC condition) | `circNotIn` with the TAG |
| coercion | `laxOf : Stab Γ .tru P → Stab Γ .lax P` | `tOK`'s `t = .barren ∨ …` — a barren tag serves a chain demand |

Two structural readings fall out.

**(a) The JOIN has no rule-level dual.**  A proof picks ONE rule
instance; a refutation must defeat ALL of them.  So `⋈^At`/`⋈^∨`/`⋈^◯`
are not dual to any LJF◯ rule — they are dual to the *choice* in proof
search, i.e. to `succs`.  `LJFOSearch.lean` makes this explicit:

    Inst s := Σ' ps : List LSeq, (ps ∈ succs s) ×' Prems ps
    succs_complete : ∀ s, s.holds → Inst s
    search_sound   : search n s = true → s.holds
    search_complete: s.holds → Σ' n, search n s = true

`s.holds` is `∃ instance, ∀ premise`; its negation is
`∀ instance, ∃ premise` — and THAT tree is what a refutation is.  This is
why the paper's duality "costs a second calculus and a search procedure"
(`docs/frj-lax-plan.md`): the correspondence lives at the level of the
search space, not as a bijection on derivations.

**(b) The modal side conditions weaken/strengthen dually.**  Proving `◯P`
WEAKENS the judgment (`tru ⇝ lax`, more is provable); refuting `◯Z`
STRENGTHENS the certificate (the tag asserts the whole root cone refutes
`Z`).  `laxOf` is the proof-side weakening; `tOK`'s barren-serves-chain
disjunction is the refutation-side counterpart.  That much is a genuine
correspondence, not a slogan.

## 3. The asymmetry, and why it matters right now

LJF◯'s lax phase is a **single Boolean flag** `JD = tru | lax`, carried
unchanged through `impR`/`andR`/`circR` while the goal changes.  FRJ's
tag is a **flag plus a formula** (`chain D`) plus a side condition
(`Covers Γ D Z`) re-checked at every propagation step.

If the duality is exact, one side is doing work the other does not need.
The proof side manages with a flag because the goal is already in the
sequent; the refutation side re-derives, via `Covers`, which formula the
pledge still covers.

This is not idle: **the formula-indexed tag is exactly what emptied
`TagLeafV` today** (`wip/tagleaf_refute.lean`).  `not_clo_of_tagged`
(PROVED) says a row whose tag satisfies the `◯∈`/`◯∉` condition at `C`
can retain neither `C` nor `◯C` — and that is a statement about the tag,
with no analogue on the LJF◯ side.  So the working hypothesis worth
testing is:

> **the tag is stronger than duality requires**, and a flag-only pledge
> (or a pledge indexed by the sequent's own goal) would suffice for
> soundness while leaving the retention the completeness recursion needs.

(OPEN.  It is a soundness question about `◯∈`, answerable by re-running
the `tag_cone` argument with a weaker tag, and per the V5 licence rule
(`docs/refat-plan.md`) it needs a kernel-checked separating cell before
any calculus round.)

## 4. What a duality proof would need, and what exists

Target: `⊬_FRJV G → ⊢_{LJF◯} G`, then `bridge_iff` to PLL, then
contrapose for completeness.

| ingredient | status |
|---|---|
| FRJV forward engine with subsumption | PROVED/BUILT (`FRJ/Search/Core.lean`, `V.vOps`) |
| its saturation terminates (no `rounds`/`maxRS`/`lamCap` cap binding) | OPEN — the probe prints the caps precisely because this is not settled |
| LJF◯ search sound + complete | PROVED (`search_sound`, `search_complete`) on branch `claude/t1-lax-logic-refutation-37c0bf`, unmerged |
| uniform fuel bound for LJF◯ search | OPEN — the file's own comment calls it "the pigeonhole layer", the `PLLG4Dec` analogue |
| `LJF◯ ⊢ φ ↔ PLL ⊢ φ` | PROVED (`bridge_iff`), same unmerged branch |
| read-back: saturated FRJV database with no goal row ⟹ LJF◯ derivation | OPEN — this is the whole theorem |

Two things recommend it over the seven semantic routes: the read-back is
**syntactic** (no `Λ*`, no forcing, so the local/global mismatch that
killed the minimal-model line cannot arise in the same form), and the
termination measures it needs are the focusing weights that LJF◯ already
carries (`LJFOHeight`, `LJFOUniverse`, `LJFOFuel`).

Two things count against it: the read-back is exactly the content of the
theorem (no free lunch — §1), and it inherits BOTH open termination
questions above.

## 5. First move, if this is taken up

Not the read-back.  Settle §3 first: is the formula-indexed tag needed
for `◯∈`'s soundness, or would the flag its dual uses suffice?  That is
a small, self-contained soundness question, it is the one place the two
calculi visibly disagree, and it is where the completeness campaign has
actually been failing.
