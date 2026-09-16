# Reassessment, 2026-08-16 21:40 — `FRJLax/` against the finished `FRJ/`

*Matthew: "the definitions of FRJ have changed since you began … later
parts of the making-all-constructive process changed earlier parts of the
system than I had anticipated.  Please re-read the handoff and plan and
fidelity docs and reassess this development and make any necessary
changes to keep faithful to the ◯-free theory so far developed."*

## What changed under this development

`frj-lax` moved from `cc6ed4b` to `7393ed1` while `FRJLax/` was being
built.  `FRJ/` is now **finished**: nine modules, `lake build FRJ` green,
sorry-free, `[propext, Quot.sound]` throughout with the pins
`#guard_msgs`-guarded in `FRJ/Audit.lean`.  The handoff was rewritten
front to back — its §1 now reads "**Extend** the finished FRJ(G)
development with the lax modality ◯.  Not rebuild it" — and its staging
inverted: W1 is now "add ◯ to `Form` and to forcing, everything ◯-free
must still build", not "reproduce §2".

Three changes to the ◯-free theory land directly on this development.

### 1. Canonical contexts (`nf`) — the one that supersedes my rule table

    nf G l = (gHat G).filter (· ∈ l)

with `nf_ext`: two contexts with the same members inside `Ĝ` are
*literally the same list*.  The handoff's §4.3 states the reason and the
obligation: "any new rule with a COMPUTED context in its conclusion must
write it as `nf G (...)` … Design for this from the first rule, not
afterwards."

`FRJLax/Calculus.lean` solves the same problem the other way, by never
computing an index at all: every conclusion context enters through the
membership-equality hypothesis `≐`.  That is a real solution — the
argument `nf` exists to defeat ("same members implies same derivations is
false, because `Ax^I` pins its own zone") does not arise when the zone is
not pinned but constrained up to membership — but it is **a second design
for a problem the ◯-free theory has already settled**, and it is exactly
the duplication I flagged earlier in this session.

**Verdict: superseded.**  Not wrong; redundant, and redundant in the way
that costs most.

### 2. The constructive divergence — and my statement is on the wrong side

    frj_iff_countermodel : Provable G ↔ ∃ K, ¬ K.valid G     -- choice-free
    frj_iff_not_IPL      : Provable G ↔ ¬ IPL G              -- the paper's,
                                                             -- and the ONLY
                                                             -- place choice enters

because `¬ ∀ K, K.valid G → ∃ K, ¬ K.valid G` is not constructively
valid.  The handoff: "**Keep both shapes when you extend to ◯, and keep
the modal results on the countermodel side of that line.**"

`FRJLax/Circ.lean` states `not_PLL_G : ¬ PLL G` — the classical side, and
the side that would drag `Classical.choice` into the modal results.
**This is a genuine defect in what I built**, independent of where the
code lives, and it is fixed below.

### 3. `Kripke` is the carrier, and `◯` extends it in place

`FRJ/Basic.lean`'s `Kripke` already carries `elems`/`complete`,
`decEq`/`decLe`/`decV` and hence `decForce`.  Adding ◯ means adding `Rm`
and `Fal` **to that structure**, and the modal clause to `force` and
`decForce` — which is W1 of the new staging, and which by design breaks
whichever of the eight modules are modality-sensitive, telling us where
the work is.  `FRJLax/Model.lean` made that same extension in a parallel
namespace, so it tells us nothing about `FRJ/`.

## What survives, and where it goes

| Artefact | Verdict |
|---|---|
| the source reading: arXiv ≠ journal, the numbering table | **kept** — already in `docs/frj-lax-plan.md` §1 and the renumbered `docs/frj-fidelity.md` |
| the three-zone `Ĝ = Ĝ_at ∪ Ĝ_imp ∪ Ĝ_◯`, with its two independent justifications | **kept, and must now be applied to `FRJ/`'s `gHat`** — note this changes `nf`, hence every canonical context, hence `wfR`/`wfI`.  A W1 change, before any rule |
| the six modal semantic lemmas (`circ_intro`, `not_force_circ`, `not_force_circ_of_no_promise`, `not_force_circ_of_above`, `circ_of_force`, `circ_of_fallible_cone`) | **kept** — they are about forcing and port to `Kripke` once it has `Rm`/`Fal` |
| the three screens (selective witness; per-world witness; the corrected fallible-cone lemma) | **kept** — models are small and rebuild on `Kripke` |
| the rule design: barrenness, the promise join, the fallible promise | **kept as a design**, to be re-expressed with `nf`-canonical conclusions |
| the `◯p ⊃ p` gap finding | **kept** — the sharpest thing this development produced, and encoding-independent |
| `FRJLax/Core.lean`, `Calculus.lean`, `Paper.lean`, `Circ.lean` | **superseded** — archived, not deleted |

The gap finding, restated so it survives the archiving: *the countermodel
for `◯p ⊃ p` needs a world forcing `p`; there `◯p` holds by the unit,
hence `G` holds, and `⊥ ∉ Sf^R(G)`, so that world refutes **nothing** in
`Sf^R(G)`.  Every world of `Mod(D)` is a p-sequent and so refutes its own
goal.  The witness therefore cannot be a p-sequent: it is a fallible
world.*  That argument is about `Mod(D)` and `Sf^R`, which `FRJ/` has, so
it transfers verbatim.

## Changes made

1. `FRJLax/` archived to `Archive/FRJLax-parallel/` with its lakefile
   entry removed.  Superseded, not deleted, per the repo convention.
2. The constructive-divergence defect recorded here and not carried
   forward: when the modal results are restated on `FRJ/`, they go on the
   **countermodel side** — `∃ K, ¬ K.valid G`, or better, the exhibited
   model — never `¬ IPL G`.
3. `docs/frjlax-modal-rules.md` keeps the rule design and the screens; its
   §4 figures must be re-expressed with `nf`-canonical conclusion
   contexts before implementation.

## What W1 now is

Per the rewritten handoff, and in this order:

1. `Form` gains `circ`; `size`, `sf`, `sfPos`/`sfNeg` gain their clauses.
2. `Kripke` gains `Rm`, `Fal` and their conditions; `force` gains the
   modal clause; `decForce` gains it too, so forcing stays decidable.
3. `gHat` gains `Ĝ_◯` — and this is the change that reaches furthest
   back, since `nf` filters against `gHat`.
4. The eight modules are rebuilt, and whichever break are the
   modality-sensitive ones.  `FRJ/Audit.lean`'s pins must come out
   unchanged.

Only then the rules.
