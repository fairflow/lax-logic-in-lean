import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.PLLLaxInfinite
import wip.negFour
import wip.rnClassify
import wip.gapWidth

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The variable-free fragment" =>

`RN(◯,∅)` is the *variable-free* fragment of PLL: formulas built from `⊥`,
the connectives and `◯`, with no propositional variables at all, taken up to
interderivability.  The `∅` in the name is the empty set of variables.

It is *infinite*, and infinite in three independent ways — which is exactly
what distinguishes it from the classical Rieger–Nishimura lattice it is
named after.  Pure RN is the *one-variable* fragment of IPC: a ladder,
infinite in height but of width at most two, and drawable.  `RN(◯,∅)` has no
variables at all and is nonetheless infinite in height, in depth *and* in
width.  That is what makes it worth studying rather than tabulating.

What *is* finite, and what the Hasse diagram draws, is a scoped catalogue —
the ρ-order: 462 cells with the `⊬` side kernel-pinned by certificates and
the `⊢` side engine-certified, 22 representatives, 37 cover edges.  The
catalogue is a studied portion of the fragment, not the fragment.  Keeping
those two apart is the first thing to get right here, and the section
headings below are arranged to keep them apart.

Two abbreviations run through everything:

$$`a := ◯⊥ \qquad b := ◯¬◯⊥ \;\; (= ◯¬a)`

Sources are `RNDB/`, `docs/rho-structure.md` and `docs/rho-order.md`; the
conjectures recorded alongside the regularities there are deliberately not
repeated.

# The fragment is infinite

:::group "rn_infinitudes"
Three infinitudes, and a boundedness result that survives them.
:::

:::theorem "rn_infinite" (parent := "rn_infinitudes") (lean := "PLLND.LaxInfinite.closed_lax_infinite")
`RN(◯,∅)` is infinite: its `⊣⊢`-Lindenbaum quotient over variable-free PLL
formulas has infinitely many classes.  Reduced, sorry-free, to the
Rieger–Nishimura independence.

This is the result that says the fragment is a subject rather than a table.
Note what it does *not* need: no variables, and no appeal to a modality
beyond `◯⊥` and its negations.
:::

:::theorem "rn_bool_four" (parent := "rn_infinitudes") (lean := "PLLND.NegFour.neg_exactly_four")
Against those infinitudes, one sharp bound: for every variable-free `A`, the
negation $`¬A` is interderivable with one of $`⊥`, $`¬◯⊥`, $`¬¬◯⊥`, $`⊤`.
Since the regular elements are the image of $`¬`, the booleanization of
`RN(◯,∅)` has *exactly four* elements — and the result holds over an
arbitrary axiom set.

Set beside {uses "rn_infinite"}[], the two results bracket the closed
fragment from opposite sides.  `RN(◯,∅)` is infinite in height, in width
and in `◯`-depth, and has no floor, so no finite operation table can ever
close it; yet its regular elements, the image of double negation, form a
four-element Boolean algebra `⊥ < ¬◯⊥, ¬¬◯⊥ < ⊤`, over any axiom set.  The
infinity lives entirely in the non-regular part, the Rieger–Nishimura-style
ladder that `◯⊥` generates; the Boolean skeleton sees none of it.  That is
the shape a reader should carry: an infinite Heyting algebra whose
booleanization is the four-element one.
:::

# The shape of the catalogue

:::group "rn_shape"
Four verified regularities of the ρ-order catalogue, all
certificate-backed.  These are facts about the finite scoped portion, not
about the whole fragment.
:::

:::proposition "rn_graded" (parent := "rn_shape")
*Graded.*  Every cover edge spans exactly one rank.  The rank profile is
`1-2-2-3-5-5-3-1`, so the height is 7.

The Hasse diagram of the catalogue is `docs/rho-hasse-pll.svg`, and the
interactive explorer `docs/rn-explorer.html` draws the same order with the
certificate of every edge one click away.  The profile above is the
diagram's shadow; the diagram itself shows which classes are join-
irreducible, where the two rails (the Rieger–Nishimura ladder at `a` and
the modal rail from `◯¬a`) meet, and which covers are the `⊃`-classes.  The
diagram is generated from the database, never drawn by hand, so it is exactly
as trustworthy as the `ok` fields behind it.
:::

:::proposition "rn_irreducibles" (parent := "rn_shape")
*Lower-cover join-generation, in the poset sense.*  Every join-reducible
node is the poset least upper bound of its own lower covers, and there are
ten poset-join-irreducibles: $`⊥`, $`a`, $`¬a`, $`¬¬a`, $`b`, and
$`ρ_{12}`, $`ρ_{13}`, $`ρ_{14}`, $`ρ_{19}`, $`ρ_{20}`.  Every one of them
except the rails' atoms is an implication.

The distinction a first reading gets wrong, and which the source document
corrects explicitly: the poset least upper bound is *weaker* than the class
of the syntactic join.  Whether a node is interderivable with the join of
its lower covers is a separate question at each node.  It is certified at
$`ρ_{10}`, $`ρ_{15}` and $`ρ_{18}`, and open at three frontier cells.
:::

:::proposition "rn_cubes" (parent := "rn_shape")
*Two stacked cubes.*  The interval $`[ρ_4, ρ_{18}]` is exactly $`2^3` on the
atoms $`ρ_6`, $`ρ_7`, $`ρ_{14}`, and its identities are certified as *class*
identities rather than merely poset ones.  A dual cube sits over $`ρ_9` on
$`ρ_{12}`, $`ρ_{18}`, $`ρ_{20}`; three of its four vertices are new classes
and the fourth is open.
:::

:::proposition "rn_two_generators" (parent := "rn_shape")
*A two-generator presentation.*  Every one of the 22 representatives is a
Heyting-algebra term over $`a` and $`b` alone: *exactly two
`◯`-applications occur in the entire catalogue*, namely $`◯⊥` and
$`◯¬◯⊥`.

This is what makes the lattice finite and drawable, and it is exactly what
fails on extension.  The q-dictionary's $`q_{12} = ◯ρ_6` and
$`q_{13} = ◯ρ_{11}` sit *outside* the catalogue: they are the first depth-2
`◯`-generators.  See {uses "rn_extension"}[].
:::

# What is proved

:::group "rn_proved"
The two headline results, both mechanised.
:::

:::theorem "rn_classification" (parent := "rn_proved") (lean := "PLLND.RNEmbed.rn_classification, PLLND.RNEmbed.image_classification")
*The classification.*  For every `◯`-free formula $`A` whose only variable
is $`p`, the substitution $`A[p := ◯⊥]` is interderivable either with some
rung of the ladder or with $`⊤`.  So the image of $`h` is the rungs
together with $`⊤`.

The method deserves recording, because it is reusable.  Classify
*semantically* first: a function computes the ladder truth set of $`A` by
structural recursion through three fully tabulated Heyting operations on
up-set codes.  Then *derive* each of the 48 table rows — each hard side a
short modus-ponens composition through the Rieger–Nishimura recursion, each
easy side rung order through the decision procedure.  Then glue by
congruence in the structural induction.

A consequence worth advertising ahead of the theorem itself: the
classification doubles as a *decision procedure for interderivability* on
the whole `◯`-free one-variable fragment.
:::

:::theorem "rn_complement_infinite" (parent := "rn_proved") (lean := "PLLND.RNEmbed.complement_infinite_final")
*The complement of the image is infinite*, with no caveat: the boxed odd
rungs are pairwise distinct and all lie off the image.  Depends on
{uses "rn_classification"}[].
:::

:::theorem "rn_width" (parent := "rn_proved") (lean := "PLLND.RNEmbed.width_infinite, PLLND.RNEmbed.gap_incomparable")
*`RN(◯,∅)` has unbounded width* — one of the three infinitudes.  The family
$$`\mathrm{gap}\,k \;:=\; ◯(\mathrm{rnSub}\,(2k{+}1)) ⊃ \mathrm{rnSub}\,(2k{+}1)`
generalises the dictionary class $`q_8` level by level — $`\mathrm{gap}\,1`
is $`q_8` — and for $`k ≥ 2` the $`\mathrm{gap}\,k` are pairwise
`⊬`-incomparable.  That is an $`ℕ`-indexed antichain, so the width question
is settled, and settled the interesting way: infinite, not bounded.

This is the result that makes the lattice worth studying rather than
tabulating, and a single new semantic computation carries it, on an edged
lift with one extra constraint edge.
:::

# The database

:::group "rn_db"
Why the catalogue is a database and not a table in a document.
:::

:::definition "rn_claim" (parent := "rn_db")
`Claim`, `Evidence`, `Entry` and `Frontier` (`RNDB/Types.lean`), with the
un-sorriable `ok` field: *an entry cannot record a claim it has no
evidence for.*  That is the design decision that makes a machine-maintained
catalogue trustworthy, and it is why the `⊬` side of the 462-cell matrix can
be relied on rather than spot-checked.

A whole entry, as the database constructs it.  An interderivability entry
is built by `interdEntryR1 id a b h`, where `h : Interd a b` is the proof;
it fills four fields: `id`, the entry's identifier; `claim`, the pair
`⟨a, b, Rel.interd, none⟩` (the two formulas, the relation, and no scope,
since a positive relation needs none); `ev`, the evidence record, here
`Evidence.proof Engine.hand`, naming the instrument that settled it; and
`ok`, the proof that the claim is well-scoped, that the relation is
positive, and `h` itself.  The `ok` field is a proof term, so an entry
without evidence cannot be written down: the elaborator refuses it.  An
entry with a negative relation (`⊬`) carries instead a kernel-checked
countermodel certificate and the engine that found it, and its `ok` field
is that certificate's soundness theorem applied.  Nothing in the catalogue
is a table cell filled in by hand.
:::

:::definition "rn_order_def" (parent := "rn_db")
`Lt`, `Covers` and `CoversIn` (`RNDB/Order.lean`): the strict order and the
covering relation, the latter being what the Hasse diagram actually draws.

Covering is computed rather than read off the order because the order is
infinite and only finitely much of it is in the catalogue at any time.
`Covers a b` in the absolute sense would assert that nothing in the whole
fragment lies strictly between `a` and `b`, which no finite database can
know; `CoversIn S a b` asserts `a < b` and that no member of the named set
`S` lies strictly between, which the database can decide from its own
entries.  The Hasse diagram draws `CoversIn R`, the covering relative to the
current catalogue `R`, and a newly certified class can split an edge; that
is the intended behaviour, and it is why the diagram is regenerated with
the database rather than maintained.
:::

:::definition "rn_engines" (parent := "rn_db")
`Engine` and `DerivRule`: which instrument settled each cell, kept in the
record so a later reader can re-run it rather than trust it.
:::

# The open direction

:::proposition "rn_extension" (parent := "rn_db")
OPEN — extension to more complex formulas.

{uses "rn_two_generators"}[] localises the obstruction exactly, and this is
not vagueness dressed as future work: the catalogue is closed under Heyting
operations over $`a` and $`b`, but $`q_{12} = ◯ρ_6` and
$`q_{13} = ◯ρ_{11}` are depth-2 `◯`-generators and leave it.  So the
question is not whether the lattice extends, but what the right generated
object is once a second `◯`-application is admitted.

Two things are known and one is not.  Known: every representative of the
catalogue is a Heyting-algebra term over `a` and `b` with exactly two
`◯`-applications in the whole catalogue, `◯⊥` and `◯¬◯⊥`, so the catalogue
is a depth-one object; and the first depth-two generators, `q₁₂ = ◯ρ₆` and
`q₁₃ = ◯ρ₁₁`, are certified outside every known class, so the fragment does
extend at depth two (`docs/rho-structure.md`, R4).  Not known: what the
depth-two stratum is as a generated object.  The construction conjecture
C1 of the same document proposes that the fragment is generated stratum by
stratum by the `◯`-images of its own elements modulo `◯◯φ ≡ ◯φ` and
`◯⊤ ≡ ⊤`, and names the depth-two generators to test.  Whether the
antichain construction of {uses "rn_width"}[] lifts to depth two is the
question that would make the stratum's width a theorem; nothing in the
catalogue decides it either way, and it is recorded as OPEN.
:::
