import Verso
import VersoManual
import LaxLogic.QLL
import CLPPaper.Src
import CLPPaper.Decl
import CLPPaper.Math

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Math
open LaxLogic.QLL LaxLogic.QLL.SLD
open LaxLogic.QLL.Form (openAt instAll strip)

#doc (Manual) "Abstraction, extraction and refinement" =>

This section mechanises the second pass of the 1997 report: abstraction
(Definition 6.2 and Theorem 6.3), the abstract derivations of its Fig. 3,
extraction by a writer monad (its §4, Lemmas 8.3 and 8.4), refinement
(Definition 6.5, Proposition 6.6 and Theorem 6.8), Theorem 9.7, and the
four-world canonical model of its §7 (Lemmas 7.2 and 7.3, Theorem 7.5 at
worlds 0, 1 and 2).  A derivation of the first pass interleaves two kinds of
step: logical steps, which choose clauses and disjuncts, and constraint
steps, which are the solver's business.  The second pass separates them.
Abstraction deletes the constraints, so that the logical part of a
computation becomes a proof in lax logic of $`\bigcirc S`, which says that
$`S` holds up to a constraint not yet named; extraction then reads the
constraint off that proof.  Theorem 9.7 checks that nothing is lost: the
composite computes the conventional answer constraint of Section 5.  The
canonical model shows why the passes must be two: no argument at the abstract
level can see whether a constraint is solvable.  This is the
abstraction-and-refinement method of Fairtlough, Mendler and Cheng
(TPHOLs 2001), applied to CLP.

Throughout, $`\Theta` is a program, $`\mathit{isC}` says which predicates are
constraints, and $`q` is the polarity of the modality used for the abstract
program.

# Abstraction

$`S^\sharp` replaces each constraint atom of $`S` by $`\top`.  The abstract
program $`\Theta^\sharp` replaces each clause
$`\forall \tilde{x}.\, S \twoheadrightarrow P(\tilde{x})` by
$`\forall \tilde{x}.\, S^\sharp \twoheadrightarrow \bigcirc_q P(\tilde{x})`:
every head becomes modal.  Abstract proof trees are the derivations of Fig. 3
of the 1997 report, whose judgement always has the form $`\bigcirc S`: the rule
$`\mathit{val}` proves $`\bigcirc \top`, the rules $`\land\bigcirc`,
$`\lor\bigcirc` and $`\exists\bigcirc` combine abstract proofs, and
$`{\twoheadrightarrow}\bigcirc` applies a clause with a modal head.

{stmt}`AProof`

{leanDecl AProof}

In displays an abstract tree is written with the names of these rules:
$`\mathit{val}`, $`{\land}{\bigcirc}(p,\, r)`, $`{\lor}{\bigcirc}_1(p)`,
$`{\lor}{\bigcirc}_2(p)`, $`{\exists}{\bigcirc}_t(p)` and
$`{\twoheadrightarrow}{\bigcirc}_w^{\tilde{t}}(p)`.

$`\mathsf{ATyped}(\Theta, q, S, a)`, the judgement
$`\Theta \vdash a : \bigcirc_q S`, says that $`a` proves $`\bigcirc_q S`.  The
clause rule demands
a modal head of polarity $`q`; as for concrete trees, the instantiated head is
given by equations.

{stmt}`ATyped`

{leanDecl ATyped}

*Abstract proofs are proofs.*  The cases of the proof are the QLL derivations
that justify each rule of Fig. 3 (they are listed in Section 7).

{stmt}`ATyped.prv`

{leanDecl ATyped.prv}

*Theorem 6.3, at the level of trees.*  If no clause head is a constraint
predicate, the abstraction map `toA` sends a concrete proof tree of $`S` from
$`\Theta` to an abstract proof tree of $`S^\sharp` from $`\Theta^\sharp`.

{stmt}`CTyped.toA`

{leanDecl CTyped.toA}

*Theorem 6.3.*  Consequently a concrete proof of $`S` gives
$`\Theta^\sharp \vdash \bigcirc_q S^\sharp`.

{stmt}`CTyped.prv_abs`

{leanDecl CTyped.prv_abs}

# Extraction

Constraints are formulas.  The writer monad is $`\mathit{WM}\,\alpha = C \times \alpha`
with

$$`\mathit{val}\; a = (\top, a), \qquad \mathit{bind}\;(c, a)\; f = (c \land \pi_1(f\,a),\; \pi_2(f\,a)),`

and it satisfies the monad laws up to $`\dashv\vdash` in the first component
(the relation $`\mathit{WEq}`).  _Witnesses_ are the values of the refinement
types of Σ-formulas: a unit, pairs, left and right injections, and packs of a
term with a witness.  A _table_ $`T\,w\,\tilde{t}\,z` gives the constraint of
clause $`w` at the instance $`\tilde{t}` and the body witness $`z`; it is the
1997 report's $`\theta^\sharp_1`.  Extraction reads an abstract proof against a
table, clause by clause of Fig. 3, and returns a constraint and a witness,
written $`|a| = (\pi_1|a|, \pi_2|a|)`.

{stmt}`AProof.ext`

{leanDecl AProof.ext}

*The writer monad is commutative* up to $`\mathit{WEq}`.  Selection-order
independence rests on this; it is not among the monad laws the 1997 report asks for.

{stmt}`WM.bind_comm`

{leanDecl WM.bind_comm}

*Lemma 8.3.*  The concrete program's table entry at a tree's witness is the
tree's active constraint.

{stmt}`CTyped.ctable_wit`

{leanDecl CTyped.ctable_wit}

*Lemma 8.4.*  The witness extracted from the abstract image `toA p` is the
witness of $`p`, and the extracted constraint is $`\dashv\vdash` the latent
constraint of $`p`.

{stmt}`CTyped.ext_toA`

{leanDecl CTyped.ext_toA}

*Corollary.*  The extracted constraint and the active constraint together are
the total constraint, up to $`\dashv\vdash`.

{stmt}`CTyped.ext_total`

{leanDecl CTyped.ext_total}

*Theorem 9.7.*  For a _pure_ query $`\varphi` (one with no constraint atoms, so
that $`\varphi^\sharp = \varphi`), a run
$`\top \mathrel{\square} \varphi \rightsquigarrow^{*} c \mathrel{\square} \varepsilon`
yields a concrete tree $`p` whose abstract image proves $`\bigcirc_q \varphi`
from $`\Theta^\sharp` and whose extracted constraint is $`\dashv\vdash c`.  The
two passes compute the same answer.

{stmt}`thm_9_7`

{leanDecl thm_9_7}

# The running example abstracted

Abstraction replaces $`c_1, \ldots, c_4` by $`\top` in the program of
Section 4.4 and makes every head modal ({srcLink}`CLPExamples.run95_abs`):

{stmt}`CLPExamples.run95_abs`

The abstraction map of Theorem 6.3 sends the proof tree of Section 5.3 to an
abstract proof of $`\bigcirc Q` from this program.  The two constraint leaves
become $`\mathit{val}`, and every other node keeps its place
({srcLink}`CLPExamples.run95_abstree`; that the image is an abstract proof is
part of {srcLink}`CLPExamples.thm97_95`):

{stmt}`CLPExamples.run95_abstree`

Extraction reads this proof with the program's table.  The constraints $`c_1`
and $`c_3` come back through the table entries of $`\theta_1` and
$`\theta_3`, the two clauses the proof applies, and each $`\mathit{val}` and
each bind of the writer monad adds a $`\top` or a conjunction
({srcLink}`CLPExamples.run95_ext`):

{stmt}`CLPExamples.run95_ext`

*Theorem 9.7 on the running example.*  The extracted constraint is, up to
$`\dashv\vdash`, the answer $`(\top \land c_1) \land c_3` of the Table 2 run
of Section 5.3 ({srcLink}`CLPExamples.run95_agree`):

{stmt}`CLPExamples.run95_agree`

So the two passes agree on this run.  The $`\top` units are the residue of the
writer monad discussed in Section 12.

# Refinement

Definition 6.5 recombines a table with an abstract clause into a concrete one.
It is used here through its instances: $`\mathit{RefinedBy}(\Delta, \Theta^\sharp, T)`
says that $`\Delta` proves

$$`T\,w\,\tilde{t}\,z \;\land\; (S_w[\tilde{t}] \mathbin{@} z) \;\twoheadrightarrow\; P_w(\tilde{t})`

for every modal clause $`w` of $`\Theta^\sharp`, every closed instance
$`\tilde{t}` and every closed witness $`z`, where $`S \mathbin{@} z` is the
disjunct of $`S` that $`z` selects with its existential witnesses substituted.

*Theorem 6.8.*  If $`\Delta` refines $`\Theta^\sharp` through $`T`, then every
abstract proof $`a` of $`\bigcirc S` gives
$`\Delta \vdash \pi_1|a| \twoheadrightarrow S`.  The theorem is uniform in the
table.

{stmt}`thm_6_8`

{leanDecl thm_6_8}

*Proposition 6.6, first half.*  A non-modal program refines its own
abstraction through its own table.

{stmt}`refinedBy_abs`

{leanDecl refinedBy_abs}

*Corollary 9.8, by the 1997 report's route.*  An abstract proof of $`\bigcirc S`,
read with the concrete program's table, yields a constraint that implies
$`S` in the concrete program.

{stmt}`cor_9_8_abs`

{leanDecl cor_9_8_abs}

The second half of Proposition 6.6, that a modal clause follows from its
refinement, is false as stated.  Write
$`\theta = \forall x.\, (A(x) \land B(x)) \twoheadrightarrow P(x)` for the
refinement and $`\theta^\sharp = \forall x.\, A(x) \twoheadrightarrow \bigcirc_q P(x)`
for the abstract clause (`p66Refined` and `p66Abstract` in Lean).

*REFUTED: Proposition 6.6, second half.*  $`\theta \nvdash \theta^\sharp`.  The
countermodel has one world, with $`A` true of every term and $`B` and $`P`
of none.

{stmt}`p66_refuted`

{leanDecl p66_refuted}

*Repair.*  With the table's constraint lax-true, $`\forall x.\, \bigcirc_q B(x)`,
the abstract clause does follow.

{stmt}`p66_with_lax`

{leanDecl p66_with_lax}

# The canonical constraint model

The 1997 report's frame has four worlds, $`0 \to 1` and $`0 \to 2 \to 3`, with
world 3 fallible and every arrow modal.  For the abstraction of a non-modal
program with closed clauses, and constraint relations $`R`: world 0 carries
$`M(\Pi^0)`, world 1 carries $`M(\Pi^1)`, world 2 carries the least model of
$`\Theta` over $`R`, and world 3 makes everything true.  In Lean the worlds are
`w0` to `w3` of the model `canonModel`.

*Lemma 7.2.*  World 0 forces every clause of $`\Theta^\sharp`.

{stmt}`canon_clause`

{leanDecl canon_clause}

*Lemma 7.3.*  The interpretation is monotone along the frame.

{stmt}`canon_hered`

{leanDecl canon_hered}

*World 2 forces $`\bigcirc_q S` for every $`S`*, through the fallible world 3.
So solvability is recorded in world 2's atoms only, and $`\bigcirc \bot` holds
there.

{stmt}`canon_circ_w2`

{leanDecl canon_circ_w2}

*Theorem 7.5 at world 0.*  For a closed Σ-formula $`S`,
$`\Theta^\sharp \vdash S` if and only if world 0 forces $`S`.

{stmt}`thm_7_5_canon0`

{leanDecl thm_7_5_canon0}

*Theorem 7.5 at world 1.*  $`\Theta^\sharp \vdash \bigcirc_q S` if and only if
world 1 forces $`S`.

{stmt}`thm_7_5_canon1`

{leanDecl thm_7_5_canon1}

*Theorem 7.5 at world 2.*  For a pure closed Σ-formula $`S`, some abstract
proof of $`\bigcirc S` extracts a constraint true in $`R` if and only if
world 2 forces $`S`.  The 1997 report asks for a solvable constraint; with the
witness terms chosen to be the solution, that is the same.

{stmt}`thm_7_5_canon2`

{leanDecl thm_7_5_canon2}

Worlds 1 and 2 agree on derivability and differ exactly on solvability.  That
is the formal statement that no argument at the abstract level can see whether
a constraint is solvable, which is why the two passes must be two.
