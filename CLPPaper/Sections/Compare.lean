import Verso
import VersoManual
import LaxLogic.QLL
import LaxLogic.QLL.CLPCompare
import CLPPaper.Src
import CLPPaper.Cite
import CLPPaper.Decl
import CLPPaper.Math
import CLPPaper.Layout

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Math CLPPaper.Cite
open LaxLogic.QLL LaxLogic.QLL.SLD

#doc (Manual) "The cost of certification: a comparison with SWI-Prolog" =>

This section is new; the 1997 report has no counterpart.  A pragmatist will
ask how much slower the certified engine is than a standard CLP system, and
whether anything is gained for the difference.  The section runs one
well-known CLP program in both, under the same search, and times four things
separately: the untrusted search, the compiled checks, the kernel checks, and
SWI-Prolog's `library(clpq)`.

# The program and the query

The program is the mortgage program, Example 2.1 of the 1997 report, stated in
Section 9.4; the Lean definition is `CLPExamples.mortgage`, and the Prolog
text `scripts/clp-compare/mortgage.pl` is the same two clauses.  The query

$$`\mathit{mortgage}(P,\; D,\; 1/100,\; 1721.65,\; 0)`

asks for the principal $`P` that $`D` payments of $`1721.65` at $`1\%` per
period repay exactly.  Each level of the recursion contributes a constraint in
the unknown $`P`, and at the end $`P` is a single rational number, whose
numerator has 246 digits when $`D = 120`.  Both systems find the same $`P` at
every size at which both were run.  The program was chosen because it is the
one well-known CLP(R) program within reach of the engine as built: the other
examples distributed with CLP(R), such as the Laplace equation on a grid and
the analysis of RLC circuits, recurse over lists, which needs a Herbrand
equality solver that the engine does not have (Section 13).

Both systems run the program with the same search: depth-first, leftmost
selection, clauses in textual order, the first answer only.  Both pass the new
principal and duration to the recursive call as arithmetic terms, as the
program text does.  At each level the base clause is tried first and fails on
$`D \le 1`; the second clause then adds $`1 < D` and recurses.

# What is timed

* (a) _Untrusted search_, compiled to native code: the engine `run` with eager
  pruning, in which every new constraint is tested by the certified solver on
  the whole store, followed by Fourier–Motzkin elimination (`fm`, untrusted)
  for a witness fixing $`P = v` and for the Farkas multipliers that refute
  $`P < v` and $`P > v`.
* (b) _Compiled checks_: `checkC` on the proof tree, `checkWitness` on the
  witness and `checkFarkas` on the two refutations, sound by `checkC_sound`,
  `checkWitness_sound` and `checkFarkas_unsat`.  Together they establish that
  the answer constraint $`c` implies the query in QLL, is satisfiable, and
  fixes $`P = v`.  The trust base includes the Lean compiler.
* (c) _Kernel checks_: the proof tree is written into a file as a literal and
  checked by the Lean kernel through the certifier `answerK` below, which
  gives answer soundness as a theorem with the axioms `[propext, Quot.sound]`.
  The three arithmetic checks are decided by the kernel too, with
  `decide +kernel`, but outside lean-certify: the facts they give depend on
  `[propext, Classical.choice, Quot.sound]`, through Mathlib's rationals, and
  lean-certify's allow-list excludes `Classical.choice`.  The time is the
  kernel's type-checking time as Lean's profiler reports it.  Loading the
  imported modules, parsing and elaborating the literal are not included, and
  they cost more: the answer file takes 16 s to process at $`D = 60`, of which
  1.6 s is kernel checking, and 210 s at $`D = 240`, of which 23 s is.
* (d) _SWI-Prolog 10.0.2 with `library(clpq)`_ {pcite}`WielemakerEtAl2012`.
  SWI-Prolog compiles clauses to the instructions of its own virtual machine,
  which its kernel, written in C, interprets; it does not generate native
  code.  `library(clpq)` is Holzbaur's CLP(Q) {pcite}`Holzbaur1995`, written
  in Prolog over attributed variables; according to its source, it
  eliminates equations by substitution and decides inequalities by a simplex
  method, keeping the store in solved form as each constraint arrives.

Every run is bounded by a timeout, and one runs at a time, on an Apple M4 Pro
with 48 GB of memory under macOS 15.7.7, with Lean 4.31.0.  Times are wall
clock inside one process, after one untimed run; process startup and
loading are excluded on both sides.  Each figure is a median (for (a) and
(b), a sum of the medians of their stages): of 11 runs for SWI-Prolog; of 5
runs for Lean up to $`D = 240`, 3 at $`D = 480` and 1 at $`D = 960`; of 3
kernel runs up to $`D = 120` and 1 at $`D = 240`.  The executable is
`clpcompare` (`tools/ClpCompare.lean`), the producer and checkers are in
`LaxLogic/QLL/CLPCompare.lean`, and the scripts and the raw data, failed runs
included, are in `scripts/clp-compare/` (`run.py`, `table.py`, `mortgage.pl`,
`results.jsonl`).

# The certifier

Answer soundness is packaged as a certifier of lean-certify: the
specification is the classifier, the program, the query and the claimed answer
constraint; the certificate is a proof tree; the property is
$`\Theta \vdash c \twoheadrightarrow G`.  Its soundness proof is `checkC_sound`
followed by `CTyped.prv_total`, unchanged.  lean-certify's lints pass on it
(the checker is structurally recursive, the property mentions no budget, the
axioms are `[propext, Quot.sound]`), and a pinned test watches the check
reject a tree that takes the wrong disjunct.

{leanDecl Compare.answerK}

On Example 9.5 the certifier gives Corollary 9.8 as a kernel-checked theorem,
with the total $`c_1 \land c_3` of the tree as the answer
({srcLink}`Compare.answer95`):

{stmt}`Compare.answer95`

# Results

Times in milliseconds unless marked; a dash means not run.

:::wtable (widths := "0.07 0.09 0.15 0.12 0.12 0.13 0.11 0.10 0.11") +header
*
  * $`D`
  * tree nodes
  * (a) search + arithmetic
  * (b) compiled checks
  * (c) kernel: answer
  * (c) kernel: arithmetic
  * (d) SWI clpq
  * (a)/(d)
  * (b)/(d)
*
  * 15
  * 46
  * 1.61
  * 0.58
  * 174
  * 292
  * 0.12
  * 14
  * 4.9
*
  * 30
  * 91
  * 7.42
  * 1.56
  * 483
  * 438
  * 0.43
  * 17
  * 3.6
*
  * 60
  * 181
  * 48.2
  * 5.51
  * 1.57 s
  * 775
  * 1.65
  * 29
  * 3.3
*
  * 120
  * 361
  * 357
  * 20.1
  * 5.75 s
  * 1.58 s
  * 5.98
  * 60
  * 3.4
*
  * 240
  * 721
  * 2.79 s
  * 85.2
  * 22.6 s
  * 3.66 s
  * 22.4
  * 125
  * 3.8
*
  * 480
  * 1441
  * 21.6 s
  * 312
  * —
  * —
  * 90.9
  * 237
  * 3.4
*
  * 960
  * 2881
  * 166 s
  * 1.25 s
  * —
  * —
  * 360
  * 461
  * 3.5
*
  * 1920
  * —
  * —
  * —
  * —
  * —
  * 1.46 s
  * —
  * —
:::

*Reading the table.*  SWI-Prolog's time grows about fourfold each time $`D`
doubles.  The compiled producer (a) takes 14 times SWI-Prolog's time at
$`D = 15`, 60 times at $`D = 120` and 461 times at $`D = 960`, and almost all
of it is the search: at $`D = 960` the search takes 166 s and the arithmetic
0.29 s.  The search tests each new constraint by solving the whole store again
from scratch, and the store and the numbers in it both grow with $`D`; from
$`D = 60` on, its time grows about eightfold per doubling.  The first run at
$`D = 960` took 1053 s; a repeat took 166 s, in line with that rate, and the
table shows the repeat (both are in the raw data; the cause of the slow run is
not known).  At $`D = 1920` the engine was not run: at the eightfold rate the
search alone would take over 20 minutes.

The compiled checks (b) take between 3.3 and 4.9 times SWI-Prolog's whole run
at every size, and grow fourfold per doubling, as SWI-Prolog does.  The kernel
checks (c) are slower again: answer soundness takes between 950 and 1500 times
SWI-Prolog's run at the sizes measured (0.17 s at $`D = 15`, 22.6 s at
$`D = 240`).  Above
$`D = 240` the kernel checks were not run: the answer file for $`D = 240` is
5 MB, checking it took 209 s and 14.5 GB of memory, the file grows fourfold
per doubling, and the machine has 48 GB.

# What is gained, and at what cost

The table measures the cost; what is gained is what each check establishes.

* Every answer comes with evidence that a checker proved sound accepts.  After
  (b), the answer constraint implies the query in QLL, has a solution, and
  fixes $`P = v`, on the trust of the checkers' soundness theorems and of the
  Lean compiler.  After (c), answer soundness is a theorem checked by the Lean
  kernel with the axioms `[propext, Quot.sound]`.  SWI-Prolog finds the same
  rational number, and nothing outside the implementation of `clpq` and of
  SWI-Prolog vouches for it.
* The compiled checks cost between 3.3 and 4.9 times SWI-Prolog's run here,
  and they would cost the same for an answer from any producer that supplies a
  proof tree and the certificates; Section 8.5 treats Wolfram in this way.
* Kernel checking is the expensive layer, about a thousand times SWI-Prolog's
  run, and it is the layer at which an answer becomes a theorem.
* The large factor in (a) is the search, not the checking: this engine solves
  its store from scratch at every test, where SWI-Prolog keeps it solved.  The
  search is untrusted, so it could be replaced without changing anything that
  is proved; these measurements do not show what an incremental solver would
  cost here.
* The abstract pass of Section 6 and the SLD◯ machine of Section 7 are not
  exercised by this program and play no part in these times.

For a pragmatist who wants only the number $`P`, SWI-Prolog is faster at every
size, by a factor that grows with $`D`.  What the certified engine adds is a
checked answer: compiled, at a few times SWI-Prolog's cost; as a theorem of
the kernel, at about a thousand times, at the sizes at which that was run (up
to $`D = 240`).
