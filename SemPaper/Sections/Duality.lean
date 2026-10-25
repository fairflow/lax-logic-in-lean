import Verso
import VersoManual
import CLPPaper.Src
import CLPPaper.Cite
import SemPaper.Math
import SemPaper.Blocks

open Verso.Genre
open Verso.Genre.Manual
open CLPPaper CLPPaper.Cite PaperKit.Math PaperKit.Blocks
open PLLND
open EsakiaNuclear EsakiaNuclear.Gen EsakiaNuclear.Bridge EsakiaNuclear.Cells

set_option paperkit.notation "sem"

#doc (Manual) "Esakia duality for Heyting algebras with a nucleus" =>

Esakia duality represents a Heyting algebra by the ordered space of its prime
filters {pcite}`Esakia1974 Esakia2019`.  {cite}`BezhanishviliGhilardi2007`
(Theorem 30, Corollary 31, Theorem 34) represent the nuclei on a Heyting
algebra by the nuclear subsets of its dual; their results are used here
through the restatement of {cite}`AvilaBezhanishviliMorandiZaldivar2020`,
which was read in full.  The finite duality is that of
{cite}`BezhanishviliEtAlDiego2021` (Theorem 3.4, Lemmas 3.15 and 4.12), and
the subframe reading of $`\bigcirc` goes back to Goldblatt's J-spaces
{pcite}`Goldblatt1981`.  The morphism condition F10 and the bridge R1–R5 are
ours.  Each theorem below proves a statement written as a definition; the
definition is printed beneath the theorem, followed, where the definition
names a predicate, by that predicate.  Statements: `wip/esakiaNuclearFin.lean`,
`wip/esakiaNuclearGen.lean`.

# The finite layer

A finite Heyting algebra $`A` is given by its operation tables, checked by
`isHA`.  Its dual $`X_A` is the set of its meet-primes ordered dually
($`m \sqsubseteq n` iff $`n \le m`).  For $`a \in A`, a nucleus $`j` on
$`A`, and up-sets $`U, V \in \mathrm{Up}(X)` of a finite poset $`X`:

$$`\alpha(a) = \{x \in X_A \mid a \not\le x\}, \qquad S_j = \{x \in X_A \mid j\,x = x\}, \qquad U \Rightarrow V = X \setminus {\downarrow}(U \setminus V).`

The layer is without choice: every pin is `propext`, `Quot.sound`, and
`Quot.sound` enters only through function extensionality.  PROVED.

$$`\alpha : A \cong \mathrm{Up}(X_A), \qquad \alpha(a \to b) = \alpha(a) \Rightarrow \alpha(b)`

{leanStmt EsakiaNuclear.f1}

{leanDef EsakiaNuclear.F1}

{leanDef EsakiaNuclear.AlphaIso}

$$`\varepsilon(x) = X \setminus {\downarrow}x \;:\; X \cong (\text{meet-primes of } \mathrm{Up}(X))^{\mathrm{op}}`

{leanStmt EsakiaNuclear.f2}

{leanDef EsakiaNuclear.F2}

{leanDef EsakiaNuclear.EpsIso}

$`j_S` is a nucleus for every $`S` (F3); every nucleus $`j` on $`A` is
$`j_{S_j}` transported by $`\alpha` (F4); every $`S \subseteq X_A` is some
$`S_j` (F6); and $`j \mapsto S_j` reverses the order (F7).

$$`j_S(U) = X \setminus {\downarrow}(S \setminus U) \text{ is a nucleus on } \mathrm{Up}(X)`

{leanStmt EsakiaNuclear.f3}

{leanDef EsakiaNuclear.F3}

{leanDef EsakiaNuclear.JSNucleus}

$$`\alpha(j\,a) = j_{S_j}(\alpha\,a)`

{leanStmt EsakiaNuclear.f4}

{leanDef EsakiaNuclear.F4}

{leanDef EsakiaNuclear.Rep}

$$`x \in S \iff j_S(\varepsilon\,x) = \varepsilon\,x`

{leanStmt EsakiaNuclear.f5}

{leanDef EsakiaNuclear.F5}

{leanDef EsakiaNuclear.EpsS}

$$`\text{every } S \subseteq X_A \text{ is } S_j \text{ for a nucleus } j \text{ on } A, \text{ namely } j = \alpha^{-1} \circ j_S \circ \alpha`

{leanStmt EsakiaNuclear.f6}

{leanDef EsakiaNuclear.F6}

{leanDef EsakiaNuclear.Bij}

$$`j \le k \iff S_k \subseteq S_j`

{leanStmt EsakiaNuclear.f7}

{leanDef EsakiaNuclear.F7}

{leanDef EsakiaNuclear.OrdRev}

$$`S_{j \wedge k} = S_j \cup S_k`

{leanStmt EsakiaNuclear.f8}

{leanDef EsakiaNuclear.F8}

{leanDef EsakiaNuclear.MeetUnion}

$$`S_{a \vee {-}} = X_A \setminus \alpha\,a, \qquad S_{a \to {-}} = \alpha\,a, \qquad S_{({-} \to a) \to a} = \max(X_A \setminus \alpha\,a)`

{leanStmt EsakiaNuclear.f9}

{leanDef EsakiaNuclear.F9}

{leanDef EsakiaNuclear.Thm34}

For a Heyting homomorphism $`h : A \to B` let
$`h_*(y) = \bigvee \{a \in A \mid h(a) \le y\}`.  It is the dual map, and F10
characterises the homomorphisms that commute with the nuclei ($`{\uparrow}`
in the dual order):

$$`h_* : X_B \to X_A \text{ is a p-morphism}, \qquad h\,a \le x \iff a \le h_*(x)`

{leanStmt EsakiaNuclear.f10a}

{leanDef EsakiaNuclear.F10a}

{leanDef EsakiaNuclear.PMorph}

$$`h \circ j = k \circ h \iff \forall x \in X_B.\; {\uparrow}({\uparrow}h_*(x) \cap S_j) = {\uparrow}h_*({\uparrow}x \cap S_k)`

{leanStmt EsakiaNuclear.f10}

{leanDef EsakiaNuclear.F10}

{leanDef EsakiaNuclear.NuclearHom}

_REFUTED: the naive morphism condition._  Remark 4.6 of
{cite}`BezhanishviliEtAlDiego2021`, transferred to Heyting homomorphisms,
would read $`h \circ j = k \circ h \iff h_*^{-1}(S_j) = S_k`.  A kernel-checked
cell refutes it: along the embedding of the two-element algebra into the
three-element chain, with the identity on the first and $`\lnot\lnot` on the
second, $`h` commutes with the nuclei (`m_naive_cell_nuclear`) but the sets
differ.  The simplification in the source uses strict order preservation,
which p-morphisms lack.

$$`h : 2 \hookrightarrow C_3,\ j = \mathrm{id},\ k = \lnot\lnot:\qquad h \circ j = k \circ h \quad\text{and}\quad h_*^{-1}(S_j) = X_{C_3} \ne S_k`

{leanStmt EsakiaNuclear.Cells.m_naive_refuted}

{leanDef EsakiaNuclear.NaiveHom}

# The general case

For an arbitrary Heyting algebra $`A`, $`X_A` is the set of prime filters,
ordered by inclusion and topologised by the sets
$`\varphi(a) = \{x \in X_A \mid a \in x\}` and their complements; for a
nucleus $`j`, $`N_j = \{x \in X_A \mid j^{-1}(x) = x\}`; a closed
$`N \subseteq X_A` is nuclear when $`{\downarrow}(U \cap N)` is clopen for
every clopen $`U`.  These results are classical: every pin is `propext`,
`Classical.choice`, `Quot.sound`.  PROVED.

$$`X_A \text{ is an Esakia space}, \qquad \varphi : A \cong \mathrm{ClopUp}(X_A), \qquad \varphi(a \to b) = X_A \setminus {\downarrow}(\varphi\,a \setminus \varphi\,b)`

{leanStmt EsakiaNuclear.Gen.g1}

{leanDef EsakiaNuclear.Gen.G1}

{leanDef EsakiaNuclear.Gen.EsakiaObjects}

$$`\varphi(j\,a) = X_A \setminus {\downarrow}(N_j \setminus \varphi\,a)`

{leanStmt EsakiaNuclear.Gen.phi_nucleus}

$$`\begin{gathered} N_j \text{ is nuclear}; \qquad \text{each nuclear } N \text{ gives } j_N \text{ with } \varphi(j_N\,a) = X_A \setminus {\downarrow}(N \setminus \varphi\,a) \text{ and } N_{j_N} = N; \\ j \le k \iff N_k \subseteq N_j \end{gathered}`

{leanStmt EsakiaNuclear.Gen.g2}

{leanDef EsakiaNuclear.Gen.G2}

{leanDef EsakiaNuclear.Gen.BGThm30}

$$`N_{\mathrm{id}} = X_A, \qquad N_{\top} = \emptyset, \qquad N_{j \wedge k} = N_j \cup N_k`

{leanStmt EsakiaNuclear.Gen.g3}

{leanDef EsakiaNuclear.Gen.G3}

{leanDef EsakiaNuclear.Gen.BGCor31}

$$`N_{a \vee {-}} = X_A \setminus \varphi\,a, \qquad N_{a \to {-}} = \varphi\,a, \qquad N_{({-} \to a) \to a} = \max(X_A \setminus \varphi\,a)`

{leanStmt EsakiaNuclear.Gen.g4}

{leanDef EsakiaNuclear.Gen.G4}

{leanDef EsakiaNuclear.Gen.BGThm34}

`Classical.choice` enters through the prime filter theorem, Alexander's
subbasis theorem, excluded middle in several proofs, a choice of the value
$`j_N(a)` (unique, since $`\varphi` is injective), and Mathlib's
`IsCompact.elim_finite_subcover`; whether the uses beyond the first two can
be removed is OPEN.

# The bridge to constraint and subframe models

The duality meets the models of Sections 3 and 4; $`\|\varphi\|` is the truth
set of $`\varphi`, and $`{\downarrow}` is taken along the order of the model.
In a subframe model the $`\bigcirc`-clause is $`j_S`, a nucleus on the
hereditary sets:

$$`\|\bigcirc\varphi\| = j_S(\|\varphi\|), \qquad j_S(U) = W \setminus {\downarrow}(S \setminus U) \text{ is a nucleus on the hereditary subsets of } W`

{leanStmt EsakiaNuclear.Bridge.r1}

{leanDef EsakiaNuclear.Bridge.R1}

A constraint model $`C` has a complex algebra $`(H_C, j_C)`, with $`H_C` the
$`R_i`-hereditary sets that contain $`F`:

$$`\|\bigcirc\varphi\| = j_C(\|\varphi\|), \qquad j_C(U) = \{w \mid \forall v.\ w\,R_i\,v \Longrightarrow \exists u.\ v\,R_m\,u \text{ and } u \in U\} \text{ is a nucleus on } H_C`

{leanStmt EsakiaNuclear.Bridge.r2}

{leanDef EsakiaNuclear.Bridge.R2}

Its $`S`-points are the $`R_m`-final worlds (R3a), and for a finite model its
meet-primes are those of the worlds outside $`F`, ordered dually to $`R_i`
(R3b, R3c):

$$`R_i \text{ antisymmetric} \;\Longrightarrow\; \bigl(j_C(W \setminus {\downarrow}w) = W \setminus {\downarrow}w \iff w \text{ is } R_m\text{-final}\bigr)`

{leanStmt EsakiaNuclear.Bridge.r3a}

{leanDef EsakiaNuclear.Bridge.R3a}

$$`W \text{ finite} \;\Longrightarrow\; \text{every meet-prime of } H_C \text{ is } W \setminus {\downarrow}w \text{ for some } w \notin F`

{leanStmt EsakiaNuclear.Bridge.r3b}

{leanDef EsakiaNuclear.Bridge.R3b}

$$`w \notin F \;\Longrightarrow\; W \setminus {\downarrow}w \text{ is a meet-prime of } H_C, \qquad W \setminus {\downarrow}v \subseteq W \setminus {\downarrow}w \iff w\,R_i\,v`

{leanStmt EsakiaNuclear.Bridge.r3c}

{leanDef EsakiaNuclear.Bridge.R3c}

$$`\mathsf{some}(x) \text{ is } R_m\text{-final in } \mathit{toConstraint}(M) \iff x \in S`

{leanStmt EsakiaNuclear.Bridge.r4}

{leanDef EsakiaNuclear.Bridge.R4}

On $`\omega` with $`R_i = R_m = {\le}` and no fallible worlds:

$$`\begin{gathered} \text{no world is } R_m\text{-final}; \qquad j_C \ne j_S \text{ on } H_C \text{ for every } S \subseteq \omega; \\ x_\infty = \{U \in H_C \mid U \ne \emptyset\} \text{ is a prime filter of } H_C, \quad j_C^{-1}(x_\infty) = x_\infty, \quad x_\infty \text{ is not principal} \end{gathered}`

{leanStmt EsakiaNuclear.Bridge.r5}

{leanDef EsakiaNuclear.Bridge.R5}

R1, R3c and R4 each imply $`\lnot\lnot P \to P` (`r1_dne`, `r3c_dne`,
`r4_dne`, with no axioms), so they have no proof without choice: the library's
models carry arbitrary propositions as $`S`, $`V` and $`R_i`, while
$`j_S(U) = W \setminus {\downarrow}(S \setminus U)` reads the
$`\bigcirc`-clause through a double negation.  R2 is within `propext`,
`Quot.sound`; R3a and R3b use excluded middle, and whether they have
constructive proofs is OPEN.

_Reading_ (a pen argument from the theorems above).  A finite subframe model
on a poset is exactly a finite dual poset with its $`S` and a valuation: by F2,
F3 and F5, $`(W, S)` is the dual of $`(\mathrm{Up}(W), j_S)`, and by R1
$`j_S` is its $`\bigcirc`-clause.  For a finite constraint model with
antisymmetric $`R_i`, `toSubframe` of Section 4 is the dual of its complex
algebra (R2, R3a–R3c).  On $`\omega` the $`S`-points exist only in the Esakia
dual (R5), which is why `toSubframe` is stated for finite models.

# Supporting declarations

{lemmaTable EsakiaNuclear.Cells.m_naive_cell_nuclear EsakiaNuclear.Gen.isNuclear_Nj EsakiaNuclear.Gen.lower_basic_nuclear EsakiaNuclear.Gen.isClopen_lowerClosure EsakiaNuclear.Bridge.r1_dne EsakiaNuclear.Bridge.r3c_dne EsakiaNuclear.Bridge.r4_dne}

Pins (`collectAxioms`):
{axiomsOf}`EsakiaNuclear.f1 EsakiaNuclear.f2 EsakiaNuclear.f3 EsakiaNuclear.f4 EsakiaNuclear.f5 EsakiaNuclear.f6 EsakiaNuclear.f7 EsakiaNuclear.f8 EsakiaNuclear.f9 EsakiaNuclear.f10a EsakiaNuclear.f10`
for the finite layer;
{axiomsOf}`EsakiaNuclear.Cells.m_naive_refuted EsakiaNuclear.Cells.m_naive_cell_nuclear`
for the cell;
{axiomsOf}`EsakiaNuclear.Gen.g1 EsakiaNuclear.Gen.phi_nucleus EsakiaNuclear.Gen.g2 EsakiaNuclear.Gen.g3 EsakiaNuclear.Gen.g4 EsakiaNuclear.Gen.isNuclear_Nj EsakiaNuclear.Gen.lower_basic_nuclear EsakiaNuclear.Gen.isClopen_lowerClosure`
for the general case; {axiomsOf}`EsakiaNuclear.Bridge.r2` for R2;
{axiomsOf}`EsakiaNuclear.Bridge.r1 EsakiaNuclear.Bridge.r3a EsakiaNuclear.Bridge.r3b EsakiaNuclear.Bridge.r3c EsakiaNuclear.Bridge.r4 EsakiaNuclear.Bridge.r5`
for R1, R3a–R3c, R4 and R5;
{axiomsOf}`EsakiaNuclear.Bridge.r1_dne EsakiaNuclear.Bridge.r3c_dne EsakiaNuclear.Bridge.r4_dne`
for the three implications.
