import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.QLL

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Examples" =>

The examples, grouped by constraint domain and by the technique that solves
them, each in enough detail that its numbers can be recomputed by hand.

```
group  domain                          solved by                    checked by
A      uninterpreted constraint atoms  nothing                      kernel
B      linear ℚ, difference form       elimination, longest paths   kernel (6.1); compiled checkers
C      linear ℚ, general coefficients  elimination, entailment      compiled checkers
D      as above                        Wolfram through the bridge   compiled checkers
```

# A. Uninterpreted constraints: Example 9.5

Program, arity zero: `θ₀ = c₁ ⊃ P₁`, `θ₁ = c₂ ⊃ P₂`, `θ₂ = (P₁ ∧ c₃) ∨ (P₂ ∧
c₄) ⊃ Q`.  Query `Q`.  The draft's six steps, as a Table 2 run:

```
⊤ □ Q
  ⇝ ⊤ □ (P₁ ∧ c₃) ∨ (P₂ ∧ c₄)       Rule 5, θ₂
  ⇝ ⊤ □ P₁ ∧ c₃                     Rule 2
  ⇝ ⊤ □ P₁, c₃                      Rule 3
  ⇝ ⊤ □ c₁, c₃                      Rule 5, θ₀
  ⇝ ⊤ ∧ c₁ □ c₃                     Rule 1
  ⇝ (⊤ ∧ c₁) ∧ c₃ □ ε               Rule 1
```

:::group "ex"
The kernel-checked examples.
:::

:::theorem "ex_95" (parent := "ex") (uses := "trees_98") (lean := "LaxLogic.QLL.CLPExamples.cor95")
Corollary 9.8 on Example 9.5: `Θ ⊢ (⊤ ∧ c₁) ∧ c₃ ⊃ ⊤ ∧ (Q ∧ ⊤)`.
:::

:::theorem "ex_95_97" (parent := "ex") (uses := "abs_97") (lean := "LaxLogic.QLL.CLPExamples.thm97_95")
Theorem 9.7 on Example 9.5: the answer of the six steps is `⊣⊢` the
constraint extracted from an abstract proof of `◯Q`, which comes out as
`((((⊤ ∧ c₁) ∧ (⊤ ∧ ⊤)) ∧ ⊤) ∧ (⊤ ∧ c₃))`.
:::

# B. Difference constraints: Example 6.1

Program: `θ₀ = ∀s. s ≥ 5 ⊃ A₁(s)`, `θ₁ = ∀s. s ≥ 9 ⊃ A₂(s)`, `θ₂ = ∀t. ∃s.
(A₁(s) ∧ A₂(s) ∧ t ≥ s + 35) ⊃ B(t)`.  Query `B(z)`.  The engine's derivation
(with `u` the fresh variable) resolves with `θ₂` at `t := z`, opens the
existential at `u`, splits the conjunction, and resolves `A₁(u)` and `A₂(u)`
with `θ₀`, `θ₁`, moving three constraints into the store:

```
[0]  −u + 5 ≤ 0        [1]  −u + 9 ≤ 0        [2]  u − z + 35 ≤ 0
```

Elimination: `z` occurs only in `[2]`, negatively, and `u` only negatively in
`[0]`, `[1]`; nothing new is created and no contradiction arises.
Back-substitution: `u` has lower bounds `5` and `9`, so `u = 9`; `z` has lower
bound `u + 35 = 44`.  Witness `(z, u) = (44, 9)`.  Least value: longest paths
give `u = 9` via `[1]` and `z = 44` via `[2]`; the critical path `[2]`, `[1]`
gives multipliers `(0, 1, 1)`, and with multiplier `1` on `z − 44 < 0` the
combination `(−u + 9) + (u − z + 35) + (z − 44) = 0` with a strict constraint
used is a contradiction.  `z` has coefficient `−1` in its only constraint, so
the answer is upward closed in `z`.

:::theorem "ex_61_check" (parent := "ex") (uses := "trees_checkC, solve_engine") (lean := "LaxLogic.QLL.CLPExamples.check61")
The kernel runs the engine on Example 6.1 and accepts its tree.
:::

:::theorem "ex_61" (parent := "ex") (uses := "ex_61_check, solve_lower, solve_up") (lean := "LaxLogic.QLL.CLPExamples.ex61_answer")
The draft's answer `z ≥ 44`: a value `r` for `z` extends to a solution of the
answer constraint iff `44 ≤ r`.
:::

:::theorem "ex_61_ext" (parent := "ex") (uses := "ex_61_check, abs_ext_total") (lean := "LaxLogic.QLL.CLPExamples.ext61")
The `◯` pass extracts `(((⊤ ∧ u ≥ 5) ∧ (((⊤ ∧ u ≥ 9) ∧ (⊤ ∧ ⊤)) ∧ ⊤)) ∧ ⊤) ∧
(⊤ ∧ (⊤ ∧ z ≥ u + 35))`, the draft's expression, and it is `⊣⊢` the total
constraint.
:::

:::theorem "ex_61_cor" (parent := "ex") (uses := "ex_61_check, abs_98abs") (lean := "LaxLogic.QLL.CLPExamples.cor61")
Corollary 9.8 by the draft's route on Example 6.1.
:::

# B, continued: scheduling and adders

A scheduling program with four tasks, precedences, a release time and one
shared machine encoded by a two-clause `disjoint` predicate gives, with eager
pruning, earliest ends `12` on the first machine order and `11` on the
second; with deadline `10` both branches are refuted by Farkas certificates
whose multipliers are `1` on the critical path and on the deadline
constraint.  Ripple-carry adders are generated with gate delays xor `3`, and
`2`, or `2`; each gate is a clause `out(t) ⊂ ∃s. in₁(s) ∧ in₂(s) ∧ t ≥ s + d`,
and the carry-out of `n` bits settles at `4n + 3`, certified from both sides
for `n` up to `64` (`449` clauses, `1794`-node tree, `513` constraints) and
for all `33` outputs of a `32`-bit adder at once (`15330` nodes, `4385`
constraints), in tens of milliseconds compiled.  For `n = 2` the seventeen
constraints and the critical path of six are listed in the write-up.

# C. General coefficients: the mortgage program

Example 2.1 over ℚ: `mortgage(P,D,I,MP,B) ⊂ D ≤ 1 ∧ B + MP = P·(I + 1)` and
`mortgage(P,D,I,MP,B) ⊂ 1 < D ∧ mortgage(P·(I + 1) − MP, D − 1, I, MP, B)`.
With `r = 1 + I` and `B = 0` the balances satisfy `P·r^D = MP·(1 + r + … +
r^(D−1))`.  For `D = 2`, `I = 1/100` the constraints are `1 < 2`, `2 − 1 ≤ 1`
and `0 + MP = (P·(1/100 + 1) − MP)·(1/100 + 1)`, read as `(201/100)·MP =
(10201/10000)·P`, and the relation is certified as an entailment both ways.
For `D = 120`, `I = 1/100`, `MP = 1721.65` the answer has `121` constraints
and `P` is the exact rational `MP · Σ r^(−k)`, a 246-digit numerator over a
241-digit denominator, `119999.9037…`, determined.  For `D = 5` the certified
coefficients are `MP = (10510100501/51010050100)·P` at `I = 1/100` and
`MP = (161051/610510)·P` at `I = 1/10`; the draft's printed figure
`0.263797522` belongs to the second rate, and its `P = 120000` is the first
answer rounded.

# D. Wolfram

The systems above were also sent to Wolfram through the bridge and every
answer passed the Lean checks: Example 6.1 sat and least `44`; the mortgage
query sat; the schedule with deadline `10` unsat with a Farkas certificate;
the adders sat with least `4n + 3` in `0.26` to `4.9` seconds against under a
millisecond for elimination; and the designed system `±xᵢ ± xⱼ ≤ 1` over five
variables, `40` constraints, where elimination grows the rows `40 → 88 → 411
→ 10211` and stops at the cap while Wolfram answers sat at `x = 0`, and with
`Σxᵢ ≥ 5` added answers unsat with multipliers `1/5, 1/5, 2/5, 1/5, 2/5`
whose combination is `1 > 0`.
