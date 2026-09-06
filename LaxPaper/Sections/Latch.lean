import Verso
import VersoManual
import VersoBlueprint
import LaxLogic.Obligation

open Verso.Genre
open Verso.Genre.Manual
open Informal
open LaxLogic.Obligation

#doc (Manual) "Case study: the RS latch" =>

The original paper's principal example is the RS latch, the simplest of the
three memory devices Herbert verified.  It is the case where the difficulty is
real: the functional behaviour of a sequential device depends on its timing in
an essential way, so the constraints cannot be pushed to one side and recovered
later.  Herbert's own proofs, as the authors note, took several iterations to
find the constraints that made them go through.

# The theory

Three axioms specify the circuit and two the input excitation.  Following the
paper, `During r (s,t)` says the signal `r` is high throughout the interval, and
each gate is given both a delay and an _inertiality_: `d` is the maximal delay
before an input is reflected at the output, `D` the minimal time the gate keeps
propagating the input after it is gone.  Specifying both is a generalisation of
Herbert's transport model and is electrically more realistic.

```
Θ₁  = ∀s,t.        (rin)(s,t)  ⊃  (¬qout)(s + d₁, t + D₁)
Θ₂  = ∀s₁,t₁,s₂,t₂. (¬sin)(s₁,t₁) ∧ (¬qout)(s₂,t₂)
                    ⊃  (qbar)(max s₁ s₂ + d₂, min t₁ t₂ + D₂)
Θ₃  = ∀s,t.        (qbar)(s,t)  ⊃  (¬qout)(s + d₁, t + D₁)
Θₚ₁ = (rin)(sₐ,tₐ)
Θₚ₂ = ∀t ≥ sₐ. (¬sin)(sₐ,t)
```

The Lean names carry the paper's own subscripts.

:::group "latch"
The latch.
:::

:::definition "During" (parent := "latch") (lean := "Latch.During")
A signal high throughout a closed interval.
:::

:::definition "Theta1" (parent := "latch") (uses := "During") (lean := "Latch.Θ₁")
The first NOR gate.
:::

:::definition "Theta2" (parent := "latch") (uses := "During") (lean := "Latch.Θ₂")
The second NOR gate, the one that joins two signals — hence the `max` and `min`.
:::

# The induction principle

The reason a sequential device needs more than the combinational apparatus is
that its behaviour comes from a self-sustaining feedback loop.  The paper's
device is an abstract interval induction: if a property holds on an initial
interval, and whenever it holds on an interval extending that one it also holds
on an interval properly overlapping to the right, then it holds on the whole
infinite interval.  Abstractly this is

```
Ind∀ : P ⊃ (P ⊃ ◯∀P) ⊃ ◯∀P
```

with the progressiveness condition carried in the constraint part.  Given an
initial impulse and a proof that the impulse propagates round the loop, `Ind∀`
returns the constraints under which the loop sustains itself, which is exactly
the memory effect.

:::definition "Prog" (parent := "latch") (lean := "Latch.Prog")
Progressiveness of the step relation on an interval.
:::

:::theorem "ind_sound" (parent := "latch") (uses := "Prog, During") (lean := "Latch.ind_sound")
The induction principle, proved rather than assumed.
:::

The abstract form and its refinement agree by `rfl`, with no axioms — which is
the coherence check that the abstraction really is the paper's.

:::theorem "indForm_unfold" (parent := "latch") (uses := "laxall") (lean := "Latch.indForm_unfold")
The abstract induction axiom and its refinement into base logic are the same
proposition.
:::

# The result, with the constraints assumed

Stated conventionally, with the timing constraints as hypotheses:

:::theorem "latch_resets" (parent := "latch") (uses := "Theta1, Theta2, ind_sound") (lean := "Latch.latch_resets")
The reset transition: with `rin` held high long enough and at least one gate
having non-zero inertia, `qout` is permanently low after the propagation delay.
:::

# The result, with the constraints synthesised

The same derivation, with `postpone` at the two arithmetic side conditions of
the induction step and nothing else changed:

:::theorem "latch_synth" (parent := "latch") (uses := "latch_resets, postpone, reduceAtRecord") (lean := "Latch.latch_synth")
The latch derivation carrying its obligations instead of its hypotheses.
:::

What comes back is the paper's equation (8), in the form it appears there:

```
obligation1 : ∀ t₁, ta + D₁ ≤ t₁ → sa + d₁ + d₂ + d₁ ≤ t₁
obligation2 : ∀ t₁, ta + D₁ ≤ t₁ → t₁ < t₁ + D₂ + D₁
```

and the solver reduces the first, unprompted, to the paper's equation (9):

```
latch_synth.obligation1_solved : … ↔ sa + d₁ + d₂ + d₁ ≤ ta + D₁
```

which is `sₐ + 2d₁ + d₂ ≤ tₐ + D₁`, the **external hold constraint**: the input
must remain high for at least `2d₁ + d₂ - D₁` for the latch to reset fully.  The
second obligation is outside the solver's fragment — its bound mentions the
quantified time on both sides — so it is reported and left, and its reduction to
`0 < D₂ + D₁`, the **internal memory constraint** that at least one gate has
non-zero inertia, is the one hand-written right-hand side in the case studies.

:::theorem "obligation2_iff" (parent := "latch") (uses := "latch_synth") (lean := "Latch.obligation2_iff")
The internal memory constraint, reduced by hand because the solver declines it.
:::

# The two routes agree

:::theorem "latch_resets_synth" (parent := "latch") (uses := "latch_synth, obligation2_iff") (lean := "Latch.latch_resets_synth")
Discharging the synthesised obligations recovers the conventional statement: the
constraint that was derived is the constraint the conventional theorem assumes.
:::

This is the check that matters for the method's claim.  It is not enough that
some constraint comes out; the one that comes out has to be the right one, and
here the equivalence is proved in both directions rather than the implication in
one.

# How to organise a proof this way

1. State the theorem **without** its side conditions.
2. Prove it, and `postpone` every goal that is a side condition rather than part
   of the argument.
3. Read `#obligations`.  Those are the conditions under which the theorem holds,
   derived rather than guessed — and the solver has already reduced the ones in
   its fragment.
4. State the reduced forms as hypotheses if the conventional presentation is
   wanted.

Step 3 is the one that is not available with `sorry`: a `sorry`ed side condition
records nothing, so the constraint would have to be known in advance — which,
for a circuit, is precisely the thing the verification was supposed to discover.
