# Green slime: computed indices in constructor return types

McBride's rule for indexed inductive families. In a constructor's
**return type**, every index must be a *variable*, or a *constructor
applied to* variables. Never a function applied to anything.

    | andI1 {St Th} {A₁ A₂}
        (d : FRJi G St Th A₁) : FRJi G St Th (.and A₁ A₂)      -- clean
    | impInI {St Th Lam} {A B}
        (d : FRJi G St (nf G (Th ++ Lam)) B) :
        FRJi G (nf G (St ++ Lam)) (nf G Th) (.imp A B)         -- SLIME ×2

Computation in a **premise** is harmless and normal — `LaxND (φ :: Γ) ψ`
is fine, and so is `nf G (Th ++ Lam)` in `d` above. Only the return type
matters, because that is what the unifier has to invert.

## Why it matters

`cases`, `injection` and dependent pattern matching work by unifying the
scrutinee's indices with each constructor's. Against `nf G Th` the
unifier must solve `?Θ ≡ nf G Th` — it cannot invert `nf`, so the case
either fails outright or survives only behind a transport across an
equation nothing can discharge.

The damage is **not unsoundness**. A slimed development is still
kernel-checked. The damage is that the *statements bend to fit what can
be case-analysed*: you weld a normal form into the indices so the
computed forms come out syntactically equal, and the judgment quietly
stops being the one the paper defines. That is a fidelity failure, and it
is invisible from a green build with clean axiom pins.

The tell, in a session transcript, is a proof that will not go through
and a diagnosis phrased as a *carrier* problem — "the split is a literal
index equality on Finset but not on List, and no transport exists,
because `Ax^I` pins its own Θ". "Pins its own index" **is** slime, said
in other words. Changing the carrier so the computed forms coincide
accommodates it; it does not remove it.

## Desliming — a separate procedure

`#slime` **finds** slime; it does not remove it. Removing it is a distinct
operation ("desliming"), worth running as its own pass on an existing
formalisation, and it is mechanical enough to be scripted.

Replace the computed index by a fresh variable and carry the computation
as an **equation field**:

    | impInI {St Th Lam Σ' Θ'} {A B}
        (d  : FRJi G St (nf G (Th ++ Lam)) B)
        (hΣ : Σ' = nf G (St ++ Lam))
        (hΘ : Θ' = nf G Th)
        … : FRJi G Σ' Θ' (.imp A B)

Now every index is a variable, so `cases` decomposes the derivation, and
`hΣ`/`hΘ` are ordinary hypotheses to rewrite with exactly where the proof
needs them — instead of an obligation the unifier silently imposes
everywhere. The information content is identical; only its position
changes, from a place that blocks inversion to a place that does not.

Do this **at transcription time** (stage 2). Retrofitting means redoing
every proof over the family.

## Running the detector

    #slime FRJ.FRJr FRJ.FRJi

Reports, per constructor, which index positions are computed and the head
symbol doing the computing. Clean constructors are listed by name. Emits
a warning when anything is slimed, `logInfo` when nothing is — it never
fails a build.

`Nat` offsets are the standing exception: `n + 1` is definitionally
`Nat.succ n` and the unifier inverts it natively, so height-indexed
families are **not** slimed. The tool knows this; a version that did not
falsely condemned all five height-indexed calculi in this repo.

## Run a control

The check is worth nothing if it flags everything. Run it first on a
family you already believe is clean — `PLLND.LaxND`, 0 of 12 — and only
then on the family under suspicion. The `Nat`-offset bug above was caught
exactly this way: the fix had to leave the control clean, leave FRJ's 13
standing, and turn G4h from 15 to 0.

## The census that motivated this

Every judgment family in `lax-logic-in-lean`, checked 2026-08-18:

| family | slimed / constructors |
|---|---|
| `PLLND.LaxND`, `IPLND` | 0 / 12, 0 / 10 |
| `PLLND.G4`, `G4p`, `G4h`, `G4sh`, `G4cTm` | 0 / 17, 17, 17, 16, 16 |
| `PLLND.PD` | 0 / 13 |
| `LJFO.Stab/RFocus/LFoc/Inv` (+ height variants) | 0 / 20, 0 / 20 |
| `IPC.*`, `PLLND.Focused.*`, `LJF.*` focused | 0 / 17, 19, 17 |
| **`FRJ.FRJr`** | **9 / 13** — every axiom and every join |
| **`FRJ.FRJi`** | **4 / 8** |

Zero slime across roughly 210 constructors in eleven families, written
over two years; thirteen slimed out of twenty-one in the one family
transcribed in a week. The house style was already right. FRJ departed
from it and nothing caught that, because there was no check to run.
