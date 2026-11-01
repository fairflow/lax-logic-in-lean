# `wip/f0MovingTop.lean`: status

Faithful copies of F0 and of PLL in intervals strictly below `⊤`.  Matthew,
2026-11-01: "mechanise the reduction, run the test(s)"; addition the same day:
the recursive embedding, as for `H_ω` (W1–W4).  Branch `f0-moving-top`, local.

## Stage 1 (2026-11-01 15:08 GMT): statements committed

All statements are `Prop` definitions in `PLLND.F0.MovingTop`; no theorem,
no `sorry`.  Status of every statement: OPEN (Stage 1 records statements
only).  The list, with the displayed forms, is the module docstring.

    CopyF0In a b :  ∀ A B closed,  [A] ⊢ B  ⟺  [relC a b A] ⊢ relC a b B
    TopAvoid a b :  ∀ C closed,  [b] ⊢ C[⊥ := a]  ⟹  ⊢ C

| name | statement |
|---|---|
| `RelClosed` (R) | `A` closed, `[a] ⊢ b` ⟹ `rel a b x A ⊣⊢ A[⊥ := a] ∧ b` |
| `CopyIffTopAvoid` | `[a] ⊢ b` ⟹ (`CopyF0In a b` ⟺ `TopAvoid a b`) |
| `RelGen` (R') | `[a] ⊢ b` ⟹ `rel a b (p ↦ x p ∧ b) C ⊣⊢ relB a x C ∧ b`, every `C` |
| `GenIff` | `[a] ⊢ b`, `∀ p, [a] ⊢ x p` ⟹ (`FreeInPLL a b (x ∧ b)` ⟺ `∀ C, [b] ⊢ relB a x C ⟹ ⊢ C`) |
| `CopyAtBot` (N) | `b` closed ⟹ (`CopyF0In ⊥ b` ⟺ `⊢ b`) |
| `T5Cell` | `[t5] ⊢ σ²⊥` |
| `TopAvoidT3T5`, `CopyT3T5` | the candidates for `[t3, t5]` |
| `SigAvoidT6` (T6) | `∀ C, [t6] ⊢ σC ⟹ ⊢ C` |
| `TopAvoidT3T6` (T6) | `TopAvoid t3 t6` |
| `T6Below` | `[t3] ⊢ t6` and `⊬ t6` |
| `CopyT3T6` (W1) | `CopyF0In t3 t6` |
| `TopAvoidN` (T6n) | `n ≥ 1` ⟹ `TopAvoid (σⁿ⊥) (t6 ∨ σⁿ⊥)` and `⊬ t6 ∨ σⁿ⊥` |
| `NotCofinal` (C) | `∀ n, [t6] ⊬ σⁿ⊥` |
| `BasesOnlyTop` (C) | `x` closed, `(∀ n, [σⁿ⊥] ⊢ x)` ⟹ `⊢ x` |
| `IterBounds` (F) | `[τᵈ⊥] ⊢ τᵈ⁺¹⊥`, `[τᵈ⁺¹⊤] ⊢ τᵈ⊤`, `[τᵈ⊥] ⊢ τᵈA ⊢ τᵈ⊤` |
| `FixedInAll` (F) | `τx ⊣⊢ x` ⟹ `∀ d, [τᵈ⊥] ⊢ x ⊢ τᵈ⊤` |
| `SigFixedTop` (F) | `σx ⊣⊢ x` ⟹ `⊢ x` |
| `TauFixedPoint` | `∃ x closed, relC t3 t6 x ⊣⊢ x`: OPEN, not attempted |
| `IterRel`, `W2` (W2) | `τᵈ A ⊣⊢ relC (τᵈ⊥) (τᵈ⊤) A`, general and for `(t3, t6)` |
| `StrictNestOf`, `W3` (W3) | strict nesting of `[τᵈ⊥, τᵈ⊤]` at both ends |
| `IterCopyOf`, `W4` (W4) | `FreeInPLL a b x` ⟹ `τᵈ ∘ rel a b x` faithful on PLL in `[τᵈa, τᵈb]`, strictly nested; `W4`: the target ⟹ the same for `(σ³⊥, b, y ∧ b)` |
| `PLLBelowTop` (target) | `FreeInPLL σ³⊥ b (p ↦ y p ∧ b)`, `b = t6 ∨ σ³⊥` |
| `PLLBelowTopReduced` | `∀ C, [b] ⊢ relB σ³⊥ y C ⟹ ⊢ C` |
| `TargetCell C` | `[b] ⊬ relB σ³⊥ y C` |

Build: `gtimeout 3600 lake build wip.f0MovingTop`, exit 0, 41 s (it built
`wip.f0FreeInterval` and `wip.f0InsideOut`, merged today, on the way).
