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

### Stage 1 addendum (the manager, 2026-11-01): the new target

After the early warning on O3 the manager added the tower built in the free
PLL algebra and carried into F0 (statements committed before any proof):
`xP p = (p ∨ t3) ∧ t6`, `τ_P = rel t3 t6 xP` (all formulas),
`PLLSelf` (Q1) `FreeInPLL t3 t6 xP`, `PLLSelfReduced`
(`∀ C, [t6] ⊢ aTr t3 C ⟹ ⊢ C`), `PLLSelfTower` (Q2), `PLLTowerInF0` (Q3),
`TowerFirstStep` (`g(τ_P ⊥) = σ⁴⊥`, `g(τ_P ⊤) ⊣⊢ σ³ t6`), `PLLInT6` (P1,
`FreeInPLL (τ σ³⊥) t6 (τ ∘ y)`), and `BaseTauIncomparable`, which replaces
the manager's P2 (the composite tower `τᵈ ∘ g`): the decider found
`[σ³⊥] ⊬ τσ³⊥` and `[τσ³⊥] ⊬ σ³⊥`, so its intervals do not nest.

## Stage 2 (2026-11-01 15:21 GMT): the designed cells, kernel-checked

Countermodels are `SubCM` tables judged by `SubTab.no` (`decide` in the
kernel); the closed tableau of (T5) is judged by `SubTab.yes'`.  Decider:
the subframe tableau `SubTab.solve` (TOOLS.md §3), run untrusted through
`lake env lean` on `_out/` probes; tables minimised by `minimiseCM`.

| cell | verdict | object |
|---|---|---|
| (T5) `[t5] ⊢ σ²⊥` | PROVED (`t5Cell`) | closed tableau `certT5`, 6604 chars |
| gate: `certT5` on `t6 ↠ σ²⊥` | rejected, as required (`gate_t5`) | `check … = false` |
| `TopAvoid t3 t5` | REFUTED (`not_topAvoidT3T5`), `C = t3`, `⊬ t3` (`nd_t3`) | 3 worlds |
| `[t3] ⊢ t6` | PROVED (`t3_t6`) | derivation |
| `⊬ t6` | PROVED (`nd_t6`) | 3-world chain `r < s < e`, `s ∈ S` |
| (C) `[t6] ⊬ σ²⊥`, `[t6] ⊬ σ³⊥` | PROVED (`nd_t6_sig2`, `nd_t6_sig3`) | 7 and 12 worlds |
| `[σ²⊥] ⊬ t6`, `[σ³⊥] ⊬ t6` | PROVED (`nd_sig2_t6`, `nd_b3_t6`) | the 3-world chain |
| `BaseTauIncomparable` | PROVED (`baseTauIncomparable`) | 3 and 12 worlds |
| target O1: `[b] ⊬ relB σ³⊥ y O1` | PASS (`targetCell_O1`) | designed table `T1`, 7 worlds |
| target O2: `[b] ⊬ relB σ³⊥ y O2` | PASS (`targetCell_O2`) | designed table `T2`, 8 worlds |
| target O3: `[b] ⊢ relB σ³⊥ y O3` | FAIL: the cell is derivable (`bT_O3`) | derivation through `t6_gen2` |
| gate: `T1`, `T2` on the O3 cell | do not refute it (`gate_T1`) | `refutes … = false` |
| (Q1) `[t6] ⊬ aTr t3 C`, `C = p, O1, O2, O3` | PASS (`q1_cell_p` … `q1_cell_O3`) | `extT K0`, `extT K1`, `extT K2`, `extT K3` |
| gate: `extT K1` on `t6 ↠ aTr t3 (p → p)` | does not refute it (`gate_q1`) | `refutes … = false` |

**The target `PLLBelowTop` is REFUTED** (`not_pllBelowTop`; and
`not_pllBelowTopReduced` at `C = O3`).  What failed: under `t6` the readers
collapse.  `Y = t4 ∨ ¬t4` and `t3` hold at the same worlds (`t3_Y`, `Y_t3`),
so `◯Y ⊣⊢ ◯t3` (`boxt3_xf`, `xf_boxt3`) and `σ²⊥ ⊢ relX (rn 3)`
(`b2_rX3`); the odd rung `φ₃ = relX (rn 7) = A ∨ (A ↠ relX (rn 3))` then
gives `(φ₃ ↠ σ²⊥) ↠ σ²⊥` (`phi3_b2`), so

    [t6] ⊢ gen 2 = y q        (t6_gen2; q the atom of code 1)

and `[b] ⊢ y q`: the copy sends `q` to the top of `[σ³⊥, b]`
(`rel ⊤ ⊣⊢ b ⊢ y q ∧ b = rel q`, `[⊤] ⊬ q`).  In the gadget `GadR.MS K Sw`
the reason is visible: the ladder bottom `L₀` of every cell `ZL r` forces `t4`
and refutes `◯⊥`, so it refutes `t6`, and every copy `w_k` sees `ZL 0`.  The
reader of the code-0 atom survives (cells O1, O2 pass).  Pen, not mechanised:
in models of `t6`, `gen r` for `r ≥ 2` reads the `t3`-maximal worlds refuting
`t3`, whose three types all force `t7`, so `[t6] ⊢ gen r` for every `r ≥ 2`; only `r = 2` is mechanised.

Build: `gtimeout 3600 lake build wip.f0MovingTop`, exit 0, 17 s.  All pins
`[propext, Quot.sound]`.
