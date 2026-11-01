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

## Stage 3 (2026-11-01 15:31 GMT): proofs

Every theorem is sorry-free and pinned by `#axioms_within … [propext, Quot.sound]`.

| statement | status | theorem |
|---|---|---|
| (R) `RelClosed` | PROVED | `relClosed` |
| `CopyIffTopAvoid` | PROVED | `copyIffTopAvoid` |
| (R') `RelGen` | PROVED | `relGen` |
| `GenIff` | PROVED | `genIff` |
| (N) `CopyAtBot` | PROVED | `copyAtBot` |
| (T5) `T5Cell` | PROVED | `t5Cell` |
| (T5) `TopAvoidT3T5`, `CopyT3T5` | REFUTED | `not_topAvoidT3T5`, `not_copyT3T5` |
| (T6) `SigAvoidT6` (every formula) | PROVED | `sigAvoidT6` |
| (T6) `TopAvoidT3T6`, `T6Below` | PROVED | `topAvoidT3T6`, `t6Below` |
| (W1) `CopyT3T6` | PROVED | `copyT3T6` |
| (T6n) `TopAvoidN` | PROVED | `topAvoidN` |
| (C) `NotCofinal`, `BasesOnlyTop` | PROVED | `notCofinal`, `basesOnlyTop` |
| (F) `IterBounds`, `FixedInAll`, `SigFixedTop` | PROVED | `iterBounds`, `fixedInAll`, `sigFixedTop` |
| (F) `TauFixedPoint` | OPEN, not attempted | — |
| (W2) `IterRel`, `W2` | PROVED | `iterRel`, `w2` |
| (W3) `StrictNestOf`, `W3` | PROVED | `strictNestOf`, `w3` |
| (W4) `IterCopyOf`, `W4` | PROVED (`W4` is conditional on a REFUTED statement) | `iterCopyOf`, `w4` |
| target `PLLBelowTop`, `PLLBelowTopReduced` | REFUTED | `not_pllBelowTop`, `not_pllBelowTopReduced` |
| (Q1) `PLLSelfReduced`, `PLLSelf` | PROVED | `pllSelfReduced`, `pllSelf` |
| (Q2) `PLLSelfTower` | PROVED | `pllSelfTower` |
| (Q3) `PLLTowerInF0`, `TowerFirstStep` | PROVED | `pllTowerInF0`, `towerFirstStep` |
| (P1) `PLLInT6` | PROVED | `pllInT6` |
| `BaseTauIncomparable` | PROVED | `baseTauIncomparable` |

Proof notes.

* (T6), (Q1): the proof of `sig_reflects` with the hypothesis `t6` carried
  into `ext M`: `t6` holds at every world of `ext M` (`t6_ext`: at an old
  world `t5` fails, since `t3` fails there and `t4` fails by `nT`).  For (Q1),
  `orig_aTr`: at old worlds of `ext M`, `aTr t3 ψ` holds exactly where `ψ`
  holds in `M` (`p ∨ t3` reads `p`, since `t3` fails at old worlds); the
  tops satisfy every `aTr t3` formula (`top_aTr`).  Then `GenIff` with
  `x p = p ∨ t3`, `relB t3 x = aTr t3` (`relB_eq_aTr`).
* (T6n): simpler than the brief's pen argument.  `[t6 ∨ σⁿ⊥] ⊢ X` gives
  `[t6] ⊢ X`, and `C[⊥ := σⁿ⊥] = σⁿ C` (`sigN_eq_subBot`), so
  `σⁿ C = σ(σⁿ⁻¹ C)` and `SigAvoidT6`, `sigN_reflects` give `⊢ C`; no
  countermodel construction is needed.  `⊬ t6 ∨ σⁿ⊥` by the disjunction
  property (`PLLND.disjunction_property`, cut elimination).
* (W2), (Q2): `rel_comp` of `wip/f0FreeInterval.lean`, hypotheses `t3 ≤ t6`
  and `x p ≤ t6` at every world; the base case `rel ⊥ ⊤ (p ↦ p) A ⊣⊢ A`.
* (P1): a syntactic identity, `rel (rel a b x c) b (rel a b x ∘ y) A =
  rel a b x (relB c y A)` (`rel_relB`), then `freeReaders` and `copyT3T6`.
* (Q3): `freeReaders` composed with (Q2); `[σ³⊥] ⊢ g A` by `force_relB_of_b`.
  First step: `g(τ_P ⊥) = σ⁴⊥` (an equation), `g(τ_P ⊤) ⊣⊢ σ³ t6`.

Gates watched failing (`_out/gatewatch.lean`, imports the built module,
`lake env lean`, exit 1 with exactly the four intended errors): the narrowed
pins `pllSelf [propext]`, `copyT3T6 [Quot.sound]`, `not_pllBelowTop []`,
`pllTowerInF0 [propext]`.  Actual sets by `#print axioms`: `[propext,
Quot.sound]` for `pllSelf`, `pllSelfTower`, `pllTowerInF0`, `pllInT6`,
`copyT3T6`, `not_pllBelowTop`, `topAvoidN`, `sigFixedTop`, `w4`;
`[propext]` for `towerFirstStep`.  The cell gates are in the module
(`gate_t5`, `gate_T1`, `gate_q1`).

Corrections to the pen arguments of the brief.

* (T6n) needs no new countermodel (above).  The brief's suggested first check
  `[σⁿ⊥] ⊢ t6` already fails at `n = 2` (`nd_sig2_t6`), so the `∨` is needed.
* The target `FreeInPLL σ³⊥ (t6 ∨ σ³⊥) (y ∧ b)` is REFUTED, not merely
  unproved by the gadget: the gadget's failure (`t6` fails at every copy,
  through `L₀` of `ZL 0`) reflects a real collapse of the readers under `t6`.
* The manager's P2 (the composite tower `τᵈ ∘ g` in `[τᵈ σ³⊥, τᵈ⊤]`) is not
  nested: `BaseTauIncomparable`.  Replaced by (Q1)–(Q3).

Builds (all `gtimeout 3600 lake build wip.f0MovingTop`, exit 0): Stage 1
41 s (built `wip.f0FreeInterval`, `wip.f0InsideOut` on the way), Stage 2
17 s, Stage 3 22 s.  Probes (`lake env lean _out/probe*.lean`, untrusted
decider runs): one capped run, `_out/probe1.lean` at `gtimeout 600` (exit 124,
no output; it contained the same target cells as `_out/probe3.lean`), and
one killed run, `_out/probe3.lean` (exit 137, memory): the subframe tableau on
`b ↠ y q` and the O-cells of the target, whose formulas carry `phiK 3`,
`phiK 4`.  Those verdicts were obtained instead from the derivation
(`bT_O3`) and the designed tables `T1`, `T2`, checked in the interpreter
(`_out/probe4.lean`) before the kernel.  No other skip or cap.
