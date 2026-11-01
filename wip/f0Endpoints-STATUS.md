# `wip/f0Endpoints.lean`: status

Endpoint conditions for faithful interval copies of F0 and of PLL.  Matthew,
2026-11-01: "I STILL do not know what conditions on endpoints are required to
nest the PLL tower within an interval [a, b] ... regard this as the go-ahead for
that attempt."  Branch `f0-endpoints`, local, from `origin/main` 7a4af650.

## Stage 1 (2026-11-01 16:54 GMT): statements committed

All statements are `Prop` definitions in `PLLND.F0.Endpoints`; no theorem is
asserted, no `sorry`.  Status of every statement: OPEN.  The displayed forms are
the module docstring; the list:

| name | statement |
|---|---|
| `SelfStep a b` | `FreeInPLL a b (p ↦ (p ∨ a) ∧ b)` |
| `SelfStepReduced a b` | `∀ C, [b] ⊢ aTr a C ⟹ ⊢ C` |
| `ClosedStep a b` | `∃ x closed, FreeInPLL a b x` |
| `CopyStep a b` | `CopyF0In a b` |
| `SelfIffReduced` | `[a] ⊢ b ⟹ (SelfStep a b ⟺ SelfStepReduced a b)` |
| `SelfToCopy`, `ClosedToCopy` | `SelfStep a b ⟹ CopyStep a b`, `ClosedStep a b ⟹ CopyStep a b` |
| `TransportG` | `FreeInPLL a b x ⟹ FreeInPLL (g a) (g b) (g ∘ x)`, `g = relB σ³⊥ y` |
| `SelfToClosed` | `a, b` closed, `SelfStep a b ⟹ ClosedStep (σ³a) (σ³b)` |
| `SelfTower` | `SelfStep a b`, `[a] ⊬ ⊥`, `⊬ b` ⟹ the strictly nested PLL tower `SelfTowerAt a b` |
| (Na) `NecBox` | `[◯a] ⊢ a ⟹ ¬ CopyStep a b` |
| (Nb) `NecPow` | `[a] ⊢ b`, `CopyStep a b ⟹ ∀ n, [b] ⊬ Tⁿ(a)` |
| (Nc) `NecClosed`, `NecCells` | `[b] ⊬ C[⊥:=a]` for closed non-theorems `C`; instances `C = ⊥, ◯⊥, ¬◯⊥, ¬¬◯⊥` |
| (K1) `GadgetSelf` | `a, b` closed, `[a] ⊢ b`, `IsGadget G a b ⟹ SelfStep a b` |
| (K2) `BaseGadget` | `a` closed ⟹ (`CopyStep a ⊤ ⟺ ∃ G` finite, `IsGadget G a ⊤`) |
| (K1′) `TwoSidedSelf` | `SideIn a`, `SideOut a ⟹ SelfStep a ⊤` |
| `SidesOfNd` | `⊬ (◯a ↠ a) ↠ a ⟹ SideIn a`; `⊬ ◯a ↠ a ⟹ SideOut a` |
| (K2′) `BaseCriterion` | `(CopyStep a ⊤ ⟺ SelfStep a ⊤) ∧ (CopyStep a ⊤ ⟺ ⊬ ◯a ↠ a ∧ ⊬ (◯a ↠ a) ↠ a)` |
| `NoGadgetAK` | `∀ G, ¬ IsGadget G aK ⊤`, `aK = t6 ∧ (◯t3 ↠ t3)` |
| `BaseNo a`, `BaseYes a` | the base cells |
| (K3) `ExtTops` | `b` closed ⟹ (`ExtTop b ⟺ [t6] ⊢ b`) |
| (K4) `CopySelf`, `K4Cell a b C` | `CopyStep a b ⟹ SelfStep a b`; `[b] ⊬ aTr a C` |
| (K5) `K5`, `NoClosedStepT3` | `ClosedStep t3 t6`; `∀ b, ¬ ClosedStep t3 b` |

`BaseCriterion`, `TwoSidedSelf`, `SidesOfNd` and `NoGadgetAK` are additions to
the brief, stated before any cell was run: the pen analysis found that a world
in `S` and a world outside `S` may need different gadgets, and that the two
cells `⊬ ◯a ↠ a`, `⊬ (◯a ↠ a) ↠ a` decide which.

Build: `gtimeout 3600 lake build wip.f0Endpoints`, exit 0, 69 s (it built
`wip.f0InsideOut`, `wip.f0FreeInterval`, `wip.f0MovingTop` on the way).

## Stage 2 (2026-11-01 16:59 GMT): the designed cells, kernel-checked

Countermodels are `SubCM` tables judged by `SubTab.no` (`decide` in the
kernel); derivations are semantic (`Interval.deriv_of_sem`).  Every table was
designed from the pen analysis; no decider was run.  Tables: `K0` (one world
outside `S`), `KS` (one world in `S`), `Pin` (an `S`-world below a non-`S`
top), `Rout = Tfork` (a non-`S` root below an `S`-top and a non-`S` top), `Rin`
(the same, root in `S`), `DOut`/`DIn` (`ext (ext K0)`, `ext (ext KS)`),
`Klem`, `Klin`, `FreePLL.K1`–`K3`, and their `ext`, `ext ∘ ext` tables.

### K2: the base table (`b = ⊤`)

| `a` | verdict | object |
|---|---|---|
| `◯⊥` | REFUTED, `C = ¬◯⊥`: `⊢ ◯◯⊥ ↠ ◯⊥`, `⊬ ¬◯⊥` (`baseNo_e`; also (Na)) | derivation; `K0` |
| `¬◯⊥` | REFUTED, `C = ¬¬◯⊥`: `⊢ (◯¬◯⊥ ↠ ¬◯⊥) ↠ ¬◯⊥`, `⊬ ¬¬◯⊥` (`baseNo_ne`) | derivation; `KS` |
| `t4` | REFUTED, `C = ¬◯⊥`: `⊢ ◯t4 ↠ t4` (`baseNo_t4`; also (Na)) | derivation; `K0` |
| `t5` | both cells pass: `⊬ ◯t5 ↠ t5`, `⊬ (◯t5 ↠ t5) ↠ t5` (`baseYes_t5`) | `Rout`, `Rin` |
| `t6` | REFUTED, `C = ¬◯⊥`: `⊢ ◯t6 ↠ t6` (`baseNo_t6`; `t6` is a fixed point of `◯`, so (Na)) | derivation; `K0` |
| `σ²⊥` | both cells pass (`baseYes_s2`) | `DOut`, `DIn` |
| `◯t3` | REFUTED, `C = ¬◯⊥` (`baseNo_c1`; (Na)) | derivation; `K0` |
| `aK = t6 ∧ g1` | both cells pass (`baseYes_aK`) | `Rout`, `Pin` |
| `t3` | both cells pass (`baseYes_t3`), the known case | `Rout`, `Pin` |

A gadget for `t5` (b = ⊤) is the one of `ext`, `{nT, eT}`; for `σ²⊥` the four
tops of `ext ∘ ext`.  For `aK` there is none (pen, `NoGadgetAK`): a gadget `G`
forcing `aK` everywhere forces it at the root of `1_in ⊕ G` when that root
refutes `t4`, and otherwise `G ⊨ ◯⊥` everywhere, so `aK` holds at the root of
`1_out ⊕ G`.  Since `aK` passes both cells, K2 as briefed is REFUTED at `aK`
once `BaseCriterion` (the ⟸ direction) and `NoGadgetAK` are proved.

### K3: three tops strictly below `t6`

`b₁ = t6 ∧ σ²⊥`, `b₂ = t6 ∧ σt6`, `b₃ = t6 ∧ (g1 ↠ t5)`: `[t3] ⊢ bᵢ`
(`t3_b1`–`t3_b3`), `[bᵢ] ⊢ t6`, and `[t6] ⊬ bᵢ` on `ext Tfork`, `ext Tchain`,
`ext KS` (`nd_t6_b1`–`nd_t6_b3`): each fails in an `ext` model, so none is an
`ext`-top.  All PASS (t6 survives as the least `ext`-top).

### K4: 18 cells, all PASS

`[b] ⊬ aTr a C` for `(a, b) ∈ {(t3, t6), (t3, ⊤), (σ²⊥, ⊤)}` and
`C ∈ {p ∨ ¬p, ¬¬p → p, (p → q) ∨ (q → p), O1, O2, O3}` (`k4_…`), on `ext K`
and `ext (ext K)`.

### K5

The designed generators `p ↦ ◯t3 ∧ t6`, `q ↦ g1 ∧ t6` (the one-generator copy
`p ↦ ◯t3` of `freeIPL1` with its relative complement) give `[rel ⊤] ⊢ rel
¬(p ∧ q)` while `[⊤] ⊬ ¬(p ∧ q)` (`k5_cell`).  Pen, for every closed `x` and
every `b`: `noFreeHA2` gives a sign pattern `ε` with `⊢ (x₀^ε₁ ∧ x₁^ε₂) ↠ t3`,
and `rel t3 b x (p^ε) ⊢ x₀^ε`, so `[rel ⊤] ⊢ rel ¬(p^ε₁ ∧ q^ε₂)`; so
`NoClosedStepT3` (K5 REFUTED for every top).

Gates watched failing: `gate_base`, `gate_k3`, `gate_k4` (`refutes … = false`
on derivable cells).

Build: `gtimeout 3600 lake build wip.f0Endpoints`, exit 0, 15 s.  Probe:
`_out/ep_cells.lean` (`lake env lean`, 900 s cap): first run exit 1 (three
`verdict` applications missing parentheses), second run exit 0.
