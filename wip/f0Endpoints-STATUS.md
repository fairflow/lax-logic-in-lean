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
