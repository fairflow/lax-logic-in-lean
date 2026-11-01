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

## Stage 3, part 1 (2026-11-01 17:19 GMT): proofs

Every theorem is sorry-free and pinned by `#axioms_within … [propext, Quot.sound]`.
Gates watched failing (`_out/ep_gatewatch.lean`, `lake env lean`, exit 1 with
exactly the five intended errors): narrowed pins `baseCriterion [propext]`,
`noGadgetAK [Quot.sound]`, `extTops []`, `noClosedStepT3 [propext]`,
`gadgetSelf []`.  Actual sets by `#print axioms`: `[propext, Quot.sound]` for
`baseCriterion`, `not_baseGadget`, `extTops`, `noClosedStepT3`, `gadgetSelf`,
`tower_t5`, `meetNotTop`, `necBox`.

| statement | status | theorem |
|---|---|---|
| `SelfIffReduced` | PROVED | `selfIffReduced` |
| `SelfToCopy`, `ClosedToCopy` | PROVED | `selfToCopy`, `closedToCopy` |
| `TransportG`, `SelfToClosed` | PROVED | `transportG`, `selfToClosed` |
| `SelfTower` | PROVED | `selfTower` |
| (Na) `NecBox` | PROVED | `necBox` |
| (Nb) `NecPow` | PROVED | `necPow` |
| (Nc) `NecClosed`, `NecCells` | PROVED | `necClosed`, `necCells` |
| (K1) `GadgetSelf` | PROVED | `gadgetSelf` |
| (K1′) `TwoSidedSelf`, `SidesOfNd` | PROVED | `twoSidedSelf`, `sidesOfNd` |
| (K2′) `BaseCriterion` | PROVED | `baseCriterion` |
| `NoGadgetAK` | PROVED | `noGadgetAK` |
| (K2) `BaseGadget` | REFUTED | `not_baseGadget` (at `aK`) |
| (K3) `ExtTops` | PROVED | `extTops` |
| (K4) `CopySelf` at `b = ⊤` | PROVED | `copySelf_top` |
| (K4) `CopySelf`, general `b` | OPEN | — |
| (K5) `K5`, `NoClosedStepT3` | REFUTED; PROVED | `not_k5`; `noClosedStepT3` |

Corollaries: `SelfStep t5 ⊤`, `SelfStep σ²⊥ ⊤`, `SelfStep aK ⊤`
(`selfStep_t5`, `selfStep_s2`, `selfStep_aK`); K1 validated by the gadget
`G2` of `ext`: `gadget_t3_t6` (reproves `pllSelf` as `selfStep_t3_t6`) and
`selfStep_t5_t56`, a new interval `[t5, t5 ∨ t6]` with a strictly nested PLL
tower (`tower_t5`).

**The base criterion** (answers Paper III's open item for `b = ⊤`):

    a closed:   ⊥ ↦ a faithful on F0  ⟺  PLL embeds in [a, ⊤] by the A-translation
                ⟺  ⊬ ◯a ↠ a  ∧  ⊬ (◯a ↠ a) ↠ a

Proof route (`ts_realizes`): the two non-theorems give a world maximal among the
refuters of `a` in `S` and one with no `S` in its cluster (`sidesOfNd`); above
the worlds of a finite countermodel `M` that see `S` go the strict successors of
the first, above those that see a world with no `S` above it the strict
successors of the second (`TS`); terminal clusters are bisimilar to the matching
side (`isBisimIn`, `isBisimOut`, `bisim_force`), so the old worlds are exactly
the refuters of `a`, and `realize` (the induction of `orig_aTr`) reads `M` off.

**K2 as briefed fails** because one gadget must serve both kinds of terminal
world: `aK = t6 ∧ g1` passes the criterion, but a gadget forcing `aK` forces it
at the root of `1_in ⊕ G` unless that root forces `t4`, and then `G ⊨ ◯⊥`, so
the root of `1_out ⊕ G` forces `t3`, hence `aK` (`noGadgetAK`).

**K3** (`extTops`): a finite model of `t6` is bisimilar for closed formulas to
`ext` of its `R`-part (`isBisimExt`).

**K5** (`noClosedStepT3`): `noFreeHA2` for the two generators.

## Addition (the manager): tops over `t3`

Statements committed with the cells (before the proof of T1):
`TopT3Alt` (T1: `SelfStep t3 b′ ∧ [t6] ⊬ b′ ∧ [b′] ⊬ t6`, `b′ = g1 ↠ t5`),
`MeetNotTop` (T2: `¬ CopyStep t3 (t6 ∧ b′)`), `TopsT3NotMeet`, `NoLeastTopT3`.

| cell | verdict | object |
|---|---|---|
| `[t3] ⊢ b′` | PROVED (`t3_bP`) | derivation |
| `[b′] ⊬ t6` | PROVED (`nd_bP_t6`) | `Pin` |
| `[t6] ⊬ b′` | PROVED (`nd_t6_bP`) | `ext KS` |
| T2: `[t6 ∧ b′] ⊢ σ(¬¬◯⊥) = g1 ↠ t3` | PROVED (`meet_sig_nne`) | derivation |
| (T2) `MeetNotTop` | PROVED (`meetNotTop`) | `C = ¬¬◯⊥` |
| gate | `Pin`, `ext KS` do not refute `[t3] ⊢ b′` (`gate_T`) | |

Builds: `gtimeout 3600 lake build wip.f0Endpoints`, exit 0, 42 s.  Probes
(`lake env lean _out/ep_proofsA/B/C/T.lean`, 900 s cap): A exit 0; B exit 1
twice (set-builder syntax, implicit arguments, a continuation line), then 0;
C exit 0 with one unused-section-variable warning (fixed), T exit 0.

## Stage 3, part 2 (2026-11-01 17:26 GMT): T1 proved; L statements and cells

| statement | status | theorem |
|---|---|---|
| (T1) `TopT3Alt` | PROVED | `topT3Alt` (`selfStep_t3_bP`) |
| (T2) `MeetNotTop` | PROVED | `meetNotTop` |
| `TopsT3NotMeet` | PROVED | `topsT3NotMeet` (`t6`, `b′`) |
| `NoLeastTopT3` | PROVED | `noLeastTopT3` |

So over the base `t3` the admissible tops (`CopyStep t3 b`, `[t3] ⊢ b`) are
upward closed, contain the incomparable `t6` and `b′ = (◯t3 ↠ t3) ↠ t5`
(each with a faithful copy of PLL by the A-translation), are not closed under
`∧`, and have no least element.  `t6` is the least top of the gadget `ext`
(`extTops`); `b′` comes from the realization `MinR` (the non-`S` top above every
world, the `S`-top only above the worlds seeing a world with no `S` above it).

The L addition (statements committed with cells, before any proof):
`TowerEnds` (L1), `Closing` (L2), `InAll`, `InAllUnique`, `InAllFixed`,
`FixedIffInAll` (L3), `NoTauFixedPoint` (L4, the conjecture, OPEN).

| cell | verdict | object |
|---|---|---|
| `[⊤] ⊬ τ⊤` | PROVED (`notFixed_top`) | `Tchain` |
| `[t6] ⊬ τt6` | PROVED (`notFixed_t6`) | `ext Tchain` |
| `[U₂] ⊬ τU₂` | PROVED (`notFixed_U2`) | `ext (ext Tchain)` |
| gate: the tables on the derivable `[τx] ⊢ x` | rejected (`gate_L`) | |

Build: `gtimeout 3600 lake build wip.f0Endpoints -q`, exit 0, 18 s (olean
written 17:26:10).  Probes `_out/ep_proofsT1.lean`, `_out/ep_L.lean`: exit 0.

## Stage 3, part 3 (2026-11-01 17:29 GMT): L1–L3 proved, L4 OPEN

| statement | status | theorem |
|---|---|---|
| (L1) `TowerEnds`: `τᵈ⊤ ⊣⊢ U_d`, `τᵈ⊥ ⊣⊢ σᵈ⊥ ∧ U_d` | PROVED | `towerEnds` (from `tauN_closed`: `τᵈA ⊣⊢ σᵈA ∧ U_d`, closed `A`) |
| (L2) `Closing` | PROVED | `closing` (`cm_eventually`: in a finite model `σᴺ⊥` holds everywhere for large `N`) |
| `InAllUnique`, `InAllFixed` | PROVED | `inAllUnique`, `inAllFixed` |
| (L3) `FixedIffInAll` | PROVED | `fixedIffInAll` |
| (L4) `NoTauFixedPoint` | OPEN, no proof attempted | cells `notFixed_top`, `notFixed_t6`, `notFixed_U2` |

So the intervals `[τᵈ⊥, τᵈ⊤] = [σᵈ⊥ ∧ U_d, U_d]` close on at most one element of
F0, which is then the unique closed fixed point of `τ`; otherwise they close on a
gap.

**L4, where the route stops.**  Pen: a fixed point `x` satisfies
`x ⊣⊢ σᵈx ∧ U_d` for every `d`, so in a finite model it agrees with "`σᵈ t6` for
every `d`"; peeling `M ↦ M ∖ ⟦t3⟧` (the restriction lemma behind `realize`),
that set is "`t6` holds at every peeling stage until the world forces `t3`",
and the number of stages is unbounded over finite models.  A proof needs (i) a
depth measure on closed formulas with invariance under depth-bounded
bisimulation of subframe models, choice-free, and (ii) for each depth `k` a
pair of finite models, `k`-bisimilar at the roots, one with `U_D` and not
`σᴰ t6`, one with every `σᵈ t6`.  The repository has neither in usable form:
its layered bisimulation (`LaxLogic/PLL/SemUI/SemUILayered.lean`) is for
constraint models with a budget over a finite formula set and is pinned
`[propext, Classical.choice, Quot.sound]`; `SubframeAmalg.lean` has budgeted
bisimulations only inside its amalgamation construction.  The obvious pair
`ext^D Tchain`, `ext^D KS` does not work: `U_D` holds at both roots, but the
roots differ in `S`-membership, which a formula of depth 1 detects.  Stopped
here, as instructed.

Gates watched failing, round 2 (`_out/ep_gatewatch2.lean`, exit 1, exactly five
errors): `closing [propext]`, `selfStep_t3_bP [Quot.sound]`,
`noLeastTopT3 []`, `fixedIffInAll [propext]`, `towerEnds []`; actual sets
`[propext, Quot.sound]`.

## Builds, probes, caps

| run | command | exit | time |
|---|---|---|---|
| build 1 (stage 1) | `gtimeout 3600 lake build wip.f0Endpoints` | 0 | 69 s (built `f0InsideOut`, `f0FreeInterval`, `f0MovingTop`) |
| build 2 (stage 2) | same | 0 | 15 s |
| build 3 (stage 3, part 1) | same | 0 | 42 s |
| build 4 (T1, L statements) | same, `-q` | 0 | 18 s |
| build 5 (L1–L3) | same, `-q` | 0 | 16 s |
| probes | `lake env lean _out/ep_*.lean` under `gtimeout 900` | `ep_cells` 1 then 0; `ep_proofsB` 1, 1, then 0; all others 0 | each under 1 min |
| gate watches | `_out/ep_gatewatch.lean`, `_out/ep_gatewatch2.lean` | 1 (as required) | |

No decider run (`SubTab.solve`, `pllfast`, `plldecide`) was needed: every table
was designed by hand.  No cap was hit, nothing was skipped.
