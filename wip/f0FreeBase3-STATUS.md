# wip/f0FreeBase3.lean — status

Does one family of generators above `σ³⊥ = base 3` freely generate the free
Heyting algebra on every finite number of generators?  (Brief 2026-10-28,
follow-up to `wip/f0FreePair.lean`.)  Public order theory about F0.  Pins
`[propext, Quot.sound]` throughout; no `Classical.choice`, no `sorry`, no
`native_decide`.

## The statement (committed before any proof, METHOD.md §1)

    σ³⊥  = ◯σ²⊥ ∨ (◯σ²⊥ ↠ σ²⊥)                          (`base_three`, by `rfl`)
    φ_k  = relX (rn (2k+1))                              (`phiK`)
    c_r  = φ_{r+1} ∨ (φ_{r+2} ↠ σ²⊥)                     (`sepC`)
    x₀   = ◯σ³⊥,   x_r = σ³⊥ ∨ ((c_r ↠ σ²⊥) ↠ σ²⊥)  (r ≥ 1)   (`gen`)
    x3 a = gen (utf8ByteSize a - 1),  so x3 (pvar i) = gen i    (`x3`)

    Free3 :  ∀ n A B ◯-free with varsBelow n,
               [A] ⊢ B  ⟺  [relB σ³⊥ x3 A] ⊢ relB σ³⊥ x3 B

    FreeFamily3 :  ∃ x, (∀ a, x a variable-free) ∧ (∀ a, [σ³⊥] ⊢ x a) ∧
                      ∀ n A B ◯-free with varsBelow n,
                        [A] ⊢ B ⟺ [relB σ³⊥ x A] ⊢ relB σ³⊥ x B

    Free3 → FreeFamily3 → ∀ n, FreeHAnAbove (σ³⊥) n → Conjecture

Side cell: `⊢? (g1 ↠ g3) ∨ (g3 ↠ g1)`, `g1 = oddGap 0`, `g3 = oddGap 1`
(`sideCell`).

Fragment first (CLAUDE.md rule 8): degenerate, as in `f0FreePair` (the ◯-free
variable-free fragment is `{⊥, ⊤}`).

## Status table

| statement | theorem | status |
|-----------|---------|--------|
| `σ³⊥ = ◯σ²⊥ ∨ (◯σ²⊥ ↠ σ²⊥)` | `base_three` | PROVED (`rfl`) |
| generators variable-free, above `σ³⊥` | `x3_vf`, `b3_le_x3` | PROVED |
| `Free3 → FreeFamily3` | `freeFamily3_of_free3` | PROVED (packaging) |
| `FreeFamily3 → ∀ n, FreeHAnAbove (σ³⊥) n` | `freeHAnAbove_of_family` | PROVED (packaging) |
| `(∀ n, FreeHAnAbove (σ³⊥) n) → Conjecture` | `conjecture_of_base3` | PROVED (packaging) |
| side cell `⊬ (g1 ↠ g3) ∨ (g3 ↠ g1)` | `side_cell` | PROVED (countermodel 27 → 8 worlds) |
| Stage 1 cells Ca, Cb, Cc (images no theorems) | `cell_Ca`, `cell_Cb`, `cell_Cc` | PROVED (gadget tables) |
| forcing invariant under p-morphisms | `force_pmorph` | PROVED |
| every world of `ZL r` forces `σ³⊥` | `Cell.b3_all` | PROVED |
| `c_s` at the bottom of `ZL r`, `r ≠ s` | `Cell.sep_bot` | PROVED |
| `c_r ↠ σ²⊥` at the bottom of `ZL r` | `Cell.sepimp_bot` | PROVED |
| `◯Y ⊩` every `φ_k` | `force_phiK_of_xf` | PROVED |
| the cells embed in the gadget | `Gad.zforce` | PROVED |
| killer facts (`kn ⊩ ◯Y`, `kn ⊮ σ²⊥`, `kn ⊩ ◯σ²⊥`, `kn ⊩ c_s`) | `Gad.kn_xf`, `kn_not_b2`, `kn_c2`, `kn_sep` | PROVED |
| `w_k ⊮ σ³⊥`; back condition | `Gad.w_not_b3`, `Gad.w_back` | PROVED |
| `w_k ⊩ x₀ ⟺ ¬ D 0 k`; `w_k ⊩ x_{s+1} ⟺ ¬ D (s+1) k` | `Gad.w_gen0`, `Gad.w_gen_succ` | PROVED |
| `x3 (pvar i) = gen i` | `x3_pvar` (via `utf8ByteSize_pvar`) | PROVED |
| the gadget transfer `w_k ⊩ relB σ³⊥ x3 A ⟺ k ⊩ A` | `Gad.transfer` | PROVED |
| `Free3`, `⟹` / `⟸` | `free3_preserves` / `free3_reflects` | PROVED |
| **`Free3`** | `free3` | **PROVED** |
| **`FreeFamily3`** | `freeFamily3` | **PROVED** |
| **`∀ n, FreeHAnAbove (σ³⊥) n`** | `freeHAnAbove_base3` | **PROVED** |
| **`Conjecture`** (`∀ n ∃ m, FreeHAnAbove (σᵐ⊥) n`) | `conjecture` (`m = 3`) | **PROVED** |
| `code : String → Nat` injective (UTF-8 bytes) | `code_inj` (via `encB_inj`) | PROVED |
| `relB_transfer`, `relB_preserves` without `varsBelow` | `relB_transferω`, `relB_preservesω` | PROVED |
| `FreeOmega3`: `∀ A B ◯-free, [A] ⊢ B ⟺ [relB σ³⊥ xω A] ⊢ relB σ³⊥ xω B`, `xω a = gen (code a)` | `freeOmega3` | PROVED |
| **`FreeHAωAbove (σ³⊥)`** | `freeHAωAbove_base3` | **PROVED** |

## The gadget design (pen, checked against the brief before building on it)

Brief points, verified:

1. Syntax: `base 3 = ◯σ²⊥ ∨ (◯σ²⊥ ↠ σ²⊥)` by `rfl` (`base_three`).
2. A `σ²⊥`-maximal world `m` forces `σ³⊥`: if `m ∉ S`, every `S`-point above
   it is a proper successor and forces `σ²⊥`, so `m ⊩ ◯σ²⊥`; if `m ∈ S`, any
   `v ≥ m` forcing `◯σ²⊥` and refuting `σ²⊥` lies below `m` (maximality), so
   `◯σ²⊥` at `v` gives `σ²⊥` at `m ∈ S`, impossible: `m ⊩ ◯σ²⊥ ↠ σ²⊥`.
   (The case `m ∉ S` uses antisymmetry at `m`; the gadget is a partial order.)
3. Killers above a copy `w`: an `S`-killer refutes `σ²⊥`, so `w ⊮ ◯σ²⊥`; a
   non-`S` killer forces `◯σ²⊥` and refutes `σ²⊥`, so `w ⊮ ◯σ²⊥ ↠ σ²⊥`.  So
   `w ⊮ σ³⊥`.
4. `x₀ = ◯σ³⊥` at `w_k` ⟺ no copy `w_j ∈ S` above ⟺ `k ⊩ p₀`, with
   `w_j ∈ S ⟺ j ⊮ p₀`.
5. `x_r` at `w_k` ⟺ `(c_r ↠ σ²⊥) ↠ σ²⊥` at `w_k` ⟺ the reader `m_r` is not
   above `w_k` ⟺ `k ⊩ p_r`.  Needed: both killers force `c_r` and refute
   `σ²⊥` (so they, and every copy below them, refute `c_r ↠ σ²⊥`), every
   other world above a copy forces `σ²⊥` or is a reader, and a reader `m_s`
   forces `c_r ↠ σ²⊥` iff `s = r`.
6. Readers: `c_r = φ_{r+1} ∨ (φ_{r+2} ↠ σ²⊥)` fails at the bottom of `ZL r`
   and holds at the bottom of `ZL n` for `n ≠ r` (`cell_force n k`: bottom of
   `ZL n` forces `φ_k` iff `n + 2 ≤ k`).

Choice of killers (brief point 8, mine):

* `S`-killer `m₀` = the bottom of `ZL 0` (in `S`).  Since `r ≥ 1`, `0 + 2 ≤ r + 1`,
  so `m₀ ⊩ φ_{r+1}`, hence `m₀ ⊩ c_r` for every reader `r`.
* non-`S` killer `kn` = the bottom of `ZL 0` taken OUT of `S` (it sees `e₀`,
  `n₀`, `L₀`, `f`).  Its `S`-successors `n₀`, `L₀` force `Y`, so `kn ⊩ ◯Y`,
  the generator of the ladder; every odd rung `rn (2k+1)` has `p` as an
  iterated first disjunct, so `kn ⊩ φ_k` for every `k`, hence `kn ⊩ c_r`.
  `kn ⊮ ◯t3` (by `L₀`), `kn ⊮ ◯t3 ↠ t3` (by `f`), so `kn ⊮ σ²⊥`; its proper
  successors force `σ²⊥`.
* An `S`-killer forcing `◯Y` does not exist (pen): an `S`-point refuting
  `σ²⊥` must see a world forcing `◯⊥` (so it refutes `¬t4`) and an `S`-top
  (to refute `◯t3 ↠ t3`), so it refutes `t4`, hence `Y`, hence `◯Y`.  This is
  why the `S`-killer is read off the ladder (`φ_{r+1}` at `ZL 0`) and the
  non-`S` killer off the generator.

Correction to the brief: the cell `(p₁ → p₂) ∨ (p₂ → p₁)` (and
`(p₀ → p₂) ∨ (p₂ → p₀)`) has no one- or two-node IPC countermodel (every
linear model validates it); the designed `K` is the three-node fork.

## Stage 1: the designed cells (CLAUDE.md rules 7, 9)

`p₀ = pvar 0 = "p"`, `p₁ = "pp"`, `p₂ = "ppp"`.  The gadget over `K`, upper
structure shared between the cells (worlds `0 e₀`, `1 n₀`, `2–4 L₀–L₂`,
`5 f`, `6 m₀`, `7 m₁`, `8 m₂`, `9 kn`, `10… w_k`), as `SubCM` tables.

| cell | IPC formula | `K` | gadget | verdict | theorem |
|------|-------------|-----|--------|---------|---------|
| Ca | `(p₁ → p₂) ∨ (p₂ → p₁)` | fork, `p₁` at `k₁`, `p₂` at `k₂` | 13 worlds | PASS (image no theorem) | `cell_Ca` |
| Cb | `¬¬p₂ → p₂` | chain, `p₂` at `k₁` | 12 worlds | PASS | `cell_Cb` |
| Cc | `(p₀ → p₂) ∨ (p₂ → p₀)` | fork, `p₀` at `k₁`, `p₂` at `k₂` | 13 worlds | PASS | `cell_Cc` |

Base facts on each table (`baseFacts_Ca/Cb/Cc`): `0–5` force `σ²⊥`; `6–9`
refute `σ²⊥` and are `σ²⊥`-maximal; every non-copy forces `σ³⊥` and every
copy refutes it; `c₁` fails at `m₁` and holds at `m₀`, `m₂`, `kn`; `c₂` fails
at `m₂` and holds at `m₀`, `m₁`, `kn`; `m_r ⊩ c_r ↠ σ²⊥`; `m₀ ∈ S`,
`kn ∉ S`, `kn ⊩ ◯σ²⊥`, `kn ⊩ ◯Y`.  Readings (`read_Ca/Cb/Cc`): `gen i` holds
at `w_k` iff `p_i` holds at `k`, all nine (six) entries.  All by
`decide +kernel`; the largest image (Ca, 3915 nodes) checks in 0.5 s.

Side cell: `⊬ (g1 ↠ g3) ∨ (g3 ↠ g1)` (`side_cell`; `refbench fact`, built
binary under `gtimeout 300`, under a second, countermodel 27 → 8 worlds,
kernel-checked against `sideCell` as computed in Lean).  The cell does not
rule out the odd-gap pair.

## Stage 2: the proof (PROVED)

The gadget `Gad.MK hD` over a Kripke model `K` and a family `D : Nat → K → Prop`
of down-sets (`hD`).  Worlds (`Gad.Pt`, a bare inductive, no `Fin`):

    z r a   a world a of the cell ZL r (every r : Nat)      order and S of ZL r
    kn      the non-S killer                                sees z 0 a for a < 4 (e₀, n₀, w₀, f of ZL 0)
    w k     a copy of k ∈ K                                 w_j ≤ w_k ⟺ j ≤ k; w_k sees kn and all of ZL 0;
                                                            w_k sees ZL (r+1) iff D (r+1) k;  w_k ∈ S ⟺ D 0 k

The cells are generated submodels (`Gad.zforce`, by `force_pmorph`), so every
fact of `wip/f0FreeHAn.lean` about `ZL r` transfers: `ZL.force_b2`,
`ZL.not_force_b2_m`, `ZL.cell_force`, `ZL.force_Y_iff`, `ZL.not_force_t3`,
`ZL.force_c1_f`.  The `S`-killer is `z 0 (bottom)`; the reader of `x_r` is
`z r (bottom)`.  The model is infinite (one cell for every `r`); soundness
holds in every subframe model, and only `K` needs to be finite
(`completeness_imp`).  For `x3` the family is `D r k ⟺ k ⊮ pvar r`
(`Gad.Dp`); `Gad.w_read` reads the valuation (decidable by `FinDec K`), and
`relB_transfer` of `f0FreePair` with `φ = w`, `b = σ³⊥`, gives `Gad.transfer`.
`free3_reflects`: `completeness_imp` reduces `[A] ⊢ B` to forcing in finite
`K`; at `k ⊩ A`, `w_k ⊩ relB A` (transfer), `w_k ⊩ relB B` (soundness), `k ⊩ B`
(transfer).  `free3_preserves` is `relB_preserves` of `f0FreePair`.

`x3 (pvar i) = gen i` uses `String.ofList_append`, `String.utf8ByteSize_append`
(both choice-free) and `decide` on `"p"`.

## Stage 2 (f): every variable a generator (PROVED)

`FreeHAωAbove (σ³⊥)` (optional in the brief; done because the injection was
cheap): `encB (b :: l) = b + 1 + 257 · encB l` on byte lists, `code a =
encB a.toByteArray.data.toList`, injective by `String.toByteArray_inj`,
`ByteArray.ext`, `Array.toList_inj`, `UInt8.toNat_inj` (all choice-free; no
`String.toList`, no `String.length`).  `xω a = gen (code a)`; the empty string
gets `x₀`.  Same gadget with `D r k ⟺ ∀ a, code a = r → k ⊮ a` (`Gad.Dω`);
`Gad.w_readω` uses `code_inj`.  Contrast: the same statement at `t3`
(`FreeIPLInAboveT3`) is REFUTED (`not_FreeIPLInAboveT3`, `wip/f0FreeIPL.lean`).

## Gates (watched failing, 2026-10-28, scratch gate file, `lake env lean`)

* `#axioms_within free3 [propext]`: FAIL ("depends on Quot.sound"); the
  module's `[propext, Quot.sound]` pin passes.
* `#axioms_within Gad.transfer []`: FAIL (propext, Quot.sound).
* `TCb` with the reader `m₂` (and `L₂`) taken from above `w_{k₀}`: REJECTED by
  `decide` (the root then forces `x₂`).
* `TCc` with the non-`S` killer `kn` taken from above the copies: REJECTED
  (the copies then force `◯σ²⊥ ↠ σ²⊥`, hence `σ³⊥` and every generator).
* `#axioms_within freeHAωAbove_base3 [propext]`: FAIL (Quot.sound).
* `code "pq" = code "qp"` by `decide`: REJECTED ("is false"); control:
  `idx "pq" = idx "qp"` by `decide` passes (`idx` is not injective).

## Skips and caps

None.  One producer run (`refbench fact` on the side cell, `gtimeout 300`,
under a second).  Builds: `lake build wip.f0FreeBase3` only; `lake env lean`
on scratch files (probes, the Stage 2 draft, the gate file).

## Log

* 2026-10-28: Stage 0, statement written and built
  (`lake build wip.f0FreeBase3`, 35 s), committed before any proof.
* 2026-10-28: Stage 1, three designed cells PASS, base facts and readings
  kernel-checked; side cell decided (not provable).
* 2026-10-28: Stage 2, `Free3`, `FreeFamily3`, `∀ n, FreeHAnAbove (σ³⊥) n`
  and `Conjecture` PROVED (`lake build wip.f0FreeBase3` clean, every pin
  `[propext, Quot.sound]`); gates watched failing.
* 2026-10-28: Stage 2 (f), `FreeHAωAbove (σ³⊥)` PROVED (`lake build
  wip.f0FreeBase3` clean); gates watched failing.
