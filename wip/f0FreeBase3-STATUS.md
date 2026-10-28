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
| `Free3` | — | OPEN |
| side cell `⊬ (g1 ↠ g3) ∨ (g3 ↠ g1)` | `side_cell` | PROVED (countermodel 27 → 8 worlds) |
| Stage 1 cells Ca, Cb, Cc (images no theorems) | `cell_Ca`, `cell_Cb`, `cell_Cc` | PROVED (gadget tables) |

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
| Cc | `(p₀ → p₂) ∨ (p₀ → p₂ swapped)` | fork, `p₀` at `k₁`, `p₂` at `k₂` | 13 worlds | PASS | `cell_Cc` |

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

## Log

* 2026-10-28: Stage 0, statement written and built
  (`lake build wip.f0FreeBase3`, 35 s), committed before any proof.
* 2026-10-28: Stage 1, three designed cells PASS, base facts and readings
  kernel-checked; side cell decided (not provable).
