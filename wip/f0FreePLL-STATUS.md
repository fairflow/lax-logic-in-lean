# wip/f0FreePLL.lean — status

Does PLL embed faithfully into its own closed fragment, `◯` included?  Drop
the generator `x₀ = ◯σ³⊥` of `wip/f0FreeBase3.lean`, keep only its readers
`gen (r+1)`, and map `◯` to `◯`.  (Conjecture approved by Matthew
2026-10-28; brief from the manager the same day.)  Public order theory
about F0.

## The statement (committed before any proof, METHOD.md §1)

    y a = gen (code a + 1)                                         (`xr`)

    FreeReaders :       ∀ A B,  [A] ⊢ B  ⟺  [relB σ³⊥ y A] ⊢ relB σ³⊥ y B

    FreePLLAbove b :    ∃ x, (∀ a, x a variable-free) ∧ (∀ a, [b] ⊢ x a) ∧
                           ∀ A B,  [A] ⊢ B  ⟺  [relB b x A] ⊢ relB b x B
    target:             FreePLLAbove (σ³⊥)

    FreePLLnAbove b n : the same, A and B over pvar 0, …, pvar (n-1)

    Stage A (rule 8):   FreeReadersIPC : the same as FreeReaders, A and B ◯-free

Designed cells (Stage B), atoms `a0 = ""` (code 0, read by `gen 1`) and
`a1 = "\x00"` (code 1, read by `gen 2`):

    O1 = ◯p → p,    O2 = ◯p ∨ ¬◯p,    O3 = ◯(p ∨ q) → ◯p ∨ ◯q

## Status table

| statement | theorem | status |
|-----------|---------|--------|
| readers variable-free, above `σ³⊥` | `xr_vf`, `b3_le_xr` | PROVED |
| the readers' gadget: cells embed, killer facts, `w_k ⊮ σ³⊥`, back condition, for every `S` on the copies | `GadR.zforce`, `GadR.kn_*`, `GadR.w_not_b3`, `GadR.w_back` | PROVED |
| `w_k ⊩ gen (s+1) ⟺ ¬ Dr (s+1) k`; `w_k ⊩ xr a ⟺ k ⊩ a` | `GadR.w_gen_succ`, `GadR.w_read` | PROVED |
| ◯-free transfer, every `S` on the copies | `GadR.transferIPC` | PROVED |
| **`FreeReadersIPC`** (Stage A) | `freeReadersIPC` | **PROVED** |
| `⊬ O1`, `⊬ O2`, `⊬ O3` in PLL | `pll_O1`, `pll_O2`, `pll_O3` | PROVED (1-, 2-, 3-world countermodels) |
| Stage B images `relB σ³⊥ xr Oᵢ` no theorems | `cell_O1`, `cell_O2`, `cell_O3` | PROVED (gadget tables, 11, 12, 13 worlds) |
| base facts and readings on the three tables | `baseFacts_K1/K2/K3`, `reads_K1/K2/K3` | PROVED |
| relativisation lemma with `◯` (under `hS`) | `relB_transferO` | PROVED |
| restriction `R_b` keeping `S`; transfer to it | `restrictS`, `relB_restrictS` | PROVED |
| preservation for all formulas (`⟹`) | `relB_preservesO` | PROVED |
| gadget transfer, `◯` included, copies with `K`'s `S` | `GadR.transfer` | PROVED |
| `FreeReaders`, `⟹` / `⟸` | `freeReaders_preserves` / `freeReaders_reflects` | PROVED |
| **`FreeReaders`** | `freeReaders` | **PROVED** |
| **`FreePLLAbove (σ³⊥)`** | `freePLLAbove_base3` | **PROVED** |
| `FreePLLAbove b → FreePLLnAbove b n` | `freePLLnAbove_of` | PROVED (packaging) |
| **`∀ n, FreePLLnAbove (σ³⊥) n`** | `freePLLnAbove_base3` | **PROVED** |
| `FreePLLAbove b → FreeHAωAbove b` | `freeHAωAbove_of_freePLL` | PROVED (packaging) |
| `x3`-gadget: `w_k ⊩ ◯x₁ ⟹ k ⊩ p₀ ∨ p₁` | `x3gad_circ_x1` | PROVED |
| `⊬ ◯x₁ ↠ x₀ ∨ x₁` (`x₀ = ◯σ³⊥`, `x₁ = gen 1`) | `sep_circ_x1` | PROVED (12-world table `Tsep`) |
| complement: `◯x₁` ⊣⊢ no `x3`-image of a ◯-free formula over `pvar 0 … pvar (n-1)` | `not_image_circ_x1` | PROVED |

## Stage A (rule 8): the ◯-free fragment, PROVED

The gadget `GadR.MS K Sw` is `Base3.Gad.MK` with two changes: `w_k ∈ S`
iff `Sw k` (a parameter), and the reading `Dr`: `Dr 0` empty (the `S`-killer,
the bottom of `ZL 0`, sits above every copy in `Base3.Gad.Le` whatever `D 0`
is), `Dr (r+1) k ⟺ k` refutes every atom of code `r`.  The order is
`Base3.Gad.Le K (Dr K)` unchanged, so `Base3.Gad.Le.refl`/`Le.trans` are
reused; the lemmas `zforce` … `w_gen_succ` are those of `Base3.Gad` with the
model replaced (none of them looks at the `S` of a copy).  `relB_transferω`
of `f0FreeBase3` gives `transferIPC` for every `Sw`; the direction `⟸` uses
`Sw = ∅`, the direction `⟹` is `relB_preservesω`.  No
`wip/f0FreeAnyFamily` was on main (da627e0), so nothing to cite.

## Stage B (rule 9): three designed cells, all PASS

| cell | PLL formula | `K` | gadget `gadT K` | image | theorem |
|------|-------------|-----|-----------------|-------|---------|
| O1 | `◯p → p` | one world, `∉ S`, no atoms | 11 worlds | PASS (no theorem) | `cell_O1` |
| O2 | `◯p ∨ ¬◯p` | `k₀ ∈ S` below `k₁ ∉ S` | 12 worlds | PASS | `cell_O2` |
| O3 | `◯(p ∨ q) → ◯p ∨ ◯q` | `k₀ ∉ S` below `S`-tops `k₁ ⊩ p`, `k₂ ⊩ q` | 13 worlds | PASS | `cell_O3` |

`p = a0 = ""`, `q = a1 = "\x00"`, so `xr p = gen 1`, `xr q = gen 2` (the
kernel computes `code` on these literals; the code of `"p"` is 113, whose
reader `gen 114` would be far too large to evaluate).  `gadT K` builds the
table in Lean from `K`: the upper worlds `0 … 9` of `f0FreeBase3`
(`e₀ n₀ L₀ L₁ L₂ f m₀ m₁ m₂ kn`), then the copy `10 + i` of each world `i`,
in `S` iff `i ∈ S`, seeing `e₀ n₀ L₀ f m₀ kn` always, `m₁` and `L₁` iff
`i ⊮ p`, `m₂`, `L₁`, `L₂` iff `i ⊮ q`.  On each table `f0FreeBase3`'s
`baseFacts` holds, and `readsB`: at every copy `xr p`, `xr q` hold iff `p`,
`q` hold at the world, and the copy is in `S` iff the world is.

## Stage C: the proof (PROVED)

`relB_transferO` is `relB_transferω` of `f0FreeBase3` with a `◯` case,
under `hS : ∀ k, φ k ∈ M.S ⟺ k ∈ K.S`:

* `⟹`: for `j ≥ k` in `K.S`, `φ j ≥ φ k` and `φ j ∈ M.S`, so `φ j ⊩ relB A`,
  so `j ⊩ A`.
* `⟸`: an `S`-point `v ≥ φ k` either forces `b`, hence every `relB`-image
  (`force_relB_of_b`, which already covers `◯`), or is `φ j`, `j ≥ k`, and
  then `j ∈ K.S`, so `j ⊩ A`, so `φ j ⊩ relB A`.

Direction `⟹` of the theorem (`relB_preservesO`), semantic route: at a world
`v ⊮ b` of a finite model, the restriction `R_b` to the worlds refuting `b`,
with `S` restricted and `V a = {u : u ⊩ x a}` (`restrictS`), satisfies the
hypotheses of `relB_transferO` with `φ = Subtype.val` (`hS` by definition);
soundness on `R_b` and `completeness_imp` finish.  (The repository has term
substitution, `LaxLogic/PLL/ND/Subst.lean`, but no atom-substitution lemma on
`LaxND`; the semantic route needed no new syntax.)

Direction `⟸` (`freeReaders_reflects`): the readers' gadget
`GadR.MS K (· ∈ K.S)` satisfies `hS` by definition; every other hypothesis
is a Stage A lemma, all independent of the copies' `S`.  So
`w_k ⊩ relB σ³⊥ xr A ⟺ k ⊩ A` for every `A` (`GadR.transfer`), and
`completeness_imp` reduces `[A] ⊢ B` to finite `K`.

The manager's pen argument holds as written; nothing in it was wrong.  The
one thing the brief did not say: the Stage B cells cannot use the atoms
`pvar i`, since `code "p" = 113` and the reader `gen 114` is too large to
evaluate; the atoms `""` and `"\x00"` (codes `0`, `1`) were used.

## The complement witness (optional in the brief; PROVED, about 50 lines)

With the `x₀` generators of `f0FreeBase3` (`x3`), the range is not closed
under `◯`:

    ¬ ∃ n A,  A ◯-free over pvar 0 … pvar (n-1)  ∧
              [◯x₁] ⊢ relB σ³⊥ x3 A  ∧  [relB σ³⊥ x3 A] ⊢ ◯x₁

(`not_image_circ_x1`).  In every `f0FreeBase3` gadget `w_k ∈ S ⟺ k ⊮ p₀`,
so `w_k ⊩ ◯x₁` gives `k ⊩ p₀ ∨ p₁` (`x3gad_circ_x1`); with `Gad.transfer`
of `f0FreeBase3` and `completeness_imp`, `[relB A] ⊢ ◯x₁` gives
`[A] ⊢ p₀ ∨ p₁`, then `relB_preservesω` gives `[relB A] ⊢ x₀ ∨ x₁`, and with
`[◯x₁] ⊢ relB A` the cut `[◯x₁] ⊢ x₀ ∨ x₁`.  The table `Tsep` (upper worlds
`0 … 9`, then `w ∉ S` below `s ∈ S`, the reader `m₁` and `L₁` above `w`
only) refutes `◯x₁ ↠ x₀ ∨ x₁` (`sep_circ_x1`).  The pen argument said
`◯x₁ ⟺ p₀ ∨ p₁` at the copies; only the direction `⟹` is needed.  The
statement is for formulas over `pvar 0 … pvar (n-1)`; since
`x3 a = gen (idx a)`, every `x3`-image is the image of such a formula, but
that renaming is not mechanised here.

## Gates (watched failing, 2026-10-28, scratch gate file, `lake env lean`)

* `#axioms_within freePLLAbove_base3 [propext]`: FAIL (Quot.sound).
* `#axioms_within GadR.transfer []`: FAIL (propext, Quot.sound).
* `gadT K2` with the copies' `S` read as in the `x₀` gadget (`w_k ∈ S` iff
  `k ⊮ p`, here both copies): the O2 verdict is REJECTED (`decide`: false).
  So the copies must carry `K`'s own `S`.
* `gadT K2` with no copy in `S` (Stage A's choice `Sw = ∅`): O2 REJECTED.
* `gadT K1` with the readers `m₁`, `m₂` (and `L₁`, `L₂`) taken from above
  the copy: O1 REJECTED (the copy then forces `gen 1`).
* Control: the unmodified `gadT K2` is accepted.
* `Tsep` with `s` taken out of `S`: `sep_circ_x1` REJECTED (`w` then
  forces `x₀ = ◯σ³⊥`).
* `#axioms_within not_image_circ_x1 [Quot.sound]`: FAIL (propext).

## Skips and caps

None.  No producer run (every countermodel and gadget table was designed by
hand and checked by `decide +kernel`).  Builds: `lake build wip.f0FreePLL`
only; `lake env lean` on scratch files (the probe of `code` on literals, the
drafts, the gate file).

## Log

* 2026-10-28: Stage 0, statement written and checked (`lake env lean`),
  committed before any proof.
* 2026-10-28: Stage A, `FreeReadersIPC` PROVED, pins `[propext, Quot.sound]`.
* 2026-10-28: Stage B, three designed cells PASS (`decide +kernel` on the
  gadget tables), base facts and readings kernel-checked.
* 2026-10-28: Stage C, `FreeReaders`, `FreePLLAbove (σ³⊥)` and
  `∀ n, FreePLLnAbove (σ³⊥) n` PROVED (`lake build wip.f0FreePLL` clean,
  every pin `[propext, Quot.sound]`); gates watched failing.
* 2026-10-28: the complement witness for `x3` PROVED
  (`not_image_circ_x1`); gates watched failing.
