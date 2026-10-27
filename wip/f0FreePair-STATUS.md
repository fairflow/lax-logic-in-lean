# wip/f0FreePair.lean — status

Does the pair `(x₀, x₁)` of `wip/f0FreeHAn.lean` freely generate a copy of
the free Heyting algebra `H₂` on two generators inside `[σ²⊥, ⊤]` of F0,
with bottom `σ²⊥`?  (Matthew, 2026-10-27.)  Public order theory about F0.
Pins `[propext, Quot.sound]` throughout; no `Classical.choice`, no `sorry`,
no `native_decide`.

## The statement (committed before any proof, METHOD.md §1)

    b  = σ²⊥ = ◯t3 ∨ (◯t3 ↠ t3)                      (`b2 = base 2`)
    x₀ = ◯σ²⊥,   x₁ = σ²⊥ ∨ ((◯Y ↠ t3) ↠ t3),   Y = t4 ∨ ¬t4
    xs (pvar 0) = x₀,  xs (pvar 1) = x₁,  xs a = x₀ otherwise        (`xs`)

    FreePair :  ∀ A B ◯-free with varsBelow 2,
                  [A] ⊢ B  ⟺  [relB σ²⊥ xs A] ⊢ relB σ²⊥ xs B

    freeHAn_of_freePair :  FreePair → FreeHAnAbove (σ²⊥) 2

`pvar 0 = p`, `pvar 1 = pp` (written `p`, `q` below).  `⟹` is substitution;
the content is `⟸`.

Fragment first (CLAUDE.md rule 8): the ◯-free variable-free fragment is
`{⊥, ⊤}`; it has no interval to carry generators, and the IPC instance of
the question (`H₂` free on `p, q`) is the definition.  Degenerate here.

## Status table

| statement | theorem | status |
|-----------|---------|--------|
| `FreePair → FreeHAnAbove (base 2) 2` | `freeHAn_of_freePair` | PROVED (packaging) |
| lemma (a), general form (below) | `relB_transfer` | PROVED |
| lemma (a) on `R_b` | `relB_restrict` | PROVED |
| `⟹` for any base below the generators | `relB_preserves` | PROVED |
| `FreePair`, direction `⟹` | `freePair_preserves` | PROVED |
| `FreePair`, direction `⟸` | — | OPEN |

## Stage 1: the designed cells (CLAUDE.md rules 7, 9)

`¬A = A → ⊥`; the image of `Cᵢ` is `relB σ²⊥ xs Cᵢ` (`¬` becomes `↠ σ²⊥`).
Each `Cᵢ` is no theorem of IPC (`ipc_Cᵢ`: two- and three-world Kripke
models), so freeness needs each image to be no theorem of PLL.

| cell | IPC formula | image | verdict | certificate | theorem |
|------|-------------|-------|---------|-------------|---------|
| C1 | `¬¬q → q` | `((x₁ ↠ σ²⊥) ↠ σ²⊥) ↠ x₁` | PASS (not provable) | tableau countermodel 37 worlds, minimised to 10 | `cell_C1` |
| C2 | `¬q ∨ ¬¬q` | `(x₁ ↠ σ²⊥) ∨ ((x₁ ↠ σ²⊥) ↠ σ²⊥)` | PASS | 37 → 14 worlds | `cell_C2` |
| C3 | `(p → q) ∨ (q → p)` | `(x₀ ↠ x₁) ∨ (x₁ ↠ x₀)` | PASS | 30 → 12 worlds | `cell_C3` |
| C4 | `¬¬p → p` | `((x₀ ↠ σ²⊥) ↠ σ²⊥) ↠ x₀` | PASS | 19 → 8 worlds | `cell_C4` |

Producer: `refbench fact` (the subframe tableau, untrusted), the built binary
under `gtimeout 300`, each run in under a second; no flag, no cap reached.
Checker: `SubTab.no.verdict` (`decide +kernel`) on the images as computed by
`relB` in Lean (the producer's parse is not trusted for the formula).  The
predicted killer C1 does not kill: `x₁ = σ²⊥ ∨ ¬¬_{t3}◯Y` is `¬¬`-stable
relative to `t3`, but relative to `σ²⊥` its cofinality condition ranges over
the shell `{σ²⊥, ¬t3}`, which the `σ²⊥`-relative negations cannot see.

## Stage 2 (a): the relativisation lemma

Semantic `b ≤ x a` (`hbx : ∀ v a, v ⊩ b → v ⊩ x a`) gives

    v ⊩ b  →  v ⊩ relB b x A          (every A; `force_relB_of_b`)

General form (`relB_transfer`): `K` a subframe model (read as a Kripke
model), `φ : K → M` with

    φ k ⊮ b;   k ≤ j → φ k ≤ φ j;   φ k ≤ v → v ⊩ b ∨ ∃ j ≥ k, φ j = v;
    φ k ⊩ x (pvar i) ⟺ k ∈ V(pvar i)   (i < n).

Then for ◯-free `A` with `varsBelow n A`:

    φ k ⊩_M relB b x A   ⟺   k ⊩_K A.

As briefed (`relB_restrict`, `M` finite): `R_b = {v : v ⊮ b}` with the
order restricted and `V a = {v : v ⊩ x a}` (`restrict`), `φ = Subtype.val`.
Direction `⟹` (`relB_preserves`): if `[A] ⊢ B` then at a world of a finite
model forcing `relB A`, either it forces `b` (then `relB B`), or it lies in
`R_b`, where soundness of `[A] ⊢ B` and lemma (a) give `relB B`;
completeness for finite subframe models (`SubframeModel.CF.completeness_imp`,
choice-free) gives `[relB A] ⊢ relB B`.  No syntactic substitution lemma for
`⊥ ↦ b` was needed.  `ZL.transfer` (`wip/f0FreeHAn.lean`) is the
one-variable template (there the map runs the other way, a p-morphism onto
the ladder skeleton).

## Stage 2 (b), (c): the gadget design (committed before its proof)

(b) Finite models: `SubframeModel.CF.completeness_imp` (choice-free) reduces
`[A] ⊢ B` to `k ⊩ A → k ⊩ B` at every world `k` of every finite decidable
subframe model `K`; for ◯-free `A`, `B` the set `S` of `K` is irrelevant, so
`K` is a finite Kripke model on `p`, `q` (a preorder; neither rootedness nor
antisymmetry is used).

(c) The gadget `M(K)`.  Worlds: `e`, `n` (tops), `f`, `g`, `h` (shell), and
`w_k` for `k ∈ K`.  Order (reflexive, and):

    w_j ≤ w_k ⟺ j ≤_K k
    w_k ≤ e, n, f, g          (always)
    w_k ≤ h ⟺ k ⊮ q           (down-closed in k, so transitive)
    f ≤ e, n;   g ≤ e;   h ≤ e, n

    S = {n, g, h} ∪ {w_k : k ⊮ p};   no atoms.

The forcing it is designed for (pen; each line is a lemma of the proof):

| world | in `S` | above | forces | refutes | shell type `(s, n)` |
|-------|--------|-------|--------|---------|---------------------|
| `e` | no | — | `◯⊥`, `t3`, `σ²⊥`, `t4` | | |
| `n` | yes | — | `¬◯⊥`, `t3`, `σ²⊥`, `¬t4`, `Y` | `◯⊥`, `t4` | |
| `f` | no | `e, n` | `◯t3`, `σ²⊥`, `◯Y` | `t3` | `(0, 1)` |
| `g` | yes | `e` | `◯t3 ↠ t3`, `σ²⊥`, `t4`, `Y`, `◯Y` | `t3`, `◯t3` | `(1, 0)` |
| `h` | yes | `e, n` | `◯t3 ↠ t3`, `σ²⊥`, `◯Y ↠ t3` | `t3`, `◯t3`, `t4`, `¬t4`, `Y`, `◯Y` | `(1, 1)` |
| `w_k` | iff `k ⊮ p` | `e, n, f, g` (`h` iff `k ⊮ q`), `w_j` (`j ≥ k`) | | `σ²⊥` (by `g`: `◯t3` fails; by `f`: `◯t3 ↠ t3` fails) | |

So `R_{σ²⊥} = {w_k}`, order-isomorphic to `K`, and

    x₀ = ◯σ²⊥ at w_k  ⟺  no S-world refuting σ²⊥ above w_k  ⟺  ∀ j ≥ k, j ⊩ p  ⟺  k ⊩ p
    x₁ at w_k  ⟺  (◯Y ↠ t3) ↠ t3 at w_k  ⟺  w_k ≰ h  ⟺  k ⊩ q

(for `x₁`: `σ²⊥` fails at `w_k`; the worlds above `w_k` refuting `t3` are the
`w_j`, `f`, `g` and possibly `h`; `f`, `g` force `◯Y` and refute `t3`, every
`w_j` sees `f`, so each of these refutes `◯Y ↠ t3`; `h` forces `◯Y ↠ t3` and
refutes `t3`).  Lemma (a) with `φ = w` (back condition: every successor of
`w_k` is a shell world or top, which forces `σ²⊥`, or a `w_j` with `j ≥ k`)
then gives, for ◯-free `A` over `p`, `q`,

    w_k ⊩ relB σ²⊥ xs A   ⟺   k ⊩_K A,

and reflection follows: if `[relB A] ⊢ relB B` and `k ⊩_K A`, then
`w_k ⊩ relB A`, by soundness `w_k ⊩ relB B`, so `k ⊩_K B`; by (b),
`[A] ⊢ B`.

The design works for every finite `K`, with no case on its shape: the only
`K`-dependence is `S ∩ R` (read off `p`) and the edges `w_k ≤ h` (read off
`q`).  The roles: `x₀` reads the `S`-membership of the `R`-worlds (the
mechanism of `freeIPL1`, one level up), `x₁` reads which shell worlds lie
above (the cofinality mechanism of `ZL`), and the two do not interfere
because `x₀` is blind to the shell (every shell world forces `σ²⊥`) and `x₁`
is blind to `S ∩ R` (it only asks for `◯Y`-worlds outside `R`).

Validation (kernel-checked, `gadget_C1` … `gadget_C4`): the gadget over the
IPC countermodel of each Stage 1 cell, as a `SubCM` table, refutes the
image at `w_root` (7, 8, 8, 7 worlds).

## Log

* 2026-10-27 19:38: statement written and built (`lake build wip.f0FreePair`),
  committed before any proof.
* 2026-10-27 19:45: Stage 1, the four cells: all PASS, kernel-checked
  (`lake build wip.f0FreePair` clean, pins `[propext, Quot.sound]`).
* 2026-10-27 19:50: lemma (a) and the direction `⟹` PROVED, module clean.
* 2026-10-27 19:55: gadget design written (above) and validated on the four
  cells (`gadget_C1` … `gadget_C4`, kernel-checked); committed before its
  general proof.
