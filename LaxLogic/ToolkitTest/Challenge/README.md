# Challenge set

Four **proved** lemmas from the development, re-stated with `sorry`. Each has a
known human proof of 6–15 lines, so a claim of success can be checked against
something real — unlike the open UI claims, which are research problems, and
unlike `../NewClaims.lean`, whose statements were invented for the purpose.

| file | from | ground truth |
|---|---|---|
| `conservativity.lean` | `LaxLogic/PLLNDCore.lean` | 14 lines |
| `conservativity_prop.lean` | `LaxLogic/PLLNDCore.lean` | 14 lines |
| `pfree_trans.lean` | `LaxLogic/LJFComplete.lean` | 15 lines |
| `focalization.lean` | `LaxLogic/LJFComplete.lean` | 6 lines |

Two further candidates (`force_circ_transparent`, `mem_gHat_shape`, both from
`FRJ/Erase.lean`) were dropped: their prefixes do not compile standalone, which
is a limitation of prefix-truncation extraction, not of the lemmas.

Each file was self-contained and compiled with exactly one `sorry`. **All four
are now proved** (2026-08-30) and carry no `sorry`; the axiom pins are
`[propext, Quot.sound]` for `conservativity` and `conservativity_prop`,
`[propext, Classical.choice, Quot.sound]` for `focalization` (inherited from
this file's own `sound`, not from the added proof), and none at all for
`pfree_trans`. To re-run the exercise, take the statements from git history.

Treat the results with care: the set is **contaminated by construction**.
Prefix truncation puts everything the ground-truth proof used above the cut,
`conservativity_prop`'s answer is in `conservativity.lean`, and only
`pfree_trans` needed anything its own file did not contain. See
`docs/toolkit-test-design.md`.

Do not consult the original proof before attempting one.
