# The one-variable quantifier value table

2026-07-19 · produced by `wip/semui_probe.lean` (G4c search oracle,
sound on `true`; candidate filters at fuel 500, certificate searches
fuel- and weight-capped — see the probe header).  Every candidate below
is oracle-SOUND (candA ⊢ M and M ⊢ candE verified), and **every row is
certified**, i.e. carries derivability facts that the criteria of
`wip/semantic_ui.lean` convert into a machine-checked
`IsSemAll`/`IsSemEx` proof.

## The closed ladder (values live here)

RN(◯,{}) truncated to weight ≤ 8 has exactly **7 classes**:

    ⊥,  ◯⊥,  ⊤,  ¬◯⊥,  ◯¬◯⊥,  ¬¬◯⊥,  ¬◯⊥ ∨ ◯⊥

## Certificate legend

* `SUBST[χ…]` — substitution instances `M[p:=χ]` suffice
  (`isSemAll_of_certificates` / `isSemEx_of_certificates`);
* `LOW` — the lower transform of the doubled model is needed
  (`…_of_certificates_low`);
* `SIDE` — the sideways transform of the Löb variant is needed
  (`…_of_certificates_side`).

## The table (all 25 one-variable classes, weight ≤ 5, plus extras)

| M | ∀p.M | ∀-certificate | ∃p.M | ∃-certificate | p essential? |
|---|---|---|---|---|---|
| p | ⊥ | SUBST[⊥] | ⊤ | SUBST[⊤] | yes |
| ⊥ | ⊥ | SUBST | ⊥ | SUBST | no (≡ ⊥) |
| ◯⊥ | ◯⊥ | SUBST | ◯⊥ | SUBST | no (≡ ◯⊥) |
| ◯p | ◯⊥ | SUBST[⊥] | ⊤ | SUBST[⊤] | yes |
| ⊤ | ⊤ | SUBST | ⊤ | SUBST | no (≡ ⊤) |
| ¬p | ⊥ | SUBST[⊤] | ⊤ | SUBST[⊥] | yes |
| ◯¬p | ◯⊥ | SUBST[⊤] | ⊤ | SUBST[⊥] | yes |
| ¬◯p | ⊥ | SUBST[⊤] | ¬◯⊥ | SUBST[⊥] | yes |
| ◯p ⊃ p | ⊥ | **LOW** | ⊤ | SUBST[◯⊥] | yes |
| ¬◯⊥ | ¬◯⊥ | SUBST | ¬◯⊥ | SUBST | no (≡ ¬◯⊥) |
| ◯⊥ ⊃ p | ¬◯⊥ | SUBST[⊥] | ⊤ | SUBST[◯⊥] | yes |
| ◯⊥ ∨ p | ◯⊥ | SUBST[⊥] | ⊤ | SUBST[⊤] | yes |
| p ⊃ ◯⊥ | ◯⊥ | SUBST[⊤] | ⊤ | SUBST[⊥] | yes |
| ◯(◯⊥ ⊃ p) | ◯¬◯⊥ | SUBST[⊥] | ⊤ | SUBST[◯⊥] | yes |
| ◯¬◯⊥ | ◯¬◯⊥ | SUBST | ◯¬◯⊥ | SUBST | no (≡ ◯¬◯⊥) |
| ◯(◯p ⊃ p) | ◯⊥ | **SIDE** | ⊤ | SUBST[◯⊥] | yes |
| ◯¬◯p | ◯⊥ | SUBST[⊤] | ◯¬◯⊥ | SUBST[⊥] | yes |
| ¬¬p | ⊥ | SUBST[⊥] | ⊤ | SUBST[⊤] | yes |
| ¬p ∨ p | ⊥ | **LOW** | ⊤ | SUBST[⊥] | yes |
| ◯⊥ ∧ p | ⊥ | SUBST[⊥] | ◯⊥ | SUBST[◯⊥] | yes |
| ¬¬p ⊃ p | ⊥ | (lowT weight-capped in probe; PROVED in Lean: `semAll_nnp_imp_p`) | ⊤ | SUBST[⊥] | yes |
| ◯(p ∨ ¬p) | ◯⊥ | **SIDE** | ⊤ | SUBST[⊥] | yes |
| ¬◯⊥ ∨ p | ¬◯⊥ | SUBST[⊥] | ⊤ | SUBST[⊤] | yes |
| ◯¬◯⊥ ∨ p | ◯¬◯⊥ | SUBST[⊥] | ⊤ | SUBST[⊤] | yes |
| ¬◯p ∨ ◯p | ◯⊥ | **SIDE** | ⊤ | **LOW** | yes |

(Notation: ¬A = A ⊃ ⊥; the probe prints `False`/`True` for ⊥/⊤.)

## Findings

1. **The three-generator basis certifies everything.**  25/25 rows on
   both sides.  Substitution singles cover 19/25 of the ∀-side; the
   doubling (`LOW`) covers `◯p ⊃ p` and `¬p ∨ p` — exactly the rows
   `em_p_no_certificate`-style arguments show substitution cannot
   reach; the sideways construction (`SIDE`) covers exactly the
   ◯-guarded classical schemata `◯(◯p ⊃ p)`, `◯(p ∨ ¬p)`,
   `¬◯p ∨ ◯p`; `¬¬p ⊃ p` was weight-capped in the probe but is
   proved in Lean through `lowT` (`semAll_nnp_imp_p`).  No row needed
   a pair of substitutions.
2. **The probe agrees with the Lean theorems on every overlapping
   case**: `∀p.p = ⊥`, `∀p.◯p = ◯⊥`, `∀p.¬p = ⊥`,
   `∀p.(p∨¬p) = ∀p.(◯p⊃p) = ⊥` (LOW), `∀p.◯(◯p⊃p) = ◯⊥` (SIDE).
3. **First ∃-side value beyond substitution** (machine-found):
   `∃p.(¬◯p ∨ ◯p) = ⊤` needs the doubled variant — no substitution
   instance works because `¬◯χ ∨ ◯χ` is underivable for closed χ
   (weak excluded middle for ◯⊥ was kernel-checked underivable in the
   2026-07-13 session).  Mechanisable via
   `isSemEx_of_certificates_low`.
4. **The value landscape is tame**: every candidate is a UNIQUE
   maximum/minimum over the 7-class ladder (never a join or meet of
   incomparable elements), and the values attained at weight ≤ 5 are
   {⊥, ◯⊥, ⊤, ¬◯⊥, ◯¬◯⊥} on both sides.  The remaining ladder
   classes (¬¬◯⊥, ¬◯⊥∨◯⊥) are attained essentially by the fibre
   witnesses ξ ∨ p / ξ ∧ p at weight 8–9 (`essential_semAll_image`).
5. **Essentiality fully classified**: inessential exactly for the five
   p-free-equivalent classes appearing; every essential row certified
   by a separation pair (always `⊥` against one of `◯⊥`/`⊤`).
6. **Oracle pathology** (tooling): the cost of a FAILING `search` call
   is chaotic — non-monotone in fuel ([inst(¬¬◯⊥)] ⊢ ◯⊥: 0 ms at fuel
   ≤ 200, minutes at 500; [lowT, inst(¬◯⊥)] ⊢ ◯⊥: 0 ms at 350,
   minutes at 200).  Successes are instant even at weight 40.  The
   probe therefore weight-caps failing-prone calls, orders cheap
   attempts first, and restricts combination premises to {⊥, ◯⊥, ⊤}.

## What this sets up

Definability at one variable (`semAll_definable`/`semEx_definable`
restricted to atoms ⊆ {p}) is now an empirically complete conjecture
with a concrete uniform proof target: **for every one-variable M, the
generator instances {M[p:=⊥], M[p:=⊤], lowT p M, sideT p M} derive the
maximum closed ξ with ξ ⊢ M** — a purely syntactic statement, testable
level-by-level over the RN lattice, whose proof would close the ∀-side
(dually for ∃).  The tower picture (2-level, 3-level, …) predicts where
deeper generators would be needed: ◯/⊃-alternation depth beyond the
probe's weight cap.
