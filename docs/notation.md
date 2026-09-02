# Notation register: contexts, zones and binder names

*Opened 2026-09-02 on Matthew's ruling.  The rule: Greek for contexts
and zones, in the text AND in the Lean binders; Roman for formulas,
tags, indices and functions.  A programmer's abbreviation (`St`, `Th`,
`stab`, `th`) standing for a Greek letter in the prose is the defect
this register exists to remove.*

## The letters

Lean cannot use `Σ` or `Π` as identifiers (they are the dependent-type
binders), so two of the paper's letters need replacements.  Everything
else is the paper's.

| letter | meaning | source | Lean binder | status |
|---|---|---|---|---|
| `Γ` | a regular disproof's context, `t : Γ ⇒ C`; also a generic context | Fiorentini–Ferrari | `Γ` | in use |
| `Ξ` | the STABLE zone of an irregular disproof, `Ξ ; Θ → C` (the paper's `Σ`) | ours, 2026-09-02 | `Ξ` | **rename pending**: the binders read `St` (and `stab` for join families) at `b2f2525` |
| `Θ` | the second zone of an irregular disproof | the paper | `Θ` | **rename pending**: the binders read `Th` (and `th`) at `b2f2525` |
| `Ψ` | a `Gbu(G)`/`Gbu◯(G)` context, `Ψ ⇒g C` and `Ψ →g C`; the paper's `Wg` counts `Sf^L(G) ∖ Cl(Ψ)` | the paper | `Ψ` | in use |
| `Ω` | the irregular `Gbu◯` context in the search statements (`WSearchOk (false, Ω, C)`, `WEvalI D Ω C`) | ours | `Ω` | in use |
| `Λ` | the zone moved by `⊃∈ᵢ` (`Ξ ; Θ ++ Λ → B` to `Ξ ++ Λ ; Θ → A ⊃ B`) | the paper | `Lam` | **rename pending** |
| `Υ` | the goals of a join's premises, `upsilon rhs` | the paper | `upsilon` (function) | function name, stays |
| `Δᵢ` | the contexts of a promise join's regular premises, `tᵢ : Δᵢ ⇒ Dᵢ` | ours | `Δs` | in use (the `s` marks a family) |
| `Φ` | free | | | reserved for the next need |

Not to be used for zones or contexts: `Σ`, `Π` (unavailable), `Ψ` (taken
by `Gbu◯`, as in the paper), `Δ` (taken by the promise joins).

## Families

A `Fin (n+1)`-indexed family of zones is written with a plural `s`:
`Ξs`, `Θs`, `Δs`, `Ds`, `tps` (tags).  The paper writes the family as a
displayed list `{ Ξⱼ ; Θⱼ → Cⱼ }ⱼ`; the register keeps the subscript in
prose and the `s` in Lean.

## Roman names that stay Roman

Formulas (`A B C F G X Y Z`), tags (`t t'`), indices (`i j k n`),
Booleans (`reg`, `cone`), and every FUNCTION name, however it is
pronounced: `stabOf`/`thOf` may be renamed to `xiOf`/`thetaOf` for
consistency but a Roman function name is not a defect.

## Where the rename lands

The binder rename `St Th → Ξ Θ`, `stab th → Ξs Θs`, `Lam → Λ` is done
inside the promotion of the FRJW/Gbu◯ chain out of `wip/`
(`docs/frjw-compaction.md`, deferred items), because that touches every
file concerned.  FRJV files stay byte-for-byte untouched (standing
rule), so `FRJ/CalculusV.lean` keeps `St`/`Th`; the register applies
to the W family and to the `Gbu◯` chain.  Other developments in the
repository that carry the same mix (Matthew: "wrt other formalisations
elsewhere in this repo") are to be swept against this register
separately.
