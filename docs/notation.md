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
| `Ξ` | the STABLE zone of an irregular disproof, `Ξ ; Θ → C` (the paper's `Σ`) | ours, 2026-09-02 | `Ξ` (families `Ξs`) | in use since the rename commit of 2026-09-02 (`St → Ξ`, `stab → Ξs`); before it the binders read `St`/`stab` (so at `b2f2525`, the explainer's anchor) |
| `Θ` | the second zone of an irregular disproof | the paper | `Θ` (families `Θs`) | in use since the same commit (`Th → Θ`, `th → Θs`); `Th`/`th` at `b2f2525` |
| `Ψ` | a `Gbu(G)`/`Gbu◯(G)` context, `Ψ ⇒g C` and `Ψ →g C`; the paper's `Wg` counts `Sf^L(G) ∖ Cl(Ψ)` | the paper | `Ψ` | in use |
| `Ω` | the irregular `Gbu◯` context in the search statements (`WSearchOk (false, Ω, C)`, `WEvalI D Ω C`) | ours | `Ω` | in use |
| `Λ` | the zone moved by `⊃∈ᵢ` (`Ξ ; Θ ++ Λ → B` to `Ξ ++ Λ ; Θ → A ⊃ B`) | the paper | `Λ` | in use since the same commit (`Lam → Λ`); the compound zone `Θ ++ Λ` of that rule is bound `ΘΛ` (was `ThLam`), a choice the table did not cover, FOR REVIEW |
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

## Where the rename landed (2026-09-02)

The binder rename `St Th → Ξ Θ`, `stab th → Ξs Θs`, `Lam → Λ` was done
in one commit, directly after the promotion of the FRJW/Gbu◯ chain out
of `wip/` (`docs/frjw-compaction.md`, "Promotion"): a whole-identifier
rename carrying subscripts and primes, 3194 occurrences across the W
family (`FRJ/CalculusW.lean`, `FRJ/StepW.lean`, `FRJ/ExtractW.lean`,
`FRJ/SoundW.lean`) and the fourteen `FRJ/Gbu/` modules; no function
name and no hypothesis name (`hSt`, `hTh`, …) was touched, no proof
text changed, every pin byte-identical, build green.  FRJV files stay
byte-for-byte untouched (standing rule), so `FRJ/CalculusV.lean` keeps
`St`/`Th`; the register applies to the W family and to the `Gbu◯`
chain.

Three places where the mechanical rule could not be applied, each FOR
REVIEW by Matthew:

1. **Six V-family named arguments** in `FRJ/SoundW.lean` (lines 132,
   139, 320, 323, 550, 554) call `stab_mem_baseAtV` /
   `stab_mem_baseOrV`, whose binder lives in `FRJ/CalculusVLemmas.lean`
   (V, untouched), so the LABEL stays Roman while the value moves:
   `(th := Θs)`.  The only bare Roman zone tokens left in the W scope.
2. **`ThLam`, `ThLam₂ → ΘΛ`, `ΘΛ₂`**, the compound zone `Θ ++ Λ` of
   `⊃∈ᵢ` (`FRJ/CalculusW.lean`, `FRJ/StepW.lean`, the W chain): not in
   the table; leaving it Roman beside `Ξ Θ Λ` would reinstate the
   defect, so it was carried along.
3. **Families named `St`/`Th` rather than `stab`/`th`.**  In
   `FRJ/Gbu/W/Corner.lean`, `Closure.lean` and `Saturate.lean` some
   binders named `St`/`Th` are `Fin (n+1)`-indexed FAMILIES (`X ∈ Th
   j`), not single zones; the table's `St → Ξ`, `Th → Θ` was applied
   verbatim, so they now read `Ξ`/`Θ` where the Families section wants
   `Ξs`/`Θs`.  Telling the two apart is not mechanical (it needs the
   binder's type); a by-hand pass over those three files is the fix if
   Matthew wants it.

Other developments in the repository that carry the same mix (Matthew:
"wrt other formalisations elsewhere in this repo") are to be swept
against this register separately; not started.
