# FRJ◯ — the real refutation calculus: sources read, design, plan

*2026-08-16, for a fresh session. Written after Matthew's correction:
the previous attempt (`FRJO/Core.lean`'s `RT` + `wf`) is an
un-indexed certificate format with validity outside the data — the
derivation-vs-countermodel mistake made a second time. This plan is
for the calculus as originally promised: (1) an indexed judgment with
one rule per connective, (2) refutation completeness as a theorem,
(3) extraction soundness once and for all.*

## 0. Sources actually read (this morning, at source)

* **Ferrari–Fiorentini–Fiorino, "Forward Countermodel Construction in
  Modal Logic K", CILC 2018, CEUR Vol-2214 paper 8** — READ IN FULL
  (7 pp). The modal instance of the method, with the complete rule
  table, the soundness model-construction and the completeness
  induction. The template below.
* **Fiorentini–Ferrari, "Forward proof-search and Countermodel
  Construction in IPC", CEUR Vol-2756 paper 27** — READ IN FULL
  (extended abstract of the TOCL 2020 paper). Adds: the saturation
  DATABASE with forward/backward SUBSUMPTION; countermodels are DAGs
  (sequent re-use), minimum-height; and the DUALITY — a FAILED
  refutation-search's saturated database is a proof certificate for
  the goal, read back through a backtracking-free backward calculus
  `Gbu(G)`.
* `docs/frj-lifting.md` — the in-repo record of the TABLEAUX-2017
  appendix (FRJ(G)'s zones, Lemmas 3–5), the ◯-arity probe, and the
  `Cl` screen (GO, with boxes forced into the determining part).
* Still unread: the JLC 2021 S4 paper (paywalled; the K paper by the
  same authors substitutes for the architecture) and the TOCL 2020
  full paper (the CEUR abstract + the 2017 appendix record cover it).

## 1. RK(Ξ), transcribed — the template

Derivation nodes are SETS `Δ ⊆ Sf⁺(Ξ)` read "jointly satisfiable";
`Sf⁺` is the subformula closure (`□α ↦ α`, `¬□α ↦ ¬α`, ∧/¬∧/¬¬ as
usual). Rules:

    Lit:   ⊢ X                X a MAXIMAL lit-consistent subset of Sf⁺(Ξ)

    ∧ :    Γ,α,β ⊢ Γ,α,β,α∧β          ⎫  Cl-rules — applied only if the
    ¬∧:    Γ,¬αₖ ⊢ Γ,¬αₖ,¬(α₁∧α₂)     ⎬  introduced formula ∈ Sf⁺(Ξ)
    ¬¬:    Γ,α ⊢ Γ,α,¬¬α              ⎭

    ⋈ :    Γ₁ … Γₙ   H   (n ≥ 1, H a □-free "cl-set")
           ─────────────────────────────────────────
           ⟦□(⋂ᵢΓᵢ)⟧, {¬□α | ¬α ∈ ⋃ᵢΓᵢ}, H          ⟦Γ⟧ = Γ ∩ Sf⁺(Ξ)

    ⋈₀:    H ⊢ {□α | □α ∈ Sf⁺(Ξ)}, H                (no successors)

Reading of `⋈`: create a fresh world with classical content `H`,
`R`-successors the premise worlds; `□α` holds there when α holds at
every successor (the intersection), `¬□α` when some successor kills α.

* **Soundness** (their Thm 1) is a MODEL CONSTRUCTION by induction on
  the derivation: Lit = one world; Cl-rules change nothing; `⋈` =
  disjoint union of premise models + fresh root wired to the premise
  roots. **This is Reject's `solo`/`join` verbatim.**
* **Completeness** (their Lemma 1) : `Γ h-satisfiable → ∃ derivation
  of some Δ ⊇ Γ with rank ≤ h`, by induction on the MODEL's height
  with an inner induction on `|Γ|`; the `□Θ,¬□α₁…¬□αₙ,H` case picks a
  witness world per `¬□αⱼ` and joins. Rank (⋈-count per branch) =
  extracted model height, so models are HEIGHT-MINIMAL. **This is
  Reject's `height_induction` + `genJoin` verbatim.**

The IPC version (FRJ(G)) adds what K does not need: intuitionistic
persistence forces the two-zone irregular sequents `Σ ; Θ → C` (Σ
stable at the root, Θ above it), the `Cl`-closure absorbing all left
rules (Lemma 5: a world is determined by its non-∧/∨ part), the `⊃∈`
/`⊃∉` split, and goal-directedness (everything inside `Sf⁺(G)`).

## 2. What PLL adds, and the design (from `frj-lifting.md` §4, now grounded)

Sequents, goal-parametrised by the cell `Γ₀ ⊢ C₀` (so the finite rule
property is free):

    regular    Γ ⇒ C            "some world forces Γ and refutes C"
    irregular  Σ ; Θ ; μ → C    Σ stable at the root, Θ above it,
                                μ = the modal zone: the root's
                                Rm-cone content (on reduced confluent
                                frames, the single maximum successor's
                                theory — the promise world)

* `Cl` = PLL-consequence closure over `Sf⁺(Γ₀ ⊢ C₀)` with the
  determining part = atoms + ⊥ + implications + **boxes** (the screen
  in `frj-lifting.md` §7: the literal IPC choice FAILS with 32
  certified cells; adding boxes gives 0/156 — the repair is forced).
  Computable by the repo's G4 deciders over the finite closure.
* Rules: the FRJ(G) right rules for ∨ and the `⊃∈`/`⊃∉` pair,
  unchanged; plus
  - `◯∈` — the refuting world is the root: premise `A ∉ Cl(μ)`
    (the root's own cone misses `A`);
  - `◯∉` — strictly above: an irregular premise refuting `◯A`;
  - joins `⋈` gain the modal component: each join DECLARES which
    premise sub-models are Rm-successors of the fresh root, subject to
    `Rm ⊆ Ri` + reflexivity + transitivity, with the ◯-POSITIVE
    obligations (`◯A ∈ Σ` ⟹ every Ri-successor has an Rm-successor
    forcing `A`) as decidable side conditions against the premises —
    the ∀ discharged by construction, exactly the RK(Ξ) move;
  - fallibility is a zone flag: `⊥ ∈ Cl(Σ)` marks a fallible world;
    fallible worlds carry no refutation premise; refuting `◯⊥` = "no
    fallible world in the cone" falls out.
* **PCLL-first over REDUCED frames** (arity probe, 52,800 worlds:
  reduced+confluent ⟹ the ◯-rule is UNARY, the witness being the
  maximum Rm-successor — canonical instance `obInvW`, with
  `rmC_le_obInv` already proved). Full PLL needs a premise-LIST rule
  schema (arity grows with frame size); defer.

## 3. The three commitments, with proof routes and named machinery

**(1) The judgment.** A genuine indexed inductive family, one
constructor per rule:

    inductive FRJ (G : Cell) : RSeq G → Type
      | lit …    | orR …    | impIn … | impOut …
      | circIn … | circOut …
      | join (mods : …) (D : ModalDecl …)
          (side₁ : … = true) … : FRJ G (regular …)
      | join0 …

  indexed by the sequent (statable lemmas), rule-per-connective
  (inductable derivations), side conditions as decidable `= true`
  fields (kernel-checkable applications). NO histories anywhere: the
  calculus is FORWARD — new worlds only via joins over the finite
  sequent set, so termination is structural (RK(Ξ)'s Finite Rule
  Property). **The anti-pattern to avoid is on record twice**: a plain
  tree + external checker is a certificate format, not a calculus.

**(2) Completeness** — `Γ₀ ⊬ C₀ in PLL ⟹ FRJ-derivable`:

    ¬Nonempty (LaxND Γ₀ C₀)
      → finite REDUCED countermodel          (PROVED: emitter_completeness + (R),
                                              Reject/Reduce.lean `exists_reduced_countermodel`)
      → Built tree, bisimilar                 (PROVED: T2 `gen_of_reduced`)
      → FRJ-derivation, by height induction   (NEW: the Lemma-1 analogue —
        on the model: rank ≤ height, worlds    `Reject/Height.lean
        to sequents by Λ* + Cl, joins from     height_induction` is the
        the model's own successor structure)   induction, `genJoin` the shape

  The last step is the ONE genuinely new induction, and it is RK(Ξ)'s
  Lemma 1 with zones. My 2026-08-16 substrate
  (`wip/ljfo_completeness.lean`: `isEmpty_holds_iff_search`,
  `exists_allFail`) is NOT needed on this route — it serves only the
  optional search-side corollary (`¬search-at-any-fuel ⟹ FRJ`) and
  can be retired to that role.

**(3) Extraction soundness, once and for all:**

    extract : FRJ G S → Σ (M : ConstraintModel) (w : M.W), …
    extract_forces : root forces the Σ/Γ-zone, refutes the goal

  by induction on the derivation, consuming `Reject.solo`,
  `Reject.join`, `join_force_comp`, `boxRefuteHere`, `boxRefuteAbove`,
  `boxHolds` — the T1 kit used as intended. Corollary
  `not_laxND_of_FRJ` via `not_laxND_of_root`; `FinCM`/`checkB` replay
  optional for cheap kernel `decide`, no longer the trust anchor.

**With (2)+(3): `FRJ-derivable ↔ Γ₀ ⊬ C₀` — the biconditional that
makes "REFUTED" a derivation, settles flags by absence-of-proof only
when the search side is also closed, and directly certifies them when
the refutation search succeeds.**

## 4. Work plan for the fresh session

* **W1** Sequent + zone types over `Sf⁺(Γ₀ ⊢ C₀)`; `Cl` as a computed
  closure with the (Cl1)–(Cl6) properties PROVED (the screen's caveat
  discharged). New lib `FRJO/` v2 — replace `Core.lean`'s RT layer;
  keep its corpus screen harness.
* **W2** The indexed inductive (§3.1), PCLL-reduced instance first
  (unary `◯∈`/`◯∉`, μ a single zone).
* **W3** Extraction + `extract_forces` (§3.3) — do this BEFORE
  completeness; it debugs the rule side conditions cheaply.
* **W4** The saturation searcher over the sequent database with
  forward subsumption (the CEUR abstract's engine), emitting
  derivations; corpus test: the 302 refutable ρ-cells + the 2 flags
  (`lean_exe frjoscreen` pattern). Expect DAG re-use to beat the
  battery on model size.
* **W5** Completeness (§3.2): the height-induction Lemma-1 analogue.
  The heavy stage; `genJoin`'s proof is the worked precedent.
* **W6** The duality corollary (CEUR abstract): a SATURATED database
  with no derivation of the goal certifies PLL-provability — ties back
  to `bridge_iff`/LJF◯ and would settle the two flags from the
  refutation side alone.

Recommended: Opus 5, max effort, W1–W3 in the first session; W5 alone
in its own session. Verify every stage with `#print axioms` pins
transcribed verbatim; sorry = OPEN, per mandate.

---

## Addendum, 2026-08-16 end of session — what got built, and the v3 correction

W1–W3a and the W5 reduction are CODE now (`FRJO/{Seq,Calc,Extract,
Complete,Reconstruct}.lean`, all compiling, zero sorries):
`completenessFRJO` is PROVED conditional on `Reconstruction` alone,
pinned. The solo case was proved against worldOK v2 and thereby
EXPOSED v2's unsoundness (goal conjuncts read the bounded searcher;
budget failure admits wrong `world` nodes, falsifying W3b). worldOK v3
replaces every closure-read with structural membership/shape
conjuncts; the v2 solo proof is invalidated by design and both
`Reconstruction` cases are OPEN again — each with a complete worked
analysis in `FRJO/HANDOVER.md`, which is the fresh session's brief.
The join case reduces further than §3.2 hoped: component worlds are a
one-liner via `join_force_comp`; only the root case's inner induction
on the goal (with the realiser/leaf dichotomy) is real work.


---

## Addendum, 2026-08-16 evening — W5 CLOSED, W3b REFUTED for v3

Branch `claude/frjo-completeness`.

**W5 is done.** `Reconstruction` and `ReconstructionSolo` are PROVED
(`FRJO/Recon.lean`), so `completenessFRJO` is unconditional
(`FRJO.completenessFRJO'`).  The Lemma-1 analogue the plan called "the
ONE genuinely new induction" is `FRJO.recon`: structural induction on
`Reject.Built`, inner induction on the goal at each root, with the
join's root case running the realiser/leaf dichotomy
(`FRJO.exists_cone_kids`).  It is CHOICE-FREE, pinned
`[propext, Quot.sound]`, over the `Effective` package.

**W3b is refuted for worldOK v3** (`FRJO/Screen.lean`, three certified
cells).  The reason is not v2's — no budget is read any more — but the
opposite: v3 constrains the zone only by membership in the universe, so
the `world` rule admits zones that no world forces.  §3's commitment (3)
("extraction soundness, once and for all") therefore cannot be
discharged against the current rule table, and the biconditional of §3
is still OPEN.  The v4 repair is specified in that file, its zone half
is coded and checked both ways, and the design decision it forces (the
five goal-directed rules become derived, and two of them are separately
extraction-unsound as written) is recorded in `docs/disproof-handoff.md`
§2026-08-16 (evening) for Matthew.

**W4** (searcher + 302-cell corpus) should wait for the v4 rule table:
a searcher emitting `FRJD` v3 would emit certificates that do not
certify.
