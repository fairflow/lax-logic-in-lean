# The structure of the ρ-order: verified regularities and construction conjectures

2026-08-25.  Data sources: the 462-cell PLL matrix (kernel-pinned ⊬
side, `Certified/RhoSeparations.lean` + banks; engine-certified ⊢
side), the 37-edge scoped Hasse diagram (`wip/rhocover_out.txt`,
`docs/rho-hasse-pll.svg`), and the extension probe
(`wip/rhoprobe_out.txt`).  Notation: `a := ◯⊥`, `b := ◯¬◯⊥` (= ◯¬a).
PROVED / REFUTED claims below are certificate-backed; everything
labelled CONJECTURE or PREDICTED is exactly that.

## 1. Verified regularities

**R1 — graded.**  Every cover edge spans one rank; profile
`1‑2‑2‑3‑5‑5‑3‑1`, height 7.

**R2 — lower-cover join-generation (POSET sense) and the ten
poset-join-irreducibles.**  Every join-reducible node is the POSET
least upper bound of its own lower covers; the poset-irreducibles are

    ⊥,  a,  ¬a,  ¬¬a,  b,  ρ12 = ρ8⊃b,  ρ13 = ρ8⊃ρ4,
    ρ14 = ρ9⊃ρ4,  ρ19 = ρ11⊃b,  ρ20 = ρ11⊃ρ6.

CORRECTION (2026-08-25, after probe round 2): poset-lub is WEAKER than
class-of-the-syntactic-join, and the first draft of this note
conflated them.  Whether `v ≡ ⋁(lower covers of v)` is an R6 identity
question per node.  Probe round 2 CERTIFIED it for
`ρ10 ≡ ρ8∨ρ18`, `ρ15 ≡ ρ11∨ρ18`, `ρ18 ≡ ρ9∨ρ16 ≡ ρ9∨ρ17 ≡ ρ16∨ρ17`,
and left it OPEN (frontier cells) for
`ρ8 ⊢? ρ16∨ρ19` (class(ρ16∨ρ19) is otherwise NEW and < ρ8),
`ρ11 ≡? ρ13∨ρ17`, `ρ21 ≡? ρ12∨ρ20` (untested).  Every
poset-irreducible except the rails' atoms is an implication.

**R3 — two stacked cubes.**  The interval [ρ4, ρ18] is exactly 2³ on
atoms {ρ6, ρ7, ρ14}, and round 2 certified its identities as CLASS
identities: joins ρ9∨ρ16 ≡ ρ9∨ρ17 ≡ ρ16∨ρ17 ≡ ρ18, meets ρ6∧ρ7 ≡
ρ7∧ρ14 ≡ ρ6∧ρ14 ≡ ρ4.  The dual cube over ρ9 on atoms {ρ12, ρ18,
ρ20}: three vertices are the new classes X₄ = ρ12∨ρ18, X₃ = ρ18∨ρ20,
X₅ = ρ12∨ρ18∨ρ20; the fourth, ρ12∨ρ20, is the poset-lub ρ21 but the
class identity `ρ21 ≡? ρ12∨ρ20` is OPEN (untested).

**R4 — a two-generator presentation of the catalogue.**  Every one of
the 22 representatives is a Heyting-algebra term over `{a, b}` alone:
exactly two `◯`-applications occur in the entire catalogue (`◯⊥` and
`◯¬◯⊥`).  The q-dictionary's `q12 = ◯ρ6` and `q13 = ◯ρ11` sit OUTSIDE
the catalogue — they are the first depth-2 ◯-generators.

**R5 — the two rails.**  The Rieger–Nishimura ladder at `p := a` is
the left rail: ρ0, ρ2=a, ρ3=¬a, ρ4, ρ5=¬¬a, ρ6, ρ8, ρ10, ρ13 (= rn₈ in the
code's 0-indexed rungs — R5's first draft said rn₉, off by one; truth
sets checked — a sweep DISCOVERY that the ladder predicts).  The modal rail starts at
`b = ◯¬a` (ρ7) and interacts with the pure rail through joins and the
five ⊃-classes.

**R6 — local disjunction properties (the key reduction).**  For any
classes with `x < u` and `y < u`:

    u ⊢ x ∨ y   ⟺   u ≡ x ∨ y

(since `u ≡ (u∧x)∨(u∧y)`, `u∧x ≡ x`, `u∧y ≡ y` — distributivity at
class level, kernel-provable per instance).  Consequences:

* the classical disjunction property is the instance u = ⊤ ("⊤ is
  join-prime");
* every question "is the hub join ⋁S a NEW class or equal to the hub's
  cover u" is ONE cell, `u ⊢? ⋁S`;
* every open probe cell of that shape is an identity question, e.g.
  `ρ20 ⊢? ρ9∨ρ19` ⟺ X₁ = ρ20, and `ρ12 ⊢? ρ7∨ρ13` ⟺ X₂ = ρ12.

## 2. Construction conjectures

**C1 (generation by ◯-strata).**  CONJECTURE: the closed fragment is
generated, as a Heyting algebra, by the ◯-images of its own elements,
stratified by ◯-depth: depth ≤1 gives RN(a) (the proved embedding);
adding `b` gives (at least) the current catalogue; each next stratum
adjoins `◯φ` for the φ already constructed, modulo the certified laws
`◯◯φ ≡ ◯φ`, `◯⊤ ≡ ⊤` (so ◯ρ2, ◯ρ7 collapse).  PREDICTED new
generators to test: `◯ρ4, ◯ρ5, ◯ρ6 (= q12), ◯ρ8, ◯ρ9, ◯ρ10,
◯ρ11 (= q13)` — each either lands on a known class or is a new
join-irreducible.

**C2 (cube growth / hub completion).**  CONJECTURE: every node with k
upper covers spawns a 2ᵏ cube of joins, and the fragment realises all
its vertices; the catalogue's gaps are missing vertices.  Verified
instances: hub ρ4 (cube complete in the 22), hub ρ9 (completed by
X₃/X₄/X₅), hubs ρ6/ρ7 (first vertices X₂/X₁ found).  PREDICTED and
under probe (round 2): ρ9∨ρ17, ρ9∨ρ13∨ρ17 (hub ρ6); ρ9∨ρ16, ρ16∨ρ19,
ρ9∨ρ16∨ρ19 (hub ρ7); ρ11∨ρ12, ρ16∨ρ17, ρ8∨ρ18, ρ11∨ρ18, ρ10∨ρ15,
ρ8∨ρ20; dually the co-hub meets ρ6∧ρ7, ρ16∧ρ19, ρ13∧ρ17, ρ9∧ρ13,
ρ7∧ρ14, ρ6∧ρ14, ρ12∧ρ20, ρ8∧ρ18.

**C3 (the descending ladder makes the irreducibles).**  All five
non-atomic join-irreducibles have the shape `(join class) ⊃ (low rung)`
with exactly two target patterns: `X ⊃ b` (ρ12, ρ19, and ρ21 — though
ρ21 proves reducible) and `X ⊃ ρ4` / `X ⊃ ρ6` (ρ13, ρ14, ρ20).  This
is the RN recursion `gₙ₊₁ = gₙ ⊃ gₙ₋₁` transplanted to the two-rail
setting.  PREDICTED next irreducibles: `X₁⊃b, X₂⊃ρ4, X₃⊃b, X₄⊃ρ4,
ρ21⊃ρ12`-shapes — apply the same two schemas to the new join classes.

**C4 (the general proof approach).**  Combine R2 + R6: certify once,
per class, its canonical join-decomposition into irreducibles; then

* the ⊢ side of ANY cell between join classes reduces to finitely many
  irreducible-vs-irreducible cells (join-primality of irreducibles in
  a distributive lattice: `u ⊢ x∨y ⟹ u ⊢ x or u ⊢ y` when u is
  join-irreducible — per-instance kernel-provable by R6's identity);
* the ⊬ side needs countermodels only for irreducible pairs — the
  battery + FRJ(◯) hunt shrinks to the ~10 irreducibles per stratum;
* the ascending ladder (joins) is handled by bookkeeping, the
  descending ladder (⊃-classes) is where search effort belongs.

This is the route to a finite PRESENTATION of each stratum: poset of
irreducibles + join tables, from which the whole stratum's order and
Hasse diagram are computed, not searched.

## 3. Decision cells now carrying the structure

    ρ12 ⊢? ρ15            (the standing flag; = "is ρ15 ≡ ρ12∨ρ18∨…?")
    ρ20 ⊢? ρ9∨ρ19         ⟺ X₁ = ρ20    (else X₁ is a 25th class)
    ρ12 ⊢? ρ7∨ρ13         ⟺ X₂ = ρ12
    ρ10∧ρ21 ⊢? ρ10∧ρ20,  ρ15∧ρ21 ⊢? ρ12∧ρ15   (meet dedups)

Each needs either a proof (LJF◯ deep fuel) or a countermodel BEYOND
the battery — the FRJ(◯) Profile engine on custom sequents is the
designated finder (extend `frjconstruct` past ρ-pairs; it found the
8-world model for ρ20⊬ρ10 that the battery lacks).

## 4. Probe round 2 (2026-08-25, `wip/rhoprobe2_out.txt`)

37 candidates (round 1 + remaining hub joins, co-hub meets, ◯-shifts).
Control green.  Results (COUNTS CORRECTED 2026-08-25 by the v18
rebuild audit; first draft said 36 and 12):

* **15 IDENT lines plus `◯ρ6 ≡ ◯ρ9` from the candidate matrix**.  The
  four ◯-identities

      ◯(a∨¬a) ≡ b   ◯¬¬a ≡ ¬¬a   ◯(¬¬a⊃a) ≡ ¬¬a⊃a   ◯ρ6 ≡ ◯ρ9

  are NOT new: all four were already kernel-proved AND in `rndSet`
  (`wip/rnDict.lean:1460–1472`, cells cBox_4/6/9/10, explicit G4iLL″
  terms; v17 already displayed two of them).  The probe re-finding
  them is a CROSS-VALIDATION of the engine pipeline, not a discovery
  — a lookup-before-claiming failure, caught by the audit.  ρ5 and ρ8
  ◯-fixed matches the nucleus law "x ⊃ y is j-fixed when y is", a = ◯⊥
  being ◯-fixed.  Also ρ8∨ρ18 ≡ ρ10, ρ11∨ρ18 ≡ ρ15, and the meet
  identities of R3.
* **22 NEW verdicts, collapsing to 17 distinct new-class candidates**
  under certified mutual derivability (an upper bound; some
  candidate-pairs remain open).  Fully-settled unconditional members (empty
  open-cell list vs the 22): `class(ρ8∨ρ20)` AND `class(ρ10∧ρ20)`.
  The ◯-stratum contributes `◯ρ6 (≡ ◯ρ9)` and `◯ρ11` as new classes;
  `◯ρ4, ◯ρ5, ◯ρ8` collapse (the laws above), confirming C1's shape:
  most shifts collapse, a few are genuinely new generators.
* The catalogue is heading from 22 to ≈ 39 classes at this depth;
  every remaining "?" is a recorded frontier cell, and R6 turns each
  hub-join "?" into a single identity question.
