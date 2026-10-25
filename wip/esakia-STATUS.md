# Nuclear Esakia duality: campaign status

Tracked status note (brief: LaxLogic manager, 2026-10-24). Committed at every
step so that a pause loses nothing. Dated sections, newest last; never
rewrite a section, append.

Goal (Matthew's): Esakia duality extended to nuclear Heyting algebras,
mechanised; the missing section of Paper I ("Semantics and decision for
PLL"); related to F–M constraint models and to subframe models
(`LaxLogic/PLL/Semantics/Subframe.lean`, `LaxLogic/PLL/SubTab`).

Method: fragment first (plain Heyting algebras before nuclei, finite before
general); statements first; a refutation stage on three designed cells;
then REPORT AND STOP for Matthew's inspection of the statements.

## 2026-10-24 20:39 BST: round 1 opened

Branch `worktree-agent-a18ba9fa90bc301be` (local only, no upstream).
Build cache seeded from `agent-ad132f5974d72ca18`.

Planned files:
- `wip/esakiaNuclearFin.lean`: the finite layer, choice-free, decidable:
  definitions and the statements F1–F10 as `def … : Prop`.
- `wip/esakiaNuclearCells.lean`: the three designed cells (3-chain,
  four-element Boolean algebra, Rieger–Nishimura truncation RN₈) and the
  morphism cells, by `decide +kernel`, pinned; negative gates watched.
- `wip/esakiaNuclearGen.lean`: the general (topological) statements G1–G4
  and the bridge statements R1–R5 to constraint and subframe models, over
  Mathlib; statements only.

## 2026-10-24 20:39 BST: Stage 0, literature (verified records)

Verified by fetched records this session (crossref API, arXiv abstract
pages, and the full texts of arXiv:1906.03636v3 and arXiv:2001.11060,
extracted with pdftotext):

1. G. Bezhanishvili, S. Ghilardi, "An algebraic approach to subframe
   logics. Intuitionistic case", Ann. Pure Appl. Logic 147(1–2):84–100,
   2007, doi:10.1016/j.apal.2007.04.001 (crossref record). Full text NOT
   reached (ScienceDirect 403). Its Thm 30, Cor 31 and Thm 34 are used
   through the verbatim restatement in item 2.
2. F. Ávila, G. Bezhanishvili, P. J. Morandi, A. Zaldívar, "When is the
   frame of nuclei spatial: a new approach", J. Pure Appl. Algebra
   224(7):106302, 2020, doi:10.1016/j.jpaa.2019.106302 (crossref);
   arXiv:1906.03636 (full text read). NOTE: the brief's lead described
   arXiv:1906.03636 as "on nuclear implicative semilattices"; that is wrong.
   1906.03636 is this paper (frames, nuclear points). The nuclear
   implicative semilattice paper is item 3.
   - Def 3.1 (Priestley space), Def 3.4 (Esakia space: ↓U clopen for U
     clopen), Thm 3.5 (Esakia duality Esa ≃ Heytᵒᵖ, U → V = X ∖ ↓(U ∖ V)).
   - Def 4.1: a CLOSED F ⊆ X is a nuclear subset iff ↓(U ∩ F) is clopen for
     every clopen U. (Called "subframes" in item 1, "L-sets" in
     Pultr–Sichler 2000.)
   - Thm 4.3 = [item 1, Thm 30]: for ANY Heyting algebra L, N(L) is dually
     isomorphic to N(X_L), by N_j := {x ∈ X_L | j⁻¹(x) = x} and
     φ(j_N a) = X_L ∖ ↓(N ∖ φ(a)).
   - [item 1, Cor 31]: bottom of N(L) ↔ X_L, top ↔ ∅, N_{j∧k} = N_j ∪ N_k.
   - Thm 4.4 = [item 1, Thm 34]: N_{u_a} = X_L ∖ φ(a) (u_a x = a ∨ x),
     N_{v_a} = φ(a) (v_a x = a → x), N_{w_a} = max(X_L ∖ φ(a))
     (w_a x = (x → a) → a).
   - Example 4.7: off-frame, the intersection of two nuclear sets need not
     be nuclear.
3. G. Bezhanishvili, N. Bezhanishvili, L. Carai, D. Gabelaia, S. Ghilardi,
   M. Jibladze, "Diego's Theorem for nuclear implicative semilattices",
   Indag. Math. 32(2):498–535, 2021, doi:10.1016/j.indag.2020.12.005
   (crossref); arXiv:2001.11060 (full text read). The FINITE duality, the
   statement transcribed in `wip/esakiaNuclearFin.lean`:
   - Thm 3.4 (finite HAs ≃ finite posetsᵒᵖ, p-morphisms), with the meet-prime
     presentation of Def 3.5 and (†): α_A(a) = {x ∈ X_A | a ≰ x},
     ε_X(x) = X ∖ ↓x, order on X_A the dual of ≤.
   - §3: j_S(U) = X ∖ ↓(S ∖ U) is a nucleus on Up(X) for EVERY S ⊆ X;
     S_j = X_A ∩ A_j (meet-primes fixed by j); Lemma 3.15:
     α_A(j a) = j_{S_j}(α_A(a)); Thm 3.16: (A, j) ≅ (Up(X_A), j_{S_j}).
   - Lemma 4.3: a Köhler morphism f has f* nuclear iff
     ↑(f(↑x) ∩ T) = f(↑(↑x ∩ S)) for all x. Lemma 4.4/Def 4.5
     (S-morphisms), Lemma 4.12 (ε_X(S) = S_{j_S}), Thm 4.13 (finite nuclear
     implicative semilattices ≃ finite S-posetsᵒᵖ). The morphisms are
     implicative-semilattice homomorphisms (Köhler partial maps), NOT
     Heyting homomorphisms.
   - It cites Fairtlough–Mendler 1997 and Goldblatt 1981 for the lax
     modality.
4. L. Esakia, "Topological Kripke models", Dokl. Akad. Nauk SSSR
   214:298–301, 1974; English: Soviet Math. Dokl. 15:147–151, 1974
   (both read in the fetched bibliographies of items 2 and 3; primary not
   reached). L. Esakia, *Heyting Algebras: Duality Theory*, eds.
   G. Bezhanishvili and W. H. Holliday, Trends in Logic (vol. 50 per
   item 3's bibliography), Springer 2019, doi:10.1007/978-3-030-12096-2
   (crossref record).
5. R. Goldblatt, "Grothendieck topology as geometric modality",
   Z. Math. Logik Grundlag. Math. (crossref: Mathematical Logic Quarterly)
   27(31–35):495–529, 1981, doi:10.1002/malq.19810273104 (crossref).
6. M. Fairtlough, M. Mendler, "Propositional Lax Logic", Inform. and
   Comput. 137(1):1–33, 1997, doi:10.1006/inco.1997.2627 (crossref).

GAP (not filled from memory): no fetched source states the nuclear
condition for HEYTING homomorphisms and p-morphisms (the Esakia-category
morphisms). Statement F10 adapts the computation of item 3, Lemma 4.3, and
is marked OURS.

Mathlib (pinned version in this worktree's `.lake/packages/mathlib`):
- HAS: `PriestleySpace` (separation axiom only; compactness NOT included,
  `Topology/Order/Priestley.lean`); `PseudoEpimorphism`, `EsakiaHom`
  (morphisms only, `Topology/Order/Hom/Esakia.lean`); `Nucleus` on a
  `SemilatticeInf`, complete lattice of nuclei on a complete lattice, Heyting
  algebra and frame of nuclei on a frame, `Nucleus.range` a frame
  (`Order/Nucleus.lean`); prime ideals/filters `Order.Ideal.IsPrime`,
  `Order.PFilter.IsPrime`, `PrimePair` (`Order/PrimeIdeal.lean`); the prime
  ideal theorem for distributive lattices
  `DistribLattice.prime_ideal_of_disjoint_filter_ideal`
  (`Order/PrimeSeparator.lean`); finite Birkhoff representation
  `OrderIso.lowerSetSupIrred` (noncomputable; "TODO: extend to
  morphisms", `Order/Birkhoff.lean`); Alexander's subbasis theorem
  `isCompact_generateFrom` (`Topology/Compactness/Compact.lean`);
  categories `HeytAlg`, `FinPartOrd`, `FinBddDistLat`, `Frm`, and the
  frame/space adjunction (`Topology/Order/Category/FrameAdjunction.lean`).
- MISSING: an Esakia-space class; the prime spectrum of a distributive
  lattice or Heyting algebra as a Priestley space; Priestley duality and
  Esakia duality (objects and morphisms); nuclear subsets; anything on
  duals of nuclei.

## 2026-10-24 20:48 BST: finite statements and cells built

`wip/esakiaNuclearFin.lean` (statements F1–F10, F10a, NaiveHom; no Mathlib,
no `Fin`, no `Finset`) and `wip/esakiaNuclearCells.lean` (cells), both in the
`wipshared` globs. `lake build wip.esakiaNuclearCells`: green, 9.6 s.

Every cell is a closed instance decided by `decide +kernel`; every pin is
`#axioms_within … [propext]` (measured: `[propext]` or `[]`); the pin gate
(`c3_F6` at `[]`) watched failing with the expected message.

Cells (all PASS):
- C0 boundary: 1-element algebra, empty poset (F1, F2, F3, F4, F5, F6).
- C1 3-chain / 2-chain: exactly 4 of 27 self-maps are nuclei; F1–F9 for
  every nucleus, pair of nuclei, subset and element.
- C2 2² / 2-antichain: exactly 4 of 256 self-maps are nuclei, all closed
  (`j x = j ⊥ ∨ x`, control); F1–F9 likewise.
- C3 RN₈ / 4-point ladder: computed dual of RN₈ = the ladder
  (`rn8.mprimes = [2,4,5,6]` = ¬p, ¬¬p, ¬¬p ∨ ¬p, ¬¬p → p); designed nuclei
  u_p, v_p, w_p, w_⊥ = ¬¬, u_p ∧ ¬¬ (F4); F9 at all 8 elements; F6 at all 16
  subsets (so all 16 nuclei of RN₈); F7 and F8 at all 256 pairs; F3, F5 at
  all 16 subsets of the ladder.
- M morphisms 2 ↪ C₃ and C₃ ↠ 2: F10a (◯-free) at both; F10 at all 8 nucleus
  pairs of each (3 resp. 4 pairs nuclear; (∗) agrees in all 16).

REFUTED (kernel-checked, `m_naive_refuted`): the naive transfer of
[BBCGGJ] Remark 4.6 to Heyting homomorphisms ("h nuclear iff
h_*⁻¹(S_j) = S_k"). Witness: 2 ↪ C₃ with id on 2 and ¬¬ on C₃ is nuclear,
but h_*⁻¹(S_id) = X_{C₃} ≠ S_{¬¬} = {top point}. The Köhler simplification
uses strict order preservation, which p-morphisms lack.

Negative gates (watched failing): G1 `j_S` with ↑ for ↓ breaks F4 at C₃;
G2 [BG] Thm 34(3) without `max` breaks at RN₈; G3 a non-idempotent map is
rejected; G4 a corrupted presentation of 2² is rejected by `isHA`.

Non-vacuity inspected (`_out/esakiaInspect.lean`, untracked): duals
nonempty, the S_j of the 4 + 4 + 16 nuclei pairwise distinct, both nuclear
and non-nuclear morphism pairs present.

Scope note on "exhaustive": the C1/C2 cells range over nuclei given as
tables of length n; reading them as "every j : Nat → Nat" uses only that the
predicates read j on the carrier (not yet written as a lemma).

## 2026-10-24 21:04 BST: general and bridge statements; R3 screen; round 1 closed for review

`wip/esakiaNuclearGen.lean` (in `wipshared`; `lake build
wip.esakiaNuclearGen` green, 14 s): statements only, all OPEN.
- G1 (Esakia 1974; [ABMZ] Thm 3.5 objects), G2 ([BG] Thm 30 = [ABMZ]
  Thm 4.3), G3 ([BG] Cor 31), G4 ([BG] Thm 34 = [ABMZ] Thm 4.4), over a
  hand-written prime-filter spectrum `Spec A` with the inclusion order and
  the patch topology. Divergences D1–D5 recorded in the file header.
- Statement-level axioms measured: G1, G2, G4 `[propext, Quot.sound]`, G3
  `[]`. Two Mathlib choice leaks avoided at statement level, both found with
  `#axiom_path`: `PartialOrder (Set A)` (via `Set.instCompleteAtomicBoolean
  Algebra`), replaced by a written-out order on `Spec`; `Nucleus.instBot` and
  `Nucleus.instMin` (via `Nucleus.le_apply`), avoided by naming nuclei by
  their values (D5). Pin gate on G2 watched failing.
- R1–R5 (OURS) relate the dual to `PLLND.SubframeModel` and
  `PLLND.ConstraintModel`; statement-level axioms `[]`. Hypotheses trimmed to
  what the (paper) argument uses: R1's and R2's clauses carry heredity only
  where inflationarity or the meet law needs it; R3a has no `w ∉ F`; R3 split
  into R3a (antisymmetric Rᵢ, any size), R3b (finite), R3c (any).

R3 screen in the finite encoding (`wip/esakiaNuclearCells.lean`, section R):
- `cR_R3`: at a designed 4-world model (one fallible top, Rₘ-edges 0→1 and
  2→3) R2, R3a, R3b, R3c all PASS; non-vacuous (`j_C` neither id nor ⊤; the
  only Rₘ-final non-fallible world is 1).
- `cPre_R3a_fails`: R3a FAILS without antisymmetry of Rᵢ (2-world preorder
  0 ≡ 1 with 0 Rₘ 1): the antisymmetry hypothesis is needed.

Also added: `chain3_dual_iso_chain2`, `bool4_dual_iso_anti2` (each cell's
poset is the computed dual of its algebra). All cell pins `[propext]`.

`python3 scripts/check-imports.py`: 3037 imports in 1230 modules, every one
resolves. `df -m /System/Volumes/Data`: 138 524 MB free at start, 138 206 MB
at close.

Termination condition of round 1: STATEMENTS AND CELLS DONE, HANDED BACK for
Matthew's inspection (no proofs built, per the brief). No literature
statement refuted at any cell; one plausible statement of ours refuted
(`m_naive_refuted`); one hypothesis shown necessary (`cPre_R3a_fails`).

Next round (only after review), in dependency order:
1. Finite layer proofs F1–F10 (choice-free; plain fragment F1, F2, F10a
   first), plus the congruence lemma that makes the table cells cover every
   `j : Nat → Nat`.
2. R1, R2, R4 (short), R3a/R3b/R3c, R5 (the ω-cell, by hand).
3. General G1 (Esakia duality, objects) then G2–G4; Classical.choice enters
   at the prime filter theorem and Alexander's subbasis theorem.

## 2026-10-25 10:57 GMT: Phase A (finite layer and bridge) PROVED; checkpoint

Matthew's decision (via the coordinator): prove the nuclear Esakia duality,
finite layer first; statements stand as written. No statement text was
changed; no hypothesis added; no statement refuted.

Finite layer, all PROVED for the unchanged `def … : Prop` of
`wip/esakiaNuclearFin.lean`, every pin `[propext, Quot.sound]`:

| theorem | statement | module | commit |
|---|---|---|---|
| `EsakiaNuclear.f1` | `F1` | `wip/esakiaNuclearFinProofs.lean` | 8113d9e |
| `EsakiaNuclear.f2` | `F2` | same | 8113d9e |
| `EsakiaNuclear.f3` | `F3` | same | 8113d9e |
| `EsakiaNuclear.f4` | `F4` | same | 8113d9e |
| `EsakiaNuclear.f5` | `F5` | same | 8113d9e |
| `EsakiaNuclear.f6` | `F6` | `wip/esakiaNuclearFinProofs2.lean` | ec43812 |
| `EsakiaNuclear.f7` | `F7` | same | ec43812 |
| `EsakiaNuclear.f8` | `F8` | same | ec43812 |
| `EsakiaNuclear.f9` | `F9` | same | ec43812 |
| `EsakiaNuclear.f10a` | `F10a` | `wip/esakiaNuclearFinProofs3.lean` | d8aaea6 |
| `EsakiaNuclear.f10` | `F10` | same | d8aaea6 |

Proof kit `wip/esakiaNuclearFinBase.lean` (8745048): bit-list
extensionality, enumeration of `allSubs`, maximal/minimal elements by
counting, the finite prime filter theorem (`FinHA.Ax.exists_prime`, by a
maximal element and the himp-candidate trick, no distributivity used),
separation by meet-primes, the dual is a poset.

Deviation from the requested pin "[propext] or less": `Quot.sound` is in
every pin. It enters only through `funext` (core `List.all_eq_true`,
`Nat.instLawfulBEq`, `List.ext_getElem`; for the bridge, `Set.ext`).
`Classical.choice` is absent from the whole finite layer. Choice leaks met
and removed on the way: `List.nodup_range` (own `nodup_range'`), the simp
lemma `Nat.right_eq_add` (replaced by `Nat.noConfusion`), and
`beq_self_eq_true` on `Nat` via `Nat.instTransOrd` (replaced by
`beq_iff_eq.mpr rfl`).

Bridge, `wip/esakiaNuclearBridgeProofs.lean` (45220ec), statements of
`wip/esakiaNuclearGen.lean` unchanged:

| theorem | statement | pin |
|---|---|---|
| `Bridge.r1` | `R1` | `[propext, Classical.choice, Quot.sound]` |
| `Bridge.r2` | `R2` | `[propext, Quot.sound]` |
| `Bridge.r3a` | `R3a` | `[propext, Classical.choice, Quot.sound]` |
| `Bridge.r3b` | `R3b` | `[propext, Classical.choice, Quot.sound]` |
| `Bridge.r3c` | `R3c` | `[propext, Classical.choice, Quot.sound]` |
| `Bridge.r4` | `R4` | `[propext, Classical.choice, Quot.sound]` |
| `Bridge.r1_dne` | `R1 → ∀ P : Prop, ¬¬P → P` | `[]` |
| `Bridge.r3c_dne` | `R3c → ∀ P : Prop, ¬¬P → P` | `[]` |
| `Bridge.r4_dne` | `R4 → ∀ P : Prop, ¬¬P → P` | `[]` |

So R1, R3c and R4 have no choice-free proof: each implies double-negation
elimination (witnesses: a one-point subframe model with `V p = {_ | P}`; a
two-world constraint model with `false Rᵢ true` iff `P`; a one-point
subframe model with `S = {_ | P}`). The cause: the library's models carry
arbitrary propositions as `S`, `V a`, `Rᵢ`, while `j_S(U) = X ∖ ↓(S ∖ U)`
and `mPt` read the ◯-clause and the order through a double negation. R2 is
constructive. R3a (⇒) and R3b use excluded middle in the proof (choice
enters only through `Classical.propDecidable`, found with `#axiom_path`);
whether they are constructively provable is OPEN.

Gates. Every pin was watched failing once (`_out/esakiaPinsFail.lean`,
untracked): each choice-free pin tightened to `[propext]` fails on
`Quot.sound` and to `[Quot.sound]` fails on `propext` (f1–f10, f10a, r2);
each classical pin tightened to `[propext, Quot.sound]` fails on
`Classical.choice` (r1, r3a, r3b, r3c, r4). The three `[]` pins cannot be
tightened. No `sorry`, `admit` or `native_decide` in any Phase A module.

Skipped: the congruence lemma for the "exhaustive" reading of the C1/C2
cells. Reason: F1–F10 are now PROVED for every `j : Nat → Nat`, so the
cells' coverage no longer carries any claim.

`python3 scripts/check-imports.py`: 3046 imports in 1236 modules, every one
resolves. `df -m /System/Volumes/Data`: 137 927 MB free at the last build.

Next: Phase B (G1–G4, R5; classical), on the coordinator's resume.
