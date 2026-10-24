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
