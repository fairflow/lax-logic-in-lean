/-
# The FRJV ◯-delta, round 1: `minModV` extends `minMod` past `.circ`

Matthew's directive (2026-08-26): extend `FRJ/Minimal.lean`'s `minMod`
past its `.circ` case, USING THE EXISTING PROOF AS A FIRM TEMPLATE —
same witness structures, same recursion, same measure, new cases only.

Round-1 scope (the smallest delta that gives the recursion modal
content on both sides):

* the goal may contain `◯` anywhere — both `.circ` cases of the
  recursion are BUILT (`◯∈` regular, `◯∉` irregular), and `Υ` may
  contain `◯`-formulas (antecedents `◯Z` of `Λ*`-implications reach the
  irregular `.circ` case through the join `ih`s);
* `hcf` (the ◯-free hypothesis) is GONE;
* `hloc : ∀ b, circPart (Λ*_b) = []` remains — the join cases stay
  barren-tagged, exactly the template's joins on the V-formers (the
  paper's `Θ^⊃/Υ` zone is re-created as a `KeptChain` via
  `keptChain_of_ups`).  Lifting `hloc` = the promise-join port, round 2;
* `hinf : K.Infallible` remains (per-wit infallibility is round 3);
* the ONE un-orderable edge — the irregular `◯Z`-demand at a world all
  of whose proper extensions force `Z` (the §9 wall of `docs/frj-w4.md`;
  no lexicographic measure orders `I(◯Z)@a → R(Z)@a`) — is taken as the
  named supply `CircSupplyV`, consumed at exactly that branch and
  nowhere else.  Round 2 discharges it (maximal-world `Ax^I◯`,
  chosen-valuation `Ax^I◯`, `Clo`-grounding, and NEW here: the V-kept
  chains make the stuck-member retention of frj-w4 §11 a decidable
  `RefAt` question).

Every other case is `Minimal.lean` verbatim on the V-constructors.
-/
import FRJ.Minimal
import FRJ.CalculusV
import FRJ.Saturate

namespace FRJ

open Form

/-! ## The V-witness structures — the template's, plus the tag

`RegWitV` carries the derivation's tag together with the obligation
(`tOK`) that `circIn`/`circNotIn` consume; under `hloc` every wit built
here is barren, but the field is what the promise-join round will
inhabit with `chain`-tags, so it is carried from the start. -/

structure IrrWitV (K : Kripke) (G : Form) (a : K.W) (C : Form) : Type where
  stab : List Form
  th : List Form
  der : FRJVi G stab th C
  sub : stab ⊆ lamStar K a G
  cov : lamStar K a G ⊆ stab ++ th

structure RegWitV (K : Kripke) (G : Form) (a : K.W) (C : Form) : Type where
  ctx : List Form
  t : Tag
  der : FRJVr G t ctx C
  tOK : t = .barren ∨ ∃ W, t = .chain W ∧ Covers ctx W C
  wld : K.W
  wle : K.le a wld
  cov : lamStar K wld G ⊆ ctx

/-- Lemma 6.4 for the repaired calculus, indexed by `t`. -/
def MinModStmtV (K : Kripke) (G : Form) (a : K.W) (t : Nat) (C : Form) : Type :=
  match t with
  | 0 => IrrWitV K G a C
  | _ => RegWitV K G a C

/-- Transport of the tag obligation along a `Covers`-preserving map. -/
theorem tOK_lift {Γ : List Form} {t : Tag} {C C' : Form}
    (h : t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W C)
    (f : ∀ {W : Form}, Covers Γ W C → Covers Γ W C') :
    t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W C' := by
  rcases h with h | ⟨W, ht, hc⟩
  · exact Or.inl h
  · exact Or.inr ⟨W, ht, f hc⟩

/-! ## The named supply — the §9 wall as a hypothesis

The irregular `◯Z`-case floats to any proper extension refuting `Z`
(height drops).  When none exists — every `u > a` forces `Z` — the only
anchor is `a` itself and the edge `I(◯Z)@a → R(Z)@a` raises `t` at fixed
height: `docs/frj-w4.md` §9–§10 prove no reordering of `(ht, t, |C|)`
admits it.  The supply names that corner; it asserts nothing about any
other world. -/

def CircSupplyV (K : Kripke) (G : Form) : Type :=
  ∀ (a : K.W) (Z : Form), Form.circ Z ∈ sfR G →
    ¬ K.force a (.circ Z) →
    (∀ u, K.le a u → u ≠ a → K.force u Z) →
    IrrWitV K G a (.circ Z)

/-! ## `hloc` replaces the `hcf`-derived nil lemmas -/

theorem not_circ_lamStar_of_loc {K : Kripke} {a : K.W} {G X : Form}
    (hloc : circPart (lamStar K a G) = [])
    (hX : X ∈ lamStar K a G) (hc : X.isCirc = true) : False := by
  have hmem : X ∈ circPart (lamStar K a G) := List.mem_filter.mpr ⟨hX, hc⟩
  rw [hloc] at hmem
  exact List.not_mem_nil hmem

theorem circPart_stab_nil {K : Kripke} {a : K.W} {G : Form}
    (hloc : circPart (lamStar K a G) = [])
    {n : Nat} {stab : Fin (n + 1) → List Form}
    (hsub : ∀ j, stab j ⊆ lamStar K a G) :
    unionAll (fun j => circPart (stab j)) = [] := by
  refine eq_nil_of_forall_not_mem (fun X hX => ?_)
  obtain ⟨j, hj⟩ := mem_unionAll.mp hX
  obtain ⟨hmem, hc⟩ := List.mem_filter.mp hj
  exact not_circ_lamStar_of_loc hloc (hsub j hmem) hc

/-! ## The paper's `Θ^⊃/Υ` zone as a `KeptChain`

The V-joins replace the restricted second implication zone by a kept
zone; the paper zone `restrict (Θ^⊃∩) Υ` is a chain in any order
(`keptChain_of_ups`), so the template's context is recovered exactly. -/

theorem keptChain_restrict {n : Nat} {rhs : Fin (n + 1) → Form}
    (base : List Form) (th : Fin (n + 1) → List Form) :
    KeptChain (upsilon rhs) base (thPool th)
      (restrict (thPool th) (upsilon rhs)) :=
  keptChain_of_ups (fun _ hX => restrict_subset hX)
    (fun h => (mem_restrict.mp h).2)
    (fun _ hX => (List.mem_filter.mp (restrict_subset hX)).2)

/-! ## The three regular cases, templated -/

/-- The `⋈^At` case on the V-former: `Minimal.lean`'s `regPrime_join`
with `hloc` for the two `hcf`-discharges and the second zone as the kept
chain. -/
def regPrimeV_join (K : Kripke) (G : Form) (a : K.W) (C : Form)
    (hloc : circPart (lamStar K a G) = [])
    (hCp : C.isPrime) (hC : C ∈ sfR G) (hnf : ¬ K.force a C)
    (hne : upsPrime K a G ≠ [])
    (ih : ∀ (A : Form), A ∈ sfR G → ¬ K.force a A → IrrWitV K G a A) :
    RegWitV K G a C :=
  let E := enumOf (upsPrime K a G) hne
  let f := E.f
  let hfmem : ∀ j, f j ∈ upsPrime K a G := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  let wit : ∀ j, IrrWitV K G a (f j) := fun j =>
    ih (f j) (upsPrime_spec (hfmem j)).1 (upsPrime_spec (hfmem j)).2
  let stab := fun j => (wit j).stab
  let th := fun j => (wit j).th
  { ctx := joinCtxAtVBase stab th C ++ restrict (thPool th) (upsilon f)
    t := .barren
    tOK := Or.inl rfl
    wld := a
    wle := K.le_refl a
    der := by
      refine .joinAt (fun j => (wit j).der)
        (fun i j _ X hX => (wit j).cov ((wit i).sub hX))
        (fun A B hmem => ?_)
        (circPart_stab_nil hloc (fun j => (wit j).sub))
        (keptChain_restrict _ th)
        hCp (fun hmem => ?_) hC (CtxEq.refl _)
      · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
        exact (E.spec A).mpr (mem_upsPrime ((wit i).sub (List.mem_filter.mp hi).1))
      · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
        exact not_mem_lamStar_of_not_force hnf ((wit i).sub (List.mem_filter.mp hi).1)
    cov := by
      intro X hX
      have hXG := lamStar_subset_gHat hX
      simp only [gHat, List.mem_append] at hXG
      by_cases hin : ∃ j, X ∈ stab j
      · obtain ⟨j, hj⟩ := hin
        simp only [joinCtxAtVBase, List.mem_append]
        rcases hXG with (h | h) | h
        · exact Or.inl (Or.inl (Or.inl (mem_unionAll.mpr
            ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩)))
        · exact Or.inl (Or.inr (mem_unionAll.mpr
            ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩))
        · exact absurd ((List.mem_filter.mp h).2)
            (fun hc => not_circ_lamStar_of_loc hloc hX hc)
      · have hin' : ∀ j, X ∉ stab j := fun j hj => hin ⟨j, hj⟩
        have hallTh : ∀ j, X ∈ th j :=
          fun j => (List.mem_append.mp ((wit j).cov hX)).resolve_left (hin' j)
        simp only [joinCtxAtVBase, List.mem_append]
        rcases hXG with (h | h) | h
        · refine Or.inl (Or.inl (Or.inr (mem_rm.mpr
            ⟨fun hc => not_mem_lamStar_of_not_force hnf (hc ▸ hX), ?_⟩)))
          exact mem_interAll.mpr (fun j =>
            List.mem_filter.mpr ⟨hallTh j, (List.mem_filter.mp h).2⟩)
        · refine Or.inr ?_
          have himp : X.isImp := (List.mem_filter.mp h).2
          match X, himp with
          | .imp A B, _ =>
              refine mem_restrict.mpr ⟨?_, (E.spec A).mpr (mem_upsPrime hX)⟩
              exact List.mem_filter.mpr ⟨mem_interAll.mpr (fun j => hallTh j), rfl⟩
        · exact absurd ((List.mem_filter.mp h).2)
            (fun hc => not_circ_lamStar_of_loc hloc hX hc) }

/-- `C` prime with `Λ*_a` free of implications: the `Ax^R` sub-case. -/
def regPrimeV_ax (K : Kripke) (G : Form) (a : K.W) (C : Form)
    (hloc : circPart (lamStar K a G) = [])
    (hCp : C.isPrime) (hC : C ∈ sfR G) (hnf : ¬ K.force a C)
    (hempty : impPart (lamStar K a G) = []) : RegWitV K G a C :=
  { ctx := rm (gAt G) C
    t := .barren
    tOK := Or.inl rfl
    der := .axR C hCp hC (CtxEq.refl _)
    wld := a
    wle := K.le_refl a
    cov := by
      intro X hX
      have hXG := lamStar_subset_gHat hX
      simp only [gHat, List.mem_append] at hXG
      rcases hXG with (h | h) | h
      · exact mem_rm.mpr ⟨fun hc => not_mem_lamStar_of_not_force hnf (hc ▸ hX), h⟩
      · exfalso
        have hmem : X ∈ impPart (lamStar K a G) :=
          List.mem_filter.mpr ⟨hX, (List.mem_filter.mp h).2⟩
        rw [hempty] at hmem
        exact List.not_mem_nil hmem
      · exact absurd ((List.mem_filter.mp h).2)
            (fun hc => not_circ_lamStar_of_loc hloc hX hc) }

/-- The `⋈^∨` case on the V-former: `Minimal.lean`'s `regOr_join`; the
disjunct conditions lift into `RefAt` through its `ups` clause. -/
def regOrV_join (K : Kripke) (G : Form) (a : K.W) (C₁ C₂ : Form)
    (hloc : circPart (lamStar K a G) = [])
    (hC : Form.or C₁ C₂ ∈ sfR G) (hnf : ¬ K.force a (.or C₁ C₂))
    (ih : ∀ (A : Form), A ∈ sfR G → ¬ K.force a A → IrrWitV K G a A) :
    RegWitV K G a (.or C₁ C₂) :=
  let hn1 : ¬ K.force a C₁ := fun hc => hnf (Or.inl hc)
  let hn2 : ¬ K.force a C₂ := fun hc => hnf (Or.inr hc)
  let U := C₁ :: C₂ :: upsPrime K a G
  let E := enumOf U (by simp [U])
  let f := E.f
  let hfmem : ∀ j, f j ∈ U := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  let wit : ∀ j, IrrWitV K G a (f j) := fun j =>
    if h1 : f j = C₁ then by rw [h1]; exact ih C₁ (sfR_or hC).1 hn1
    else if h2 : f j = C₂ then by rw [h2]; exact ih C₂ (sfR_or hC).2 hn2
    else
      have hm : f j ∈ upsPrime K a G := by
        rcases List.mem_cons.mp (hfmem j) with h | h
        · exact absurd h h1
        · rcases List.mem_cons.mp h with h' | h'
          · exact absurd h' h2
          · exact h'
      ih (f j) (upsPrime_spec hm).1 (upsPrime_spec hm).2
  let stab := fun j => (wit j).stab
  let th := fun j => (wit j).th
  { ctx := joinCtxOrVBase stab th ++ restrict (thPool th) (upsilon f)
    t := .barren
    tOK := Or.inl rfl
    wld := a
    wle := K.le_refl a
    der := by
      refine .joinOr (fun j => (wit j).der)
        (fun i j _ X hX => (wit j).cov ((wit i).sub hX))
        (fun A B hmem => ?_)
        (circPart_stab_nil hloc (fun j => (wit j).sub))
        (keptChain_restrict _ th)
        ⟨.ups ((E.spec C₁).mpr List.mem_cons_self),
         .ups ((E.spec C₂).mpr (List.mem_cons_of_mem _ List.mem_cons_self))⟩
        hC (CtxEq.refl _)
      · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
        exact (E.spec A).mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (mem_upsPrime ((wit i).sub (List.mem_filter.mp hi).1))))
    cov := by
      intro X hX
      have hXG := lamStar_subset_gHat hX
      simp only [gHat, List.mem_append] at hXG
      by_cases hin : ∃ j, X ∈ stab j
      · obtain ⟨j, hj⟩ := hin
        simp only [joinCtxOrVBase, List.mem_append]
        rcases hXG with (h | h) | h
        · exact Or.inl (Or.inl (Or.inl (mem_unionAll.mpr
            ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩)))
        · exact Or.inl (Or.inr (mem_unionAll.mpr
            ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩))
        · exact absurd ((List.mem_filter.mp h).2)
            (fun hc => not_circ_lamStar_of_loc hloc hX hc)
      · have hin' : ∀ j, X ∉ stab j := fun j hj => hin ⟨j, hj⟩
        have hallTh : ∀ j, X ∈ th j :=
          fun j => (List.mem_append.mp ((wit j).cov hX)).resolve_left (hin' j)
        simp only [joinCtxOrVBase, List.mem_append]
        rcases hXG with (h | h) | h
        · exact Or.inl (Or.inl (Or.inr (mem_interAll.mpr (fun j =>
            List.mem_filter.mpr ⟨hallTh j, (List.mem_filter.mp h).2⟩))))
        · refine Or.inr ?_
          have himp : X.isImp := (List.mem_filter.mp h).2
          match X, himp with
          | .imp A B, _ =>
              refine mem_restrict.mpr ⟨?_, (E.spec A).mpr
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_upsPrime hX)))⟩
              exact List.mem_filter.mpr ⟨mem_interAll.mpr (fun j => hallTh j), rfl⟩
        · exact absurd ((List.mem_filter.mp h).2)
            (fun hc => not_circ_lamStar_of_loc hloc hX hc) }

/-! ## Lemma 6.4 for FRJV — the extended recursion -/

def minModV (K : Kripke) (G : Form)
    (hloc : ∀ b : K.W, circPart (lamStar K b G) = [])
    (hinf : K.Infallible) (hsup : CircSupplyV K G)
    (a : K.W) (t : Nat) (C : Form)
    (hC : C ∈ sfR G) (hnf : ¬ K.force a C) : MinModStmtV K G a t C := by
  match t, C with
  | 0, .circ Z =>
      -- THE ◯-DELTA, irregular: `◯∉` from a floated regular `Z`-wit
      -- when some proper extension refutes `Z` (height drops), else the
      -- sole-candidate supply — the §9 wall, and nothing else.
      have hnfZ : ¬ K.force a Z := fun hZ => hnf (force_circ_of_force hZ)
      match hcand : K.elems.filter
          (fun u => decide (K.le a u ∧ u ≠ a ∧ ¬ K.force u Z)) with
      | [] =>
          refine hsup a Z hC hnf (fun u hau hune => ?_)
          by_contra hufZ
          have hmem : u ∈ K.elems.filter
              (fun u => decide (K.le a u ∧ u ≠ a ∧ ¬ K.force u Z)) :=
            List.mem_filter.mpr ⟨K.complete u, by simp [hau, hune, hufZ]⟩
          rw [hcand] at hmem
          exact absurd hmem List.not_mem_nil
      | u :: _ =>
          have hu : u ∈ K.elems.filter
              (fun u => decide (K.le a u ∧ u ≠ a ∧ ¬ K.force u Z)) := by
            rw [hcand]; exact List.mem_cons_self
          have hspec : K.le a u ∧ u ≠ a ∧ ¬ K.force u Z := by
            have := (List.mem_filter.mp hu).2
            simpa using this
          let w := minModV K G hloc hinf hsup u 1 Z (sfR_circ hC) hspec.2.2
          exact { stab := [], th := lamStar K a G
                  der := .circNotIn w.der w.tOK
                    (fun X hX => ⟨clo_mono w.cov (lamStar_mono (hinf _)
                        (K.le_trans hspec.1 w.wle) X hX),
                      lamStar_subset_gHat hX⟩) hC
                  sub := fun _ h => absurd h List.not_mem_nil
                  cov := fun _ hx => hx }
  | (n+1), .circ Z =>
      -- THE ◯-DELTA, regular: `¬(a ⊩ ◯Z)` gives `¬(a ⊩ Z)` outright
      -- (`Rm` is reflexive), so recurse on `Z` at the same world — the
      -- right-formula size drops — and close with `◯∈`; the tag
      -- obligation transports through the `Covers` `circ`-clause.
      have hnfZ : ¬ K.force a Z := fun hZ => hnf (force_circ_of_force hZ)
      let w := minModV K G hloc hinf hsup a (n+1) Z (sfR_circ hC) hnfZ
      exact { ctx := w.ctx, t := w.t
              der := .circIn w.der w.tOK hC
              tOK := tOK_lift w.tOK (fun hc => .circ hc)
              wld := w.wld, wle := w.wle, cov := w.cov }
  | 0, .atom p =>
      exact { stab := [], th := (rm (gAt G) (.atom p)) ++ gImp G ++ gCirc G
              der := .axI (.atom p) rfl hC (CtxEq.refl _)
              sub := fun _ h => absurd h List.not_mem_nil
              cov := fun _ hx => lamStar_subset_axI hnf hx }
  | 0, .bot =>
      exact { stab := [], th := (rm (gAt G) .bot) ++ gImp G ++ gCirc G
              der := .axI .bot rfl hC (CtxEq.refl _)
              sub := fun _ h => absurd h List.not_mem_nil
              cov := fun _ hx => lamStar_subset_axI hnf hx }
  | 0, .and C₁ C₂ =>
      obtain ⟨hC1, hC2⟩ := sfR_and hC
      by_cases h1 : K.force a C₁
      · have h2 : ¬ K.force a C₂ := fun hc => hnf ⟨h1, hc⟩
        let w := minModV K G hloc hinf hsup a 0 C₂ hC2 h2
        exact { stab := w.stab, th := w.th, der := .andI2 w.der hC
                sub := w.sub, cov := w.cov }
      · let w := minModV K G hloc hinf hsup a 0 C₁ hC1 h1
        exact { stab := w.stab, th := w.th, der := .andI1 w.der hC
                sub := w.sub, cov := w.cov }
  | 0, .or C₁ C₂ =>
      obtain ⟨hC1, hC2⟩ := sfR_or hC
      have h1 : ¬ K.force a C₁ := fun hc => hnf (Or.inl hc)
      have h2 : ¬ K.force a C₂ := fun hc => hnf (Or.inr hc)
      let w₁ := minModV K G hloc hinf hsup a 0 C₁ hC1 h1
      let w₂ := minModV K G hloc hinf hsup a 0 C₂ hC2 h2
      refine { stab := w₁.stab ++ w₂.stab, th := cap w₁.th w₂.th
               der := .orI w₁.der w₂.der (fun X hX => w₂.cov (w₁.sub hX))
                        (fun X hX => w₁.cov (w₂.sub hX)) hC (CtxEq.refl _)
                        (CtxEq.refl _)
               sub := ?_, cov := ?_ }
      · intro X hX
        rcases List.mem_append.mp hX with hX' | hX'
        · exact w₁.sub hX'
        · exact w₂.sub hX'
      · intro X hX
        by_cases hx1 : X ∈ w₁.stab
        · exact List.mem_append_left _ (List.mem_append_left _ hx1)
        · by_cases hx2 : X ∈ w₂.stab
          · exact List.mem_append_left _ (List.mem_append_right _ hx2)
          · exact List.mem_append_right _ (mem_cap.mpr
              ⟨(List.mem_append.mp (w₁.cov hX)).resolve_left hx1,
               (List.mem_append.mp (w₂.cov hX)).resolve_left hx2⟩)
  | 0, .imp A B =>
      obtain ⟨hA, hB⟩ := sfR_imp hC
      let m := minEta hnf
      by_cases hea : m.e = a
      · have heA : K.force a A := hea ▸ m.fA
        have heB : ¬ K.force a B := hea ▸ m.nfB
        let w := minModV K G hloc hinf hsup a 0 B hB heB
        have hLamTh : sdiff (lamStar K a G) w.stab ⊆ w.th := by
          intro x hx
          obtain ⟨hx1, hx2⟩ := mem_sdiff.mp hx
          exact (List.mem_append.mp (w.cov hx1)).resolve_left hx2
        have hStLam : lamStar K a G ⊆ w.stab ++ sdiff (lamStar K a G) w.stab := by
          intro x hx
          by_cases hs : x ∈ w.stab
          · exact List.mem_append_left _ hs
          · exact List.mem_append_right _ (mem_sdiff.mpr ⟨hx, hs⟩)
        have hzone : w.th ≐ sdiff w.th (sdiff (lamStar K a G) w.stab) ++
            sdiff (lamStar K a G) w.stab := by
          intro x
          constructor
          · intro hx
            by_cases hL : x ∈ sdiff (lamStar K a G) w.stab
            · exact List.mem_append_right _ hL
            · exact List.mem_append_left _ (mem_sdiff.mpr ⟨hx, hL⟩)
          · intro hx
            rcases List.mem_append.mp hx with hx' | hx'
            · exact (mem_sdiff.mp hx').1
            · exact hLamTh hx'
        have hAclo : Clo (w.stab ++ sdiff (lamStar K a G) w.stab) A :=
          clo_mono hStLam (mem_clo_lamStar (hinf _) hA heA)
        refine { stab := w.stab ++ sdiff (lamStar K a G) w.stab
                 th := sdiff w.th (sdiff (lamStar K a G) w.stab)
                 der := .impInI w.der hzone cap_sdiff_eq_nil hAclo hC
                          (CtxEq.refl _) (CtxEq.refl _)
                 sub := ?_, cov := ?_ }
        · intro X hX
          rcases List.mem_append.mp hX with hX' | hX'
          · exact w.sub hX'
          · exact (mem_sdiff.mp hX').1
        · intro X hX
          exact List.mem_append_left _ (hStLam hX)
      · have hnaA : ¬ K.force a A :=
          m.min a (K.le_refl a) m.le (fun hc => hea hc.symm)
        let w := minModV K G hloc hinf hsup m.e 1 B hB m.nfB
        exact { stab := [], th := lamStar K a G
                der := .impNotIn w.der
                  (fun X hX => ⟨clo_mono w.cov (lamStar_mono (hinf _)
                      (K.le_trans m.le w.wle) X hX),
                    lamStar_subset_gHat hX⟩)
                  (clo_mono w.cov (mem_clo_lamStar (hinf _) hA
                    (K.force_mono w.wle m.fA)))
                  (fun hc => hnaA (forces_clo_lamStar hc)) hC
                sub := fun _ h => absurd h List.not_mem_nil
                cov := fun _ hx => hx }
  | (n+1), .atom p =>
      by_cases hempty : impPart (lamStar K a G) = []
      · exact regPrimeV_ax K G a (.atom p) (hloc a) rfl hC hnf hempty
      · refine regPrimeV_join K G a (.atom p) (hloc a) rfl hC hnf ?_
          (fun A hA hnA => minModV K G hloc hinf hsup a 0 A hA hnA)
        intro hc
        refine hempty (eq_nil_of_forall_not_mem (fun X hX => ?_))
        obtain ⟨hXl, hXi⟩ := List.mem_filter.mp hX
        match X, hXi with
        | .imp A B, _ =>
            exact absurd (mem_upsPrime hXl) (by rw [hc]; exact List.not_mem_nil)
  | (n+1), .bot =>
      by_cases hempty : impPart (lamStar K a G) = []
      · exact regPrimeV_ax K G a .bot (hloc a) rfl hC hnf hempty
      · refine regPrimeV_join K G a .bot (hloc a) rfl hC hnf ?_
          (fun A hA hnA => minModV K G hloc hinf hsup a 0 A hA hnA)
        intro hc
        refine hempty (eq_nil_of_forall_not_mem (fun X hX => ?_))
        obtain ⟨hXl, hXi⟩ := List.mem_filter.mp hX
        match X, hXi with
        | .imp A B, _ =>
            exact absurd (mem_upsPrime hXl) (by rw [hc]; exact List.not_mem_nil)
  | (n+1), .and C₁ C₂ =>
      obtain ⟨hC1, hC2⟩ := sfR_and hC
      by_cases h1 : K.force a C₁
      · have h2 : ¬ K.force a C₂ := fun hc => hnf ⟨h1, hc⟩
        let w := minModV K G hloc hinf hsup a (n+1) C₂ hC2 h2
        exact { ctx := w.ctx, t := w.t, der := .andR2 w.der hC
                tOK := tOK_lift w.tOK (fun hc => .andR hc)
                wld := w.wld, wle := w.wle, cov := w.cov }
      · let w := minModV K G hloc hinf hsup a (n+1) C₁ hC1 h1
        exact { ctx := w.ctx, t := w.t, der := .andR1 w.der hC
                tOK := tOK_lift w.tOK (fun hc => .andL hc)
                wld := w.wld, wle := w.wle, cov := w.cov }
  | (n+1), .or C₁ C₂ =>
      exact regOrV_join K G a C₁ C₂ (hloc a) hC hnf
        (fun A hA hnA => minModV K G hloc hinf hsup a 0 A hA hnA)
  | (n+1), .imp A B =>
      obtain ⟨hA, hB⟩ := sfR_imp hC
      let m := minEta hnf
      by_cases hea : m.e = a
      · have heA : K.force a A := hea ▸ m.fA
        have heB : ¬ K.force a B := hea ▸ m.nfB
        let w := minModV K G hloc hinf hsup a (n+1) B hB heB
        have hAclo : Clo w.ctx A := clo_mono w.cov
          (mem_clo_lamStar (hinf _) hA (K.force_mono w.wle heA))
        exact { ctx := w.ctx, t := w.t
                der := .impIn w.der hAclo hC
                tOK := tOK_lift w.tOK (fun hc => .imp hc hAclo)
                wld := w.wld, wle := w.wle, cov := w.cov }
      · let w := minModV K G hloc hinf hsup m.e 1 B hB m.nfB
        have hAclo : Clo w.ctx A := clo_mono w.cov
          (mem_clo_lamStar (hinf _) hA (K.force_mono w.wle m.fA))
        exact { ctx := w.ctx, t := w.t
                der := .impIn w.der hAclo hC
                tOK := tOK_lift w.tOK (fun hc => .imp hc hAclo)
                wld := w.wld, wle := K.le_trans m.le w.wle, cov := w.cov }
termination_by (ht K a, t, C.size)
decreasing_by
  all_goals
    first
      | (apply Prod.Lex.left
         exact ht_lt m.le hea)
      | (apply Prod.Lex.left
         exact ht_lt hspec.1 hspec.2.1)
      | (apply Prod.Lex.right
         apply Prod.Lex.left
         omega)
      | (apply Prod.Lex.right
         apply Prod.Lex.right
         first
           | omega
           | (simp only [Form.size]; omega))

/-! ## Round-1 completeness -/

/-- **Round-1 completeness of the repaired calculus**: over models with
world-wise `◯`-free `Λ*`, infallible throughout, and the sole-candidate
supply, every countermodel of `G` yields an FRJV derivation of `G` —
with `G` MODAL on both sides of the recursion. -/
theorem completenessV_of_supply {G : Form} (K : Kripke)
    (hloc : ∀ b : K.W, circPart (lamStar K b G) = [])
    (hinf : K.Infallible) (hsup : CircSupplyV K G)
    (hK : ¬ K.valid G) : ProvableV G :=
  let w := minModV K G hloc hinf hsup K.root 1 G (sfR_self G) hK
  ⟨w.t, w.ctx, ⟨w.der⟩⟩

/-- info: 'FRJ.minModV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms minModV

/-- info: 'FRJ.completenessV_of_supply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completenessV_of_supply

/-! ## Round 2: the supply discharged

The corner's own hypotheses pin the demanding world's modal cone to
`{a}` (`coneTrivial_of_corner`, hypothesis-free).  On a CONE-GROUNDED
frame — every cone-trivial world is `≤`-maximal, which holds in
particular whenever `Rm = ≤`, and on discrete frames — the corner world
is therefore maximal, where the generalised `Ax^I◯` over the world's own
classical theory produces the wit outright (`circWit_of_maximal`,
`FRJ/Saturate.lean`).  `FRJVi` is the paper family verbatim, so the wit
embeds by `toVi` and `CircSupplyV` is DISCHARGED — round 1's supply
hypothesis disappears on cone-grounded frames.

What does NOT discharge: the corner at a cone-trivial world that is not
`≤`-maximal (an `Rm` strictly finer than `≤`).  There the chosen
valuation can be beaten by a poisoned `Λ*`-implication (classically true
antecedent, unforced at the world — frj-w4 §9 addendum), and the open
kernel is exactly that residue — for BOTH calculi.  The V-lever for it
is the kept chain on the row a `circNotIn` premise needs; note the
peer's refutation (2026-08-26): kept members are IMPLICATIONS, full
stop, so the lever addresses poisoned implications only, and no
supply-form hypothesis can organise the promise side
(`V.PledgeSupply` is FALSE in the kernel — `not_pledgeFam_of_circ_mem`). -/

/-- The paper wit embeds. -/
def IrrWit.toV {K : Kripke} {G : Form} {a : K.W} {C : Form}
    (w : IrrWit K G a C) : IrrWitV K G a C :=
  ⟨w.stab, w.th, toVi w.der, w.sub, w.cov⟩

/-- **The chosen-valuation route** (frj-w4 §11 route 3), maximality-free:
any classical valuation `ats ⊆ Ĝ_at` whose theory contains `Λ*_a` and
refutes `Z` closes the corner by the generalised `Ax^I◯`.  Both
hypotheses are decidable per world on a finite model; it is blocked
exactly when `Λ*_a ⊨_cl Z` (the poisoned residue). -/
def circWitV_of_ats {K : Kripke} {G : Form} {a : K.W} {Z : Form}
    (ats : List Form) (hats : ats ⊆ gAt G)
    (hZf : classForce ats Z = false) (hZ : Form.circ Z ∈ sfR G)
    (hcov : ∀ X ∈ lamStar K a G, classForce ats X = true) :
    IrrWitV K G a (.circ Z) :=
  { stab := []
    th := vacZoneA G ats
    der := .axIC Z ats hats hZf hZ (CtxEq.refl _)
    sub := List.nil_subset _
    cov := fun X hX =>
      List.mem_filter.mpr ⟨lamStar_subset_gHat hX, hcov X hX⟩ }

/-- **`CircSupplyV` discharged on cone-grounded frames**: the corner is
cone-trivial, the frame condition makes it maximal, and the generalised
`Ax^I◯` closes it. -/
def circSupplyV_of_coneGrounded {K : Kripke} {G : Form}
    (hg : K.ConeGrounded) : CircSupplyV K G :=
  fun _ _ hZ hnf hsole =>
    (circWit_of_maximal (hg _ (coneTrivial_of_corner hnf hsole)) hZ hnf).toV

/-- **Round-1 completeness with NO supply hypothesis** on cone-grounded
frames (in particular on every `Rm = ≤` model and every discrete
model). -/
theorem completenessV_of_coneGrounded {G : Form} (K : Kripke)
    (hloc : ∀ b : K.W, circPart (lamStar K b G) = [])
    (hinf : K.Infallible) (hg : K.ConeGrounded)
    (hK : ¬ K.valid G) : ProvableV G :=
  completenessV_of_supply K hloc hinf (circSupplyV_of_coneGrounded hg) hK

/-- **FRJV completeness over endpoint-seeing models, UNCONDITIONAL** —
no `hloc`, no infallibility, no supply: the peer campaign's two-tier
recursion (`completeness_of_endpoints`, `FRJ/Saturate.lean`) composed
with the embedding.  On frames whose every modal cone contains a
`≤`-maximal world, the repaired calculus derives every refuted goal.
(The #80/#81 incompleteness witnesses live on NON-endpoint frames, which
is where FRJV must eventually go beyond FRJ.) -/
theorem completenessV_of_endpoints {G : Form} (K : Kripke)
    (hep : K.Endpoints) (hK : ¬ K.valid G) : ProvableV G :=
  provableV_of_provable (completeness_of_endpoints hep hK)

/-- info: 'FRJ.circSupplyV_of_coneGrounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms circSupplyV_of_coneGrounded

/-- info: 'FRJ.completenessV_of_coneGrounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completenessV_of_coneGrounded

/-- info: 'FRJ.completenessV_of_endpoints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completenessV_of_endpoints

end FRJ
