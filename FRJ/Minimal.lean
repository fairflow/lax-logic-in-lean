/-
# Completeness of FRJ(G): Lemma 6.4 and Theorem 6.2

Section 6's direct construction.  Triple induction, exactly the paper's:
(IH1) on `h(α)`, (IH2) on the sequent type (irregular before regular),
(IH3) on `size C` — realised as the lexicographic measure
`(ht K a, t, C.size)`.

**Type-valued.**  The paper states Lemma 6.4 as an existence claim, and
so did the first version of this file; extracting the derivations from it
then needed `choose` and `Nonempty.some`, both of which are
`Classical.choice`.  Here the two halves are *records carrying the
derivation*, so nothing is chosen — and completeness becomes an
algorithm taking a countermodel to a derivation, which is what the whole
development is for.
-/
import FRJ.Complete

namespace FRJ

open Form

theorem not_mem_lamStar_of_not_force {K : Kripke} {a : K.W} {G C : Form}
    (h : ¬ K.force a C) : C ∉ lamStar K a G :=
  fun hc => h (K.forceStar_force (mem_lamStar.mp hc).2)

/-! ## Enumerating a nonempty context

The join rules take `n ≥ 1` premises indexed by `Fin (n+1)`, so the set
`Υ` they range over has to be presented in that shape.  The enumeration
is DATA, so this is a `Type`, not an existence claim. -/

/-- An enumeration of `S` by `Fin (n+1)`, up to membership. -/
structure Enum (S : List Form) : Type where
  n : Nat
  f : Fin (n + 1) → Form
  spec : ∀ y, y ∈ upsilon f ↔ y ∈ S

/-- Any nonempty list can be enumerated: take its own indexing. -/
def enumOf : ∀ (S : List Form), S ≠ [] → Enum S
  | [], h => absurd rfl h
  | x :: xs, _ =>
      { n := xs.length
        f := fun j => (x :: xs)[j.val]'j.isLt
        spec := by
          intro y
          constructor
          · intro hy
            obtain ⟨j, -, hj⟩ := List.mem_map.mp hy
            exact hj ▸ List.getElem_mem _
          · intro hy
            obtain ⟨i, hi, hval⟩ := List.getElem_of_mem hy
            exact List.mem_map.mpr ⟨⟨i, hi⟩, List.mem_finRange _, hval⟩ }

/-! ## `Υ` for the prime case -/

/-- The antecedent of an implication. -/
def ante : Form → Form
  | .imp A _ => A
  | X => X

/-- `Υ` for the prime case: the antecedents of the implications of `Λ*_a`. -/
def upsPrime (K : Kripke) (a : K.W) (G : Form) : List Form :=
  (impPart (lamStar K a G)).map ante

/-- Members of `Υ` are right subformulas that `a` refutes. -/
theorem upsPrime_spec {K : Kripke} {a : K.W} {G Y : Form}
    (h : Y ∈ upsPrime K a G) : Y ∈ sfR G ∧ ¬ K.force a Y := by
  obtain ⟨X, hX, hante⟩ := List.mem_map.mp h
  obtain ⟨hXl, hXimp⟩ := List.mem_filter.mp hX
  match X, hXimp with
  | .imp A B, _ =>
      obtain ⟨hsf, hst⟩ := mem_lamStar.mp hXl
      obtain ⟨hA, -⟩ := sfL_imp hsf
      subst hante
      exact ⟨hA, hst.2⟩

/-- An implication of `Λ*_a` has its antecedent in `Υ`. -/
theorem mem_upsPrime {K : Kripke} {a : K.W} {G A B : Form}
    (h : Form.imp A B ∈ lamStar K a G) : A ∈ upsPrime K a G :=
  List.mem_map.mpr ⟨.imp A B, List.mem_filter.mpr ⟨h, rfl⟩, rfl⟩

/-! ## The two halves of Lemma 6.4, as data -/

/-- The irregular half: a derivation of `Σ ; Θ → C` with `Σ ⊆ Λ*_a` and
`Λ*_a ⊆ Σ, Θ`.  No canonicity field: the `⊃∈` step below splits the zone
EXTENSIONALLY (`Θ₁ ≐ Θ ++ Λ`), which is what the paper's "contexts denote
sets" means, so nothing has to be normalised first. -/
structure IrrWit (K : Kripke) (G : Form) (a : K.W) (C : Form) : Type where
  stab : List Form
  th : List Form
  der : FRJi G stab th C
  sub : stab ⊆ lamStar K a G
  cov : lamStar K a G ⊆ stab ++ th

/-- The regular half: a derivation of `Γ ⇒ C` and a world `b ≥ a` whose
`Λ*` the context covers. -/
structure RegWit (K : Kripke) (G : Form) (a : K.W) (C : Form) : Type where
  ctx : List Form
  /-- W4 note: the completeness construction never uses a promise or
  fallible join — its input is an infallible countermodel of a `◯`-free
  goal (`hcf`), whose `Λ*` carries no modal formula — so every derivation
  it builds is BARREN-tagged. -/
  der : FRJr G .barren ctx C
  wld : K.W
  wle : K.le a wld
  cov : lamStar K wld G ⊆ ctx

/-- Lemma 6.4, indexed by `t`: `t = 0` is the irregular half, `t ≠ 0` the
regular one. -/
def MinModStmt (K : Kripke) (G : Form) (a : K.W) (t : Nat) (C : Form) : Type :=
  match t with
  | 0 => IrrWit K G a C
  | _ => RegWit K G a C

/-! ## The three regular cases -/

/-- The `⋈^At` case: `C` prime, `Λ*_a` containing at least one
implication.  The join's premises are the irregular derivations for the
members of `Υ`, supplied by the induction hypothesis `ih`. -/
def regPrime_join (K : Kripke) (G : Form) (a : K.W) (C : Form)
    (hcf : ∀ X ∈ sfR G ++ sfL G, X.isCirc = false)
    (hCp : C.isPrime) (hC : C ∈ sfR G) (hnf : ¬ K.force a C)
    (hne : upsPrime K a G ≠ [])
    (ih : ∀ (A : Form), A ∈ sfR G → ¬ K.force a A → IrrWit K G a A) :
    RegWit K G a C :=
  let E := enumOf (upsPrime K a G) hne
  let f := E.f
  let hfmem : ∀ j, f j ∈ upsPrime K a G := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  let wit : ∀ j, IrrWit K G a (f j) := fun j =>
    ih (f j) (upsPrime_spec (hfmem j)).1 (upsPrime_spec (hfmem j)).2
  let stab := fun j => (wit j).stab
  let th := fun j => (wit j).th
  { ctx := joinCtxAt stab th f C
    wld := a
    wle := K.le_refl a
    der := by
      refine .joinAt (fun j => (wit j).der) (fun i j _ X hX => (wit j).cov ((wit i).sub hX))
        (fun A B hmem => ?_) (unionAll_circPart_nil hcf (fun j => (wit j).sub))
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
        simp only [joinCtxAt, List.mem_append]
        rcases hXG with (h | h) | h
        · exact Or.inl (Or.inl (Or.inl (mem_unionAll.mpr
            ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩)))
        · exact Or.inl (Or.inr (mem_unionAll.mpr
            ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩))
        · exact absurd ((List.mem_filter.mp h).2) (fun hc => lamStar_not_circ hcf hX hc)
      · have hin' : ∀ j, X ∉ stab j := fun j hj => hin ⟨j, hj⟩
        have hallTh : ∀ j, X ∈ th j :=
          fun j => (List.mem_append.mp ((wit j).cov hX)).resolve_left (hin' j)
        simp only [joinCtxAt, List.mem_append]
        rcases hXG with (h | h) | h
        · refine Or.inl (Or.inl (Or.inr (mem_rm.mpr
            ⟨fun hc => not_mem_lamStar_of_not_force hnf (hc ▸ hX), ?_⟩)))
          exact mem_interAll.mpr (fun j =>
            List.mem_filter.mpr ⟨hallTh j, (List.mem_filter.mp h).2⟩)
        · refine Or.inr ?_
          have himp : X.isImp := (List.mem_filter.mp h).2
          match X, himp with
          | .imp A B, _ =>
              refine mem_restrict.mpr ⟨mem_interAll.mpr (fun j =>
                List.mem_filter.mpr ⟨hallTh j, rfl⟩), ?_⟩
              exact (E.spec A).mpr (mem_upsPrime hX)
        · exact absurd ((List.mem_filter.mp h).2)
            (fun hc => lamStar_not_circ hcf hX hc) }

/-- `C` prime with `Λ*_a` purely atomic: the `Ax^R` sub-case. -/
def regPrime_ax (K : Kripke) (G : Form) (a : K.W) (C : Form)
    (hcf : ∀ X ∈ sfR G ++ sfL G, X.isCirc = false)
    (hCp : C.isPrime) (hC : C ∈ sfR G) (hnf : ¬ K.force a C)
    (hempty : impPart (lamStar K a G) = []) : RegWit K G a C :=
  { ctx := rm (gAt G) C
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
            (fun hc => lamStar_not_circ hcf hX hc) }

/-- The `⋈^∨` case. -/
def regOr_join (K : Kripke) (G : Form) (a : K.W) (C₁ C₂ : Form)
    (hcf : ∀ X ∈ sfR G ++ sfL G, X.isCirc = false)
    (hC : Form.or C₁ C₂ ∈ sfR G) (hnf : ¬ K.force a (.or C₁ C₂))
    (ih : ∀ (A : Form), A ∈ sfR G → ¬ K.force a A → IrrWit K G a A) :
    RegWit K G a (.or C₁ C₂) :=
  let hn1 : ¬ K.force a C₁ := fun hc => hnf (Or.inl hc)
  let hn2 : ¬ K.force a C₂ := fun hc => hnf (Or.inr hc)
  let U := C₁ :: C₂ :: upsPrime K a G
  let E := enumOf U (by simp [U])
  let f := E.f
  let hfmem : ∀ j, f j ∈ U := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  let wit : ∀ j, IrrWit K G a (f j) := fun j =>
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
  { ctx := joinCtxOr stab th f
    wld := a
    wle := K.le_refl a
    der := by
      refine .joinOr (fun j => (wit j).der) (fun i j _ X hX => (wit j).cov ((wit i).sub hX))
        (fun A B hmem => ?_) (unionAll_circPart_nil hcf (fun j => (wit j).sub))
        ⟨?_, ?_⟩ hC (CtxEq.refl _)
      · obtain ⟨i, hi⟩ := mem_unionAll.mp hmem
        exact (E.spec A).mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (mem_upsPrime ((wit i).sub (List.mem_filter.mp hi).1))))
      · exact (E.spec C₁).mpr List.mem_cons_self
      · exact (E.spec C₂).mpr (List.mem_cons_of_mem _ List.mem_cons_self)
    cov := by
      intro X hX
      have hXG := lamStar_subset_gHat hX
      simp only [gHat, List.mem_append] at hXG
      by_cases hin : ∃ j, X ∈ stab j
      · obtain ⟨j, hj⟩ := hin
        simp only [joinCtxOr, List.mem_append]
        rcases hXG with (h | h) | h
        · exact Or.inl (Or.inl (Or.inl (mem_unionAll.mpr
            ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩)))
        · exact Or.inl (Or.inr (mem_unionAll.mpr
            ⟨j, List.mem_filter.mpr ⟨hj, (List.mem_filter.mp h).2⟩⟩))
        · exact absurd ((List.mem_filter.mp h).2)
            (fun hc => lamStar_not_circ hcf hX hc)
      · have hin' : ∀ j, X ∉ stab j := fun j hj => hin ⟨j, hj⟩
        have hallTh : ∀ j, X ∈ th j :=
          fun j => (List.mem_append.mp ((wit j).cov hX)).resolve_left (hin' j)
        simp only [joinCtxOr, List.mem_append]
        rcases hXG with (h | h) | h
        · exact Or.inl (Or.inl (Or.inr (mem_interAll.mpr (fun j =>
            List.mem_filter.mpr ⟨hallTh j, (List.mem_filter.mp h).2⟩))))
        · refine Or.inr ?_
          have himp : X.isImp := (List.mem_filter.mp h).2
          match X, himp with
          | .imp A B, _ =>
              refine mem_restrict.mpr ⟨mem_interAll.mpr (fun j =>
                List.mem_filter.mpr ⟨hallTh j, rfl⟩), ?_⟩
              exact (E.spec A).mpr (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (mem_upsPrime hX)))
        · exact absurd ((List.mem_filter.mp h).2)
            (fun hc => lamStar_not_circ hcf hX hc) }

/-- The `Ax^I` zone contains `Λ*_a` whenever `C` is unforced there. -/
theorem lamStar_subset_axI {K : Kripke} {a : K.W} {G C : Form}
    (h : ¬ K.force a C) :
    lamStar K a G ⊆ (rm (gAt G) C) ++ gImp G ++ gCirc G := by
  intro X hX
  have hne : X ≠ C := by
    intro hc; exact h (hc ▸ K.forceStar_force (mem_lamStar.mp hX).2)
  have hG := lamStar_subset_gHat hX
  simp only [gHat, List.mem_append] at hG
  rcases hG with (h1 | h1) | h1
  · exact List.mem_append_left _ (List.mem_append_left _ (mem_rm.mpr ⟨hne, h1⟩))
  · exact List.mem_append_left _ (List.mem_append_right _ h1)
  · exact List.mem_append_right _ h1

/-! ## Lemma 6.4 -/

def minMod (K : Kripke) (G : Form) (hcf : ∀ X ∈ sfR G ++ sfL G, X.isCirc = false)
    (hinf : K.Infallible) (a : K.W) (t : Nat) (C : Form)
    (hC : C ∈ sfR G) (hnf : ¬ K.force a C) : MinModStmt K G a t C := by
  match t, C with
  | _, .circ A =>
      -- W1: no rule of the calculus concludes a `◯`-goal, and `Λ*` does
      -- not carry the `◯`-formulas.  Out of scope until the modal rules
      -- arrive; see the note on `gHat`.
      exact absurd (hcf _ (List.mem_append_left _ hC)) (by simp [Form.isCirc])
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
        let w := minMod K G hcf hinf a 0 C₂ hC2 h2
        exact { stab := w.stab, th := w.th, der := .andI2 w.der hC
                sub := w.sub, cov := w.cov }
      · let w := minMod K G hcf hinf a 0 C₁ hC1 h1
        exact { stab := w.stab, th := w.th, der := .andI1 w.der hC
                sub := w.sub, cov := w.cov }
  | 0, .or C₁ C₂ =>
      obtain ⟨hC1, hC2⟩ := sfR_or hC
      have h1 : ¬ K.force a C₁ := fun hc => hnf (Or.inl hc)
      have h2 : ¬ K.force a C₂ := fun hc => hnf (Or.inr hc)
      let w₁ := minMod K G hcf hinf a 0 C₁ hC1 h1
      let w₂ := minMod K G hcf hinf a 0 C₂ hC2 h2
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
        let w := minMod K G hcf hinf a 0 B hB heB
        have hLamTh : sdiff (lamStar K a G) w.stab ⊆ w.th := by
          intro x hx
          obtain ⟨hx1, hx2⟩ := mem_sdiff.mp hx
          exact (List.mem_append.mp (w.cov hx1)).resolve_left hx2
        have hStLam : lamStar K a G ⊆ w.stab ++ sdiff (lamStar K a G) w.stab := by
          intro x hx
          by_cases hs : x ∈ w.stab
          · exact List.mem_append_left _ hs
          · exact List.mem_append_right _ (mem_sdiff.mpr ⟨hx, hs⟩)
        -- **The Θ-split of Lemma 6.3**, as the paper states it: `Θ₁ = Θ ∪ Λ`
        -- is an equation between SETS, so here it is a membership
        -- equivalence and nothing has to be normalised to make it hold.
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
        let w := minMod K G hcf hinf m.e 1 B hB m.nfB
        have hab : K.le a w.wld := K.le_trans m.le w.wle
        exact { stab := [], th := lamStar K a G
                der := .impNotIn w.der
                  (fun X hX => ⟨clo_mono w.cov (lamStar_mono (hinf _) hab X hX),
                    lamStar_subset_gHat hX⟩)
                  (clo_mono w.cov (mem_clo_lamStar (hinf _) hA (K.force_mono w.wle m.fA)))
                  (fun hc => hnaA (forces_clo_lamStar hc)) hC
                sub := fun _ h => absurd h List.not_mem_nil
                cov := fun _ hx => hx }
  | (n+1), .atom p =>
      by_cases hempty : impPart (lamStar K a G) = []
      · exact regPrime_ax K G a (.atom p) hcf rfl hC hnf hempty
      · refine regPrime_join K G a (.atom p) hcf rfl hC hnf ?_
          (fun A hA hnA => minMod K G hcf hinf a 0 A hA hnA)
        intro hc
        refine hempty (eq_nil_of_forall_not_mem (fun X hX => ?_))
        obtain ⟨hXl, hXi⟩ := List.mem_filter.mp hX
        match X, hXi with
        | .imp A B, _ =>
            exact absurd (mem_upsPrime hXl) (by rw [hc]; exact List.not_mem_nil)
  | (n+1), .bot =>
      by_cases hempty : impPart (lamStar K a G) = []
      · exact regPrime_ax K G a .bot hcf rfl hC hnf hempty
      · refine regPrime_join K G a .bot hcf rfl hC hnf ?_
          (fun A hA hnA => minMod K G hcf hinf a 0 A hA hnA)
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
        let w := minMod K G hcf hinf a (n+1) C₂ hC2 h2
        exact { ctx := w.ctx, der := .andR2 w.der hC
                wld := w.wld, wle := w.wle, cov := w.cov }
      · let w := minMod K G hcf hinf a (n+1) C₁ hC1 h1
        exact { ctx := w.ctx, der := .andR1 w.der hC
                wld := w.wld, wle := w.wle, cov := w.cov }
  | (n+1), .or C₁ C₂ =>
      exact regOr_join K G a C₁ C₂ hcf hC hnf (fun A hA hnA => minMod K G hcf hinf a 0 A hA hnA)
  | (n+1), .imp A B =>
      obtain ⟨hA, hB⟩ := sfR_imp hC
      let m := minEta hnf
      by_cases hea : m.e = a
      · have heA : K.force a A := hea ▸ m.fA
        have heB : ¬ K.force a B := hea ▸ m.nfB
        let w := minMod K G hcf hinf a (n+1) B hB heB
        exact { ctx := w.ctx
                der := .impIn w.der (clo_mono w.cov
                  (mem_clo_lamStar (hinf _) hA (K.force_mono w.wle heA))) hC
                wld := w.wld, wle := w.wle, cov := w.cov }
      · let w := minMod K G hcf hinf m.e 1 B hB m.nfB
        exact { ctx := w.ctx
                der := .impIn w.der (clo_mono w.cov
                  (mem_clo_lamStar (hinf _) hA (K.force_mono w.wle m.fA))) hC
                wld := w.wld, wle := K.le_trans m.le w.wle, cov := w.cov }
termination_by (ht K a, t, C.size)
decreasing_by
  all_goals
    first
      | (apply Prod.Lex.left
         exact ht_lt m.le hea)
      | (apply Prod.Lex.right
         apply Prod.Lex.left
         omega)
      | (apply Prod.Lex.right
         apply Prod.Lex.right
         first
           | omega
           | (simp only [Form.size]; omega))

/-! ## Theorem 6.2 (Completeness) and the biconditional -/

/-- A derivation of `G` in `FRJ(G)`, as data.  The completeness
construction only produces barren-tagged derivations. -/
def Derivation (G : Form) : Type := Σ Γ : List Form, FRJr G .barren Γ G

/-- **Completeness, as an algorithm** (Theorem 6.2(i)): a countermodel
for `G` is turned into an `FRJ(G)`-derivation of `G`.  Apply Lemma 6.4 at
the countermodel's root, in the regular half, with goal `G`. -/
def completenessData {G : Form} (hcf : ∀ X ∈ sfR G ++ sfL G, X.isCirc = false)
    (K : Kripke) (hinf : K.Infallible) (hK : ¬ K.valid G) : Derivation G :=
  let w := minMod K G hcf hinf K.root 1 G (sfR_self G) hK
  ⟨w.ctx, w.der⟩

/-- **Completeness** (Theorem 6.2(i)).

W3 added the hypothesis `hinf`: the construction reads a derivation off an
INFALLIBLE countermodel.  At a fallible world every formula is forced, so
`Ω_α` is empty and `Cl(Λ*_α)` cannot reach `⊥`; a fallible countermodel
carries no data the calculus can consume.  This is not a gap in the proof
but the exact statement of what the calculus does: `Mod(D)` is always
infallible, so no derivation refutes a formula that every infallible model
validates — and `¬◯⊥` is one (`FRJ/Fallible.lean`). -/
theorem completeness {G : Form} (hcf : ∀ X ∈ sfR G ++ sfL G, X.isCirc = false)
    (K : Kripke) (hinf : K.Infallible) (hK : ¬ K.valid G) : Provable G :=
  ⟨.barren, (completenessData hcf K hinf hK).1,
    ⟨(completenessData hcf K hinf hK).2⟩⟩

/-- **The biconditional, constructively**: `FRJ(G)` proves `G` exactly
when `G` has a countermodel.  Soundness (Theorem 3.1, via Theorem 3.10)
gives one direction, completeness the other. -/
theorem frj_iff_countermodel (G : Form)
    (hcf : ∀ X ∈ sfR G ++ sfL G, X.isCirc = false) :
    Provable G ↔ ∃ K : Kripke, K.Infallible ∧ ¬ K.valid G := by
  constructor
  · rintro ⟨t, Γ, ⟨d⟩⟩
    -- the extracted model may use declared fallible worlds; for a
    -- `◯`-free goal the restriction deletes them (`infallible_countermodel`)
    exact infallible_countermodel hcf (modR_countermodel d)
  · rintro ⟨K, hinf, hK⟩
    exact completeness hcf K hinf hK

/-- **The paper's statement** (Theorem 6.2(i) with Theorem 3.1):
`FRJ(G)` proves `G` iff `G` is not intuitionistically valid.

The only step here that is not constructive is the passage from "not
every model validates `G`" to "some model refutes `G`", which is where
this pins `Classical.choice`; `frj_iff_countermodel` is the same result
with that step left to the caller, and depends on no choice. -/
theorem frj_iff_not_IPL (G : Form)
    (hcf : ∀ X ∈ sfR G ++ sfL G, X.isCirc = false) :
    Provable G ↔ ¬ IPL G := by
  rw [frj_iff_countermodel G hcf]
  constructor
  · rintro ⟨K, hinf, hK⟩ h
    exact hK (h K hinf)
  · intro h
    by_contra hc
    push_neg at hc
    exact h (fun K hinf => not_not.mp (fun hn => hn (hc K hinf)))

end FRJ
