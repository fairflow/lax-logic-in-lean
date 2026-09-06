/-
Route (B), node **N4**, WP9, part A: the closure, the three components of
`qMu`, and the two arithmetic lemmas that flatten the lexicographic measure
of `docs/n4-loopcheck.md` §4 into a `Nat`.

Everything here is about the MEASURE alone; not one line mentions `stepQ`.
The edge-by-edge descent is `wip/ui_routeB_n4q_bound.lean`.

The flattening, in one line.  With `κ` the guard deficiency, `W` a power of
three above every weight of the closure, and `ν` the weight measure:

* an ORDINARY edge has `κ' ≤ κ`, `W' ≤ W`, `ν' < ν`, hence
  `κ'·W' + ν' ≤ κ·W + ν' < κ·W + ν`;
* a GUARD edge has `κ' + 1 ≤ κ`, `W' ≤ W`, `ν' < ν + W`, hence
  `κ'·W' + ν' ≤ κ'·W + ν' < (κ'+1)·W + ν ≤ κ·W + ν`.

Both are `qMu_lt_of_ordinary` and `qMu_lt_of_guard` below.
-/
import wip.ui_routeB_n4q_meas
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 1 · `seenMem` as membership -/

theorem seenMem_iff (s : List Pos) (Q : Pos) : seenMem s Q = true ↔ Q ∈ s := by
  induction s with
  | nil => simp [seenMem]
  | cons R s ih =>
      simp only [seenMem, List.mem_cons]
      by_cases h : R = Q
      · subst h; simp
      · rw [if_neg h, ih]
        constructor
        · intro hq; exact Or.inr hq
        · rintro (rfl | hq)
          · exact absurd rfl h
          · exact hq

theorem not_seenMem_iff (s : List Pos) (Q : Pos) : seenMem s Q = false ↔ Q ∉ s := by
  constructor
  · intro hf hq
    have ht := (seenMem_iff s Q).mpr hq
    rw [hf] at ht
    exact Bool.noConfusion ht
  · intro hq
    cases hb : seenMem s Q with
    | false => rfl
    | true => exact absurd ((seenMem_iff s Q).mp hb) hq

/-! # Part 2 · The closure: equations and the subset kit -/

theorem subP_atom (a : String) : subP (.atom a) = [.up (.atom a), .circ (.atom a)] := by
  simp [subP]

theorem subP_fls : subP .fls = [.up .fls, .circ .fls] := by simp [subP]

theorem subP_or (P₁ P₂ : Pos) :
    subP (.or P₁ P₂) = .up (.or P₁ P₂) :: .circ (.or P₁ P₂) :: (subP P₁ ++ subP P₂) := by
  simp [subP]

theorem subP_down (M : Neg) :
    subP (.down M) = .up (.down M) :: .circ (.down M) :: subN M := by simp [subP]

theorem subN_up (P : Pos) : subN (.up P) = .up P :: subP P := by simp [subN]

theorem subN_circ (P : Pos) : subN (.circ P) = .circ P :: subP P := by simp [subN]

theorem subN_and (M₁ M₂ : Neg) :
    subN (.and M₁ M₂) = .and M₁ M₂ :: (subN M₁ ++ subN M₂) := by simp [subN]

theorem subN_imp (Q : Pos) (N : Neg) :
    subN (.imp Q N) = .imp Q N :: (subP Q ++ subN N ++ subD Q N) := by simp [subN]

theorem subD_dyk (Q' : Pos) (N' N : Neg) :
    subD (.down (.imp Q' N')) N = subN (.imp (.down N') N) := by simp [subD]

/-- Every positive contributes its own `↑` and `◯`. -/
theorem up_mem_subP (P : Pos) : Neg.up P ∈ subP P := by
  cases P with
  | atom a => simp [subP_atom]
  | fls => simp [subP_fls]
  | or P₁ P₂ => simp [subP_or]
  | down M => simp [subP_down]

theorem circ_mem_subP (P : Pos) : Neg.circ P ∈ subP P := by
  cases P with
  | atom a => simp [subP_atom]
  | fls => simp [subP_fls]
  | or P₁ P₂ => simp [subP_or]
  | down M => simp [subP_down]

theorem subN_up_sub (P : Pos) : subN (.up P) ⊆ subP P := by
  rw [subN_up]
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact up_mem_subP P
  · exact hx

theorem subN_circ_sub (P : Pos) : subN (.circ P) ⊆ subP P := by
  rw [subN_circ]
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact circ_mem_subP P
  · exact hx

theorem subP_or_left (P₁ P₂ : Pos) : subP P₁ ⊆ subP (.or P₁ P₂) := by
  rw [subP_or]; intro x hx; simp [List.mem_append, hx]

theorem subP_or_right (P₁ P₂ : Pos) : subP P₂ ⊆ subP (.or P₁ P₂) := by
  rw [subP_or]; intro x hx; simp [List.mem_append, hx]

theorem subN_sub_subP_down (M : Neg) : subN M ⊆ subP (.down M) := by
  rw [subP_down]; intro x hx; simp [hx]

theorem subP_sub_subN_imp (Q : Pos) (N : Neg) : subP Q ⊆ subN (.imp Q N) := by
  rw [subN_imp]; intro x hx; simp [List.mem_append, hx]

theorem subN_con_sub_imp (Q : Pos) (N : Neg) : subN N ⊆ subN (.imp Q N) := by
  rw [subN_imp]; intro x hx; simp [List.mem_append, hx]

/-- **The Dyckhoff residual is in the closure**: this is the one clause of
`interpQ` that manufactures an implication, and the closure is built to
absorb it. -/
theorem subN_dyk_sub (Q' : Pos) (N' N : Neg) :
    subN (.imp (.down N') N) ⊆ subN (.imp (.down (.imp Q' N')) N) := by
  intro x hx
  rw [subN_imp]
  refine List.mem_cons_of_mem _ ?_
  refine List.mem_append.mpr (Or.inr ?_)
  rw [subD_dyk]; exact hx

/-- Each branch of an inverted positive lies in the positive's closure. -/
theorem invert_sub : ∀ (P : Pos), ∀ b ∈ invertPos P, ∀ M ∈ b, subN M ⊆ subP P
  | .atom a, b, hb, M, hM => by
      simp only [invertPos, List.mem_singleton] at hb; subst hb
      rcases List.mem_singleton.mp hM with rfl
      exact subN_up_sub (.atom a)
  | .fls, b, hb, _, _ => by simp [invertPos] at hb
  | .or P₁ P₂, b, hb, M, hM => by
      simp only [invertPos, List.mem_append] at hb
      rcases hb with hb | hb
      · exact fun x hx => subP_or_left P₁ P₂ (invert_sub P₁ b hb M hM hx)
      · exact fun x hx => subP_or_right P₁ P₂ (invert_sub P₂ b hb M hM hx)
  | .down M₀, b, hb, M, hM => by
      simp only [invertPos, List.mem_singleton] at hb; subst hb
      rcases List.mem_singleton.mp hM with rfl
      exact subN_sub_subP_down _
termination_by P => sizePos P
decreasing_by all_goals (simp only [sizePos]; omega)

/-! ## Lists of formulas -/

theorem mem_subL {M : Neg} {l : List Neg} (h : M ∈ l) : subN M ⊆ subL l := by
  intro x hx
  exact List.mem_flatMap.mpr ⟨M, h, hx⟩

theorem subL_mono {l₁ l₂ : List Neg} (h : l₁ ⊆ l₂) : subL l₁ ⊆ subL l₂ := by
  intro x hx
  obtain ⟨M, hM, hxM⟩ := List.mem_flatMap.mp hx
  exact List.mem_flatMap.mpr ⟨M, h hM, hxM⟩

theorem subL_cons (M : Neg) (l : List Neg) : subL (M :: l) = subN M ++ subL l := by
  simp [subL, List.flatMap_cons]

theorem subL_append (l₁ l₂ : List Neg) : subL (l₁ ++ l₂) = subL l₁ ++ subL l₂ := by
  simp [subL, List.flatMap_append]

theorem self_mem_subN (M : Neg) : M ∈ subN M := by
  cases M with
  | up P => simp [subN_up]
  | circ P => simp [subN_circ]
  | and M₁ M₂ => simp [subN_and]
  | imp Q N => simp [subN_imp]

theorem mem_subL_self {M : Neg} {l : List Neg} (h : M ∈ l) : M ∈ subL l :=
  mem_subL h (self_mem_subN M)

/-- The rest of a positional split is a sublist. -/
theorem splits_rest {Γ : List Neg} :
    ∀ {X rest}, (X, rest) ∈ splits Γ → rest ⊆ Γ := by
  induction Γ with
  | nil => intro X rest h; simp [splits] at h
  | cons Y Γ ih =>
      intro X rest h
      simp only [splits, List.mem_cons, List.mem_map] at h
      rcases h with h | ⟨⟨Z, rest'⟩, hZ, hEq⟩
      · cases h; exact fun x hx => List.mem_cons_of_mem _ hx
      · cases hEq
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih hZ hx)

/-! # Part 3 · The maximum weight, and `W` -/

theorem mxW_ge {M : Neg} : ∀ {l : List Neg}, M ∈ l → wNeg M ≤ mxW l := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons X l ih =>
      intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem mxW_le {b : Nat} : ∀ {l : List Neg}, (∀ M ∈ l, wNeg M ≤ b) → mxW l ≤ b := by
  intro l
  induction l with
  | nil => intro _; simp [mxW]
  | cons X l ih =>
      intro h
      simp only [mxW, Nat.max_le]
      exact ⟨h X (List.mem_cons_self ..), ih (fun M hM => h M (List.mem_cons_of_mem _ hM))⟩

theorem mxW_mono {l₁ l₂ : List Neg} (h : l₁ ⊆ l₂) : mxW l₁ ≤ mxW l₂ :=
  mxW_le (fun M hM => mxW_ge (h hM))

theorem bigW_mono {s t : QState} (h : clSt t ⊆ clSt s) : bigW t ≤ bigW s := by
  simp only [bigW]
  exact p3_mono (by have := mxW_mono h; omega)

/-- **`W` dominates every antecedent of the closure**: the guard row's goal
weight is strictly below `W`, which is what pays for the guard edge. -/
theorem pow_ant_lt_bigW {s : QState} {Q' : Pos} {N : Neg}
    (h : Neg.imp Q' N ∈ clSt s) : 3 ^ wPos Q' < bigW s := by
  have hw : wNeg (Neg.imp Q' N) ≤ mxW (clSt s) := mxW_ge h
  simp only [wNeg] at hw
  simp only [bigW]
  exact p3_strict (by omega)

/-! # Part 4 · The guard deficiency `κ` -/

theorem mem_caOf {Q : Pos} : ∀ {l : List Neg}, Q ∈ caOf l ↔ ∃ N, Neg.imp Q N ∈ l := by
  intro l
  induction l with
  | nil => simp [caOf]
  | cons X l ih =>
      match X with
      | .imp Q₀ N₀ =>
          simp only [caOf, List.mem_cons]
          constructor
          · rintro (rfl | h)
            · exact ⟨N₀, Or.inl rfl⟩
            · obtain ⟨N, hN⟩ := ih.mp h; exact ⟨N, Or.inr hN⟩
          · rintro ⟨N, h | h⟩
            · cases h; exact Or.inl rfl
            · exact Or.inr (ih.mpr ⟨N, h⟩)
      | .up _ | .and _ _ | .circ _ =>
          simp only [caOf]
          constructor
          · intro h; obtain ⟨N, hN⟩ := ih.mp h; exact ⟨N, List.mem_cons_of_mem _ hN⟩
          · rintro ⟨N, h⟩
            rcases List.mem_cons.mp h with h | h
            · cases h
            · exact ih.mpr ⟨N, h⟩

theorem caOf_mono {l₁ l₂ : List Neg} (h : l₁ ⊆ l₂) : caOf l₁ ⊆ caOf l₂ := by
  intro Q hQ
  obtain ⟨N, hN⟩ := mem_caOf.mp hQ
  exact mem_caOf.mpr ⟨N, h hN⟩

theorem ddup_nil : ddup [] = [] := rfl

theorem ddup_cons (Q : Pos) (l : List Pos) :
    ddup (Q :: l) = if seenMem (ddup l) Q then ddup l else Q :: ddup l := rfl

theorem mem_ddup {Q : Pos} : ∀ {l : List Pos}, Q ∈ ddup l ↔ Q ∈ l := by
  intro l
  induction l with
  | nil => simp [ddup_nil]
  | cons R l ih =>
      rw [ddup_cons]
      by_cases hm : seenMem (ddup l) R = true
      · rw [if_pos hm, ih, List.mem_cons]
        constructor
        · exact Or.inr
        · rintro (rfl | h)
          · exact ih.mp ((seenMem_iff _ _).mp hm)
          · exact h
      · rw [if_neg hm, List.mem_cons, List.mem_cons, ih]

theorem nodup_ddup : ∀ (l : List Pos), (ddup l).Nodup := by
  intro l
  induction l with
  | nil => simp [ddup_nil]
  | cons R l ih =>
      rw [ddup_cons]
      by_cases hm : seenMem (ddup l) R = true
      · rw [if_pos hm]; exact ih
      · rw [if_neg hm]
        refine List.nodup_cons.mpr ⟨?_, ih⟩
        intro h
        exact hm ((seenMem_iff _ _).mpr h)

/-- Removal of one occurrence, by hand: `List.erase`'s lemmas go through
`Classical.propDecidable` (`List.erase_eq_eraseP`), and this layer must stay
choice-free. -/
def rmv (Q : Pos) : List Pos → List Pos
  | [] => []
  | R :: l => if R = Q then l else R :: rmv Q l

theorem rmv_cons (Q R : Pos) (l : List Pos) :
    rmv Q (R :: l) = if R = Q then l else R :: rmv Q l := rfl

theorem length_rmv : ∀ {l : List Pos} {Q : Pos}, Q ∈ l →
    (rmv Q l).length + 1 = l.length := by
  intro l
  induction l with
  | nil => intro Q h; simp at h
  | cons R l ih =>
      intro Q h
      rw [rmv_cons]
      by_cases hr : R = Q
      · rw [if_pos hr]; simp
      · rw [if_neg hr]
        rcases List.mem_cons.mp h with rfl | h
        · exact absurd rfl hr
        · simp only [List.length_cons]
          have := ih h
          omega

theorem mem_rmv : ∀ {l : List Pos} {Q x : Pos}, x ∈ l → x ≠ Q → x ∈ rmv Q l := by
  intro l
  induction l with
  | nil => intro Q x h _; simp at h
  | cons R l ih =>
      intro Q x h hne
      rw [rmv_cons]
      by_cases hr : R = Q
      · rw [if_pos hr]
        rcases List.mem_cons.mp h with rfl | h
        · exact absurd hr hne
        · exact h
      · rw [if_neg hr]
        rcases List.mem_cons.mp h with rfl | h
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih h hne)

/-- Nodup lists inject into their supersets. -/
theorem nodup_length_le : ∀ {l₁ l₂ : List Pos}, l₁.Nodup → l₁ ⊆ l₂ →
    l₁.length ≤ l₂.length := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _ _; simp
  | cons Q l ih =>
      intro l₂ hnd hsub
      have hQ : Q ∈ l₂ := hsub (List.mem_cons_self ..)
      have hQl : Q ∉ l := (List.nodup_cons.mp hnd).1
      have hsub' : l ⊆ rmv Q l₂ := by
        intro x hx
        exact mem_rmv (hsub (List.mem_cons_of_mem _ hx)) (by rintro rfl; exact hQl hx)
      have h1 := ih (List.nodup_cons.mp hnd).2 hsub'
      have h2 := length_rmv hQ
      simp only [List.length_cons]
      omega

theorem mem_caFree {s : QState} {Q : Pos} :
    Q ∈ caFree s ↔ Q ∈ caOf (clSt s) ∧ Q ∉ s.2.2.2 := by
  simp only [caFree, List.mem_filter, Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, (not_seenMem_iff _ _).mp h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (not_seenMem_iff _ _).mpr h2⟩

/-- **`κ` is monotone** along an edge that carries `seen` and does not grow
the closure. -/
theorem kap_le {s t : QState} (hcl : clSt t ⊆ clSt s) (hseen : t.2.2.2 = s.2.2.2) :
    kap t ≤ kap s := by
  refine nodup_length_le (nodup_ddup _) ?_
  intro Q hQ
  have hQ' := mem_caFree.mp (mem_ddup.mp hQ)
  refine mem_ddup.mpr (mem_caFree.mpr ⟨caOf_mono hcl hQ'.1, ?_⟩)
  rw [← hseen]; exact hQ'.2

/-- **`κ` strictly drops** along a guard edge: the antecedent recorded is in
the closure and was not in `seen`. -/
theorem kap_lt {s t : QState} {Q' : Pos} (hcl : clSt t ⊆ clSt s)
    (hseen : t.2.2.2 = Q' :: s.2.2.2) (hmem : Q' ∈ caOf (clSt s))
    (hnew : Q' ∉ s.2.2.2) : kap t + 1 ≤ kap s := by
  have hsub : ddup (caFree t) ⊆ ddup (caFree s) := by
    intro Q hQ
    have hQ' := mem_caFree.mp (mem_ddup.mp hQ)
    refine mem_ddup.mpr (mem_caFree.mpr ⟨caOf_mono hcl hQ'.1, ?_⟩)
    intro hc
    exact hQ'.2 (by rw [hseen]; exact List.mem_cons_of_mem _ hc)
  have hQ'notin : Q' ∉ ddup (caFree t) := by
    intro hc
    have := (mem_caFree.mp (mem_ddup.mp hc)).2
    exact this (by rw [hseen]; exact List.mem_cons_self ..)
  have hQ'in : Q' ∈ ddup (caFree s) :=
    mem_ddup.mpr (mem_caFree.mpr ⟨hmem, hnew⟩)
  have hnd : (Q' :: ddup (caFree t)).Nodup :=
    List.nodup_cons.mpr ⟨hQ'notin, nodup_ddup _⟩
  have hs : (Q' :: ddup (caFree t)) ⊆ ddup (caFree s) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hQ'in
    · exact hsub hx
  have hlen := nodup_length_le hnd hs
  rw [List.length_cons] at hlen
  exact hlen

/-! # Part 5 · The two descent lemmas -/

/-- **An ordinary edge**: the closure does not grow, `seen` is carried, and
`ν` strictly drops. -/
theorem qMu_lt_of_ordinary {s t : QState} (hcl : clSt t ⊆ clSt s)
    (hseen : t.2.2.2 = s.2.2.2) (hnu : nu t < nu s) : qMu t < qMu s := by
  have hk : kap t ≤ kap s := kap_le hcl hseen
  have hw : bigW t ≤ bigW s := bigW_mono hcl
  have : kap t * bigW t ≤ kap s * bigW s :=
    Nat.le_trans (Nat.mul_le_mul_left _ hw) (Nat.mul_le_mul_right _ hk)
  simp only [qMu]; omega

/-- **A guard edge**: the closure does not grow, `seen` gains an antecedent
of the closure that was not in it, and `ν` stays below `ν s + W s`. -/
theorem qMu_lt_of_guard {s t : QState} {Q' : Pos} (hcl : clSt t ⊆ clSt s)
    (hseen : t.2.2.2 = Q' :: s.2.2.2) (hmem : Q' ∈ caOf (clSt s))
    (hnew : Q' ∉ s.2.2.2) (hnu : nu t < nu s + bigW s) : qMu t < qMu s := by
  have hk : kap t + 1 ≤ kap s := kap_lt hcl hseen hmem hnew
  have hw : bigW t ≤ bigW s := bigW_mono hcl
  have h1 : kap t * bigW t ≤ kap t * bigW s := Nat.mul_le_mul_left _ hw
  have h2 : (kap t + 1) * bigW s ≤ kap s * bigW s := Nat.mul_le_mul_right _ hk
  have h3 : (kap t + 1) * bigW s = kap t * bigW s + bigW s := by ring
  simp only [qMu]
  omega

end LJFO

/-! ## Pins -/

#axioms_within LJFO.seenMem_iff [propext, Quot.sound]
#axioms_within LJFO.invert_sub [propext, Quot.sound]
#axioms_within LJFO.subN_dyk_sub [propext, Quot.sound]
#axioms_within LJFO.nodup_length_le [propext, Quot.sound]
#axioms_within LJFO.kap_le [propext, Quot.sound]
#axioms_within LJFO.kap_lt [propext, Quot.sound]
#axioms_within LJFO.bigW_mono [propext, Quot.sound]
#axioms_within LJFO.pow_ant_lt_bigW [propext, Quot.sound]
#axioms_within LJFO.qMu_lt_of_ordinary [propext, Quot.sound]
#axioms_within LJFO.qMu_lt_of_guard [propext, Quot.sound]
