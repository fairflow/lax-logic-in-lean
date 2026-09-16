/-
BiLax round 1 — the labelled sequent calculus `BiLaxL`.

Cut-free by design (no cut rule anywhere), in the Negri style with the
Pinto–Uustalu system as template [LITERATURE — VERIFY: docs/bilax-plan.md
§6.2].  Sequents carry a label graph: relational atoms `x ≤ y`
(`.ri`), `x Rm y` (`.rm`), the fallibility predicate `F x` (`.fal`),
and the auxiliary `.cw v u` ("every Rm-successor of v is ≤ u", the
inner ∀ of the counit law, split geometrically into `counit1`/
`counit2`).  Labelled formulas come in two sorts: `.fm A` (A forced
here) and the auxiliary `.dm A` ("some Rm-successor forces A", the
inner ∃ of the `◯∀` clause).

Every frame law of `BiModel` is a geometric rule; fallibility is
first-class syntax (`falForward` is fragment-relative exfalso).
Soundness (`biLaxL_sound`) is proved here and pinned in
BiLax/Soundness.lean's companion audit below.  Completeness via
saturation-with-countermodel-extraction is round 2
(docs/bilax-plan.md §7.1); cut/contraction admissibility is the
§6.2(ii) obligation.
-/
import BiLax.Soundness

namespace BiLax

abbrev Label := Nat

/-- Relational atoms of the label graph. -/
inductive LAtom where
  | ri : Label → Label → LAtom
  | rm : Label → Label → LAtom
  | rc : Label → Label → LAtom
  | fal : Label → LAtom
  | cw : Label → Label → LAtom
deriving DecidableEq, Repr

/-- Labelled formula sorts: `fm A` = "A here", `dm A` = "some
Rm-successor forces A". -/
inductive LForm where
  | fm : BiForm → LForm
  | dm : BiForm → LForm
deriving DecidableEq, Repr

/-- Labelled sequents. -/
structure LSeq where
  rels : List LAtom
  left : List (Label × LForm)
  right : List (Label × LForm)

namespace LSeq

def addRel (S : LSeq) (a : LAtom) : LSeq := { S with rels := a :: S.rels }
def addLeft (S : LSeq) (x : Label) (A : LForm) : LSeq :=
  { S with left := (x, A) :: S.left }
def addRight (S : LSeq) (x : Label) (A : LForm) : LSeq :=
  { S with right := (x, A) :: S.right }

def atomLabels : LAtom → List Label
  | .ri x y => [x, y]
  | .rm x y => [x, y]
  | .rc x y => [x, y]
  | .fal x => [x]
  | .cw x y => [x, y]

def labels (S : LSeq) : List Label :=
  S.rels.flatMap atomLabels ++ S.left.map (·.1) ++ S.right.map (·.1)

/-- `y` occurs nowhere in `S`. -/
def Fresh (y : Label) (S : LSeq) : Prop := y ∉ S.labels

theorem Fresh.rel {S : LSeq} {y : Label} (hf : Fresh y S)
    {a : LAtom} (ha : a ∈ S.rels) : ∀ z ∈ atomLabels a, z ≠ y := by
  intro z hz rfl
  exact hf (List.mem_append.mpr (.inl (List.mem_append.mpr
    (.inl (List.mem_flatMap.mpr ⟨a, ha, hz⟩)))))

theorem Fresh.left {S : LSeq} {y : Label} (hf : Fresh y S)
    {p : Label × LForm} (hp : p ∈ S.left) : p.1 ≠ y := by
  intro h
  exact hf (List.mem_append.mpr (.inl (List.mem_append.mpr
    (.inr (List.mem_map.mpr ⟨p, hp, h⟩)))))

theorem Fresh.right {S : LSeq} {y : Label} (hf : Fresh y S)
    {p : Label × LForm} (hp : p ∈ S.right) : p.1 ≠ y := by
  intro h
  exact hf (List.mem_append.mpr (.inr (List.mem_map.mpr ⟨p, hp, h⟩)))

end LSeq

/-- Satisfaction of a relational atom. -/
def ratom (M : BiModel) (ρ : Label → M.W) : LAtom → Prop
  | .ri x y => M.Ri (ρ x) (ρ y)
  | .rm x y => M.Rm (ρ x) (ρ y)
  | .rc x y => M.Rc (ρ x) (ρ y)
  | .fal x => ρ x ∈ M.F
  | .cw x y => ∀ u, M.Rm (ρ x) u → M.Ri u (ρ y)

/-- Satisfaction of a labelled formula at a world. -/
def lforce (M : BiModel) (w : M.W) : LForm → Prop
  | .fm A => bforce M w A
  | .dm A => ∃ u, M.Rm w u ∧ bforce M u A

theorem ratom_ext {M : BiModel} {ρ ρ' : Label → M.W} {a : LAtom}
    (h : ∀ z ∈ LSeq.atomLabels a, ρ z = ρ' z) :
    ratom M ρ a ↔ ratom M ρ' a := by
  cases a with
  | ri x y =>
      simp only [ratom]
      rw [show ρ x = ρ' x from h x (by simp [LSeq.atomLabels]),
          show ρ y = ρ' y from h y (by simp [LSeq.atomLabels])]
  | rm x y =>
      simp only [ratom]
      rw [show ρ x = ρ' x from h x (by simp [LSeq.atomLabels]),
          show ρ y = ρ' y from h y (by simp [LSeq.atomLabels])]
  | rc x y =>
      simp only [ratom]
      rw [show ρ x = ρ' x from h x (by simp [LSeq.atomLabels]),
          show ρ y = ρ' y from h y (by simp [LSeq.atomLabels])]
  | fal x =>
      simp only [ratom]
      rw [show ρ x = ρ' x from h x (by simp [LSeq.atomLabels])]
  | cw x y =>
      simp only [ratom]
      rw [show ρ x = ρ' x from h x (by simp [LSeq.atomLabels]),
          show ρ y = ρ' y from h y (by simp [LSeq.atomLabels])]

/-- Validity of a labelled sequent. -/
def LSeq.Valid (S : LSeq) : Prop :=
  ∀ (M : BiModel) (ρ : Label → M.W),
    (∀ a ∈ S.rels, ratom M ρ a) →
    (∀ p ∈ S.left, lforce M (ρ p.1) p.2) →
    ∃ p ∈ S.right, lforce M (ρ p.1) p.2

open LSeq in
/-- **The labelled calculus** (no cut rule). -/
inductive BiLaxL : LSeq → Type
  -- identity and ⊥
  | init {S x A} (h1 : (x, A) ∈ S.left) (h2 : (x, A) ∈ S.right) : BiLaxL S
  | botR {S x} (h1 : LAtom.fal x ∈ S.rels)
      (h2 : (x, LForm.fm .bot) ∈ S.right) : BiLaxL S
  | botL {S x} (h : (x, LForm.fm .bot) ∈ S.left)
      (p : BiLaxL (S.addRel (.fal x))) : BiLaxL S
  | falForward {S x A} (h : LAtom.fal x ∈ S.rels) (hA : IsForward A)
      (p : BiLaxL (S.addLeft x (.fm A))) : BiLaxL S
  | monoLe {S x y A} (hrel : LAtom.ri x y ∈ S.rels)
      (h : (x, LForm.fm A) ∈ S.left)
      (p : BiLaxL (S.addLeft y (.fm A))) : BiLaxL S
  -- the label graph: geometric rules for the frame laws
  | riRefl {S} (x : Label) (p : BiLaxL (S.addRel (.ri x x))) : BiLaxL S
  | riTrans {S x y z} (h1 : LAtom.ri x y ∈ S.rels)
      (h2 : LAtom.ri y z ∈ S.rels)
      (p : BiLaxL (S.addRel (.ri x z))) : BiLaxL S
  | rmRefl {S} (x : Label) (p : BiLaxL (S.addRel (.rm x x))) : BiLaxL S
  | rmTrans {S x y z} (h1 : LAtom.rm x y ∈ S.rels)
      (h2 : LAtom.rm y z ∈ S.rels)
      (p : BiLaxL (S.addRel (.rm x z))) : BiLaxL S
  | subMi {S x y} (h : LAtom.rm x y ∈ S.rels)
      (p : BiLaxL (S.addRel (.ri x y))) : BiLaxL S
  | falHered {S x y} (h1 : LAtom.fal x ∈ S.rels)
      (h2 : LAtom.ri x y ∈ S.rels)
      (p : BiLaxL (S.addRel (.fal y))) : BiLaxL S
  | squareR {S w x v} (w' : Label) (h1 : LAtom.rc w x ∈ S.rels)
      (h2 : LAtom.ri x v ∈ S.rels) (hf : Fresh w' S)
      (p : BiLaxL ((S.addRel (.ri w w')).addRel (.rc w' v))) : BiLaxL S
  | serialC {S} (v : Label) (u : Label) (hne : v ≠ u) (hf : Fresh u S)
      (p : BiLaxL ((S.addRel (.rm v u)).addRel (.rc v u))) : BiLaxL S
  | counit1 {S w u} (v : Label) (h : LAtom.rc w u ∈ S.rels)
      (hf : Fresh v S)
      (p : BiLaxL ((S.addRel (.ri w v)).addRel (.cw v u))) : BiLaxL S
  | counit2 {S v u y} (h1 : LAtom.cw v u ∈ S.rels)
      (h2 : LAtom.rm v y ∈ S.rels)
      (p : BiLaxL (S.addRel (.ri y u))) : BiLaxL S
  -- ∧, ∨
  | andL {S x A B} (h : (x, LForm.fm (.and A B)) ∈ S.left)
      (p : BiLaxL ((S.addLeft x (.fm A)).addLeft x (.fm B))) : BiLaxL S
  | andR {S x A B} (h : (x, LForm.fm (.and A B)) ∈ S.right)
      (p1 : BiLaxL (S.addRight x (.fm A)))
      (p2 : BiLaxL (S.addRight x (.fm B))) : BiLaxL S
  | orL {S x A B} (h : (x, LForm.fm (.or A B)) ∈ S.left)
      (p1 : BiLaxL (S.addLeft x (.fm A)))
      (p2 : BiLaxL (S.addLeft x (.fm B))) : BiLaxL S
  | orR {S x A B} (h : (x, LForm.fm (.or A B)) ∈ S.right)
      (p : BiLaxL ((S.addRight x (.fm A)).addRight x (.fm B))) : BiLaxL S
  -- ⇾ (forward) and ⤙ (retrospective)
  | impL {S x y A B} (h : (x, LForm.fm (A ⇾ B)) ∈ S.left)
      (hrel : LAtom.ri x y ∈ S.rels)
      (p1 : BiLaxL (S.addRight y (.fm A)))
      (p2 : BiLaxL (S.addLeft y (.fm B))) : BiLaxL S
  | impR {S x A B} (y : Label) (h : (x, LForm.fm (A ⇾ B)) ∈ S.right)
      (hf : Fresh y S)
      (p : BiLaxL (((S.addRel (.ri x y)).addLeft y (.fm A)).addRight
        y (.fm B))) : BiLaxL S
  | coimpL {S x A B} (y : Label) (h : (x, LForm.fm (A ⤙ B)) ∈ S.left)
      (hf : Fresh y S)
      (p : BiLaxL (((S.addRel (.ri y x)).addLeft y (.fm A)).addRight
        y (.fm B))) : BiLaxL S
  | coimpR {S x y A B} (h : (x, LForm.fm (A ⤙ B)) ∈ S.right)
      (hrel : LAtom.ri y x ∈ S.rels)
      (p1 : BiLaxL (S.addRight y (.fm A)))
      (p2 : BiLaxL (S.addLeft y (.fm B))) : BiLaxL S
  -- ◯∀ via the auxiliary dm, ◯∃ directly
  | laxL {S x y A} (h : (x, LForm.fm (◯∀A)) ∈ S.left)
      (hrel : LAtom.ri x y ∈ S.rels)
      (p : BiLaxL (S.addLeft y (.dm A))) : BiLaxL S
  | laxR {S x A} (y : Label) (h : (x, LForm.fm (◯∀A)) ∈ S.right)
      (hf : Fresh y S)
      (p : BiLaxL ((S.addRel (.ri x y)).addRight y (.dm A))) : BiLaxL S
  | dmL {S x A} (y : Label) (h : (x, LForm.dm A) ∈ S.left)
      (hf : Fresh y S)
      (p : BiLaxL ((S.addRel (.rm x y)).addLeft y (.fm A))) : BiLaxL S
  | dmR {S x y A} (h : (x, LForm.dm A) ∈ S.right)
      (hrel : LAtom.rm x y ∈ S.rels)
      (p : BiLaxL (S.addRight y (.fm A))) : BiLaxL S
  | colaxL {S x A} (y : Label) (h : (x, LForm.fm (◯∃A)) ∈ S.left)
      (hf : Fresh y S)
      (p : BiLaxL ((S.addRel (.rc y x)).addLeft y (.fm A))) : BiLaxL S
  | colaxR {S x y A} (h : (x, LForm.fm (◯∃A)) ∈ S.right)
      (hrel : LAtom.rc y x ∈ S.rels)
      (p : BiLaxL (S.addRight y (.fm A))) : BiLaxL S

end BiLax

namespace BiLax

/-! ## Soundness -/

section Soundness

theorem sat_update_rels {M : BiModel} {S : LSeq} {y : Label} {v : M.W}
    {ρ : Label → M.W} (hf : LSeq.Fresh y S)
    (hr : ∀ a ∈ S.rels, ratom M ρ a) :
    ∀ a ∈ S.rels, ratom M (Function.update ρ y v) a := by
  intro a ha
  exact (ratom_ext (fun z hz =>
    (Function.update_of_ne (hf.rel ha z hz) v ρ).symm)).mp (hr a ha)

theorem sat_update_list {M : BiModel} {L : List (Label × LForm)}
    {y : Label} {v : M.W} {ρ : Label → M.W}
    (hne : ∀ p ∈ L, p.1 ≠ y)
    (hl : ∀ p ∈ L, lforce M (ρ p.1) p.2) :
    ∀ p ∈ L, lforce M (Function.update ρ y v p.1) p.2 := by
  intro p hp
  rw [Function.update_of_ne (hne p hp)]
  exact hl p hp

theorem sat_update_back {M : BiModel} {y : Label} {v : M.W}
    {ρ : Label → M.W} {p : Label × LForm} (hne : p.1 ≠ y)
    (h : lforce M (Function.update ρ y v p.1) p.2) :
    lforce M (ρ p.1) p.2 := by
  rwa [Function.update_of_ne hne] at h

/-- Premise-lift for `addRel`. -/
theorem valid_addRel {S : LSeq} {a : LAtom}
    (hp : (S.addRel a).Valid)
    (hj : ∀ (M : BiModel) (ρ : Label → M.W),
      (∀ b ∈ S.rels, ratom M ρ b) →
      (∀ q ∈ S.left, lforce M (ρ q.1) q.2) → ratom M ρ a) :
    S.Valid := by
  intro M ρ hr hl
  refine hp M ρ ?_ hl
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact hj M ρ hr hl
  · exact hr b hb

/-- Premise-lift for `addLeft`. -/
theorem valid_addLeft {S : LSeq} {x : Label} {A : LForm}
    (hp : (S.addLeft x A).Valid)
    (hj : ∀ (M : BiModel) (ρ : Label → M.W),
      (∀ b ∈ S.rels, ratom M ρ b) →
      (∀ q ∈ S.left, lforce M (ρ q.1) q.2) → lforce M (ρ x) A) :
    S.Valid := by
  intro M ρ hr hl
  refine hp M ρ hr ?_
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hj M ρ hr hl
  · exact hl q hq

/-- **Soundness of the labelled calculus.** -/
theorem biLaxL_sound {S : LSeq} (p : BiLaxL S) : S.Valid := by
  induction p with
  | init h1 h2 => exact fun M ρ hr hl => ⟨_, h2, hl _ h1⟩
  | botR h1 h2 => exact fun M ρ hr hl => ⟨_, h2, hr _ h1⟩
  | botL h _ ih => exact valid_addRel ih (fun M ρ hr hl => hl _ h)
  | falForward h hA _ ih =>
      exact valid_addLeft ih
        (fun M ρ hr hl => bforce_of_fallible_forward M hA (hr _ h))
  | monoLe hrel h _ ih =>
      exact valid_addLeft ih
        (fun M ρ hr hl => bforce_hered M (hr _ hrel) (hl _ h))
  | riRefl x _ ih =>
      exact valid_addRel ih (fun M ρ _ _ => M.refl_i (ρ x))
  | riTrans h1 h2 _ ih =>
      exact valid_addRel ih
        (fun M ρ hr _ => M.trans_i (hr _ h1) (hr _ h2))
  | rmRefl x _ ih =>
      exact valid_addRel ih (fun M ρ _ _ => M.refl_m (ρ x))
  | rmTrans h1 h2 _ ih =>
      exact valid_addRel ih
        (fun M ρ hr _ => M.trans_m (hr _ h1) (hr _ h2))
  | subMi h _ ih =>
      exact valid_addRel ih (fun M ρ hr _ => M.sub_mi (hr _ h))
  | falHered h1 h2 _ ih =>
      exact valid_addRel ih
        (fun M ρ hr _ => M.hered_F (hr _ h2) (hr _ h1))
  | @squareR S w x v w' h1 h2 hf _ ih =>
      intro M ρ hr hl
      obtain ⟨c, hwc, hcv⟩ := M.square_c (hr _ h1) (hr _ h2)
      have hwne : w ≠ w' := hf.rel h1 w (by simp [LSeq.atomLabels])
      have hvne : v ≠ w' := hf.rel h2 v (by simp [LSeq.atomLabels])
      obtain ⟨q, hq, hfq⟩ := ih M (Function.update ρ w' c)
        (by
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · show M.Rc (Function.update ρ w' c w')
              (Function.update ρ w' c v)
            rw [Function.update_self, Function.update_of_ne hvne]
            exact hcv
          rcases List.mem_cons.mp hb with rfl | hb
          · show M.Ri (Function.update ρ w' c w)
              (Function.update ρ w' c w')
            rw [Function.update_self, Function.update_of_ne hwne]
            exact hwc
          · exact sat_update_rels hf hr b hb)
        (sat_update_list (fun p hp => hf.left hp) hl)
      exact ⟨q, hq, sat_update_back (hf.right hq) hfq⟩
  | @serialC S v u hvne hf _ ih =>
      intro M ρ hr hl
      obtain ⟨c, hmc, hcc⟩ := M.serial_c (ρ v)
      obtain ⟨q, hq, hfq⟩ := ih M (Function.update ρ u c)
        (by
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · show M.Rc (Function.update ρ u c v) (Function.update ρ u c u)
            rw [Function.update_self, Function.update_of_ne hvne]
            exact hcc
          rcases List.mem_cons.mp hb with rfl | hb
          · show M.Rm (Function.update ρ u c v) (Function.update ρ u c u)
            rw [Function.update_self, Function.update_of_ne hvne]
            exact hmc
          · exact sat_update_rels hf hr b hb)
        (sat_update_list (fun p hp => hf.left hp) hl)
      exact ⟨q, hq, sat_update_back (hf.right hq) hfq⟩
  | @counit1 S w u v h hf _ ih =>
      intro M ρ hr hl
      obtain ⟨t, hwt, hall⟩ := M.counit_c (hr _ h)
      have hwne : w ≠ v := hf.rel h w (by simp [LSeq.atomLabels])
      have hune : u ≠ v := hf.rel h u (by simp [LSeq.atomLabels])
      obtain ⟨q, hq, hfq⟩ := ih M (Function.update ρ v t)
        (by
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · show ∀ z, M.Rm (Function.update ρ v t v) z →
              M.Ri z (Function.update ρ v t u)
            rw [Function.update_self, Function.update_of_ne hune]
            exact hall
          rcases List.mem_cons.mp hb with rfl | hb
          · show M.Ri (Function.update ρ v t w)
              (Function.update ρ v t v)
            rw [Function.update_self, Function.update_of_ne hwne]
            exact hwt
          · exact sat_update_rels hf hr b hb)
        (sat_update_list (fun p hp => hf.left hp) hl)
      exact ⟨q, hq, sat_update_back (hf.right hq) hfq⟩
  | counit2 h1 h2 _ ih =>
      exact valid_addRel ih (fun M ρ hr _ => hr _ h1 _ (hr _ h2))
  | andL h _ ih =>
      exact valid_addLeft
        (valid_addLeft ih
          (fun M ρ hr hl =>
            (hl _ (List.mem_cons_of_mem _ h)).2))
        (fun M ρ hr hl => (hl _ h).1)
  | andR h _ _ ih1 ih2 =>
      intro M ρ hr hl
      obtain ⟨q, hq, hfq⟩ := ih1 M ρ hr hl
      rcases List.mem_cons.mp hq with rfl | hq
      · obtain ⟨q', hq', hfq'⟩ := ih2 M ρ hr hl
        rcases List.mem_cons.mp hq' with rfl | hq'
        · exact ⟨_, h, hfq, hfq'⟩
        · exact ⟨q', hq', hfq'⟩
      · exact ⟨q, hq, hfq⟩
  | orL h _ _ ih1 ih2 =>
      intro M ρ hr hl
      rcases hl _ h with hA | hB
      · refine ih1 M ρ hr ?_
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hA
        · exact hl q hq
      · refine ih2 M ρ hr ?_
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hB
        · exact hl q hq
  | orR h _ ih =>
      intro M ρ hr hl
      obtain ⟨q, hq, hfq⟩ := ih M ρ hr hl
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨_, h, .inr hfq⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨_, h, .inl hfq⟩
      · exact ⟨q, hq, hfq⟩
  | impL h hrel _ _ ih1 ih2 =>
      intro M ρ hr hl
      obtain ⟨q, hq, hfq⟩ := ih1 M ρ hr hl
      rcases List.mem_cons.mp hq with rfl | hq
      · have hB := hl _ h _ (hr _ hrel) hfq
        refine ih2 M ρ hr ?_
        intro q' hq'
        rcases List.mem_cons.mp hq' with rfl | hq'
        · exact hB
        · exact hl q' hq'
      · exact ⟨q, hq, hfq⟩
  | @impR S x A B y h hf _ ih =>
      intro M ρ hr hl
      classical
      by_contra hno
      push_neg at hno
      have hun : ¬ ∀ v, M.Ri (ρ x) v → bforce M v A → bforce M v B :=
        hno _ h
      push_neg at hun
      obtain ⟨c, hRi, hA, hnB⟩ := hun
      have hxne : x ≠ y := hf.right h
      obtain ⟨q, hq, hfq⟩ := ih M (Function.update ρ y c)
        (by
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · show M.Ri (Function.update ρ y c x)
              (Function.update ρ y c y)
            rw [Function.update_self, Function.update_of_ne hxne]
            exact hRi
          · exact sat_update_rels hf hr b hb)
        (by
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · show bforce M (Function.update ρ y c y) A
            rw [Function.update_self]
            exact hA
          · exact sat_update_list (fun p hp => hf.left hp) hl q hq)
      rcases List.mem_cons.mp hq with rfl | hq
      · rw [show Function.update ρ y c y = c from Function.update_self ..]
          at hfq
        exact hnB hfq
      · exact hno q hq (sat_update_back (hf.right hq) hfq)
  | @coimpL S x A B y h hf _ ih =>
      intro M ρ hr hl
      obtain ⟨c, hci, hA, hnB⟩ := hl _ h
      have hxne : x ≠ y := hf.left h
      obtain ⟨q, hq, hfq⟩ := ih M (Function.update ρ y c)
        (by
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · show M.Ri (Function.update ρ y c y)
              (Function.update ρ y c x)
            rw [Function.update_self, Function.update_of_ne hxne]
            exact hci
          · exact sat_update_rels hf hr b hb)
        (by
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · show bforce M (Function.update ρ y c y) A
            rw [Function.update_self]
            exact hA
          · exact sat_update_list (fun p hp => hf.left hp) hl q hq)
      rcases List.mem_cons.mp hq with rfl | hq
      · rw [show Function.update ρ y c y = c from Function.update_self ..]
          at hfq
        exact absurd hfq hnB
      · exact ⟨q, hq, sat_update_back (hf.right hq) hfq⟩
  | @coimpR S x y A B h hrel _ _ ih1 ih2 =>
      intro M ρ hr hl
      classical
      by_cases hB : bforce M (ρ y) B
      case pos =>
        refine ih2 M ρ hr ?_
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hB
        · exact hl q hq
      case neg =>
        obtain ⟨q, hq, hfq⟩ := ih1 M ρ hr hl
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨_, h, _, hr _ hrel, hfq, hB⟩
        · exact ⟨q, hq, hfq⟩
  | laxL h hrel _ ih =>
      exact valid_addLeft ih
        (fun M ρ hr hl => hl _ h _ (hr _ hrel))
  | @laxR S x A y h hf _ ih =>
      intro M ρ hr hl
      classical
      by_contra hno
      push_neg at hno
      have hun : ¬ ∀ v, M.Ri (ρ x) v →
          ∃ u, M.Rm v u ∧ bforce M u A := hno _ h
      push_neg at hun
      obtain ⟨c, hRi, hnex⟩ := hun
      have hxne : x ≠ y := hf.right h
      obtain ⟨q, hq, hfq⟩ := ih M (Function.update ρ y c)
        (by
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · show M.Ri (Function.update ρ y c x)
              (Function.update ρ y c y)
            rw [Function.update_self, Function.update_of_ne hxne]
            exact hRi
          · exact sat_update_rels hf hr b hb)
        (sat_update_list (fun p hp => hf.left hp) hl)
      rcases List.mem_cons.mp hq with rfl | hq
      · rw [show (Function.update ρ y c) y = c from Function.update_self ..]
          at hfq
        obtain ⟨u, hu, hA⟩ := hfq
        exact hnex u hu hA
      · exact hno q hq (sat_update_back (hf.right hq) hfq)
  | @dmL S x A y h hf _ ih =>
      intro M ρ hr hl
      obtain ⟨c, hc, hA⟩ := hl _ h
      have hxne : x ≠ y := hf.left h
      obtain ⟨q, hq, hfq⟩ := ih M (Function.update ρ y c)
        (by
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · show M.Rm (Function.update ρ y c x)
              (Function.update ρ y c y)
            rw [Function.update_self, Function.update_of_ne hxne]
            exact hc
          · exact sat_update_rels hf hr b hb)
        (by
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · show bforce M (Function.update ρ y c y) A
            rw [Function.update_self]
            exact hA
          · exact sat_update_list (fun p hp => hf.left hp) hl q hq)
      exact ⟨q, hq, sat_update_back (hf.right hq) hfq⟩
  | dmR h hrel _ ih =>
      intro M ρ hr hl
      obtain ⟨q, hq, hfq⟩ := ih M ρ hr hl
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨_, h, _, hr _ hrel, hfq⟩
      · exact ⟨q, hq, hfq⟩
  | @colaxL S x A y h hf _ ih =>
      intro M ρ hr hl
      obtain ⟨c, hc, hA⟩ := hl _ h
      have hxne : x ≠ y := hf.left h
      obtain ⟨q, hq, hfq⟩ := ih M (Function.update ρ y c)
        (by
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · show M.Rc (Function.update ρ y c y)
              (Function.update ρ y c x)
            rw [Function.update_self, Function.update_of_ne hxne]
            exact hc
          · exact sat_update_rels hf hr b hb)
        (by
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · show bforce M (Function.update ρ y c y) A
            rw [Function.update_self]
            exact hA
          · exact sat_update_list (fun p hp => hf.left hp) hl q hq)
      exact ⟨q, hq, sat_update_back (hf.right hq) hfq⟩
  | colaxR h hrel _ ih =>
      intro M ρ hr hl
      obtain ⟨q, hq, hfq⟩ := ih M ρ hr hl
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨_, h, _, hr _ hrel, hfq⟩
      · exact ⟨q, hq, hfq⟩

/-- The labelled sequent of an (embedded) consequence problem. -/
def LSeq.ofSeq (Γ : List BiForm) (φ : BiForm) : LSeq :=
  ⟨[], Γ.map (fun A => (0, .fm A)), [(0, .fm φ)]⟩

/-- Labelled derivations certify local consequence. -/
theorem biLaxL_sound_consequence {Γ : List BiForm} {φ : BiForm}
    (p : BiLaxL (LSeq.ofSeq Γ φ)) : BiConsequence Γ φ := by
  intro M w hΓ
  obtain ⟨q, hq, hfq⟩ := biLaxL_sound p M (fun _ => w)
    (by intro a ha; simp [LSeq.ofSeq] at ha)
    (by
      intro q hq
      simp only [LSeq.ofSeq, List.mem_map] at hq
      obtain ⟨A, hA, rfl⟩ := hq
      exact hΓ A hA)
  simp only [LSeq.ofSeq, List.mem_singleton] at hq
  subst hq
  exact hfq

end Soundness

/-! ## Pins -/

/--
info: 'BiLax.biLaxL_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms biLaxL_sound

/--
info: 'BiLax.biLaxL_sound_consequence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms biLaxL_sound_consequence

end BiLax
