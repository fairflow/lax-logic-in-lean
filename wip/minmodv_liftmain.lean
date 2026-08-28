/-
# The hloc-lift, stages 3–4: the lifted recursion and `completenessV_lift`

`minModL` extends the assembly's `minModF` to models WITHOUT the
world-wise `◯`-free hypothesis `hloc`.  Three witness grades:

    g = 0    irregular   `IrrWitV`
    g = 1    TAGGED      `RegWitV`   (tOK — feeds `◯∈`/`◯∉`)
    g ≥ 2    FREE        `FreeWitV`  (any tag — everything else)

The per-case story (docs/next-session.md, HANDOFF §2026-08-28c):

  * free prime/or at a circ-carrying world: the fallible joins
    (stage 1) — blocked tag, modal zone kept unconditionally;
  * tagged prime/or at a circ-carrying world: cone-refuted goals take
    the PLEDGED promise joins (stage 2 — family = tagged rows at the
    proper `Rm`-successors, which the circ-carrier guarantees exist);
    the one case neither serves — refuted at the world but forced at
    some proper `Rm`-successor — is the named interface `TagLeafV`,
    VACUOUS under `hloc` (so `completenessV` is re-derived below as a
    supersession gate);
  * every `◯Z`-goal, regular grade: `circRegWit` (the round-1 brick) —
    re-anchor `minZeta ∘ maxRmAbove`, one barren `⋈^◯`, no `Z`-row;
  * the irregular `(0, ◯Z)`-cell: `minZeta` gives a cone-refuting
    anchor `e ≥ a`; when `e ≠ a` (or a proper `Rm`-walk exists) the
    tagged `Z`-row is built at strictly lower height and `◯∉` closes;
    when `a` is itself cone-trivial, the assembly's corner machinery
    serves in place, its floats at strictly lower height.

The measure is the assembly's `(ht, grade, size)` — the §9 wall stays
dodged because no case recurses tag-upward at fixed world.
-/
import wip.minmodv_assembly
import wip.minmodv_port
import wip.minmodv_lift

namespace FRJ

open Form

/-! ## Height antitonicity (for the re-anchored floats) -/

theorem ht_le {K : Kripke} {a b : K.W} (hab : K.le a b) :
    ht K b ≤ ht K a := by
  refine List.countP_mono_left (fun c _ hc => ?_)
  simp only [decide_eq_true_eq] at hc ⊢
  refine ⟨K.le_trans hab hc.1, fun hca => ?_⟩
  subst hca
  exact hc.2 (K.le_antisymm hab hc.1)

theorem ht_lt_of_le {K : Kripke} {a b e : K.W} (hab : K.le a b)
    (hbe : K.le b e) (hne : e ≠ b) : ht K e < ht K a :=
  Nat.lt_of_lt_of_le (ht_lt hbe hne) (ht_le hab)

/-! ## The interface: the one un-served tagged leaf -/

/-- A tagged prime/or witness at a circ-carrying world where the goal
is refuted but NOT cone-refuted (some proper `Rm`-successor forces it).
Everything else in the lifted recursion is constructed; this is the
named residual — VACUOUS under `hloc`. -/
def TagLeafV (K : Kripke) (G : Form) : Type :=
  ∀ (w : K.W) (C : Form), C ∈ sfR G → ¬ K.force w C →
    (C.isPrime = true ∨ ∃ C₁ C₂, C = Form.or C₁ C₂) →
    circPart (lamStar K w G) ≠ [] →
    (∃ c, K.Rm w c ∧ c ≠ w ∧ K.force c C) →
    RegWitV K G w C

/-- `hloc` makes the interface vacuous. -/
def tagLeafV_of_hloc {K : Kripke} {G : Form}
    (hloc : ∀ b : K.W, circPart (lamStar K b G) = []) : TagLeafV K G :=
  fun w _ _ _ _ hcirc _ => absurd (hloc w) hcirc

/-- A circ-carrying world has a proper `Rm`-successor: the carried
`◯Y`'s own forcing supplies the witness. -/
theorem properSucc_ne_of_circ {K : Kripke} {G : Form} {w : K.W}
    (hcirc : circPart (lamStar K w G) ≠ []) : properSucc K w ≠ [] := by
  match hm : circPart (lamStar K w G) with
  | [] => exact absurd hm hcirc
  | X :: _ =>
      have hX : X ∈ circPart (lamStar K w G) := hm ▸ List.mem_cons_self
      obtain ⟨hXl, hXc⟩ := List.mem_filter.mp hX
      match X, hXc with
      | .circ Y, _ =>
          obtain ⟨-, hstar⟩ := mem_lamStar.mp hXl
          obtain ⟨c, hrc, hcY⟩ := hstar.1 w (K.le_refl w)
          have hcne : c ≠ w := fun h => hstar.2 (h ▸ hcY)
          intro hnil
          exact absurd (hnil ▸ mem_properSucc.mpr ⟨hrc, hcne⟩)
            List.not_mem_nil

/-! ## The graded statement -/

def MinModStmtL (K : Kripke) (G : Form) (a : K.W) (g : Nat) (C : Form) :
    Type :=
  match g with
  | 0 => IrrWitV K G a C
  | 1 => RegWitV K G a C
  | _ + 2 => FreeWitV K G a C

/-! ## The lifted recursion -/

def minModL (K : Kripke) (G : Form)
    (hinf : K.Infallible) (tl : TagLeafV K G)
    (a : K.W) (g : Nat) (C : Form)
    (hC : C ∈ sfR G) (hnf : ¬ K.force a C) : MinModStmtL K G a g C := by
  match g, C with
  | 0, .circ Z =>
      let mz := minZeta hnf
      by_cases hea : mz.e = a
      · let mr := maxRmAbove K a
        by_cases hma : mr.m = a
        · -- `a` cone-trivial with its own cone refuting `Z`: the corner
          have hcone : K.ConeTrivial a := hma ▸ mr.cone
          exact cornerIrrWit
            (mkCornerCtx
              (fun A B hsf hnfY hnA =>
                let m := minEta hnfY
                have hea' : ¬(m.e = a) := fun h => hnA (h ▸ m.fA)
                let w := minModL K G hinf tl m.e 2 B (sfR_imp hsf).2 m.nfB
                have hthg : thGoodAt K G a
                    ((gHat G).filter (fun X =>
                      cloB w.ctx X && decide (K.force a X))) := by
                  intro X hX hfX
                  refine List.mem_filter.mpr ⟨hX, ?_⟩
                  have hclo : Clo w.ctx X := clo_mono w.cov
                    (mem_clo_lamStar (hinf _) (gHat_subset_sfL hX)
                      (K.force_mono (K.le_trans m.le w.wle) hfX))
                  simp [cloB_iff.mpr hclo, hfX]
                ⟨⟨⟨[], (gHat G).filter (fun X =>
                      cloB w.ctx X && decide (K.force a X)), .imp A B,
                    .impNotIn w.der
                      (fun X hX => ⟨cloB_iff.mp
                          (Bool.and_elim_left ((List.mem_filter.mp hX).2)),
                        (List.mem_filter.mp hX).1⟩)
                      (clo_mono w.cov (mem_clo_lamStar (hinf _)
                        (sfR_imp hsf).1 (K.force_mono w.wle m.fA)))
                      (fun hc => hnA (clo_forces
                        (fun X hX => of_decide_eq_true
                          (Bool.and_elim_right ((List.mem_filter.mp hX).2)))
                        hc))
                      hsf⟩,
                  rfl, hthg⟩, rfl⟩)
              hC hnf)
            hcone (hinf a)
            (fun A B hsf hnfY hnA =>
              let m := minEta hnfY
              have hea' : ¬(m.e = a) := fun h => hnA (h ▸ m.fA)
              let w := minModL K G hinf tl m.e 1 B (sfR_imp hsf).2 m.nfB
              have hAclo : Clo w.ctx A := clo_mono w.cov
                (mem_clo_lamStar (hinf _) (sfR_imp hsf).1
                  (K.force_mono w.wle m.fA))
              { ctx := w.ctx, t := w.t
                der := .impIn w.der hAclo hsf
                tOK := tOK_lift w.tOK (fun hc => .imp hc hAclo)
                covF := fun X hXs hfX => clo_mono w.cov
                  (mem_clo_lamStar (hinf _) hXs
                    (K.force_mono (K.le_trans m.le w.wle) hfX)) })
            hC hnf
        · -- walk `Rm`-up to the cone-trivial `mr.m ≠ a`: tagged row there
          have hnfZ : ¬ K.force mr.m Z := (hea ▸ mz.cone) mr.m mr.rm
          let w := minModL K G hinf tl mr.m 1 Z (sfR_circ hC) hnfZ
          exact { stab := [], th := lamStar K a G
                  der := .circNotIn w.der w.tOK
                    (fun X hX => ⟨clo_mono w.cov (lamStar_mono (hinf _)
                        (K.le_trans (K.sub_mi mr.rm) w.wle) X hX),
                      lamStar_subset_gHat hX⟩) hC
                  sub := fun _ h => absurd h List.not_mem_nil
                  cov := fun _ hx => hx }
      · -- the anchor is strictly above: tagged row at `mz.e`
        have hnfZ : ¬ K.force mz.e Z := mz.cone mz.e (K.rm_refl mz.e)
        let w := minModL K G hinf tl mz.e 1 Z (sfR_circ hC) hnfZ
        exact { stab := [], th := lamStar K a G
                der := .circNotIn w.der w.tOK
                  (fun X hX => ⟨clo_mono w.cov (lamStar_mono (hinf _)
                      (K.le_trans mz.le w.wle) X hX),
                    lamStar_subset_gHat hX⟩) hC
                sub := fun _ h => absurd h List.not_mem_nil
                cov := fun _ hx => hx }
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
        let w := minModL K G hinf tl a 0 C₂ hC2 h2
        exact { stab := w.stab, th := w.th, der := .andI2 w.der hC
                sub := w.sub, cov := w.cov }
      · let w := minModL K G hinf tl a 0 C₁ hC1 h1
        exact { stab := w.stab, th := w.th, der := .andI1 w.der hC
                sub := w.sub, cov := w.cov }
  | 0, .or C₁ C₂ =>
      obtain ⟨hC1, hC2⟩ := sfR_or hC
      have h1 : ¬ K.force a C₁ := fun hc => hnf (Or.inl hc)
      have h2 : ¬ K.force a C₂ := fun hc => hnf (Or.inr hc)
      let w₁ := minModL K G hinf tl a 0 C₁ hC1 h1
      let w₂ := minModL K G hinf tl a 0 C₂ hC2 h2
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
        let w := minModL K G hinf tl a 0 B hB heB
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
        let w := minModL K G hinf tl m.e 2 B hB m.nfB
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
  | 1, .atom p =>
      by_cases hcirc : circPart (lamStar K a G) = []
      · by_cases hempty : impPart (lamStar K a G) = []
        · exact regPrimeV_ax K G a (.atom p) hcirc rfl hC hnf hempty
        · refine regPrimeV_join K G a (.atom p) hcirc rfl hC hnf ?_
            (fun A hA hnA => minModL K G hinf tl a 0 A hA hnA)
          intro hc
          refine hempty (eq_nil_of_forall_not_mem (fun X hX => ?_))
          obtain ⟨hXl, hXi⟩ := List.mem_filter.mp hX
          match X, hXi with
          | .imp A B, _ =>
              exact absurd (mem_upsPrime hXl) (by rw [hc]; exact List.not_mem_nil)
      · match hw : K.elems.filter (fun v => decide (K.Rm a v ∧ K.force v (.atom p))) with
        | [] =>
            have hcone : ∀ v, K.Rm a v → ¬ K.force v (.atom p) := by
              intro v hrv hfv
              have hmem : v ∈ K.elems.filter
                  (fun v => decide (K.Rm a v ∧ K.force v (.atom p))) :=
                List.mem_filter.mpr ⟨K.complete v, by simp [hrv, hfv]⟩
              rw [hw] at hmem
              exact absurd hmem List.not_mem_nil
            exact tagPrimeP_join K G hinf a (.atom p) rfl hC hcone
              (properSucc_ne_of_circ hcirc)
              (fun A hA hnA => minModL K G hinf tl a 0 A hA hnA)
              (fun c hrm hne => minModL K G hinf tl c 1 (.atom p) hC
                (hcone c hrm))
        | c :: _ =>
            have hcmem : c ∈ K.elems.filter
                (fun v => decide (K.Rm a v ∧ K.force v (.atom p))) := by
              rw [hw]; exact List.mem_cons_self
            have hcspec : K.Rm a c ∧ K.force c (.atom p) := by
              have := (List.mem_filter.mp hcmem).2
              simpa using this
            exact tl a (.atom p) hC hnf (Or.inl rfl) hcirc
              ⟨c, hcspec.1, fun h => hnf (h ▸ hcspec.2), hcspec.2⟩
  | 1, .bot =>
      by_cases hcirc : circPart (lamStar K a G) = []
      · by_cases hempty : impPart (lamStar K a G) = []
        · exact regPrimeV_ax K G a .bot hcirc rfl hC hnf hempty
        · refine regPrimeV_join K G a .bot hcirc rfl hC hnf ?_
            (fun A hA hnA => minModL K G hinf tl a 0 A hA hnA)
          intro hc
          refine hempty (eq_nil_of_forall_not_mem (fun X hX => ?_))
          obtain ⟨hXl, hXi⟩ := List.mem_filter.mp hX
          match X, hXi with
          | .imp A B, _ =>
              exact absurd (mem_upsPrime hXl) (by rw [hc]; exact List.not_mem_nil)
      · match hw : K.elems.filter (fun v => decide (K.Rm a v ∧ K.force v .bot)) with
        | [] =>
            have hcone : ∀ v, K.Rm a v → ¬ K.force v .bot := by
              intro v hrv hfv
              have hmem : v ∈ K.elems.filter
                  (fun v => decide (K.Rm a v ∧ K.force v .bot)) :=
                List.mem_filter.mpr ⟨K.complete v, by simp [hrv, hfv]⟩
              rw [hw] at hmem
              exact absurd hmem List.not_mem_nil
            exact tagPrimeP_join K G hinf a .bot rfl hC hcone
              (properSucc_ne_of_circ hcirc)
              (fun A hA hnA => minModL K G hinf tl a 0 A hA hnA)
              (fun c hrm hne => minModL K G hinf tl c 1 .bot hC
                (hcone c hrm))
        | c :: _ =>
            have hcmem : c ∈ K.elems.filter
                (fun v => decide (K.Rm a v ∧ K.force v .bot)) := by
              rw [hw]; exact List.mem_cons_self
            have hcspec : K.Rm a c ∧ K.force c .bot := by
              have := (List.mem_filter.mp hcmem).2
              simpa using this
            exact tl a .bot hC hnf (Or.inl rfl) hcirc
              ⟨c, hcspec.1, fun h => hnf (h ▸ hcspec.2), hcspec.2⟩
  | 1, .or C₁ C₂ =>
      by_cases hcirc : circPart (lamStar K a G) = []
      · exact regOrV_join K G a C₁ C₂ hcirc hC hnf
          (fun A hA hnA => minModL K G hinf tl a 0 A hA hnA)
      · match hw : K.elems.filter (fun v => decide (K.Rm a v ∧ K.force v (.or C₁ C₂))) with
        | [] =>
            have hcone : ∀ v, K.Rm a v → ¬ K.force v (.or C₁ C₂) := by
              intro v hrv hfv
              have hmem : v ∈ K.elems.filter
                  (fun v => decide (K.Rm a v ∧ K.force v (.or C₁ C₂))) :=
                List.mem_filter.mpr ⟨K.complete v, by simp [hrv, hfv]⟩
              rw [hw] at hmem
              exact absurd hmem List.not_mem_nil
            exact tagOrP_join K G hinf a C₁ C₂ hC hcone
              (properSucc_ne_of_circ hcirc)
              (fun A hA hnA => minModL K G hinf tl a 0 A hA hnA)
              (fun c hrm hne => minModL K G hinf tl c 1 (.or C₁ C₂) hC
                (hcone c hrm))
        | c :: _ =>
            have hcmem : c ∈ K.elems.filter
                (fun v => decide (K.Rm a v ∧ K.force v (.or C₁ C₂))) := by
              rw [hw]; exact List.mem_cons_self
            have hcspec : K.Rm a c ∧ K.force c (.or C₁ C₂) := by
              have := (List.mem_filter.mp hcmem).2
              simpa using this
            exact tl a (.or C₁ C₂) hC hnf (Or.inr ⟨C₁, C₂, rfl⟩) hcirc
              ⟨c, hcspec.1, fun h => hnf (h ▸ hcspec.2), hcspec.2⟩
  | 1, .circ Z =>
      exact circRegWit K G hinf hC hnf
        (fun b hab A B hsf hnfY hnA =>
          let m := minEta hnfY
          have hea' : ¬(m.e = b) := fun h => hnA (h ▸ m.fA)
          let w := minModL K G hinf tl m.e 2 B (sfR_imp hsf).2 m.nfB
          have hthg : thGoodAt K G b
              ((gHat G).filter (fun X =>
                cloB w.ctx X && decide (K.force b X))) := by
            intro X hX hfX
            refine List.mem_filter.mpr ⟨hX, ?_⟩
            have hclo : Clo w.ctx X := clo_mono w.cov
              (mem_clo_lamStar (hinf _) (gHat_subset_sfL hX)
                (K.force_mono (K.le_trans m.le w.wle) hfX))
            simp [cloB_iff.mpr hclo, hfX]
          ⟨⟨⟨[], (gHat G).filter (fun X =>
                cloB w.ctx X && decide (K.force b X)), .imp A B,
              .impNotIn w.der
                (fun X hX => ⟨cloB_iff.mp
                    (Bool.and_elim_left ((List.mem_filter.mp hX).2)),
                  (List.mem_filter.mp hX).1⟩)
                (clo_mono w.cov (mem_clo_lamStar (hinf _)
                  (sfR_imp hsf).1 (K.force_mono w.wle m.fA)))
                (fun hc => hnA (clo_forces
                  (fun X hX => of_decide_eq_true
                    (Bool.and_elim_right ((List.mem_filter.mp hX).2)))
                  hc))
                hsf⟩,
            rfl, hthg⟩, rfl⟩)
  | 1, .and C₁ C₂ =>
      obtain ⟨hC1, hC2⟩ := sfR_and hC
      by_cases h1 : K.force a C₁
      · have h2 : ¬ K.force a C₂ := fun hc => hnf ⟨h1, hc⟩
        let w := minModL K G hinf tl a 1 C₂ hC2 h2
        exact { ctx := w.ctx, t := w.t, der := .andR2 w.der hC
                tOK := tOK_lift w.tOK (fun hc => .andR hc)
                wld := w.wld, wle := w.wle, cov := w.cov }
      · let w := minModL K G hinf tl a 1 C₁ hC1 h1
        exact { ctx := w.ctx, t := w.t, der := .andR1 w.der hC
                tOK := tOK_lift w.tOK (fun hc => .andL hc)
                wld := w.wld, wle := w.wle, cov := w.cov }
  | 1, .imp A B =>
      obtain ⟨hA, hB⟩ := sfR_imp hC
      let m := minEta hnf
      by_cases hea : m.e = a
      · have heA : K.force a A := hea ▸ m.fA
        have heB : ¬ K.force a B := hea ▸ m.nfB
        let w := minModL K G hinf tl a 1 B hB heB
        have hAclo : Clo w.ctx A := clo_mono w.cov
          (mem_clo_lamStar (hinf _) hA (K.force_mono w.wle heA))
        exact { ctx := w.ctx, t := w.t
                der := .impIn w.der hAclo hC
                tOK := tOK_lift w.tOK (fun hc => .imp hc hAclo)
                wld := w.wld, wle := w.wle, cov := w.cov }
      · let w := minModL K G hinf tl m.e 1 B hB m.nfB
        have hAclo : Clo w.ctx A := clo_mono w.cov
          (mem_clo_lamStar (hinf _) hA (K.force_mono w.wle m.fA))
        exact { ctx := w.ctx, t := w.t
                der := .impIn w.der hAclo hC
                tOK := tOK_lift w.tOK (fun hc => .imp hc hAclo)
                wld := w.wld, wle := K.le_trans m.le w.wle, cov := w.cov }
  | (n+2), .atom p =>
      by_cases hcirc : circPart (lamStar K a G) = []
      · by_cases hempty : impPart (lamStar K a G) = []
        · exact (regPrimeV_ax K G a (.atom p) hcirc rfl hC hnf hempty).toFree
        · refine (regPrimeV_join K G a (.atom p) hcirc rfl hC hnf ?_
            (fun A hA hnA => minModL K G hinf tl a 0 A hA hnA)).toFree
          intro hc
          refine hempty (eq_nil_of_forall_not_mem (fun X hX => ?_))
          obtain ⟨hXl, hXi⟩ := List.mem_filter.mp hX
          match X, hXi with
          | .imp A B, _ =>
              exact absurd (mem_upsPrime hXl) (by rw [hc]; exact List.not_mem_nil)
      · exact regPrimeF_join K G a (.atom p) rfl hC hnf
          (fun A hA hnA => minModL K G hinf tl a 0 A hA hnA)
  | (n+2), .bot =>
      by_cases hcirc : circPart (lamStar K a G) = []
      · by_cases hempty : impPart (lamStar K a G) = []
        · exact (regPrimeV_ax K G a .bot hcirc rfl hC hnf hempty).toFree
        · refine (regPrimeV_join K G a .bot hcirc rfl hC hnf ?_
            (fun A hA hnA => minModL K G hinf tl a 0 A hA hnA)).toFree
          intro hc
          refine hempty (eq_nil_of_forall_not_mem (fun X hX => ?_))
          obtain ⟨hXl, hXi⟩ := List.mem_filter.mp hX
          match X, hXi with
          | .imp A B, _ =>
              exact absurd (mem_upsPrime hXl) (by rw [hc]; exact List.not_mem_nil)
      · exact regPrimeF_join K G a .bot rfl hC hnf
          (fun A hA hnA => minModL K G hinf tl a 0 A hA hnA)
  | (n+2), .or C₁ C₂ =>
      exact regOrF_join K G a C₁ C₂ hC hnf
        (fun A hA hnA => minModL K G hinf tl a 0 A hA hnA)
  | (n+2), .circ Z =>
      exact (circRegWit K G hinf hC hnf
        (fun b hab A B hsf hnfY hnA =>
          let m := minEta hnfY
          have hea' : ¬(m.e = b) := fun h => hnA (h ▸ m.fA)
          let w := minModL K G hinf tl m.e 2 B (sfR_imp hsf).2 m.nfB
          have hthg : thGoodAt K G b
              ((gHat G).filter (fun X =>
                cloB w.ctx X && decide (K.force b X))) := by
            intro X hX hfX
            refine List.mem_filter.mpr ⟨hX, ?_⟩
            have hclo : Clo w.ctx X := clo_mono w.cov
              (mem_clo_lamStar (hinf _) (gHat_subset_sfL hX)
                (K.force_mono (K.le_trans m.le w.wle) hfX))
            simp [cloB_iff.mpr hclo, hfX]
          ⟨⟨⟨[], (gHat G).filter (fun X =>
                cloB w.ctx X && decide (K.force b X)), .imp A B,
              .impNotIn w.der
                (fun X hX => ⟨cloB_iff.mp
                    (Bool.and_elim_left ((List.mem_filter.mp hX).2)),
                  (List.mem_filter.mp hX).1⟩)
                (clo_mono w.cov (mem_clo_lamStar (hinf _)
                  (sfR_imp hsf).1 (K.force_mono w.wle m.fA)))
                (fun hc => hnA (clo_forces
                  (fun X hX => of_decide_eq_true
                    (Bool.and_elim_right ((List.mem_filter.mp hX).2)))
                  hc))
                hsf⟩,
            rfl, hthg⟩, rfl⟩)).toFree
  | (n+2), .and C₁ C₂ =>
      obtain ⟨hC1, hC2⟩ := sfR_and hC
      by_cases h1 : K.force a C₁
      · have h2 : ¬ K.force a C₂ := fun hc => hnf ⟨h1, hc⟩
        let w := minModL K G hinf tl a (n+2) C₂ hC2 h2
        exact { ctx := w.ctx, t := w.t, der := .andR2 w.der hC
                wld := w.wld, wle := w.wle, cov := w.cov }
      · let w := minModL K G hinf tl a (n+2) C₁ hC1 h1
        exact { ctx := w.ctx, t := w.t, der := .andR1 w.der hC
                wld := w.wld, wle := w.wle, cov := w.cov }
  | (n+2), .imp A B =>
      obtain ⟨hA, hB⟩ := sfR_imp hC
      let m := minEta hnf
      by_cases hea : m.e = a
      · have heA : K.force a A := hea ▸ m.fA
        have heB : ¬ K.force a B := hea ▸ m.nfB
        let w := minModL K G hinf tl a (n+2) B hB heB
        have hAclo : Clo w.ctx A := clo_mono w.cov
          (mem_clo_lamStar (hinf _) hA (K.force_mono w.wle heA))
        exact { ctx := w.ctx, t := w.t
                der := .impIn w.der hAclo hC
                wld := w.wld, wle := w.wle, cov := w.cov }
      · let w := minModL K G hinf tl m.e 2 B hB m.nfB
        have hAclo : Clo w.ctx A := clo_mono w.cov
          (mem_clo_lamStar (hinf _) hA (K.force_mono w.wle m.fA))
        exact { ctx := w.ctx, t := w.t
                der := .impIn w.der hAclo hC
                wld := w.wld, wle := K.le_trans m.le w.wle, cov := w.cov }
termination_by (ht K a, g, C.size)
decreasing_by
  all_goals
    first
      | (apply Prod.Lex.left
         exact ht_lt m.le hea')
      | (apply Prod.Lex.left
         exact ht_lt m.le hea)
      | (apply Prod.Lex.left
         exact ht_lt (K.sub_mi mr.rm) hma)
      | (apply Prod.Lex.left
         exact ht_lt mz.le hea)
      | (apply Prod.Lex.left
         exact ht_lt (K.sub_mi hrm) hne)
      | (apply Prod.Lex.left
         exact ht_lt_of_le hab m.le hea')
      | (apply Prod.Lex.right
         apply Prod.Lex.left
         omega)
      | (apply Prod.Lex.right
         apply Prod.Lex.right
         first
           | omega
           | (simp only [Form.size]; omega))

/-! ## The lifted campaign statement -/

/-- **FRJV completeness with `hloc` LIFTED to the named interface**:
every infallible countermodel yields an FRJV derivation, provided the
tagged prime/or leaves at circ-carrying worlds that are NOT
cone-refuted are supplied.  Under `hloc` the interface is vacuous. -/
theorem completenessV_lift {G : Form} (K : Kripke)
    (tl : TagLeafV K G) (hinf : K.Infallible)
    (hK : ¬ K.valid G) : ProvableV G :=
  let w := minModL K G hinf tl K.root 2 G (sfR_self G) hK
  ⟨w.t, w.ctx, ⟨w.der⟩⟩

/-- The supersession gate: `completenessV` re-derived through the lift. -/
theorem completenessV_of_hloc {G : Form} (K : Kripke)
    (hloc : ∀ b : K.W, circPart (lamStar K b G) = [])
    (hinf : K.Infallible)
    (hK : ¬ K.valid G) : ProvableV G :=
  completenessV_lift K (tagLeafV_of_hloc hloc) hinf hK

/-- info: 'FRJ.minModL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms minModL

/-- info: 'FRJ.completenessV_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completenessV_lift

end FRJ
