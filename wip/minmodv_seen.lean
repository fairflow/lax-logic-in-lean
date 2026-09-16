/-
# The seen-parametrised recursion: supply-free FRJV completeness on ALL frames,
# for goals whose left-implication antecedents are hereditarily ◯-free

The ◯-delta round 3.  Round 1 took the corner (the irregular `◯Z`-demand
at a world every proper extension of which forces `Z`) as the supply
`CircSupplyV`; round 2 discharged it on cone-grounded frames only.  This
file implements the seen-mechanism (frj-w4 §11 second addendum): the
corner PUSHES `◯Z` into a `seen`-list and recurses into the regular
`Z`-row at the SAME world under the measure

    (ht a, |sfRd G| − |seen|, t, |C|)

— the push drops the budget coordinate, floats reset `seen` under a
height drop, and all other edges leave it unchanged.

What the design pass found (recorded here because it delimits the
theorem): the pushed recursion can RE-demand `I(◯Z)` — the
self-referential flight case — but ONLY through `upsPrime`, i.e. through
an antecedent position of a `Λ*`-implication.  So the syntactic guard

    hguard : ∀ A B, (A ⊃ B) ∈ Sf^L(G) → ∀ X ∈ sf A, X is not ◯

makes the flight branch UNREACHABLE: the invariant
`hCseen : ∀ Y, ◯Y ∈ seen → ◯Y ∉ sf C` survives every edge (descents
shrink `sf C`; `upsPrime`-goals are ◯-free by the guard; floats reset),
and at `C = ◯Z` it contradicts `◯Z ∈ seen` outright.  The result:

    completenessV_of_circAnteFree :
      hguard → hloc → K.Infallible → ¬ K.valid G → ProvableV G

— NO supply, NO frame condition: the first FRJV completeness statement
conditioned on the GOAL rather than the frame.  It covers the residue
instance of `wip/minmodv_residue.lean` (whose corner is cone-trivial and
non-maximal, out of round 2's reach) with the supply gone.

Beyond the guard (the remaining kernel, for the record): at a flight
corner the row under construction needs `(◯Z ⊃ W) ∈ Λ*_a` retained;
the kept chain does this from `Z ∈ Υ` (an `I(Z)`-premise, legal at
`t`-drop) via `RefAt.circ` — but a Υ-member with an `a`-FORCED
antecedent forces a fat (`⊃∈ⁱ`) premise whose stabilised zone re-demands
antecedents in Υ LITERALLY (strict hJ2), and `(◯Z ⊃ W)` stable would
re-demand `I(◯Z)`.  The candidate closures are: a support-restricted
Lemma 6.5 (thin the fat cells to `sf`-support), or calculus round 3
(relax hJ2 to `RefAt` like the kept zone — its soundness obligation is
the same `refAt_refutes` vacuity the kept clause already uses).  Neither
is needed under the guard.
-/
import wip.minmodv

namespace FRJ

open Form

/-! ## Small subformula lemmas -/

-- (the `sf_sub_*` lemmas live in `FRJ/RefAt.lean` since 2026-08-27)

/-- `◯Z` is no subformula of `Z` (sizes). -/
theorem circ_not_mem_sf_self (Z : Form) : Form.circ Z ∉ sf Z := by
  intro h
  have := size_le_of_mem_sf h
  simp only [Form.size] at this
  omega

-- (`length_le_of_nodup_subset` lives in `FRJ/RefAt.lean` since 2026-08-28)

/-- The budget universe: the right subformulas.  (No dedup: the
subperm length bound needs only the SEEN list to be Nodup, and
`List.mem_dedup` is choice-tainted.) -/
def sfRd (G : Form) : List Form := sfR G

/-- The antecedent source of an `upsPrime`-member. -/
theorem upsPrime_src {K : Kripke} {a : K.W} {G A : Form}
    (h : A ∈ upsPrime K a G) : ∃ B, Form.imp A B ∈ lamStar K a G := by
  obtain ⟨X, hX, hante⟩ := List.mem_map.mp h
  obtain ⟨hXl, hXimp⟩ := List.mem_filter.mp hX
  match X, hXimp with
  | .imp A' B, _ => exact ⟨B, by rw [show A = A' from hante.symm ▸ rfl]; exact hXl⟩

/-! ## The join helpers, with `upsPrime`-typed induction hypotheses

Identical to round 1's except that `ih` receives the MEMBERSHIP rather
than the derived facts — the caller needs the provenance to establish
the `seen`-invariant for the sub-goal. -/

def regPrimeS_join (K : Kripke) (G : Form) (a : K.W) (C : Form)
    (hloc : circPart (lamStar K a G) = [])
    (hCp : C.isPrime) (hC : C ∈ sfR G) (hnf : ¬ K.force a C)
    (hne : upsPrime K a G ≠ [])
    (ih : ∀ A, A ∈ upsPrime K a G → IrrWitV K G a A) :
    RegWitV K G a C :=
  let E := enumOf (upsPrime K a G) hne
  let f := E.f
  let hfmem : ∀ j, f j ∈ upsPrime K a G := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  let wit : ∀ j, IrrWitV K G a (f j) := fun j => ih (f j) (hfmem j)
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

def regOrS_join (K : Kripke) (G : Form) (a : K.W) (C₁ C₂ : Form)
    (hloc : circPart (lamStar K a G) = [])
    (hC : Form.or C₁ C₂ ∈ sfR G) (_hnf : ¬ K.force a (.or C₁ C₂))
    (ihU : ∀ A, A ∈ upsPrime K a G → IrrWitV K G a A)
    (ih1 : IrrWitV K G a C₁) (ih2 : IrrWitV K G a C₂) :
    RegWitV K G a (.or C₁ C₂) :=
  let U := C₁ :: C₂ :: upsPrime K a G
  let E := enumOf U (by simp [U])
  let f := E.f
  let hfmem : ∀ j, f j ∈ U := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  let wit : ∀ j, IrrWitV K G a (f j) := fun j =>
    if h1 : f j = C₁ then h1 ▸ ih1
    else if h2 : f j = C₂ then h2 ▸ ih2
    else
      have hm : f j ∈ upsPrime K a G := by
        rcases List.mem_cons.mp (hfmem j) with h | h
        · exact absurd h h1
        · rcases List.mem_cons.mp h with h' | h'
          · exact absurd h' h2
          · exact h'
      ihU (f j) hm
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

/-! ## The recursion -/

def minModS (K : Kripke) (G : Form)
    (hguard : ∀ A B, Form.imp A B ∈ sfL G → ∀ X ∈ sf A, X.isCirc = false)
    (hloc : ∀ b : K.W, circPart (lamStar K b G) = [])
    (hinf : K.Infallible)
    (a : K.W) (seen : List Form) (t : Nat) (C : Form)
    (hC : C ∈ sfR G) (hnf : ¬ K.force a C)
    (hnd : seen.Nodup) (hsub : seen ⊆ sfRd G)
    (hCseen : ∀ Y, Form.circ Y ∈ seen → Form.circ Y ∉ sf C) :
    MinModStmtV K G a t C := by
  match t, C with
  | 0, .circ Z =>
      have hnfZ : ¬ K.force a Z := fun hZ => hnf (force_circ_of_force hZ)
      by_cases hin : Form.circ Z ∈ seen
      · -- the FLIGHT case: unreachable under the invariant
        exact absurd (self_mem_sf _) (hCseen Z hin)
      · match hcand : K.elems.filter
            (fun u => decide (K.le a u ∧ u ≠ a ∧ ¬ K.force u Z)) with
        | u :: _ =>
            -- float: a proper extension refutes `Z`; `seen` resets
            have hu : u ∈ K.elems.filter
                (fun u => decide (K.le a u ∧ u ≠ a ∧ ¬ K.force u Z)) := by
              rw [hcand]; exact List.mem_cons_self
            have hspec : K.le a u ∧ u ≠ a ∧ ¬ K.force u Z := by
              have := (List.mem_filter.mp hu).2
              simpa using this
            let w := minModS K G hguard hloc hinf u [] 1 Z (sfR_circ hC)
              hspec.2.2 List.nodup_nil (fun _ h => absurd h List.not_mem_nil)
              (fun _ h => absurd h List.not_mem_nil)
            exact { stab := [], th := lamStar K a G
                    der := .circNotIn w.der w.tOK
                      (fun X hX => ⟨clo_mono w.cov (lamStar_mono (hinf _)
                          (K.le_trans hspec.1 w.wle) X hX),
                        lamStar_subset_gHat hX⟩) hC
                    sub := fun _ h => absurd h List.not_mem_nil
                    cov := fun _ hx => hx }
        | [] =>
            -- THE CORNER: push `◯Z` and build the row at `a`
            have hlen : (Form.circ Z :: seen).length ≤ (sfRd G).length :=
              length_le_of_nodup_subset (List.nodup_cons.mpr ⟨hin, hnd⟩)
                (fun x hx => by
                  rcases List.mem_cons.mp hx with rfl | hx'
                  · exact hC
                  · exact hsub hx')
            let w := minModS K G hguard hloc hinf a (Form.circ Z :: seen) 1 Z
              (sfR_circ hC) hnfZ
              (List.nodup_cons.mpr ⟨hin, hnd⟩)
              (fun x hx => by
                rcases List.mem_cons.mp hx with rfl | hx'
                · exact hC
                · exact hsub hx')
              (fun Y hY => by
                rcases List.mem_cons.mp hY with hY' | hY'
                · have : Y = Z := by injection hY'
                  subst this
                  exact circ_not_mem_sf_self Y
                · exact fun hc => hCseen Y hY' (sf_sub_circ hc))
            exact { stab := [], th := lamStar K a G
                    der := .circNotIn w.der w.tOK
                      (fun X hX => ⟨clo_mono w.cov (lamStar_mono (hinf _)
                          w.wle X hX),
                        lamStar_subset_gHat hX⟩) hC
                    sub := fun _ h => absurd h List.not_mem_nil
                    cov := fun _ hx => hx }
  | (n+1), .circ Z =>
      have hnfZ : ¬ K.force a Z := fun hZ => hnf (force_circ_of_force hZ)
      let w := minModS K G hguard hloc hinf a seen (n+1) Z (sfR_circ hC) hnfZ
        hnd hsub (fun Y hY hc => hCseen Y hY (sf_sub_circ hc))
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
        let w := minModS K G hguard hloc hinf a seen 0 C₂ hC2 h2 hnd hsub
          (fun Y hY hc => hCseen Y hY (sf_sub_and₂ hc))
        exact { stab := w.stab, th := w.th, der := .andI2 w.der hC
                sub := w.sub, cov := w.cov }
      · let w := minModS K G hguard hloc hinf a seen 0 C₁ hC1 h1 hnd hsub
          (fun Y hY hc => hCseen Y hY (sf_sub_and₁ hc))
        exact { stab := w.stab, th := w.th, der := .andI1 w.der hC
                sub := w.sub, cov := w.cov }
  | 0, .or C₁ C₂ =>
      obtain ⟨hC1, hC2⟩ := sfR_or hC
      have h1 : ¬ K.force a C₁ := fun hc => hnf (Or.inl hc)
      have h2 : ¬ K.force a C₂ := fun hc => hnf (Or.inr hc)
      let w₁ := minModS K G hguard hloc hinf a seen 0 C₁ hC1 h1 hnd hsub
        (fun Y hY hc => hCseen Y hY (sf_sub_or₁ hc))
      let w₂ := minModS K G hguard hloc hinf a seen 0 C₂ hC2 h2 hnd hsub
        (fun Y hY hc => hCseen Y hY (sf_sub_or₂ hc))
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
        let w := minModS K G hguard hloc hinf a seen 0 B hB heB hnd hsub
          (fun Y hY hc => hCseen Y hY (sf_sub_imp₂ hc))
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
        let w := minModS K G hguard hloc hinf m.e [] 1 B hB m.nfB
          List.nodup_nil (fun _ h => absurd h List.not_mem_nil)
          (fun _ h => absurd h List.not_mem_nil)
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
      · refine regPrimeS_join K G a (.atom p) (hloc a) rfl hC hnf ?_
          (fun A hA' =>
            minModS K G hguard hloc hinf a seen 0 A
              (upsPrime_spec hA').1 (upsPrime_spec hA').2 hnd hsub
              (fun Y hY hc => by
                obtain ⟨B, hAB⟩ := upsPrime_src hA'
                have := hguard A B (mem_lamStar.mp hAB).1 _ hc
                simp [Form.isCirc] at this))
        intro hc
        refine hempty (eq_nil_of_forall_not_mem (fun X hX => ?_))
        obtain ⟨hXl, hXi⟩ := List.mem_filter.mp hX
        match X, hXi with
        | .imp A B, _ =>
            exact absurd (mem_upsPrime hXl) (by rw [hc]; exact List.not_mem_nil)
  | (n+1), .bot =>
      by_cases hempty : impPart (lamStar K a G) = []
      · exact regPrimeV_ax K G a .bot (hloc a) rfl hC hnf hempty
      · refine regPrimeS_join K G a .bot (hloc a) rfl hC hnf ?_
          (fun A hA' =>
            minModS K G hguard hloc hinf a seen 0 A
              (upsPrime_spec hA').1 (upsPrime_spec hA').2 hnd hsub
              (fun Y hY hc => by
                obtain ⟨B, hAB⟩ := upsPrime_src hA'
                have := hguard A B (mem_lamStar.mp hAB).1 _ hc
                simp [Form.isCirc] at this))
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
        let w := minModS K G hguard hloc hinf a seen (n+1) C₂ hC2 h2 hnd hsub
          (fun Y hY hc => hCseen Y hY (sf_sub_and₂ hc))
        exact { ctx := w.ctx, t := w.t, der := .andR2 w.der hC
                tOK := tOK_lift w.tOK (fun hc => .andR hc)
                wld := w.wld, wle := w.wle, cov := w.cov }
      · let w := minModS K G hguard hloc hinf a seen (n+1) C₁ hC1 h1 hnd hsub
          (fun Y hY hc => hCseen Y hY (sf_sub_and₁ hc))
        exact { ctx := w.ctx, t := w.t, der := .andR1 w.der hC
                tOK := tOK_lift w.tOK (fun hc => .andL hc)
                wld := w.wld, wle := w.wle, cov := w.cov }
  | (n+1), .or C₁ C₂ =>
      obtain ⟨hC1, hC2⟩ := sfR_or hC
      have h1 : ¬ K.force a C₁ := fun hc => hnf (Or.inl hc)
      have h2 : ¬ K.force a C₂ := fun hc => hnf (Or.inr hc)
      exact regOrS_join K G a C₁ C₂ (hloc a) hC hnf
        (fun A hA' =>
          minModS K G hguard hloc hinf a seen 0 A
            (upsPrime_spec hA').1 (upsPrime_spec hA').2 hnd hsub
            (fun Y hY hc => by
              obtain ⟨B, hAB⟩ := upsPrime_src hA'
              have := hguard A B (mem_lamStar.mp hAB).1 _ hc
              simp [Form.isCirc] at this))
        (minModS K G hguard hloc hinf a seen 0 C₁ hC1 h1 hnd hsub
          (fun Y hY hc => hCseen Y hY (sf_sub_or₁ hc)))
        (minModS K G hguard hloc hinf a seen 0 C₂ hC2 h2 hnd hsub
          (fun Y hY hc => hCseen Y hY (sf_sub_or₂ hc)))
  | (n+1), .imp A B =>
      obtain ⟨hA, hB⟩ := sfR_imp hC
      let m := minEta hnf
      by_cases hea : m.e = a
      · have heA : K.force a A := hea ▸ m.fA
        have heB : ¬ K.force a B := hea ▸ m.nfB
        let w := minModS K G hguard hloc hinf a seen (n+1) B hB heB hnd hsub
          (fun Y hY hc => hCseen Y hY (sf_sub_imp₂ hc))
        have hAclo : Clo w.ctx A := clo_mono w.cov
          (mem_clo_lamStar (hinf _) hA (K.force_mono w.wle heA))
        exact { ctx := w.ctx, t := w.t
                der := .impIn w.der hAclo hC
                tOK := tOK_lift w.tOK (fun hc => .imp hc hAclo)
                wld := w.wld, wle := w.wle, cov := w.cov }
      · let w := minModS K G hguard hloc hinf m.e [] 1 B hB m.nfB
          List.nodup_nil (fun _ h => absurd h List.not_mem_nil)
          (fun _ h => absurd h List.not_mem_nil)
        have hAclo : Clo w.ctx A := clo_mono w.cov
          (mem_clo_lamStar (hinf _) hA (K.force_mono w.wle m.fA))
        exact { ctx := w.ctx, t := w.t
                der := .impIn w.der hAclo hC
                tOK := tOK_lift w.tOK (fun hc => .imp hc hAclo)
                wld := w.wld, wle := K.le_trans m.le w.wle, cov := w.cov }
termination_by (ht K a, (sfRd G).length - seen.length, t, C.size)
decreasing_by
  all_goals
    first
      | (apply Prod.Lex.left
         exact ht_lt m.le hea)
      | (apply Prod.Lex.left
         exact ht_lt hspec.1 hspec.2.1)
      | (apply Prod.Lex.right
         apply Prod.Lex.left
         simp only [List.length_cons] at hlen ⊢
         omega)
      | (apply Prod.Lex.right
         apply Prod.Lex.right
         apply Prod.Lex.left
         omega)
      | (apply Prod.Lex.right
         apply Prod.Lex.right
         apply Prod.Lex.right
         first
           | omega
           | (simp only [Form.size]; omega))

/-! ## The theorem -/

/-- **Supply-free FRJV completeness on ALL frames, for guarded goals**:
if no left-implication antecedent of `G` contains a `◯`, then every
infallible countermodel with world-wise `◯`-free `Λ*` yields an FRJV
derivation — no frame condition, no supply. -/
theorem completenessV_of_circAnteFree {G : Form} (K : Kripke)
    (hguard : ∀ A B, Form.imp A B ∈ sfL G → ∀ X ∈ sf A, X.isCirc = false)
    (hloc : ∀ b : K.W, circPart (lamStar K b G) = [])
    (hinf : K.Infallible)
    (hK : ¬ K.valid G) : ProvableV G :=
  let w := minModS K G hguard hloc hinf K.root [] 1 G (sfR_self G) hK
    List.nodup_nil (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil)
  ⟨w.t, w.ctx, ⟨w.der⟩⟩

/-- The guard, decidably: every left implication's antecedent is
hereditarily `◯`-free. -/
def guardB (G : Form) : Bool :=
  (sfL G).all (fun M => match M with
    | .imp A _ => (sf A).all (fun X => !X.isCirc)
    | _ => true)

theorem guard_of_guardB {G : Form} (h : guardB G = true) :
    ∀ A B, Form.imp A B ∈ sfL G → ∀ X ∈ sf A, X.isCirc = false := by
  intro A B hAB X hX
  have h1 := List.all_eq_true.mp h _ hAB
  have h2 : (sf A).all (fun X => !X.isCirc) = true := h1
  have h3 := List.all_eq_true.mp h2 _ hX
  simpa using h3

/-- info: 'FRJ.minModS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms minModS

/-- info: 'FRJ.completenessV_of_circAnteFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completenessV_of_circAnteFree

end FRJ
