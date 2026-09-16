/-
# The thirteen scan clauses of `checkClosed`

`DBClosedDG G db` (`wip/dbclosed_dg.lean`) has 21 fields.  Eight are
join clauses, quantified over irregular families; the remaining thirteen
-- `axR`, `andR1`, `andR2`, `impIn`, `circIn`, `axI`, `andI1`, `andI2`,
`orI`, `impInI`, `lift`, `circNotIn`, `axIC` -- quantify only over

  * a right subformula of `G` (enumerated by `goalPool G`),
  * a stored regular disproof (`regTs db`),
  * a stored irregular disproof (`irrTs db`),
  * a sublist of a stored zone (`impInI`) or of `Ĝ_at` (`axIC`),

each with a decidable side condition.  This file gives, for each, a
`Bool`-valued finite check `chkX` and a soundness theorem `chkX_sound`
turning `chkX G db = true` into the clause verbatim, and assembles the
thirteen into `chkScan`.

The FRJW objects stored in `db` are DISPROOFS; `WSubsumes s r.s` says
the stored disproof `r` covers the sequent `s`.
-/
import wip.dbclosed_dg

open FRJ Form FRJ.Gbu.W

namespace FRJ.Arity

/-! ## 0. Two combinators

Every clause's conclusion is `∃ r ∈ db, WSubsumes s r.s`, decided by the
stored-subsumer scan `findSub`; every clause's hypothesis is a decidable
side condition, which the check treats as a gate. -/

/-- The existential conclusion, as a check. -/
def chkOne {G : Form} (db : List (WRow G)) (s : WSeq) : Bool :=
  (findSub db s).isSome

theorem chkOne_sound {G : Form} {db : List (WRow G)} {s : WSeq}
    (h : chkOne db s = true) : ∃ r ∈ db, WSubsumes s r.s := by
  cases hf : findSub db s with
  | none => exact absurd h (by simp [chkOne, hf])
  | some r => exact ⟨r, findSub_mem hf, findSub_sub hf⟩

/-- A check guarded by a decidable side condition: cells failing the
condition are vacuously passed. -/
def gate (c : Prop) [Decidable c] (b : Bool) : Bool := if c then b else true

theorem gate_true {c : Prop} [Decidable c] {b : Bool}
    (h : gate c b = true) (hc : c) : b = true := by
  unfold gate at h
  rw [if_pos hc] at h
  exact h

/-! ## 1. The five regular clauses -/

section Regular

variable {G : Form} {db : List (WRow G)}

/-- `Ax^R`: every prime right subformula has its axiom row. -/
def chkAxR (G : Form) (db : List (WRow G)) : Bool :=
  (goalPool G).all fun F =>
    gate (F.isPrime = true) (chkOne db (.reg .barren (rm (gAt G) F) F))

theorem chkAxR_sound (h : chkAxR G db = true) :
    ∀ F : Form, F.isPrime → F ∈ sfR G →
      ∃ r ∈ db, WSubsumes (.reg .barren (rm (gAt G) F) F) r.s := by
  intro F hF hg
  exact chkOne_sound
    (gate_true (List.all_eq_true.mp h F (mem_goalPool.mpr hg)) hF)

/-- `∧R` on the left conjunct. -/
def chkAndR1 (G : Form) (db : List (WRow G)) : Bool :=
  (regTs db).all fun tr =>
    (goalPool G).all fun X =>
      match X with
      | .and A₁ A₂ =>
          gate (tr.C = A₁) (chkOne db (.reg tr.t tr.Γ (.and A₁ A₂)))
      | _ => true

theorem chkAndR1_sound (h : chkAndR1 G db = true) :
    ∀ (t : Tag) (Γ : List Form) (A₁ A₂ : Form),
      (WSeq.reg t Γ A₁) ∈ db.map (·.s) → Form.and A₁ A₂ ∈ sfR G →
      ∃ r ∈ db, WSubsumes (.reg t Γ (.and A₁ A₂)) r.s := by
  intro t Γ A₁ A₂ hmem hg
  obtain ⟨tr, htr, rfl, rfl, rfl⟩ := regTs_of_mem hmem
  have h1 := List.all_eq_true.mp h tr htr
  have h2 := List.all_eq_true.mp h1 (Form.and tr.C A₂) (mem_goalPool.mpr hg)
  exact chkOne_sound (gate_true h2 rfl)

/-- `∧R` on the right conjunct. -/
def chkAndR2 (G : Form) (db : List (WRow G)) : Bool :=
  (regTs db).all fun tr =>
    (goalPool G).all fun X =>
      match X with
      | .and A₁ A₂ =>
          gate (tr.C = A₂) (chkOne db (.reg tr.t tr.Γ (.and A₁ A₂)))
      | _ => true

theorem chkAndR2_sound (h : chkAndR2 G db = true) :
    ∀ (t : Tag) (Γ : List Form) (A₁ A₂ : Form),
      (WSeq.reg t Γ A₂) ∈ db.map (·.s) → Form.and A₁ A₂ ∈ sfR G →
      ∃ r ∈ db, WSubsumes (.reg t Γ (.and A₁ A₂)) r.s := by
  intro t Γ A₁ A₂ hmem hg
  obtain ⟨tr, htr, rfl, rfl, rfl⟩ := regTs_of_mem hmem
  have h1 := List.all_eq_true.mp h tr htr
  have h2 := List.all_eq_true.mp h1 (Form.and A₁ tr.C) (mem_goalPool.mpr hg)
  exact chkOne_sound (gate_true h2 rfl)

/-- `⊃∈`. -/
def chkImpIn (G : Form) (db : List (WRow G)) : Bool :=
  (regTs db).all fun tr =>
    (goalPool G).all fun X =>
      match X with
      | .imp A B =>
          gate (tr.C = B ∧ Clo tr.Γ A)
            (chkOne db (.reg tr.t tr.Γ (.imp A B)))
      | _ => true

theorem chkImpIn_sound (h : chkImpIn G db = true) :
    ∀ (t : Tag) (Γ : List Form) (A B : Form),
      (WSeq.reg t Γ B) ∈ db.map (·.s) → Clo Γ A → Form.imp A B ∈ sfR G →
      ∃ r ∈ db, WSubsumes (.reg t Γ (.imp A B)) r.s := by
  intro t Γ A B hmem hA hg
  obtain ⟨tr, htr, rfl, rfl, rfl⟩ := regTs_of_mem hmem
  have h1 := List.all_eq_true.mp h tr htr
  have h2 := List.all_eq_true.mp h1 (Form.imp A tr.C) (mem_goalPool.mpr hg)
  exact chkOne_sound (gate_true h2 ⟨rfl, hA⟩)

/-- `◯∈`: the pledge side condition is `decPledge`. -/
def chkCircIn (G : Form) (db : List (WRow G)) : Bool :=
  (regTs db).all fun tr =>
    (goalPool G).all fun X =>
      match X with
      | .circ Z =>
          gate (tr.C = Z ∧
              (tr.t = .barren ∨ ∃ W, tr.t = .chain W ∧ Covers tr.Γ W Z))
            (chkOne db (.reg tr.t tr.Γ (.circ Z)))
      | _ => true

theorem chkCircIn_sound (h : chkCircIn G db = true) :
    ∀ (t : Tag) (Γ : List Form) (Z : Form),
      (WSeq.reg t Γ Z) ∈ db.map (·.s) →
      (t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W Z) →
      Form.circ Z ∈ sfR G →
      ∃ r ∈ db, WSubsumes (.reg t Γ (.circ Z)) r.s := by
  intro t Γ Z hmem htag hg
  obtain ⟨tr, htr, rfl, rfl, rfl⟩ := regTs_of_mem hmem
  have h1 := List.all_eq_true.mp h tr htr
  have h2 := List.all_eq_true.mp h1 (Form.circ tr.C) (mem_goalPool.mpr hg)
  exact chkOne_sound (gate_true h2 ⟨rfl, htag⟩)

end Regular

/-! ## 2. The eight irregular clauses -/

section Irregular

variable {G : Form} {db : List (WRow G)}

/-- `Ax^I`. -/
def chkAxI (G : Form) (db : List (WRow G)) : Bool :=
  (goalPool G).all fun F =>
    gate (F.isPrime = true)
      (chkOne db (.irr [] (rm (gAt G) F ++ gImp G ++ gCirc G) F))

theorem chkAxI_sound (h : chkAxI G db = true) :
    ∀ F : Form, F.isPrime → F ∈ sfR G →
      ∃ r ∈ db, WSubsumes
        (.irr [] (rm (gAt G) F ++ gImp G ++ gCirc G) F) r.s := by
  intro F hF hg
  exact chkOne_sound
    (gate_true (List.all_eq_true.mp h F (mem_goalPool.mpr hg)) hF)

/-- `∧I` on the left conjunct. -/
def chkAndI1 (G : Form) (db : List (WRow G)) : Bool :=
  (irrTs db).all fun tr =>
    (goalPool G).all fun X =>
      match X with
      | .and A₁ A₂ =>
          gate (tr.C = A₁) (chkOne db (.irr tr.Ξ tr.Θ (.and A₁ A₂)))
      | _ => true

theorem chkAndI1_sound (h : chkAndI1 G db = true) :
    ∀ (Ξ Θ : List Form) (A₁ A₂ : Form),
      (WSeq.irr Ξ Θ A₁) ∈ db.map (·.s) → Form.and A₁ A₂ ∈ sfR G →
      ∃ r ∈ db, WSubsumes (.irr Ξ Θ (.and A₁ A₂)) r.s := by
  intro Ξ Θ A₁ A₂ hmem hg
  obtain ⟨tr, htr, rfl, rfl, rfl⟩ := irrTs_of_mem hmem
  have h1 := List.all_eq_true.mp h tr htr
  have h2 := List.all_eq_true.mp h1 (Form.and tr.C A₂) (mem_goalPool.mpr hg)
  exact chkOne_sound (gate_true h2 rfl)

/-- `∧I` on the right conjunct. -/
def chkAndI2 (G : Form) (db : List (WRow G)) : Bool :=
  (irrTs db).all fun tr =>
    (goalPool G).all fun X =>
      match X with
      | .and A₁ A₂ =>
          gate (tr.C = A₂) (chkOne db (.irr tr.Ξ tr.Θ (.and A₁ A₂)))
      | _ => true

theorem chkAndI2_sound (h : chkAndI2 G db = true) :
    ∀ (Ξ Θ : List Form) (A₁ A₂ : Form),
      (WSeq.irr Ξ Θ A₂) ∈ db.map (·.s) → Form.and A₁ A₂ ∈ sfR G →
      ∃ r ∈ db, WSubsumes (.irr Ξ Θ (.and A₁ A₂)) r.s := by
  intro Ξ Θ A₁ A₂ hmem hg
  obtain ⟨tr, htr, rfl, rfl, rfl⟩ := irrTs_of_mem hmem
  have h1 := List.all_eq_true.mp h tr htr
  have h2 := List.all_eq_true.mp h1 (Form.and A₁ tr.C) (mem_goalPool.mpr hg)
  exact chkOne_sound (gate_true h2 rfl)

/-- `∨I`: a double scan over the stored irregular disproofs. -/
def chkOrI (G : Form) (db : List (WRow G)) : Bool :=
  (irrTs db).all fun tr₁ =>
    (irrTs db).all fun tr₂ =>
      gate (tr₁.Ξ ⊆ tr₂.Ξ ++ tr₂.Θ ∧ tr₂.Ξ ⊆ tr₁.Ξ ++ tr₁.Θ ∧
            Form.or tr₁.C tr₂.C ∈ sfR G)
        (chkOne db (.irr (tr₁.Ξ ++ tr₂.Ξ) (cap tr₁.Θ tr₂.Θ)
          (.or tr₁.C tr₂.C)))

theorem chkOrI_sound (h : chkOrI G db = true) :
    ∀ (Ξ₁ Θ₁ Ξ₂ Θ₂ : List Form) (C₁ C₂ : Form),
      (WSeq.irr Ξ₁ Θ₁ C₁) ∈ db.map (·.s) →
      (WSeq.irr Ξ₂ Θ₂ C₂) ∈ db.map (·.s) →
      Ξ₁ ⊆ Ξ₂ ++ Θ₂ → Ξ₂ ⊆ Ξ₁ ++ Θ₁ →
      Form.or C₁ C₂ ∈ sfR G →
      ∃ r ∈ db, WSubsumes (.irr (Ξ₁ ++ Ξ₂) (cap Θ₁ Θ₂) (.or C₁ C₂)) r.s := by
  intro Ξ₁ Θ₁ Ξ₂ Θ₂ C₁ C₂ hmem₁ hmem₂ h₁ h₂ hg
  obtain ⟨tr₁, htr₁, rfl, rfl, rfl⟩ := irrTs_of_mem hmem₁
  obtain ⟨tr₂, htr₂, rfl, rfl, rfl⟩ := irrTs_of_mem hmem₂
  have hA := List.all_eq_true.mp h tr₁ htr₁
  have hB := List.all_eq_true.mp hA tr₂ htr₂
  exact chkOne_sound (gate_true hB ⟨h₁, h₂, hg⟩)

/-- `⊃I`.  The split parameter `Λ` is an arbitrary list, but the clause
sees it only through the two filters of `ΘΛ₂`, so the scan ranges over
`ΘΛ₂.sublists`; `chkImpInI_sound` transports an arbitrary `Λ` to the
sublist `ΘΛ₂.filter (· ∈ Λ)`, which induces the same two filters. -/
def chkImpInI (G : Form) (db : List (WRow G)) : Bool :=
  (irrTs db).all fun tr =>
    tr.Θ.sublists.all fun Λ =>
      (goalPool G).all fun X =>
        match X with
        | .imp A B =>
            gate (tr.C = B ∧
                Clo (tr.Ξ ++ tr.Θ.filter (fun x => decide (x ∈ Λ))) A)
              (chkOne db (.irr (tr.Ξ ++ tr.Θ.filter (fun x => decide (x ∈ Λ)))
                (tr.Θ.filter (fun x => !decide (x ∈ Λ))) (.imp A B)))
        | _ => true

theorem chkImpInI_sound (h : chkImpInI G db = true) :
    ∀ (Ξ₂ ΘΛ₂ Λ : List Form) (A B : Form),
      (WSeq.irr Ξ₂ ΘΛ₂ B) ∈ db.map (·.s) →
      Clo (Ξ₂ ++ ΘΛ₂.filter (fun x => decide (x ∈ Λ))) A →
      Form.imp A B ∈ sfR G →
      ∃ r ∈ db, WSubsumes
        (.irr (Ξ₂ ++ ΘΛ₂.filter (fun x => decide (x ∈ Λ)))
          (ΘΛ₂.filter (fun x => !decide (x ∈ Λ))) (.imp A B)) r.s := by
  intro Ξ₂ ΘΛ₂ Λ A B hmem hA hg
  obtain ⟨tr, htr, rfl, rfl, rfl⟩ := irrTs_of_mem hmem
  have hpos : tr.Θ.filter (fun x =>
      decide (x ∈ tr.Θ.filter (fun y => decide (y ∈ Λ)))) =
      tr.Θ.filter (fun x => decide (x ∈ Λ)) := by
    refine List.filter_congr (fun x hx => ?_)
    simp [List.mem_filter, hx]
  have hneg : tr.Θ.filter (fun x =>
      !decide (x ∈ tr.Θ.filter (fun y => decide (y ∈ Λ)))) =
      tr.Θ.filter (fun x => !decide (x ∈ Λ)) := by
    refine List.filter_congr (fun x hx => ?_)
    simp [List.mem_filter, hx]
  rw [← hpos, ← hneg]
  have hA' : Clo (tr.Ξ ++ tr.Θ.filter (fun x =>
      decide (x ∈ tr.Θ.filter (fun y => decide (y ∈ Λ))))) A := by
    rw [hpos]; exact hA
  have h1 := List.all_eq_true.mp h tr htr
  have h2 := List.all_eq_true.mp h1 (tr.Θ.filter (fun y => decide (y ∈ Λ)))
    (List.memSublistsP.mpr List.filter_sublist)
  have h3 := List.all_eq_true.mp h2 (Form.imp A tr.C) (mem_goalPool.mpr hg)
  exact chkOne_sound (gate_true h3 ⟨rfl, hA'⟩)

/-- `lift`: the maximal retained zone over the stored regular context. -/
def chkLift (G : Form) (db : List (WRow G)) : Bool :=
  (regTs db).all fun tr => chkOne db (.irr [] (maxTh G tr.Γ) tr.C)

theorem chkLift_sound (h : chkLift G db = true) :
    ∀ (t₂ : Tag) (Γ₂ : List Form) (C : Form),
      (WSeq.reg t₂ Γ₂ C) ∈ db.map (·.s) →
      ∃ r ∈ db, WSubsumes (.irr [] (maxTh G Γ₂) C) r.s := by
  intro t₂ Γ₂ C hmem
  obtain ⟨tr, htr, rfl, rfl, rfl⟩ := regTs_of_mem hmem
  exact chkOne_sound (List.all_eq_true.mp h tr htr)

/-- `◯∉`. -/
def chkCircNotIn (G : Form) (db : List (WRow G)) : Bool :=
  (regTs db).all fun tr =>
    gate ((tr.t = .barren ∨ ∃ W, tr.t = .chain W ∧ Covers tr.Γ W tr.C) ∧
          Form.circ tr.C ∈ sfR G)
      (chkOne db (.irr [] (maxTh G tr.Γ) (.circ tr.C)))

theorem chkCircNotIn_sound (h : chkCircNotIn G db = true) :
    ∀ (t₂ : Tag) (Γ₂ : List Form) (Z : Form),
      (WSeq.reg t₂ Γ₂ Z) ∈ db.map (·.s) →
      (t₂ = .barren ∨ ∃ W, t₂ = .chain W ∧ Covers Γ₂ W Z) →
      Form.circ Z ∈ sfR G →
      ∃ r ∈ db, WSubsumes (.irr [] (maxTh G Γ₂) (.circ Z)) r.s := by
  intro t₂ Γ₂ Z hmem htag hg
  obtain ⟨tr, htr, rfl, rfl, rfl⟩ := regTs_of_mem hmem
  exact chkOne_sound
    (gate_true (List.all_eq_true.mp h tr htr) ⟨htag, hg⟩)

/-- `Ax^{I◯}`.  The valuation `ats` is an arbitrary sublist-worth of
`Ĝ_at`; `classForce` and hence `vacZoneA` see it only through atom
membership (`classForce_congr`), so the scan ranges over
`(gAt G).sublists` and `chkAxIC_sound` transports an arbitrary
`ats ⊆ gAt G` to `(gAt G).filter (· ∈ ats)`. -/
def chkAxIC (G : Form) (db : List (WRow G)) : Bool :=
  (goalPool G).all fun X =>
    match X with
    | .circ F =>
        (gAt G).sublists.all fun ats =>
          gate (classForce ats F = false)
            (chkOne db (.irr [] (vacZoneA G ats) (.circ F)))
    | _ => true

theorem chkAxIC_sound (h : chkAxIC G db = true) :
    ∀ (F : Form) (ats : List Form), ats ⊆ gAt G →
      classForce ats F = false → Form.circ F ∈ sfR G →
      ∃ r ∈ db, WSubsumes (.irr [] (vacZoneA G ats) (.circ F)) r.s := by
  intro F ats hats hFf hg
  have hcongr : ∀ X : Form,
      classForce ((gAt G).filter (fun x => decide (x ∈ ats))) X =
        classForce ats X := by
    refine classForce_congr (fun p => ?_)
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hats h, h⟩⟩
  have hzone : vacZoneA G ((gAt G).filter (fun x => decide (x ∈ ats))) =
      vacZoneA G ats := by
    simp only [vacZoneA]
    exact List.filter_congr (fun x _ => hcongr x)
  rw [← hzone]
  have h1 := List.all_eq_true.mp h (Form.circ F) (mem_goalPool.mpr hg)
  have h2 := List.all_eq_true.mp h1
    ((gAt G).filter (fun x => decide (x ∈ ats)))
    (List.memSublistsP.mpr List.filter_sublist)
  exact chkOne_sound (gate_true h2 ((hcongr F).trans hFf))

end Irregular

/-! ## 3. The scan -/

section Scan

variable {G : Form} {db : List (WRow G)}

/-- The thirteen non-join clauses of `DBClosedDG`, as one check. -/
def chkScan (G : Form) (db : List (WRow G)) : Bool :=
  chkAxR G db && chkAndR1 G db && chkAndR2 G db && chkImpIn G db &&
  chkCircIn G db && chkAxI G db && chkAndI1 G db && chkAndI2 G db &&
  chkOrI G db && chkImpInI G db && chkLift G db && chkCircNotIn G db &&
  chkAxIC G db

theorem chkScan_parts (h : chkScan G db = true) :
    chkAxR G db = true ∧ chkAndR1 G db = true ∧ chkAndR2 G db = true ∧
    chkImpIn G db = true ∧ chkCircIn G db = true ∧ chkAxI G db = true ∧
    chkAndI1 G db = true ∧ chkAndI2 G db = true ∧ chkOrI G db = true ∧
    chkImpInI G db = true ∧ chkLift G db = true ∧
    chkCircNotIn G db = true ∧ chkAxIC G db = true := by
  simp only [chkScan, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2,
    h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- Soundness of the scan: the thirteen non-join clauses of
`DBClosedDG`, verbatim. -/
theorem chkScan_sound (h : chkScan G db = true) :
    (∀ F : Form, F.isPrime → F ∈ sfR G →
      ∃ r ∈ db, WSubsumes (.reg .barren (rm (gAt G) F) F) r.s) ∧
    (∀ (t : Tag) (Γ : List Form) (A₁ A₂ : Form),
      (WSeq.reg t Γ A₁) ∈ db.map (·.s) → Form.and A₁ A₂ ∈ sfR G →
      ∃ r ∈ db, WSubsumes (.reg t Γ (.and A₁ A₂)) r.s) ∧
    (∀ (t : Tag) (Γ : List Form) (A₁ A₂ : Form),
      (WSeq.reg t Γ A₂) ∈ db.map (·.s) → Form.and A₁ A₂ ∈ sfR G →
      ∃ r ∈ db, WSubsumes (.reg t Γ (.and A₁ A₂)) r.s) ∧
    (∀ (t : Tag) (Γ : List Form) (A B : Form),
      (WSeq.reg t Γ B) ∈ db.map (·.s) → Clo Γ A → Form.imp A B ∈ sfR G →
      ∃ r ∈ db, WSubsumes (.reg t Γ (.imp A B)) r.s) ∧
    (∀ (t : Tag) (Γ : List Form) (Z : Form),
      (WSeq.reg t Γ Z) ∈ db.map (·.s) →
      (t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W Z) →
      Form.circ Z ∈ sfR G →
      ∃ r ∈ db, WSubsumes (.reg t Γ (.circ Z)) r.s) ∧
    (∀ F : Form, F.isPrime → F ∈ sfR G →
      ∃ r ∈ db, WSubsumes
        (.irr [] (rm (gAt G) F ++ gImp G ++ gCirc G) F) r.s) ∧
    (∀ (Ξ Θ : List Form) (A₁ A₂ : Form),
      (WSeq.irr Ξ Θ A₁) ∈ db.map (·.s) → Form.and A₁ A₂ ∈ sfR G →
      ∃ r ∈ db, WSubsumes (.irr Ξ Θ (.and A₁ A₂)) r.s) ∧
    (∀ (Ξ Θ : List Form) (A₁ A₂ : Form),
      (WSeq.irr Ξ Θ A₂) ∈ db.map (·.s) → Form.and A₁ A₂ ∈ sfR G →
      ∃ r ∈ db, WSubsumes (.irr Ξ Θ (.and A₁ A₂)) r.s) ∧
    (∀ (Ξ₁ Θ₁ Ξ₂ Θ₂ : List Form) (C₁ C₂ : Form),
      (WSeq.irr Ξ₁ Θ₁ C₁) ∈ db.map (·.s) →
      (WSeq.irr Ξ₂ Θ₂ C₂) ∈ db.map (·.s) →
      Ξ₁ ⊆ Ξ₂ ++ Θ₂ → Ξ₂ ⊆ Ξ₁ ++ Θ₁ →
      Form.or C₁ C₂ ∈ sfR G →
      ∃ r ∈ db, WSubsumes
        (.irr (Ξ₁ ++ Ξ₂) (cap Θ₁ Θ₂) (.or C₁ C₂)) r.s) ∧
    (∀ (Ξ₂ ΘΛ₂ Λ : List Form) (A B : Form),
      (WSeq.irr Ξ₂ ΘΛ₂ B) ∈ db.map (·.s) →
      Clo (Ξ₂ ++ ΘΛ₂.filter (fun x => decide (x ∈ Λ))) A →
      Form.imp A B ∈ sfR G →
      ∃ r ∈ db, WSubsumes
        (.irr (Ξ₂ ++ ΘΛ₂.filter (fun x => decide (x ∈ Λ)))
          (ΘΛ₂.filter (fun x => !decide (x ∈ Λ))) (.imp A B)) r.s) ∧
    (∀ (t₂ : Tag) (Γ₂ : List Form) (C : Form),
      (WSeq.reg t₂ Γ₂ C) ∈ db.map (·.s) →
      ∃ r ∈ db, WSubsumes (.irr [] (maxTh G Γ₂) C) r.s) ∧
    (∀ (t₂ : Tag) (Γ₂ : List Form) (Z : Form),
      (WSeq.reg t₂ Γ₂ Z) ∈ db.map (·.s) →
      (t₂ = .barren ∨ ∃ W, t₂ = .chain W ∧ Covers Γ₂ W Z) →
      Form.circ Z ∈ sfR G →
      ∃ r ∈ db, WSubsumes (.irr [] (maxTh G Γ₂) (.circ Z)) r.s) ∧
    (∀ (F : Form) (ats : List Form), ats ⊆ gAt G →
      classForce ats F = false → Form.circ F ∈ sfR G →
      ∃ r ∈ db, WSubsumes (.irr [] (vacZoneA G ats) (.circ F)) r.s) := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩ :=
    chkScan_parts h
  exact ⟨chkAxR_sound p1, chkAndR1_sound p2, chkAndR2_sound p3,
    chkImpIn_sound p4, chkCircIn_sound p5, chkAxI_sound p6,
    chkAndI1_sound p7, chkAndI2_sound p8, chkOrI_sound p9,
    chkImpInI_sound p10, chkLift_sound p11, chkCircNotIn_sound p12,
    chkAxIC_sound p13⟩

end Scan

/-! ## Pins -/

/-- info: 'FRJ.Arity.chkOne_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chkOne_sound

/-- info: 'FRJ.Arity.gate_true' does not depend on any axioms -/
#guard_msgs in
#print axioms gate_true

/-- info: 'FRJ.Arity.chkAxR_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chkAxR_sound

/-- info: 'FRJ.Arity.chkAndR1_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chkAndR1_sound

/-- info: 'FRJ.Arity.chkAndR2_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chkAndR2_sound

/-- info: 'FRJ.Arity.chkImpIn_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chkImpIn_sound

/-- info: 'FRJ.Arity.chkCircIn_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chkCircIn_sound

/-- info: 'FRJ.Arity.chkAxI_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chkAxI_sound

/-- info: 'FRJ.Arity.chkAndI1_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chkAndI1_sound

/-- info: 'FRJ.Arity.chkAndI2_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chkAndI2_sound

/-- info: 'FRJ.Arity.chkOrI_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chkOrI_sound

/-- info: 'FRJ.Arity.chkImpInI_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chkImpInI_sound

/-- info: 'FRJ.Arity.chkLift_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chkLift_sound

/-- info: 'FRJ.Arity.chkCircNotIn_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chkCircNotIn_sound

/-- info: 'FRJ.Arity.chkAxIC_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chkAxIC_sound

/-- info: 'FRJ.Arity.chkScan_parts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms chkScan_parts

/-- info: 'FRJ.Arity.chkScan_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chkScan_sound

end FRJ.Arity
