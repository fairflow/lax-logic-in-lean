/-
# `checkClosed`, the join clauses

`docs/checkclosed-checks.md` §6, build item 5 (join half).  For each of
the eight join clauses of `DBClosedDG` (`wip/dbclosed_dg.lean`) a
Boolean check over BOUNDED families and its soundness proof:

  * irregular families range over `famsDG G db`: sublists of the
    irregular store of length `1 .. |Sf^R|` with pairwise distinct goals;
  * promise families over `pfams G db`: sublists of the regular store of
    length `1 .. |Ĝ^◯| + 1`;
  * the guards are the emitters' own (`FRJ/Gbu/W/Saturate.lean` S4);
  * the conclusion sequent is looked up by `findSub`.

Soundness follows the S5 coverage pattern: a clause instance reindexes
(`reindex_irr`, `reindex_reg`) to a stored sublist with the same row
set, which the bounds admit (distinct goals bound the irregular arity by
`|Sf^R|`, distinct rows bound the promise arity by the clause's own
`k ≤ |Ĝ^◯|`), the guards transfer along `SameIrr`/`SameReg`, and the
found subsumer subsumes the original conclusion through the `≐`
congruence of the contexts.  Every lemma assumes `(db.map (·.s)).Nodup`,
which `checkClosed` checks first.
-/
import wip.dbclosed_dg

open FRJ Form FRJ.Gbu.W FRJ.Arity

namespace FRJ.Arity

/-! ## 1. Bounded family enumerators -/

/-- Pairwise distinct goals along a row list. -/
def distinctB {G : Form} : List (IrrT G) → Bool
  | [] => true
  | a :: t => t.all (fun b => decide (b.C ≠ a.C)) && distinctB t

theorem distinctB_cons {G : Form} {a : IrrT G} {t : List (IrrT G)} :
    distinctB (a :: t) = true ↔ (∀ b ∈ t, b.C ≠ a.C) ∧ distinctB t = true := by
  simp [distinctB, List.all_eq_true]

/-- Irregular families: sublists of the store of length `1 .. |Sf^R|`
with pairwise distinct goals. -/
def famsDG (G : Form) (db : List (WRow G)) : List (List (IrrT G)) :=
  ((List.range (goalPool G).length).flatMap
    (fun m => List.sublistsLen (m + 1) (irrTs db))).filter distinctB

/-- Promise families: sublists of the regular store of length `1 .. |Ĝ^◯| + 1`. -/
def pfams (G : Form) (db : List (WRow G)) : List (List (RegT G)) :=
  (List.range ((dedupF (gCirc G)).length + 1)).flatMap
    (fun m => List.sublistsLen (m + 1) (regTs db))

theorem mem_famsDG {G : Form} {db : List (WRow G)} {l : List (IrrT G)}
    (hsub : l.Sublist (irrTs db)) (hlen : 1 ≤ l.length)
    (hbound : l.length ≤ (goalPool G).length) (hd : distinctB l = true) :
    l ∈ famsDG G db := by
  refine List.mem_filter.mpr ⟨?_, hd⟩
  refine List.mem_flatMap.mpr ⟨l.length - 1, ?_, ?_⟩
  · exact List.mem_range.mpr (by omega)
  · exact List.mem_sublistsLen.mpr ⟨hsub, by omega⟩

theorem mem_pfams {G : Form} {db : List (WRow G)} {l : List (RegT G)}
    (hsub : l.Sublist (regTs db)) (hlen : 1 ≤ l.length)
    (hbound : l.length ≤ (dedupF (gCirc G)).length + 1) :
    l ∈ pfams G db := by
  refine List.mem_flatMap.mpr ⟨l.length - 1, ?_, ?_⟩
  · exact List.mem_range.mpr (by omega)
  · exact List.mem_sublistsLen.mpr ⟨hsub, by omega⟩

/-! ## 2. The bounds, from distinct goals and distinct rows -/

/-- `dedupF` lists without repeats. -/
theorem dedupF_nodup' : ∀ (l : List Form), (dedupF l).Nodup
  | [] => List.nodup_nil
  | x :: xs => by
      simp only [dedupF]
      by_cases hx : x ∈ xs
      · rw [if_pos hx]; exact dedupF_nodup' xs
      · rw [if_neg hx]
        exact List.nodup_cons.mpr ⟨fun h => hx (mem_dedupF.mp h), dedupF_nodup' xs⟩

/-- The goals of a distinct-goal row list have no repeats. -/
theorem nodup_goals_of_distinctB {G : Form} : ∀ {l : List (IrrT G)},
    distinctB l = true → (l.map IrrT.C).Nodup
  | [], _ => List.nodup_nil
  | a :: t, h => by
      obtain ⟨h1, h2⟩ := distinctB_cons.mp h
      simp only [List.map_cons]
      refine List.nodup_cons.mpr ⟨?_, nodup_goals_of_distinctB h2⟩
      intro hmem
      obtain ⟨b, hb, hbc⟩ := List.mem_map.mp hmem
      exact h1 b hb hbc

/-- Every stored irregular row's goal is a right subformula. -/
theorem goal_sfR_of_irrTs {G : Form} {db : List (WRow G)} {tr : IrrT G}
    (h : tr ∈ irrTs db) : tr.C ∈ sfR G := by
  obtain ⟨r, hr, hrt⟩ := List.mem_filterMap.mp h
  match r, hrt with
  | ⟨.irr Ξ' Θ' C', d⟩, hrt =>
      injection hrt with h1
      subst h1
      exact (wfSeq_of_wDer d).2.2

/-- A distinct-goal sublist of the store has at most `|Sf^R|` rows. -/
theorem length_le_goalPool {G : Form} {db : List (WRow G)} {l : List (IrrT G)}
    (hsub : l.Sublist (irrTs db)) (hd : distinctB l = true) :
    l.length ≤ (goalPool G).length := by
  have hnd := nodup_goals_of_distinctB hd
  have hsubset : l.map IrrT.C ⊆ goalPool G := by
    intro x hx
    obtain ⟨tr, htr, rfl⟩ := List.mem_map.mp hx
    exact mem_goalPool.mpr (goal_sfR_of_irrTs (hsub.subset htr))
  have := length_le_of_nodup_subset hnd hsubset
  simpa [List.length_map] using this

/-- `distinctB` from index-wise distinctness of the goals. -/
theorem distinctB_of_get {G : Form} : ∀ (l : List (IrrT G)),
    (∀ i j : Fin l.length, i ≠ j → (l.get i).C ≠ (l.get j).C) → distinctB l = true
  | [], _ => rfl
  | a :: t, h => by
      refine distinctB_cons.mpr ⟨?_, distinctB_of_get t (fun i j hij => ?_)⟩
      · intro b hb hbc
        obtain ⟨i, hi⟩ := List.get_of_mem hb
        have := h i.succ 0 (Fin.succ_ne_zero i)
        apply this
        change (t.get i).C = a.C
        rw [hi, hbc]
      · have := h i.succ j.succ (fun e => hij (Fin.succ_injective _ e))
        simpa [List.get_cons_succ] using this

/-- The reindexed stored family of a distinct-goal clause instance has
pairwise distinct goals: two positions with the same goal are two rows
each equal to an original premise, the premises share a goal, so they
are the same premise, so the rows coincide -- against `hnd`. -/
theorem distinctB_of_reindex {G : Form} {n : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} (hdist : ∀ i j, i ≠ j → rhs i ≠ rhs j)
    {a : IrrT G} {t : List (IrrT G)}
    (hsame : SameIrr Ξs Θs rhs (fun j => ((a :: t).get j).Ξ)
      (fun j => ((a :: t).get j).Θ) (fun j => ((a :: t).get j).C))
    (hnd : ∀ i₁ i₂ : Fin (t.length + 1), i₁ ≠ i₂ →
      ¬ (((a :: t).get i₁).Ξ = ((a :: t).get i₂).Ξ ∧
         ((a :: t).get i₁).Θ = ((a :: t).get i₂).Θ ∧
         ((a :: t).get i₁).C = ((a :: t).get i₂).C)) :
    distinctB (a :: t) = true := by
  refine distinctB_of_get (a :: t) (fun i j hij hC => ?_)
  obtain ⟨j₁, hs₁, ht₁, hr₁⟩ := hsame.2 i
  obtain ⟨j₂, hs₂, ht₂, hr₂⟩ := hsame.2 j
  have hjj : j₁ = j₂ := by
    by_contra hne
    exact hdist j₁ j₂ hne (hr₁.symm.trans (hC.trans hr₂))
  subst hjj
  exact hnd i j hij ⟨hs₁.trans hs₂.symm, ht₁.trans ht₂.symm, hr₁.trans hr₂.symm⟩

/-- Distinct sequents in the store make the regular triples distinct. -/
theorem regTs_seq_nodup {G : Form} {db : List (WRow G)}
    (hnd : (db.map (·.s)).Nodup) : ((regTs db).map RegT.seq).Nodup :=
  hnd.sublist (regTs_seq_sublist db)

/-- A reindexed promise sublist has at most as many rows as the clause's
promise family: its sequents are distinct and each is one of the
family's. -/
theorem length_le_of_reindex_reg {G : Form} {db : List (WRow G)}
    (hnd : (db.map (·.s)).Nodup) {k : Nat} {tps : Fin (k + 1) → Tag}
    {Δs : Fin (k + 1) → List Form} {Ds : Fin (k + 1) → Form}
    {b : RegT G} {u : List (RegT G)} (hsub : (b :: u).Sublist (regTs db))
    (hsame : SameReg tps Δs Ds (fun i => ((b :: u).get i).t)
      (fun i => ((b :: u).get i).Γ) (fun i => ((b :: u).get i).C)) :
    (b :: u).length ≤ k + 1 := by
  have hnd' : ((b :: u).map RegT.seq).Nodup :=
    (regTs_seq_nodup hnd).sublist (hsub.map RegT.seq)
  have hsubset : (b :: u).map RegT.seq ⊆
      (List.finRange (k + 1)).map (fun i => WSeq.reg (tps i) (Δs i) (Ds i)) := by
    intro x hx
    obtain ⟨tr, htr, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, hi⟩ := List.get_of_mem htr
    obtain ⟨j, hj1, hj2, hj3⟩ := hsame.2 i
    refine List.mem_map.mpr ⟨j, List.mem_finRange j, ?_⟩
    rw [← hi]
    show WSeq.reg (tps j) (Δs j) (Ds j) =
      WSeq.reg (((b :: u).get i).t) (((b :: u).get i).Γ) (((b :: u).get i).C)
    have hj1' : ((b :: u).get i).t = tps j := hj1
    have hj2' : ((b :: u).get i).Γ = Δs j := hj2
    have hj3' : ((b :: u).get i).C = Ds j := hj3
    rw [hj1', hj2', hj3']
  have := length_le_of_nodup_subset hnd' hsubset
  rw [List.length_map, List.length_map, List.length_finRange] at this
  exact this

/-- A reindexed stored family of a distinct-goal clause instance is enumerated. -/
theorem famsDG_of_reindex {G : Form} {db : List (WRow G)} {n : Nat}
    {Ξs Θs : Fin (n + 1) → List Form} {rhs : Fin (n + 1) → Form}
    (hdist : ∀ i j, i ≠ j → rhs i ≠ rhs j) {a : IrrT G} {t : List (IrrT G)}
    (hsubl : (a :: t) ∈ (irrTs db).sublists)
    (hsame : SameIrr Ξs Θs rhs (fun j => ((a :: t).get j).Ξ)
      (fun j => ((a :: t).get j).Θ) (fun j => ((a :: t).get j).C))
    (hnd : ∀ i₁ i₂ : Fin (t.length + 1), i₁ ≠ i₂ →
      ¬ (((a :: t).get i₁).Ξ = ((a :: t).get i₂).Ξ ∧
         ((a :: t).get i₁).Θ = ((a :: t).get i₂).Θ ∧
         ((a :: t).get i₁).C = ((a :: t).get i₂).C)) :
    (a :: t) ∈ famsDG G db :=
  have hsub := List.mem_sublists.mp hsubl
  have hd := distinctB_of_reindex hdist hsame hnd
  mem_famsDG hsub (Nat.succ_le_succ (Nat.zero_le _)) (length_le_goalPool hsub hd) hd

/-- A reindexed stored promise family within the clause's bound is enumerated. -/
theorem pfams_of_reindex {G : Form} {db : List (WRow G)} (hnd : (db.map (·.s)).Nodup)
    {k : Nat} {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
    {Ds : Fin (k + 1) → Form} (hk : k ≤ (dedupF (gCirc G)).length)
    {b : RegT G} {u : List (RegT G)} (hsubl : (b :: u) ∈ (regTs db).sublists)
    (hsame : SameReg tps Δs Ds (fun i => ((b :: u).get i).t)
      (fun i => ((b :: u).get i).Γ) (fun i => ((b :: u).get i).C)) :
    (b :: u) ∈ pfams G db :=
  have hsub := List.mem_sublists.mp hsubl
  mem_pfams hsub (Nat.succ_le_succ (Nat.zero_le _))
    (Nat.le_trans (length_le_of_reindex_reg hnd hsub hsame) (by omega))

/-! ## 3. The eight checks

Each mirrors its emitter in `FRJ/Gbu/W/Saturate.lean` S4 (same guard,
same conclusion sequent), over `famsDG`/`pfams` instead of all
sublists, and looks the conclusion up with `findSub`. -/

section Checks

variable (G : Form) (db : List (WRow G))

def chkJoinAt : Bool :=
  (famsDG G db).all fun l =>
    match l with
    | [] => true
    | a :: t =>
        (goalPool G).all fun F =>
          if (∀ i j, i ≠ j → ((a :: t).get i).Ξ ⊆ ((a :: t).get j).Ξ ++ ((a :: t).get j).Θ) ∧
              (∀ x ∈ unionAll (fun j => impPart (((a :: t).get j).Ξ)), ∀ A B : Form,
                x = Form.imp A B → A ∈ upsilon (fun j => ((a :: t).get j).C)) ∧
              unionAll (fun j => circPart (((a :: t).get j).Ξ)) = [] ∧
              F.isPrime = true ∧
              F ∉ unionAll (fun j => atPart (((a :: t).get j).Ξ)) ∧
              F ∈ sfR G then
            (findSub db (.reg .barren
              (joinCtxAtVBase (fun j => ((a :: t).get j).Ξ) (fun j => ((a :: t).get j).Θ) F ++
                keptOf (upsilon (fun j => ((a :: t).get j).C))
                  (joinCtxAtVBase (fun j => ((a :: t).get j).Ξ) (fun j => ((a :: t).get j).Θ) F)
                  (thPool (fun j => ((a :: t).get j).Θ))) F)).isSome
          else true

def chkJoinAtF : Bool :=
  (famsDG G db).all fun l =>
    match l with
    | [] => true
    | a :: t =>
        (goalPool G).all fun F =>
          if (∀ i j, i ≠ j → ((a :: t).get i).Ξ ⊆ ((a :: t).get j).Ξ ++ ((a :: t).get j).Θ) ∧
              (∀ x ∈ unionAll (fun j => impPart (((a :: t).get j).Ξ)), ∀ A B : Form,
                x = Form.imp A B → A ∈ upsilon (fun j => ((a :: t).get j).C)) ∧
              F.isPrime = true ∧
              F ∉ unionAll (fun j => atPart (((a :: t).get j).Ξ)) ∧
              F ∈ sfR G then
            (findSub db (.reg .blocked
              (joinCtxAtF (fun j => ((a :: t).get j).Ξ) (fun j => ((a :: t).get j).Θ)
                (fun j => ((a :: t).get j).C) F) F)).isSome
          else true

def chkJoinOr : Bool :=
  (famsDG G db).all fun l =>
    match l with
    | [] => true
    | a :: t =>
        (goalPool G).all fun X =>
          match X with
          | .or C₁ C₂ =>
              if (∀ i j, i ≠ j → ((a :: t).get i).Ξ ⊆ ((a :: t).get j).Ξ ++ ((a :: t).get j).Θ) ∧
                  (∀ x ∈ unionAll (fun j => impPart (((a :: t).get j).Ξ)), ∀ A B : Form,
                    x = Form.imp A B → A ∈ upsilon (fun j => ((a :: t).get j).C)) ∧
                  unionAll (fun j => circPart (((a :: t).get j).Ξ)) = [] ∧
                  (RefAt true (upsilon (fun j => ((a :: t).get j).C))
                      (ctxOr (fun j => ((a :: t).get j).Ξ) (fun j => ((a :: t).get j).Θ)
                        (fun j => ((a :: t).get j).C)) C₁ ∧
                    RefAt true (upsilon (fun j => ((a :: t).get j).C))
                      (ctxOr (fun j => ((a :: t).get j).Ξ) (fun j => ((a :: t).get j).Θ)
                        (fun j => ((a :: t).get j).C)) C₂) ∧
                  Form.or C₁ C₂ ∈ sfR G then
                (findSub db (.reg .barren
                  (ctxOr (fun j => ((a :: t).get j).Ξ) (fun j => ((a :: t).get j).Θ)
                    (fun j => ((a :: t).get j).C)) (.or C₁ C₂))).isSome
              else true
          | _ => true

def chkJoinCirc : Bool :=
  (famsDG G db).all fun l =>
    match l with
    | [] => true
    | a :: t =>
        (goalPool G).all fun X =>
          match X with
          | .circ Z =>
              if (∀ i j, i ≠ j → ((a :: t).get i).Ξ ⊆ ((a :: t).get j).Ξ ++ ((a :: t).get j).Θ) ∧
                  (∀ x ∈ unionAll (fun j => impPart (((a :: t).get j).Ξ)), ∀ A B : Form,
                    x = Form.imp A B →
                    RefAt true (upsilon (fun j => ((a :: t).get j).C))
                      (ctxOr (fun j => ((a :: t).get j).Ξ) (fun j => ((a :: t).get j).Θ)
                        (fun j => ((a :: t).get j).C)) A) ∧
                  unionAll (fun j => circPart (((a :: t).get j).Ξ)) = [] ∧
                  RefAt true (upsilon (fun j => ((a :: t).get j).C))
                    (ctxOr (fun j => ((a :: t).get j).Ξ) (fun j => ((a :: t).get j).Θ)
                      (fun j => ((a :: t).get j).C)) Z ∧
                  Form.circ Z ∈ sfR G then
                (findSub db (.reg .barren
                  (ctxOr (fun j => ((a :: t).get j).Ξ) (fun j => ((a :: t).get j).Θ)
                    (fun j => ((a :: t).get j).C)) (.circ Z))).isSome
              else true
          | _ => true

def chkJoinOrF : Bool :=
  (famsDG G db).all fun l =>
    match l with
    | [] => true
    | a :: t =>
        (goalPool G).all fun X =>
          match X with
          | .or C₁ C₂ =>
              if (∀ i j, i ≠ j → ((a :: t).get i).Ξ ⊆ ((a :: t).get j).Ξ ++ ((a :: t).get j).Θ) ∧
                  (∀ x ∈ unionAll (fun j => impPart (((a :: t).get j).Ξ)), ∀ A B : Form,
                    x = Form.imp A B → A ∈ upsilon (fun j => ((a :: t).get j).C)) ∧
                  (C₁ ∈ upsilon (fun j => ((a :: t).get j).C) ∧
                    C₂ ∈ upsilon (fun j => ((a :: t).get j).C)) ∧
                  Form.or C₁ C₂ ∈ sfR G then
                (findSub db (.reg .blocked
                  (joinCtxOrF (fun j => ((a :: t).get j).Ξ) (fun j => ((a :: t).get j).Θ)
                    (fun j => ((a :: t).get j).C)) (.or C₁ C₂))).isSome
              else true
          | _ => true

end Checks

/-! ## 4. Soundness of the barren and fallible checks -/

section Sound

variable {G : Form} {db : List (WRow G)} (hnd : (db.map (·.s)).Nodup)

include hnd in
theorem chkJoinAt_sound (h : chkJoinAt G db = true) : ∀ {n : Nat}
    (Ξs Θs : Fin (n + 1) → List Form) (rhs : Fin (n + 1) → Form) (F : Form),
    (∀ i j, i ≠ j → rhs i ≠ rhs j) →
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) →
    unionAll (fun j => circPart (Ξs j)) = [] →
    F.isPrime → F ∉ unionAll (fun j => atPart (Ξs j)) → F ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.reg .barren (joinCtxAtVBase Ξs Θs F ++
        keptOf (upsilon rhs) (joinCtxAtVBase Ξs Θs F) (thPool Θs)) F) r.s := by
  intro n Ξs Θs rhs F hdist hmem hJ1 hJ2 hcirc hF hFnot hg
  obtain ⟨a, t, hsubl, hsame, hndr⟩ := reindex_irr hnd hmem
  have hctx := hsame.atCtx_sub (F := F)
  have h1 := List.all_eq_true.mp h (a :: t) (famsDG_of_reindex hdist hsubl hsame hndr)
  have h2 := List.all_eq_true.mp h1 F (mem_goalPool.mpr hg)
  try dsimp only at h2
  rw [if_pos ⟨hsame.hJ1 hndr hJ1,
    impGuard_intro (fun A B hAB => hsame.hJ2_strict hJ2 A B hAB),
    hsame.hcirc hcirc, hF, hsame.hFnot hFnot, hg⟩] at h2
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h2
  exact ⟨r, findSub_mem hr,
    wSubsumes_trans (wSubsumes_reg (tagLeB_refl _) hctx) (findSub_sub hr)⟩

include hnd in
theorem chkJoinAtF_sound (h : chkJoinAtF G db = true) : ∀ {n : Nat}
    (Ξs Θs : Fin (n + 1) → List Form) (rhs : Fin (n + 1) → Form) (F : Form),
    (∀ i j, i ≠ j → rhs i ≠ rhs j) →
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) →
    F.isPrime → F ∉ unionAll (fun j => atPart (Ξs j)) → F ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg .blocked (joinCtxAtF Ξs Θs rhs F) F) r.s := by
  intro n Ξs Θs rhs F hdist hmem hJ1 hJ2 hF hFnot hg
  obtain ⟨a, t, hsubl, hsame, hndr⟩ := reindex_irr hnd hmem
  have h1 := List.all_eq_true.mp h (a :: t) (famsDG_of_reindex hdist hsubl hsame hndr)
  have h2 := List.all_eq_true.mp h1 F (mem_goalPool.mpr hg)
  try dsimp only at h2
  rw [if_pos ⟨hsame.hJ1 hndr hJ1,
    impGuard_intro (fun A B hAB => hsame.hJ2_strict hJ2 A B hAB),
    hF, hsame.hFnot hFnot, hg⟩] at h2
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h2
  exact ⟨r, findSub_mem hr,
    wSubsumes_trans (wSubsumes_reg (tagLeB_refl _) (hsame.ctxAtF (F := F)).subset)
      (findSub_sub hr)⟩

include hnd in
theorem chkJoinOr_sound (h : chkJoinOr G db = true) : ∀ {n : Nat}
    (Ξs Θs : Fin (n + 1) → List Form) (rhs : Fin (n + 1) → Form) (C₁ C₂ : Form),
    (∀ i j, i ≠ j → rhs i ≠ rhs j) →
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) →
    unionAll (fun j => circPart (Ξs j)) = [] →
    (RefAt true (upsilon rhs) (joinCtxOrVBase Ξs Θs ++
        keptOf (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs)) C₁ ∧
      RefAt true (upsilon rhs) (joinCtxOrVBase Ξs Θs ++
        keptOf (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs)) C₂) →
    Form.or C₁ C₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.reg .barren (joinCtxOrVBase Ξs Θs ++
        keptOf (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs))
        (.or C₁ C₂)) r.s := by
  intro n Ξs Θs rhs C₁ C₂ hdist hmem hJ1 hJ2 hcirc hC hg
  obtain ⟨a, t, hsubl, hsame, hndr⟩ := reindex_irr hnd hmem
  have hctx := hsame.orCtx_sub
  have h1 := List.all_eq_true.mp h (a :: t) (famsDG_of_reindex hdist hsubl hsame hndr)
  have h2 := List.all_eq_true.mp h1 (Form.or C₁ C₂) (mem_goalPool.mpr hg)
  try dsimp only at h2
  rw [if_pos ⟨hsame.hJ1 hndr hJ1,
    impGuard_intro (fun A B hAB => hsame.hJ2_strict hJ2 A B hAB),
    hsame.hcirc hcirc,
    ⟨refAt_mono hsame.upsilon_eq.subset hctx hC.1,
      refAt_mono hsame.upsilon_eq.subset hctx hC.2⟩, hg⟩] at h2
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h2
  exact ⟨r, findSub_mem hr,
    wSubsumes_trans (wSubsumes_reg (tagLeB_refl _) hctx) (findSub_sub hr)⟩

include hnd in
theorem chkJoinCirc_sound (h : chkJoinCirc G db = true) : ∀ {n : Nat}
    (Ξs Θs : Fin (n + 1) → List Form) (rhs : Fin (n + 1) → Form) (Z : Form),
    (∀ i j, i ≠ j → rhs i ≠ rhs j) →
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      RefAt true (upsilon rhs) (joinCtxOrVBase Ξs Θs ++
        keptOf (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs)) A) →
    unionAll (fun j => circPart (Ξs j)) = [] →
    RefAt true (upsilon rhs) (joinCtxOrVBase Ξs Θs ++
      keptOf (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs)) Z →
    Form.circ Z ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.reg .barren (joinCtxOrVBase Ξs Θs ++
        keptOf (upsilon rhs) (joinCtxOrVBase Ξs Θs) (thPool Θs))
        (.circ Z)) r.s := by
  intro n Ξs Θs rhs Z hdist hmem hJ1 hJ2 hcirc hZ hg
  obtain ⟨a, t, hsubl, hsame, hndr⟩ := reindex_irr hnd hmem
  have hctx := hsame.orCtx_sub
  have hJ2' : ∀ A B : Form, Form.imp A B ∈
      unionAll (fun j => impPart (((a :: t).get j).Ξ)) →
      RefAt true (upsilon fun j => ((a :: t).get j).C)
        (ctxOr (fun j => ((a :: t).get j).Ξ) (fun j => ((a :: t).get j).Θ)
          (fun j => ((a :: t).get j).C)) A :=
    fun A B hAB => refAt_mono hsame.upsilon_eq.subset hctx
      (hJ2 A B ((hsame.unionAll_filter _ _).mpr hAB))
  have h1 := List.all_eq_true.mp h (a :: t) (famsDG_of_reindex hdist hsubl hsame hndr)
  have h2 := List.all_eq_true.mp h1 (Form.circ Z) (mem_goalPool.mpr hg)
  try dsimp only at h2
  rw [if_pos ⟨hsame.hJ1 hndr hJ1, impGuard_intro hJ2', hsame.hcirc hcirc,
    refAt_mono hsame.upsilon_eq.subset hctx hZ, hg⟩] at h2
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h2
  exact ⟨r, findSub_mem hr,
    wSubsumes_trans (wSubsumes_reg (tagLeB_refl _) hctx) (findSub_sub hr)⟩

include hnd in
theorem chkJoinOrF_sound (h : chkJoinOrF G db = true) : ∀ {n : Nat}
    (Ξs Θs : Fin (n + 1) → List Form) (rhs : Fin (n + 1) → Form) (C₁ C₂ : Form),
    (∀ i j, i ≠ j → rhs i ≠ rhs j) →
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) →
    (C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs) →
    Form.or C₁ C₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.reg .blocked (joinCtxOrF Ξs Θs rhs) (.or C₁ C₂)) r.s := by
  intro n Ξs Θs rhs C₁ C₂ hdist hmem hJ1 hJ2 hC hg
  obtain ⟨a, t, hsubl, hsame, hndr⟩ := reindex_irr hnd hmem
  have h1 := List.all_eq_true.mp h (a :: t) (famsDG_of_reindex hdist hsubl hsame hndr)
  have h2 := List.all_eq_true.mp h1 (Form.or C₁ C₂) (mem_goalPool.mpr hg)
  try dsimp only at h2
  rw [if_pos ⟨hsame.hJ1 hndr hJ1,
    impGuard_intro (fun A B hAB => hsame.hJ2_strict hJ2 A B hAB),
    ⟨(hsame.upsilon_eq _).mp hC.1, (hsame.upsilon_eq _).mp hC.2⟩, hg⟩] at h2
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h2
  exact ⟨r, findSub_mem hr,
    wSubsumes_trans (wSubsumes_reg (tagLeB_refl _) hsame.ctxOrF.subset)
      (findSub_sub hr)⟩

end Sound

/-! ## 5. The promise checks

The chain branch of each promise clause is checked here; the blocked
branch of `joinAtP`/`joinOrP` is covered by the fallible checks, since
`joinCtxAtP ⊆ joinCtxAtF` and `joinCtxOrP ⊆ joinCtxOrF`
(`ctxAtP_sub_ctxAtF`, `ctxOrP_sub_ctxOrF`). -/

section PChecks

variable (G : Form) (db : List (WRow G))

def chkJoinAtP : Bool :=
  (famsDG G db).all fun l =>
    match l with
    | [] => true
    | a :: t =>
        (pfams G db).all fun lr =>
          match lr with
          | [] => true
          | b :: u =>
              (goalPool G).all fun F =>
                if (∀ i j, i ≠ j → ((a :: t).get i).Ξ ⊆ ((a :: t).get j).Ξ ++ ((a :: t).get j).Θ) ∧
                    (∀ x ∈ unionAll (fun j => impPart (((a :: t).get j).Ξ)),
                      ∀ A B : Form, x = Form.imp A B →
                        A ∈ upsilon (fun j => ((a :: t).get j).C)) ∧
                    (∀ x ∈ unionAll (fun j => circPart (((a :: t).get j).Ξ)),
                      ∀ Y : Form, x = Form.circ Y → ∃ i, Clo (((b :: u).get i).Γ) Y) ∧
                    (∀ i j, ∀ X ∈ ((a :: t).get j).Ξ, Clo (((b :: u).get i).Γ) X) ∧
                    (∀ i, ((b :: u).get i).C = ((b :: u).get 0).C ∧
                      (((b :: u).get i).t = .barren ∨ ∃ W, ((b :: u).get i).t = .chain W ∧
                        Covers (((b :: u).get i).Γ) W (((b :: u).get 0).C))) ∧
                    F.isPrime = true ∧
                    F ∉ unionAll (fun j => atPart (((a :: t).get j).Ξ)) ∧
                    F ∈ sfR G then
                  (findSub db (.reg (.chain (((b :: u).get 0).C))
                    (joinCtxAtP (fun j => ((a :: t).get j).Ξ) (fun j => ((a :: t).get j).Θ)
                      (fun j => ((a :: t).get j).C) F (fun i => ((b :: u).get i).Γ)) F)).isSome
                else true

def chkJoinOrP : Bool :=
  (famsDG G db).all fun l =>
    match l with
    | [] => true
    | a :: t =>
        (pfams G db).all fun lr =>
          match lr with
          | [] => true
          | b :: u =>
              (goalPool G).all fun X =>
                match X with
                | .or C₁ C₂ =>
                    if (∀ i j, i ≠ j → ((a :: t).get i).Ξ ⊆ ((a :: t).get j).Ξ ++ ((a :: t).get j).Θ) ∧
                        (∀ x ∈ unionAll (fun j => impPart (((a :: t).get j).Ξ)),
                          ∀ A B : Form, x = Form.imp A B →
                            A ∈ upsilon (fun j => ((a :: t).get j).C)) ∧
                        (∀ x ∈ unionAll (fun j => circPart (((a :: t).get j).Ξ)),
                          ∀ Y : Form, x = Form.circ Y → ∃ i, Clo (((b :: u).get i).Γ) Y) ∧
                        (∀ i j, ∀ X ∈ ((a :: t).get j).Ξ, Clo (((b :: u).get i).Γ) X) ∧
                        (∀ i, ((b :: u).get i).C = ((b :: u).get 0).C ∧
                          (((b :: u).get i).t = .barren ∨ ∃ W, ((b :: u).get i).t = .chain W ∧
                            Covers (((b :: u).get i).Γ) W (((b :: u).get 0).C))) ∧
                        (C₁ ∈ upsilon (fun j => ((a :: t).get j).C) ∧
                          C₂ ∈ upsilon (fun j => ((a :: t).get j).C)) ∧
                        Form.or C₁ C₂ ∈ sfR G then
                      (findSub db (.reg (.chain (((b :: u).get 0).C))
                        (joinCtxOrP (fun j => ((a :: t).get j).Ξ) (fun j => ((a :: t).get j).Θ)
                          (fun j => ((a :: t).get j).C) (fun i => ((b :: u).get i).Γ))
                        (.or C₁ C₂))).isSome
                    else true
                | _ => true

def chkJoinCircP : Bool :=
  (famsDG G db).all fun l =>
    match l with
    | [] => true
    | a :: t =>
        (pfams G db).all fun lr =>
          match lr with
          | [] => true
          | b :: u =>
              (goalPool G).all fun X =>
                match X with
                | .circ Z =>
                    if (∀ i j, i ≠ j → ((a :: t).get i).Ξ ⊆ ((a :: t).get j).Ξ ++ ((a :: t).get j).Θ) ∧
                        (∀ x ∈ unionAll (fun j => impPart (((a :: t).get j).Ξ)),
                          ∀ A B : Form, x = Form.imp A B →
                            A ∈ upsilon (fun j => ((a :: t).get j).C)) ∧
                        (∀ x ∈ unionAll (fun j => circPart (((a :: t).get j).Ξ)),
                          ∀ Y : Form, x = Form.circ Y → ∃ i, Clo (((b :: u).get i).Γ) Y) ∧
                        (∀ i j, ∀ X ∈ ((a :: t).get j).Ξ, Clo (((b :: u).get i).Γ) X) ∧
                        (∀ i, ((b :: u).get i).C = Z ∧
                          (((b :: u).get i).t = .barren ∨ ∃ W, ((b :: u).get i).t = .chain W ∧
                            Covers (((b :: u).get i).Γ) W Z)) ∧
                        Z ∈ upsilon (fun j => ((a :: t).get j).C) ∧
                        Form.circ Z ∈ sfR G then
                      (findSub db (.reg (.chain Z)
                        (joinCtxOrP (fun j => ((a :: t).get j).Ξ) (fun j => ((a :: t).get j).Θ)
                          (fun j => ((a :: t).get j).C) (fun i => ((b :: u).get i).Γ))
                        (.circ Z))).isSome
                    else true
                | _ => true

end PChecks

section PSound

variable {G : Form} {db : List (WRow G)} (hnd : (db.map (·.s)).Nodup)

include hnd in
theorem chkJoinAtP_sound (hF : chkJoinAtF G db = true) (h : chkJoinAtP G db = true) :
    ∀ {n k : Nat} (Ξs Θs : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (F : Form) (t' : Tag)
    (tps : Fin (k + 1) → Tag) (Δs : Fin (k + 1) → List Form)
    (Ds : Fin (k + 1) → Form),
    (∀ i j, i ≠ j → rhs i ≠ rhs j) →
    k ≤ (dedupF (gCirc G)).length →
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i, (WSeq.reg (tps i) (Δs i) (Ds i)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) →
    (∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) →
      ∃ i, Clo (Δs i) Y) →
    (∀ i j, ∀ X ∈ Ξs j, Clo (Δs i) X) →
    (t' = .blocked ∨ (t' = .chain (Ds 0) ∧ ∀ i, Ds i = Ds 0 ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W (Ds 0)))) →
    F.isPrime → F ∉ unionAll (fun j => atPart (Ξs j)) → F ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg t' (joinCtxAtP Ξs Θs rhs F Δs) F) r.s := by
  intro n k Ξs Θs rhs F t' tps Δs Ds hdist hk hmemI hmemR hJ1 hJ2 hJ5 hJ6 htag hFp hFnot hg
  rcases htag with h0 | hchain
  · -- blocked branch: the fallible check covers it
    subst h0
    obtain ⟨r, hr, hsub⟩ := chkJoinAtF_sound hnd hF Ξs Θs rhs F hdist hmemI hJ1 hJ2 hFp hFnot hg
    exact ⟨r, hr, wSubsumes_trans (wSubsumes_reg (tagLeB_refl _)
      (fun x hx => ctxAtP_sub_ctxAtF hx)) hsub⟩
  · obtain ⟨a, t, hsubl, hsame, hndr⟩ := reindex_irr hnd hmemI
    obtain ⟨b, u, hsublR, hsameR⟩ := reindex_reg hmemR
    have htagG := htagP_re hsameR (Or.inr hchain)
    rcases htagG with hbad | ⟨h0G, hallG⟩
    · rw [hchain.1] at hbad
      exact Tag.noConfusion hbad
    · have h1 := List.all_eq_true.mp h (a :: t) (famsDG_of_reindex hdist hsubl hsame hndr)
      have h2 := List.all_eq_true.mp h1 (b :: u) (pfams_of_reindex hnd hk hsublR hsameR)
      have h3 := List.all_eq_true.mp h2 F (mem_goalPool.mpr hg)
      try dsimp only at h3
      rw [if_pos ⟨hsame.hJ1 hndr hJ1,
        impGuard_intro (fun A B hAB => hsame.hJ2_strict hJ2 A B hAB),
        circGuard_intro (hJ5_re hsame hsameR hJ5),
        hJ7s_re hsame hsameR hJ6, hallG, hFp, hsame.hFnot hFnot, hg⟩] at h3
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h3
      rw [h0G]
      exact ⟨r, findSub_mem hr, wSubsumes_trans (wSubsumes_reg (tagLeB_refl _)
        (ctxAtP_eq hsame hsameR).subset) (findSub_sub hr)⟩

include hnd in
theorem chkJoinOrP_sound (hF : chkJoinOrF G db = true) (h : chkJoinOrP G db = true) :
    ∀ {n k : Nat} (Ξs Θs : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (C₁ C₂ : Form) (t' : Tag)
    (tps : Fin (k + 1) → Tag) (Δs : Fin (k + 1) → List Form)
    (Ds : Fin (k + 1) → Form),
    (∀ i j, i ≠ j → rhs i ≠ rhs j) →
    k ≤ (dedupF (gCirc G)).length →
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i, (WSeq.reg (tps i) (Δs i) (Ds i)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) →
    (∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) →
      ∃ i, Clo (Δs i) Y) →
    (∀ i j, ∀ X ∈ Ξs j, Clo (Δs i) X) →
    (t' = .blocked ∨ (t' = .chain (Ds 0) ∧ ∀ i, Ds i = Ds 0 ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W (Ds 0)))) →
    (C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs) →
    Form.or C₁ C₂ ∈ sfR G →
    ∃ r ∈ db, WSubsumes (.reg t' (joinCtxOrP Ξs Θs rhs Δs) (.or C₁ C₂)) r.s := by
  intro n k Ξs Θs rhs C₁ C₂ t' tps Δs Ds hdist hk hmemI hmemR hJ1 hJ2 hJ5 hJ6 htag hC hg
  rcases htag with h0 | hchain
  · subst h0
    obtain ⟨r, hr, hsub⟩ := chkJoinOrF_sound hnd hF Ξs Θs rhs C₁ C₂ hdist hmemI hJ1 hJ2 hC hg
    exact ⟨r, hr, wSubsumes_trans (wSubsumes_reg (tagLeB_refl _)
      (fun x hx => ctxOrP_sub_ctxOrF hx)) hsub⟩
  · obtain ⟨a, t, hsubl, hsame, hndr⟩ := reindex_irr hnd hmemI
    obtain ⟨b, u, hsublR, hsameR⟩ := reindex_reg hmemR
    have htagG := htagP_re hsameR (Or.inr hchain)
    rcases htagG with hbad | ⟨h0G, hallG⟩
    · rw [hchain.1] at hbad
      exact Tag.noConfusion hbad
    · have h1 := List.all_eq_true.mp h (a :: t) (famsDG_of_reindex hdist hsubl hsame hndr)
      have h2 := List.all_eq_true.mp h1 (b :: u) (pfams_of_reindex hnd hk hsublR hsameR)
      have h3 := List.all_eq_true.mp h2 (Form.or C₁ C₂) (mem_goalPool.mpr hg)
      try dsimp only at h3
      rw [if_pos ⟨hsame.hJ1 hndr hJ1,
        impGuard_intro (fun A B hAB => hsame.hJ2_strict hJ2 A B hAB),
        circGuard_intro (hJ5_re hsame hsameR hJ5),
        hJ7s_re hsame hsameR hJ6, hallG,
        ⟨(hsame.upsilon_eq _).mp hC.1, (hsame.upsilon_eq _).mp hC.2⟩, hg⟩] at h3
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h3
      rw [h0G]
      exact ⟨r, findSub_mem hr, wSubsumes_trans (wSubsumes_reg (tagLeB_refl _)
        (ctxOrP_eq hsame hsameR).subset) (findSub_sub hr)⟩

include hnd in
theorem chkJoinCircP_sound (h : chkJoinCircP G db = true) :
    ∀ {n k : Nat} (Ξs Θs : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (Z : Form)
    (tps : Fin (k + 1) → Tag) (Δs : Fin (k + 1) → List Form)
    (Ds : Fin (k + 1) → Form),
    (∀ i j, i ≠ j → rhs i ≠ rhs j) →
    k ≤ (dedupF (gCirc G)).length →
    (∀ j, (WSeq.irr (Ξs j) (Θs j) (rhs j)) ∈ db.map (·.s)) →
    (∀ i, (WSeq.reg (tps i) (Δs i) (Ds i)) ∈ db.map (·.s)) →
    (∀ i j, i ≠ j → Ξs i ⊆ Ξs j ++ Θs j) →
    (∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (Ξs j)) →
      A ∈ upsilon rhs) →
    (∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) →
      ∃ i, Clo (Δs i) Y) →
    (∀ i j, ∀ X ∈ Ξs j, Clo (Δs i) X) →
    (∀ i, Ds i = Z ∧
      (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W Z)) →
    Z ∈ upsilon rhs → Form.circ Z ∈ sfR G →
    ∃ r ∈ db, WSubsumes
      (.reg (.chain Z) (joinCtxOrP Ξs Θs rhs Δs) (.circ Z)) r.s := by
  intro n k Ξs Θs rhs Z tps Δs Ds hdist hk hmemI hmemR hJ1 hJ2 hJ5 hJ6 hDs hZ hg
  obtain ⟨a, t, hsubl, hsame, hndr⟩ := reindex_irr hnd hmemI
  obtain ⟨b, u, hsublR, hsameR⟩ := reindex_reg hmemR
  have hZ' : Z ∈ (upsilon fun j => ((a :: t).get j).C) := (hsame.upsilon_eq Z).mp hZ
  have hDsG := hDsZ_re hsameR hDs
  have h1 := List.all_eq_true.mp h (a :: t) (famsDG_of_reindex hdist hsubl hsame hndr)
  have h2 := List.all_eq_true.mp h1 (b :: u) (pfams_of_reindex hnd hk hsublR hsameR)
  have h3 := List.all_eq_true.mp h2 (Form.circ Z) (mem_goalPool.mpr hg)
  try dsimp only at h3
  rw [if_pos ⟨hsame.hJ1 hndr hJ1,
    impGuard_intro (fun A B hAB => hsame.hJ2_strict hJ2 A B hAB),
    circGuard_intro (hJ5_re hsame hsameR hJ5),
    hJ7s_re hsame hsameR hJ6, hDsG, hZ', hg⟩] at h3
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h3
  exact ⟨r, findSub_mem hr, wSubsumes_trans (wSubsumes_reg (tagLeB_refl _)
    (ctxOrP_eq hsame hsameR).subset) (findSub_sub hr)⟩

end PSound

/-! ## 6. The join half of the checker -/

def chkJoins (G : Form) (db : List (WRow G)) : Bool :=
  chkJoinAt G db && chkJoinOr G db && chkJoinCirc G db && chkJoinAtF G db &&
    chkJoinOrF G db && chkJoinAtP G db && chkJoinOrP G db && chkJoinCircP G db

theorem chkJoins_split {G : Form} {db : List (WRow G)} (h : chkJoins G db = true) :
    chkJoinAt G db = true ∧ chkJoinOr G db = true ∧ chkJoinCirc G db = true ∧
    chkJoinAtF G db = true ∧ chkJoinOrF G db = true ∧ chkJoinAtP G db = true ∧
    chkJoinOrP G db = true ∧ chkJoinCircP G db = true := by
  simp only [chkJoins, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2,
    h.1.1.2, h.1.2, h.2⟩

/-! ## Pins -/

/-- info: 'FRJ.Arity.chkJoinAt_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chkJoinAt_sound

/-- info: 'FRJ.Arity.chkJoinCirc_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chkJoinCirc_sound

/-- info: 'FRJ.Arity.chkJoinAtP_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chkJoinAtP_sound

/-- info: 'FRJ.Arity.chkJoinCircP_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chkJoinCircP_sound

end FRJ.Arity
