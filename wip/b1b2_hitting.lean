/-
# The bounded hitting cut for promise families

`wip/b1b2_lemmas.lean` §8 proves that a reindexing `e : Fin (m+1) → Fin (k+1)`
of a promise family `Δs : Fin (k+1) → List Form` which hits every witnessed
modal formula,

    ∀ Y, ◯Y ∈ ⋃ⱼ (Ξⱼ)^◯ ++ ⋂ⱼ (Θⱼ)^◯ → (∃ i, Cl(Δᵢ) ∋ Y) → ∃ i', Cl(Δ_{e i'}) ∋ Y

makes the promise-join conclusion contexts grow (`joinCtxAtP_cut`,
`joinCtxOrP_cut`).  This file supplies the missing half: such an `e` EXISTS,
with `m` bounded by a quantity that depends on the goal formula `G` alone,

    m ≤ |dedupF (Ĝ^◯)|,

so a checker may enumerate promise sub-families of bounded size.

The construction is the obvious one.  Let

    M := ⋃ⱼ (Ξⱼ)^◯ ++ ⋂ⱼ (Θⱼ)^◯

be the list of modal formulas the full family must witness, and let `W` be the
repetition-free sublist of those members of `M` that ARE witnessed.  Choosing
for each `◯Y ∈ W` the first index `i` with `Cl(Δᵢ) ∋ Y` gives a list `chosen`
of indices; `e` enumerates it.  The bound is a counting argument: `W` is
`Nodup`, and each of its members is a `◯`-formula of `Ĝ`, hence a member of
`Ĝ^◯` — so `|W| ≤ |dedupF (Ĝ^◯)|` by `length_le_of_nodup_subset`.

Everything is choice-free; the pins are `[propext, Quot.sound]`.
-/
import wip.b1b2_lemmas
import FRJ.Gbu.W.Saturate

open FRJ Form FRJ.Gbu.W

namespace FRJ.Arity

/-! ## 1. `dedupF` is repetition-free

`FRJ/Gbu/W/Saturate.lean` proves `mem_dedupF`; the `Nodup` half is not
recorded there and is needed for the counting step. -/

theorem dedupF_nodup : ∀ l : List Form, (dedupF l).Nodup
  | [] => List.nodup_nil
  | x :: xs => by
      simp only [dedupF]
      by_cases hx : x ∈ xs
      · rw [if_pos hx]
        exact dedupF_nodup xs
      · rw [if_neg hx]
        exact List.nodup_cons.mpr
          ⟨fun h => hx (mem_dedupF.mp h), dedupF_nodup xs⟩

/-! ## 2. A `◯`-formula of `Ĝ` lies in `Ĝ^◯`

`gHat G = gAt G ++ gImp G ++ gCirc G`, and the first two zones are filters by
`isPV` and `isImp`, which no `◯`-formula passes. -/

theorem mem_gCirc_of_gHat {G Y : Form} (h : Form.circ Y ∈ gHat G) :
    Form.circ Y ∈ gCirc G := by
  simp only [gHat, List.mem_append] at h
  rcases h with (h | h) | h
  · exact absurd (List.mem_filter.mp h).2 (by simp [Form.isPV])
  · exact absurd (List.mem_filter.mp h).2 (by simp [Form.isImp])
  · exact h

/-! ## 3. The first witness

`isWitB Δs X` decides whether `X` is a `◯`-formula `◯Y` witnessed by some
member of the family; `witOf Δs X` is the first such index (and `0` when
there is none, a value the hitting proof never reads). -/

section Wit

variable {k : Nat}

/-- The first index of the family whose closure contains `Y`, or `0`. -/
def witIdx (Δs : Fin (k + 1) → List Form) (Y : Form) : Fin (k + 1) :=
  ((List.finRange (k + 1)).find? (fun i => cloB (Δs i) Y)).getD 0

/-- The first witnessing index of a modal formula `◯Y`; `0` off the `◯`s. -/
def witOf (Δs : Fin (k + 1) → List Form) : Form → Fin (k + 1)
  | .circ Y => witIdx Δs Y
  | _ => 0

/-- `X` is a modal formula witnessed by the family. -/
def isWitB (Δs : Fin (k + 1) → List Form) : Form → Bool
  | .circ Y => (List.finRange (k + 1)).any (fun i => cloB (Δs i) Y)
  | _ => false

theorem isWitB_shape {Δs : Fin (k + 1) → List Form} {X : Form}
    (h : isWitB Δs X = true) : ∃ Y, X = Form.circ Y := by
  cases X with
  | circ Y => exact ⟨Y, rfl⟩
  | _ => exact absurd h (by simp [isWitB])

theorem isWitB_of_clo {Δs : Fin (k + 1) → List Form} {Y : Form}
    (i : Fin (k + 1)) (h : Clo (Δs i) Y) : isWitB Δs (Form.circ Y) = true := by
  simp only [isWitB, List.any_eq_true]
  exact ⟨i, List.mem_finRange i, cloB_iff.mpr h⟩

/-- The chosen index really is a witness. -/
theorem clo_witIdx {Δs : Fin (k + 1) → List Form} {Y : Form}
    (h : ∃ i, Clo (Δs i) Y) : Clo (Δs (witIdx Δs Y)) Y := by
  obtain ⟨i, hi⟩ := h
  cases hf : (List.finRange (k + 1)).find? (fun i => cloB (Δs i) Y) with
  | none =>
      exact absurd (cloB_iff.mpr hi)
        (List.find?_eq_none.mp hf i (List.mem_finRange i))
  | some j =>
      have hp : cloB (Δs j) Y = true :=
        List.find?_some (p := fun i => cloB (Δs i) Y)
          (l := List.finRange (k + 1)) (a := j) hf
      have hj : witIdx Δs Y = j := by simp [witIdx, hf]
      rw [hj]
      exact cloB_iff.mp hp

end Wit

/-! ## 4. Enumerating a list of indices

A finite list of indices is the image of a map out of `Fin (m+1)` with
`m + 1 = |list|` (and `m = 0`, `e = const 0`, when the list is empty — the
hitting property is then vacuous, since nothing is witnessed). -/

theorem exists_reindex {k : Nat} (chosen : List (Fin (k + 1))) {b : Nat}
    (hb : chosen.length ≤ b) :
    ∃ (m : Nat) (e : Fin (m + 1) → Fin (k + 1)),
      m ≤ b ∧ ∀ x ∈ chosen, ∃ i', e i' = x := by
  cases chosen with
  | nil =>
      exact ⟨0, fun _ => 0, Nat.zero_le b, fun _ hx => absurd hx List.not_mem_nil⟩
  | cons c cs =>
      refine ⟨cs.length, fun i' => (c :: cs).getD i'.val c, Nat.le_of_succ_le hb, ?_⟩
      intro x hx
      obtain ⟨q, hq, hget⟩ := List.getElem_of_mem hx
      refine ⟨⟨q, hq⟩, ?_⟩
      show (c :: cs).getD q c = x
      rw [← hget]
      exact (List.getElem_eq_getD c).symm

/-! ## 5. The bounded hitting cut

The statement B2′ needs: a reindexing exists, with `m` bounded by a function
of the goal formula alone.  The wellformedness hypothesis is the one the
FRJW rules maintain — every premise zone is a sublist of `Ĝ`. -/

/-- **The bounded hitting cut.**  For a promise family `Δs` and premise zones
`Ξs`, `Θs` inside `Ĝ`, there is a sub-family `Δ ∘ e` of arity at most
`|dedupF (Ĝ^◯)| + 1` that witnesses every modal formula of
`⋃ⱼ (Ξⱼ)^◯ ++ ⋂ⱼ (Θⱼ)^◯` the full family witnesses — the hypothesis of
`joinCtxAtP_cut` and `joinCtxOrP_cut`. -/
theorem hittingCut (G : Form) {n k : Nat} {Ξs Θs : Fin (n + 1) → List Form}
    {Δs : Fin (k + 1) → List Form}
    (hwf : ∀ j, Ξs j ⊆ gHat G ∧ Θs j ⊆ gHat G) :
    ∃ (m : Nat) (e : Fin (m + 1) → Fin (k + 1)),
      m ≤ (dedupF (gCirc G)).length ∧
      ∀ Y, Form.circ Y ∈ unionAll (fun j => circPart (Ξs j)) ++
          interAll (fun j => circPart (Θs j)) →
        (∃ i, Clo (Δs i) Y) → ∃ i', Clo (Δs (e i')) Y := by
  -- the modal formulas the full family must witness, without repeats,
  -- restricted to those actually witnessed
  set M : List Form := unionAll (fun j => circPart (Ξs j)) ++
    interAll (fun j => circPart (Θs j)) with hMdef
  set W : List Form := (dedupF M).filter (isWitB Δs) with hWdef
  -- (a) `W` is repetition-free
  have hnodup : W.Nodup := List.Nodup.filter _ (dedupF_nodup M)
  -- (b) every member of `W` is a `◯`-formula of `Ĝ`
  have hsub : W ⊆ dedupF (gCirc G) := by
    intro x hx
    have hx1 : x ∈ dedupF M := (List.mem_filter.mp hx).1
    have hx2 : isWitB Δs x = true := (List.mem_filter.mp hx).2
    obtain ⟨Y, rfl⟩ := isWitB_shape hx2
    have hxM : Form.circ Y ∈ M := mem_dedupF.mp hx1
    refine mem_dedupF.mpr (mem_gCirc_of_gHat ?_)
    rcases List.mem_append.mp hxM with h | h
    · obtain ⟨j, hj⟩ := mem_unionAll.mp h
      exact (hwf j).1 (List.mem_filter.mp hj).1
    · exact (hwf 0).2 (List.mem_filter.mp (mem_interAll.mp h 0)).1
  -- (c) the counting bound
  have hlen : (W.map (witOf Δs)).length ≤ (dedupF (gCirc G)).length := by
    rw [List.length_map]
    exact length_le_of_nodup_subset hnodup hsub
  obtain ⟨m, e, hmb, he⟩ := exists_reindex (W.map (witOf Δs)) hlen
  refine ⟨m, e, hmb, ?_⟩
  intro Y hY hex
  have hWmem : Form.circ Y ∈ W := by
    obtain ⟨i, hi⟩ := hex
    exact List.mem_filter.mpr ⟨mem_dedupF.mpr hY, isWitB_of_clo i hi⟩
  obtain ⟨i', hi'⟩ := he _ (List.mem_map_of_mem hWmem)
  refine ⟨i', ?_⟩
  rw [hi']
  exact clo_witIdx hex

/-! ## Pins

The target is `[propext, Quot.sound]` — no `Classical.choice`.  The two
list-only helpers land strictly below it, on `[propext]` alone. -/

/-- info: 'FRJ.Arity.dedupF_nodup' depends on axioms: [propext] -/
#guard_msgs in
#print axioms dedupF_nodup

/-- info: 'FRJ.Arity.mem_gCirc_of_gHat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mem_gCirc_of_gHat

/-- info: 'FRJ.Arity.clo_witIdx' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms clo_witIdx

/-- info: 'FRJ.Arity.exists_reindex' depends on axioms: [propext] -/
#guard_msgs in
#print axioms exists_reindex

/-- info: 'FRJ.Arity.hittingCut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hittingCut

end FRJ.Arity
