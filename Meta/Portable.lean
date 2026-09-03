/-
# `Meta.Portable` — the handful of Mathlib facts the runtime closure needs, proved locally

`lake exe pll` must not require Mathlib: it is an untrusted engine plus a
verified Boolean check, and a user running the decider should not build a
mathematics library first (Matthew, 2026-09-03).  Measured that day: ANY
Mathlib import except `Mathlib.Tactic.Lemma` drags the same ~1307-module
foundation, so the cost is all-or-nothing — the closure is either
Mathlib-free or it is not.

Everything the closure needed was in core or Batteries EXCEPT the five
facts below.  They are stated and proved here with core tactics only, so
the whole chain — engine, `checkClosed`, `decideOfStore`, the output
layer — builds against Batteries alone.

These are deliberately the SAME statements as their Mathlib namesakes
(`Fin.succAbove`, `Fin.exists_succAbove_eq`, `Fin.succ_injective`,
`Fin.succAbove_right_injective`, `List.mem_sublists`), so a module can
drop its Mathlib import and keep its proofs verbatim.  Mathlib's
`Fin.succAbove_ne` leaks `Classical.choice` under this import set, which
is why `wip/b1b2_lemmas.lean` already carried the hand proof
`succAbove_ne'`; the definition here is the same function.
-/
import Batteries

namespace Fin

/-- `p.succAbove i` embeds `Fin n` into `Fin (n+1)` missing `p`. -/
def succAbove {n : Nat} (p : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  if i.castSucc < p then i.castSucc else i.succ

theorem succ_injective (n : Nat) : Function.Injective (Fin.succ : Fin n → Fin (n + 1)) := by
  intro a b h
  apply Fin.ext
  have : a.val + 1 = b.val + 1 := by
    have := congrArg Fin.val h
    simpa [Fin.val_succ] using this
  omega

theorem succAbove_right_injective {n : Nat} {p : Fin (n + 1)} :
    Function.Injective p.succAbove := by
  intro a b h
  unfold succAbove at h
  apply Fin.ext
  by_cases ha : a.castSucc < p <;> by_cases hb : b.castSucc < p <;>
    simp only [ha, hb, if_true, if_false, ite_true, ite_false] at h <;>
    · have hv := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at hv
      have hpa := ha; have hpb := hb
      simp only [Fin.lt_def, Fin.val_castSucc] at hpa hpb
      omega

/-- Every index other than `p` is hit by `p.succAbove`. -/
theorem exists_succAbove_eq {n : Nat} {p i : Fin (n + 1)} (h : i ≠ p) :
    ∃ j : Fin n, p.succAbove j = i := by
  have hne : i.val ≠ p.val := fun hv => h (Fin.ext hv)
  by_cases hlt : i.val < p.val
  · have hin : i.val < n := by omega
    refine ⟨⟨i.val, hin⟩, ?_⟩
    have : (⟨i.val, hin⟩ : Fin n).castSucc < p := by
      simp only [Fin.lt_def, Fin.val_castSucc]; omega
    unfold succAbove; rw [if_pos this]; exact Fin.ext rfl
  · have hgt : p.val < i.val := by omega
    have hin : i.val - 1 < n := by omega
    refine ⟨⟨i.val - 1, hin⟩, ?_⟩
    have hnot : ¬ ((⟨i.val - 1, hin⟩ : Fin n).castSucc < p) := by
      simp only [Fin.lt_def, Fin.val_castSucc]; omega
    unfold succAbove; rw [if_neg hnot]
    apply Fin.ext
    simp only [Fin.val_succ]
    omega

end Fin

namespace List

/-- **Mathlib's `List.mem_sublists`, proved locally.**  Batteries defines
`sublists` by `foldr (fun a acc => acc.flatMap fun x => [x, a :: x])
[[]]`; both directions are used in the development (`Saturate.lean` needs
`.mpr`, `Search.lean` the containment). -/
theorem mem_sublists {α : Type _} :
    ∀ {l a : List α}, a ∈ l.sublists ↔ a.Sublist l
  | [], a => by
      constructor
      · intro h
        simp only [List.sublists, List.foldr_nil, List.mem_cons,
          List.not_mem_nil, or_false] at h
        subst h; exact List.Sublist.refl _
      · intro h
        have : a = [] := List.eq_nil_of_sublist_nil h
        subst this
        simp [List.sublists]
  | b :: l, a => by
      constructor
      · intro h
        simp only [List.sublists, List.foldr_cons, List.mem_flatMap,
          List.mem_cons, List.not_mem_nil, or_false] at h
        obtain ⟨x, hx, hax⟩ := h
        have hxl : x.Sublist l := mem_sublists.mp (by simpa only [List.sublists] using hx)
        rcases hax with rfl | rfl
        · exact hxl.cons _
        · exact hxl.cons₂ _
      · intro h
        simp only [List.sublists, List.foldr_cons, List.mem_flatMap,
          List.mem_cons, List.not_mem_nil, or_false]
        cases h with
        | cons _ h' =>
            exact ⟨a, by simpa only [List.sublists] using mem_sublists.mpr h', Or.inl rfl⟩
        | cons_cons _ h' =>
            rename_i a'
            exact ⟨a', by simpa only [List.sublists] using mem_sublists.mpr h', Or.inr rfl⟩

/-- **Mathlib's `List.sublistsLen`, defined locally**: the sublists of a
given length, generated DIRECTLY.

The first attempt here filtered `l.sublists` by length, which is
correct but computes all `2^|l|` sublists per call.  `famsDG`/`pfams`
(`wip/check_join.lean`) call it once per length, so `checkClosed` went
from milliseconds to not finishing in two minutes on
`(◯p ∧ ◯q) ⊃ ◯(p ∧ q)` — caught by re-running the batch, 2026-09-03.
This recursion emits only the lists of the requested length. -/
def sublistsLen {α : Type _} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | n + 1, a :: l => (sublistsLen n l).map (a :: ·) ++ sublistsLen (n + 1) l

theorem mem_sublistsLen {α : Type _} :
    ∀ {n : Nat} {l a : List α}, a ∈ sublistsLen n l ↔ a.Sublist l ∧ a.length = n
  | 0, l, a => by
      -- `simp only [sublistsLen]` unfolds by the equation lemmas; every
      -- other step is a term proof.  A full `simp` here pulls
      -- `Classical.choice` into the checker's soundness under this import
      -- set (caught by the downstream pins twice, 2026-09-03).
      simp only [sublistsLen, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · intro h
        subst h
        exact ⟨List.nil_sublist l, rfl⟩
      · intro ⟨_, h2⟩
        exact List.eq_nil_iff_length_eq_zero.mpr h2
  | _ + 1, [], a => by
      simp only [sublistsLen, List.not_mem_nil, false_iff, not_and]
      intro h1
      have ha : a = [] := List.eq_nil_of_sublist_nil h1
      subst ha
      exact fun h2 => absurd h2.symm (Nat.succ_ne_zero _)
  | n + 1, b :: l, a => by
      simp only [sublistsLen, List.mem_append, List.mem_map]
      constructor
      · intro h
        rcases h with ⟨x, hx, rfl⟩ | h
        · have hx' := mem_sublistsLen.mp hx
          refine ⟨hx'.1.cons₂ _, ?_⟩
          rw [List.length_cons, hx'.2]
        · have h' := mem_sublistsLen.mp h
          exact ⟨h'.1.cons _, h'.2⟩
      · intro ⟨h1, h2⟩
        cases h1 with
        | cons _ h' => exact Or.inr (mem_sublistsLen.mpr ⟨h', h2⟩)
        | cons_cons _ h' =>
            rename_i a'
            refine Or.inl ⟨a', mem_sublistsLen.mpr ⟨h', ?_⟩, rfl⟩
            rw [List.length_cons] at h2
            omega

/-- A member of `l.sublists` is contained in `l`.

Batteries defines `sublists` by `foldr (fun a acc => acc.flatMap fun x =>
[x, a :: x]) [[]]`; this is the containment half of Mathlib's
`mem_sublists`, which is all the search needs (`FRJ/Gbu/W/Search.lean`
uses `(mem_sublists.mp h).subset`). -/
theorem mem_sublists_subset {α : Type _} :
    ∀ {l a : List α}, a ∈ l.sublists → a ⊆ l
  | [], a, h => by
      simp only [List.sublists, List.foldr_nil, List.mem_cons,
        List.not_mem_nil, or_false] at h
      subst h; exact List.Subset.refl _
  | b :: l, a, h => by
      simp only [List.sublists, List.foldr_cons, List.mem_flatMap,
        List.mem_cons, List.not_mem_nil, or_false] at h
      obtain ⟨x, hx, hax⟩ := h
      have hxl : x ⊆ l := by
        have : x ∈ (l.sublists) := by
          simpa only [List.sublists] using hx
        exact mem_sublists_subset this
      rcases hax with rfl | rfl
      · exact fun _ hy => List.mem_cons_of_mem _ (hxl hy)
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hxl hy')

end List
