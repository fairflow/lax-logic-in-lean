import wip.p2llInterp

/-!
# The round trips: RTP and RTJ

File 8 of the P2LL definability campaign (`wip/p2ll-STATUS.md` §9): the
proofs of `RoundTripP2LL` and `RoundTripJ` of `wip/p2llStatements.lean`, in
their fragment-restricted wording of 2026-10-25.

    RTP   LC φ, allJFree φ   ⟹   φ ⊢_P2LL (φ°)*   and   (φ°)* ⊢_P2LL φ      (`rtpD`, `roundTripP2LL`)
    RTJ   LC φ, circFree φ   ⟹   Θ ; φ ⊢_J (φ*)°  and   Θ ; (φ*)° ⊢_J φ     (`rtjD`, `roundTripJ`)

Both are by induction on the SIZE of `φ` (`size`), which opening with an atom
preserves (`size_opn_fvar`), so that the binder cases can use the hypothesis
on the opened body; the two directions are proved together (the `→` case
needs the converse on the antecedent).  Cut is `→I` followed by `→E`
(`LaxND2.cut1`, `JND.cut1`).  No fresh name is chosen anywhere: the binder
cases open with the eigenvariable of the rule's own cofinite premise.

`(−)°` followed by `(−)*` is homomorphic except at `◯`, where
`(◯°χ)* = ∀°p.((χ* → p) → p)` (`rel_circJ`, through `rel_shiftAt`), so the
`◯` case of RTP is C7 (`LaxND2.circ_to_circNuc`, `circNuc_to_circ`) composed
with the hypothesis on `χ`.  `(−)*` followed by `(−)°` is homomorphic except
at `∀°`, where `(∀°.ψ)*° = ∀p.((◯°p → p) → ψ*°)`; the `∀°` case of RTJ
instantiates `∀°.ψ` at `◯°s` (a J-formula by the `allJ` and `imp` clauses,
`isJ_circJ_fvar`) and replaces `◯°s` by `s` under the hypothesis `◯°s → s`
with the unit law `s → ◯°s`: the substitution of equivalents `JND.congrD`,
stated for `openRec k` at every `k` so that its own binder case needs no
fresh name either.
-/

namespace P2LL

open Fm

/-! ## Size, and the fragments under opening with an atom -/

def size : Fm → Nat
  | .fvar _ => 0
  | .bvar _ => 0
  | .bot => 0
  | .and φ ψ => size φ + size ψ + 1
  | .or φ ψ => size φ + size ψ + 1
  | .imp φ ψ => size φ + size ψ + 1
  | .circ φ => size φ + 1
  | .all ψ => size ψ + 1
  | .allJ ψ => size ψ + 1

theorem size_openRec_fvar (s : String) :
    ∀ (k : Nat) (φ : Fm), size (openRec k (.fvar s) φ) = size φ
  | _, .fvar _ => rfl
  | k, .bvar n => by
    show size (if n = k then Fm.fvar s else Fm.bvar n) = 0
    split <;> rfl
  | _, .bot => rfl
  | k, .and φ ψ => by
    show size (openRec k (.fvar s) φ) + size (openRec k (.fvar s) ψ) + 1 = size φ + size ψ + 1
    rw [size_openRec_fvar s k φ, size_openRec_fvar s k ψ]
  | k, .or φ ψ => by
    show size (openRec k (.fvar s) φ) + size (openRec k (.fvar s) ψ) + 1 = size φ + size ψ + 1
    rw [size_openRec_fvar s k φ, size_openRec_fvar s k ψ]
  | k, .imp φ ψ => by
    show size (openRec k (.fvar s) φ) + size (openRec k (.fvar s) ψ) + 1 = size φ + size ψ + 1
    rw [size_openRec_fvar s k φ, size_openRec_fvar s k ψ]
  | k, .circ φ => by
    show size (openRec k (.fvar s) φ) + 1 = size φ + 1
    rw [size_openRec_fvar s k φ]
  | k, .all ψ => by
    show size (openRec (k + 1) (.fvar s) ψ) + 1 = size ψ + 1
    rw [size_openRec_fvar s (k + 1) ψ]
  | k, .allJ ψ => by
    show size (openRec (k + 1) (.fvar s) ψ) + 1 = size ψ + 1
    rw [size_openRec_fvar s (k + 1) ψ]

theorem size_opn_fvar (ψ : Fm) (s : String) : size (ψ.opn (.fvar s)) = size ψ :=
  size_openRec_fvar s 0 ψ

theorem allJFree_openRec_fvar (s : String) :
    ∀ (k : Nat) (φ : Fm), allJFree φ → allJFree (openRec k (.fvar s) φ)
  | _, .fvar _, _ => trivial
  | k, .bvar n, _ => by
    show allJFree (if n = k then Fm.fvar s else Fm.bvar n)
    split <;> trivial
  | _, .bot, _ => trivial
  | k, .and φ ψ, h => ⟨allJFree_openRec_fvar s k φ h.1, allJFree_openRec_fvar s k ψ h.2⟩
  | k, .or φ ψ, h => ⟨allJFree_openRec_fvar s k φ h.1, allJFree_openRec_fvar s k ψ h.2⟩
  | k, .imp φ ψ, h => ⟨allJFree_openRec_fvar s k φ h.1, allJFree_openRec_fvar s k ψ h.2⟩
  | k, .circ φ, h => allJFree_openRec_fvar s k φ h
  | k, .all ψ, h => allJFree_openRec_fvar s (k + 1) ψ h
  | _, .allJ _, h => h.elim

theorem allJFree_opn_fvar {ψ : Fm} (s : String) (h : allJFree ψ) : allJFree (ψ.opn (.fvar s)) :=
  allJFree_openRec_fvar s 0 ψ h

theorem circFree_openRec_fvar (s : String) :
    ∀ (k : Nat) (φ : Fm), circFree φ → circFree (openRec k (.fvar s) φ)
  | _, .fvar _, _ => trivial
  | k, .bvar n, _ => by
    show circFree (if n = k then Fm.fvar s else Fm.bvar n)
    split <;> trivial
  | _, .bot, _ => trivial
  | k, .and φ ψ, h => ⟨circFree_openRec_fvar s k φ h.1, circFree_openRec_fvar s k ψ h.2⟩
  | k, .or φ ψ, h => ⟨circFree_openRec_fvar s k φ h.1, circFree_openRec_fvar s k ψ h.2⟩
  | k, .imp φ ψ, h => ⟨circFree_openRec_fvar s k φ h.1, circFree_openRec_fvar s k ψ h.2⟩
  | _, .circ _, h => h.elim
  | k, .all ψ, h => circFree_openRec_fvar s (k + 1) ψ h
  | k, .allJ ψ, h => circFree_openRec_fvar s (k + 1) ψ h

theorem circFree_opn_fvar {ψ : Fm} (s : String) (h : circFree ψ) : circFree (ψ.opn (.fvar s)) :=
  circFree_openRec_fvar s 0 ψ h

theorem lt_of_bin_left {a b n : Nat} (h : a + b + 1 < n + 1) : a < n :=
  Nat.lt_of_le_of_lt (Nat.le_add_right a b) (Nat.lt_of_succ_lt_succ h)

theorem lt_of_bin_right {a b n : Nat} (h : a + b + 1 < n + 1) : b < n :=
  Nat.lt_of_le_of_lt (Nat.le_add_left b a) (Nat.lt_of_succ_lt_succ h)

theorem lt_of_un {a n : Nat} (h : a + 1 < n + 1) : a < n := Nat.lt_of_succ_lt_succ h

/-! ## `(−)*` and `shiftAt`: `(◯°χ)* = ∀°p.((χ* → p) → p)` -/

theorem rel_shiftAt : ∀ (d : Nat) (φ : Fm), rel (shiftAt d φ) = shiftAt d (rel φ)
  | _, .fvar _ => rfl
  | d, .bvar n => by
    show rel (if d ≤ n then Fm.bvar (n + 1) else Fm.bvar n) =
      (if d ≤ n then Fm.bvar (n + 1) else Fm.bvar n)
    split <;> rfl
  | _, .bot => rfl
  | d, .and φ ψ => by
    show Fm.and (rel (shiftAt d φ)) (rel (shiftAt d ψ)) = Fm.and (shiftAt d (rel φ)) (shiftAt d (rel ψ))
    rw [rel_shiftAt d φ, rel_shiftAt d ψ]
  | d, .or φ ψ => by
    show Fm.or (rel (shiftAt d φ)) (rel (shiftAt d ψ)) = Fm.or (shiftAt d (rel φ)) (shiftAt d (rel ψ))
    rw [rel_shiftAt d φ, rel_shiftAt d ψ]
  | d, .imp φ ψ => by
    show Fm.imp (rel (shiftAt d φ)) (rel (shiftAt d ψ)) = Fm.imp (shiftAt d (rel φ)) (shiftAt d (rel ψ))
    rw [rel_shiftAt d φ, rel_shiftAt d ψ]
  | d, .circ φ => by
    show Fm.circ (rel (shiftAt d φ)) = Fm.circ (shiftAt d (rel φ))
    rw [rel_shiftAt d φ]
  | d, .all ψ => by
    show Fm.all (rel (shiftAt (d + 1) ψ)) = Fm.all (shiftAt (d + 1) (rel ψ))
    rw [rel_shiftAt (d + 1) ψ]
  | d, .allJ ψ => by
    show allNuc (rel (shiftAt (d + 1) ψ)) =
      Fm.all (.imp (.imp (.circ (if d + 1 ≤ 0 then Fm.bvar 1 else Fm.bvar 0))
        (if d + 1 ≤ 0 then Fm.bvar 1 else Fm.bvar 0)) (shiftAt (d + 1) (rel ψ)))
    rw [if_neg (Nat.not_succ_le_zero d : ¬ d + 1 ≤ 0), rel_shiftAt (d + 1) ψ]
    rfl

theorem rel_rpBody (χ : Fm) : rel (rpBody χ) = rpBody (rel χ) := by
  show Fm.imp (.imp (rel (shiftAt 0 χ)) (.bvar 0)) (.bvar 0) =
    Fm.imp (.imp (shiftAt 0 (rel χ)) (.bvar 0)) (.bvar 0)
  rw [rel_shiftAt 0 χ]

/-- `(◯°χ)* = ∀°p.((χ* → p) → p)`. -/
theorem rel_circJ (χ : Fm) : rel (circJ χ) = circNuc (rel χ) := by
  show allNuc (rel (rpBody χ)) = allNuc (rpBody (rel χ))
  rw [rel_rpBody χ]

/-- `((◯φ)°)* = ∀°p.(((φ°)* → p) → p)`. -/
theorem rel_toJ_circ (φ : Fm) : rel (toJ (.circ φ)) = circNuc (rel (toJ φ)) := rel_circJ (toJ φ)

/-- `((ψ^s)°)* = ((ψ°)*)^s`. -/
theorem rt_opn_fvar (ψ : Fm) (s : String) :
    rel (toJ (ψ.opn (.fvar s))) = (rel (toJ ψ)).opn (.fvar s) := by
  rw [toJ_opn_fvar ψ s, rel_opn_fvar (toJ ψ) s]

theorem lc_rt {φ : Fm} (h : LC φ) : LC (rel (toJ φ)) := lc_rel (lc_toJ h)

/-- `((ψ^s)*)° = ((ψ*)°)^s`. -/
theorem tr_opn_fvar (ψ : Fm) (s : String) :
    toJ (rel (ψ.opn (.fvar s))) = (toJ (rel ψ)).opn (.fvar s) := by
  rw [rel_opn_fvar ψ s, toJ_opn_fvar (rel ψ) s]

theorem lc_tr {φ : Fm} (h : LC φ) : LC (toJ (rel φ)) := lc_toJ (lc_rel h)

/-! ## Casts and cut -/

def LaxND2.castF {Γ : List Fm} {φ ψ : Fm} (e : φ = ψ) (d : LaxND2 Γ φ) : LaxND2 Γ ψ := e ▸ d
def LaxND2.castΓ {Γ Γ' : List Fm} {φ : Fm} (e : Γ = Γ') (d : LaxND2 Γ φ) : LaxND2 Γ' φ := e ▸ d

/-- Cut with one hypothesis, by `→I`, `→E`. -/
def LaxND2.cut1 {Γ : List Fm} {A B : Fm} (d : LaxND2 [A] B) (hA : LC A) (e : LaxND2 Γ A) :
    LaxND2 Γ B :=
  .impElim (LaxND2.rename (Γ := []) (fun _ h => nomatch h) (LaxND2.impIntro hA d)) e

variable {J : List String → Fm → Type}

def JND.castF {Θ : List String} {Γ : List Fm} {φ ψ : Fm} (e : φ = ψ) (d : JND J Θ Γ φ) :
    JND J Θ Γ ψ := e ▸ d
def JND.castΓ {Θ : List String} {Γ Γ' : List Fm} {φ : Fm} (e : Γ = Γ') (d : JND J Θ Γ φ) :
    JND J Θ Γ' φ := e ▸ d

/-- Cut with one hypothesis, by `→I`, `→E`. -/
def JND.cut1 {Θ : List String} {Γ : List Fm} {A B : Fm} (d : JND J Θ [A] B) (hA : LC A)
    (e : JND J Θ Γ A) : JND J Θ Γ B :=
  .impElim (JND.rename (Γ := []) (fun _ h => nomatch h) (JND.impIntro hA d)) e

/-! ## RTP -/

/-- The round trip on the P2LL side, both directions, by induction on the size
of `φ` (the bound `n`). -/
def rtpD : ∀ (n : Nat) (φ : Fm), size φ < n → LC φ → allJFree φ →
    LaxND2 [φ] (rel (toJ φ)) × LaxND2 [rel (toJ φ)] φ
  | 0, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, .fvar _, _, _, _ =>
    (.iden trivial (List.mem_cons_self ..), .iden trivial (List.mem_cons_self ..))
  | _ + 1, .bvar k, _, hlc, _ => absurd hlc (Nat.not_lt_zero k)
  | _ + 1, .bot, _, _, _ =>
    (.iden trivial (List.mem_cons_self ..), .iden trivial (List.mem_cons_self ..))
  | n + 1, .and φ ψ, h, hlc, hf =>
    let dφ := rtpD n φ (lt_of_bin_left h) hlc.1 hf.1
    let dψ := rtpD n ψ (lt_of_bin_right h) hlc.2 hf.2
    (.andIntro
        (.cut1 dφ.1 hlc.1 (.andElim1 (.iden hlc (List.mem_cons_self ..))))
        (.cut1 dψ.1 hlc.2 (.andElim2 (.iden hlc (List.mem_cons_self ..)))),
     .andIntro
        (.cut1 dφ.2 (lc_rt hlc.1)
          (.andElim1 (.iden (⟨lc_rt hlc.1, lc_rt hlc.2⟩ : LC (rel (toJ (.and φ ψ))))
            (List.mem_cons_self ..))))
        (.cut1 dψ.2 (lc_rt hlc.2)
          (.andElim2 (.iden (⟨lc_rt hlc.1, lc_rt hlc.2⟩ : LC (rel (toJ (.and φ ψ))))
            (List.mem_cons_self ..)))))
  | n + 1, .or φ ψ, h, hlc, hf =>
    let dφ := rtpD n φ (lt_of_bin_left h) hlc.1 hf.1
    let dψ := rtpD n ψ (lt_of_bin_right h) hlc.2 hf.2
    (.orElim (.iden hlc (List.mem_cons_self ..))
        (.orIntro1 (lc_rt hlc.2) (.cut1 dφ.1 hlc.1 (.iden hlc.1 (List.mem_cons_self ..))))
        (.orIntro2 (lc_rt hlc.1) (.cut1 dψ.1 hlc.2 (.iden hlc.2 (List.mem_cons_self ..)))),
     .orElim (.iden (⟨lc_rt hlc.1, lc_rt hlc.2⟩ : LC (rel (toJ (.or φ ψ)))) (List.mem_cons_self ..))
        (.orIntro1 hlc.2 (.cut1 dφ.2 (lc_rt hlc.1) (.iden (lc_rt hlc.1) (List.mem_cons_self ..))))
        (.orIntro2 hlc.1 (.cut1 dψ.2 (lc_rt hlc.2) (.iden (lc_rt hlc.2) (List.mem_cons_self ..)))))
  | n + 1, .imp φ ψ, h, hlc, hf =>
    let dφ := rtpD n φ (lt_of_bin_left h) hlc.1 hf.1
    let dψ := rtpD n ψ (lt_of_bin_right h) hlc.2 hf.2
    (.impIntro (lc_rt hlc.1)
        (.cut1 dψ.1 hlc.2
          (.impElim (.iden hlc (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
            (.cut1 dφ.2 (lc_rt hlc.1) (.iden (lc_rt hlc.1) (List.mem_cons_self ..))))),
     .impIntro hlc.1
        (.cut1 dψ.2 (lc_rt hlc.2)
          (.impElim
            (.iden (⟨lc_rt hlc.1, lc_rt hlc.2⟩ : LC (rel (toJ (.imp φ ψ))))
              (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
            (.cut1 dφ.1 hlc.1 (.iden hlc.1 (List.mem_cons_self ..))))))
  | n + 1, .circ φ, h, hlc, hf =>
    let hφ : LC φ := hlc
    let dφ := rtpD n φ (lt_of_un h) hφ hf
    (.castF (rel_toJ_circ φ).symm
        (.cut1 (LaxND2.circ_to_circNuc (Γ := []) (lc_rt hφ)) (lc_rt hφ)
          (.laxElim (.iden hlc (List.mem_cons_self ..))
            (.laxIntro (.cut1 dφ.1 hφ (.iden hφ (List.mem_cons_self ..)))))),
     .castΓ (congrArg (fun x => [x]) (rel_toJ_circ φ).symm)
        (.laxElim (LaxND2.circNuc_to_circ (Γ := []) (lc_rt hφ))
          (.laxIntro (.cut1 dφ.2 (lc_rt hφ) (.iden (lc_rt hφ) (List.mem_cons_self ..))))))
  | n + 1, .all ψ, h, hlc, hf =>
    let hψ : lcAt 1 ψ := hlc
    let hψ' : lcAt 1 (rel (toJ ψ)) := lcAt_rel 1 _ (lcAt_toJ 1 ψ hψ)
    (.allIntro [] hψ' fun s _ =>
        .castF (rt_opn_fvar ψ s)
          (.cut1 (rtpD n (ψ.opn (.fvar s)) (by rw [size_opn_fvar]; exact lt_of_un h)
                (lc_opn _ trivial hψ) (allJFree_opn_fvar s hf)).1
            (lc_opn _ trivial hψ)
            (.allElim (χ := .fvar s) trivial (.iden hlc (List.mem_cons_self ..)) rfl)),
     .allIntro [] hψ fun s _ =>
        .cut1 (rtpD n (ψ.opn (.fvar s)) (by rw [size_opn_fvar]; exact lt_of_un h)
              (lc_opn _ trivial hψ) (allJFree_opn_fvar s hf)).2
          (lc_rt (lc_opn _ trivial hψ))
          (.allElim (χ := .fvar s) trivial
            (.iden (hψ' : LC (rel (toJ (.all ψ)))) (List.mem_cons_self ..))
            (rt_opn_fvar ψ s)))
  | _ + 1, .allJ _, _, _, hf => hf.elim

/-- **RTP.** -/
theorem roundTripP2LL : RoundTripP2LL := fun φ hlc hf =>
  let d := rtpD (size φ + 1) φ (Nat.lt_succ_self _) hlc hf
  ⟨⟨d.1⟩, ⟨d.2⟩⟩


/-! ## Commutation of openings; closure under a change of instance -/

/-- Two openings at different indices, with locally closed instances, commute. -/
theorem openRec_comm {u v : Fm} (hu : LC u) (hv : LC v) :
    ∀ (ψ : Fm) (j k : Nat), j ≠ k →
      openRec j u (openRec k v ψ) = openRec k v (openRec j u ψ)
  | .fvar _, _, _, _ => rfl
  | .bot, _, _, _ => rfl
  | .bvar n, j, k, hjk => by
    show openRec j u (if n = k then v else .bvar n) = openRec k v (if n = j then u else .bvar n)
    by_cases hk : n = k
    · subst hk
      rw [if_pos rfl, if_neg (Ne.symm hjk)]
      show openRec j u v = (if n = n then v else Fm.bvar n)
      rw [openRec_lcAt u j v (lcAt_mono (Nat.zero_le j) v hv), if_pos rfl]
    · rw [if_neg hk]
      by_cases hj : n = j
      · subst hj
        rw [if_pos rfl]
        show (if n = n then u else Fm.bvar n) = openRec k v u
        rw [if_pos rfl, openRec_lcAt v k u (lcAt_mono (Nat.zero_le k) u hu)]
      · rw [if_neg hj]
        show (if n = j then u else Fm.bvar n) = (if n = k then v else Fm.bvar n)
        rw [if_neg hj, if_neg hk]
  | .and φ ψ, j, k, h => by
    show Fm.and (openRec j u (openRec k v φ)) (openRec j u (openRec k v ψ)) =
      Fm.and (openRec k v (openRec j u φ)) (openRec k v (openRec j u ψ))
    rw [openRec_comm hu hv φ j k h, openRec_comm hu hv ψ j k h]
  | .or φ ψ, j, k, h => by
    show Fm.or (openRec j u (openRec k v φ)) (openRec j u (openRec k v ψ)) =
      Fm.or (openRec k v (openRec j u φ)) (openRec k v (openRec j u ψ))
    rw [openRec_comm hu hv φ j k h, openRec_comm hu hv ψ j k h]
  | .imp φ ψ, j, k, h => by
    show Fm.imp (openRec j u (openRec k v φ)) (openRec j u (openRec k v ψ)) =
      Fm.imp (openRec k v (openRec j u φ)) (openRec k v (openRec j u ψ))
    rw [openRec_comm hu hv φ j k h, openRec_comm hu hv ψ j k h]
  | .circ φ, j, k, h => by
    show Fm.circ (openRec j u (openRec k v φ)) = Fm.circ (openRec k v (openRec j u φ))
    rw [openRec_comm hu hv φ j k h]
  | .all ψ, j, k, h => by
    show Fm.all (openRec (j + 1) u (openRec (k + 1) v ψ)) =
      Fm.all (openRec (k + 1) v (openRec (j + 1) u ψ))
    rw [openRec_comm hu hv ψ (j + 1) (k + 1) (fun e => h (Nat.succ.inj e))]
  | .allJ ψ, j, k, h => by
    show Fm.allJ (openRec (j + 1) u (openRec (k + 1) v ψ)) =
      Fm.allJ (openRec (k + 1) v (openRec (j + 1) u ψ))
    rw [openRec_comm hu hv ψ (j + 1) (k + 1) (fun e => h (Nat.succ.inj e))]

/-- The closure of an opening depends only on the closure of the instance. -/
theorem lcAt_openRec_swap {u v : Fm} (hv : LC v) :
    ∀ (ψ : Fm) (j k : Nat), lcAt j (openRec k u ψ) → lcAt j (openRec k v ψ)
  | .fvar _, _, _, _ => trivial
  | .bot, _, _, _ => trivial
  | .bvar n, j, k, h => by
    show lcAt j (if n = k then v else Fm.bvar n)
    by_cases hk : n = k
    · rw [if_pos hk]
      exact lcAt_mono (Nat.zero_le j) v hv
    · rw [if_neg hk]
      have h' : lcAt j (if n = k then u else Fm.bvar n) := h
      rw [if_neg hk] at h'
      exact h'
  | .and φ ψ, j, k, h => ⟨lcAt_openRec_swap hv φ j k h.1, lcAt_openRec_swap hv ψ j k h.2⟩
  | .or φ ψ, j, k, h => ⟨lcAt_openRec_swap hv φ j k h.1, lcAt_openRec_swap hv ψ j k h.2⟩
  | .imp φ ψ, j, k, h => ⟨lcAt_openRec_swap hv φ j k h.1, lcAt_openRec_swap hv ψ j k h.2⟩
  | .circ φ, j, k, h => lcAt_openRec_swap hv φ j k h
  | .all ψ, j, k, h => lcAt_openRec_swap hv ψ (j + 1) (k + 1) h
  | .allJ ψ, j, k, h => lcAt_openRec_swap hv ψ (j + 1) (k + 1) h

/-! ## Substitution of equivalents in the guarded calculus -/

/-- If `A ↔ B` under `Γ`, then `ψ[A/k] → ψ[B/k]` under `Γ`, for every
`◯`-free `ψ` whose only loose index is `k` (`LC (openRec k A ψ)`).  Stated for
every `k` so that the binder cases need no fresh name: the eigenvariable of the
rule's own cofinite premise opens the body, and the two openings commute
(`openRec_comm`).  The converse is the same lemma with `A`, `B` swapped, which
the `→` case uses on the antecedent. -/
def JND.congrD : ∀ (n : Nat) {Θ : List String} {Γ : List Fm} (A B : Fm), LC A → LC B →
    JND IsJ Θ Γ (.imp A B) → JND IsJ Θ Γ (.imp B A) →
    ∀ (k : Nat) (ψ : Fm), size ψ < n → circFree ψ → LC (openRec k A ψ) →
      JND IsJ Θ Γ (.imp (openRec k A ψ) (openRec k B ψ))
  | 0, _, _, _, _, _, _, _, _, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, _, _, _, _, _, _, _, _, _, .fvar _, _, _, _ =>
    .impIntro trivial (.iden trivial (List.mem_cons_self ..))
  | _ + 1, _, _, _, _, _, _, _, _, _, .bot, _, _, _ =>
    .impIntro trivial (.iden trivial (List.mem_cons_self ..))
  | _ + 1, _, _, A, B, _, _, hAB, _, k, .bvar m, _, _, hlc => by
    by_cases h : m = k
    · subst h
      show JND IsJ _ _ (.imp (if m = m then A else .bvar m) (if m = m then B else .bvar m))
      rw [if_pos rfl, if_pos rfl]
      exact hAB
    · have hlc' : lcAt 0 (if m = k then A else Fm.bvar m) := hlc
      rw [if_neg h] at hlc'
      exact absurd hlc' (Nat.not_lt_zero m)
  | n + 1, _, _, A, B, hA, hB, hAB, hBA, k, .and φ ψ, h, hf, hlc =>
    let dφ := JND.congrD n A B hA hB hAB hBA k φ (lt_of_bin_left h) hf.1 hlc.1
    let dψ := JND.congrD n A B hA hB hAB hBA k ψ (lt_of_bin_right h) hf.2 hlc.2
    .impIntro hlc (.andIntro
      (.impElim (dφ.weaken _) (.andElim1 (.iden hlc (List.mem_cons_self ..))))
      (.impElim (dψ.weaken _) (.andElim2 (.iden hlc (List.mem_cons_self ..)))))
  | n + 1, _, _, A, B, hA, hB, hAB, hBA, k, .or φ ψ, h, hf, hlc =>
    let dφ := JND.congrD n A B hA hB hAB hBA k φ (lt_of_bin_left h) hf.1 hlc.1
    let dψ := JND.congrD n A B hA hB hAB hBA k ψ (lt_of_bin_right h) hf.2 hlc.2
    .impIntro hlc (.orElim (.iden hlc (List.mem_cons_self ..))
      (.orIntro1 (lcAt_openRec_swap hB ψ 0 k hlc.2)
        (.impElim ((dφ.weaken _).weaken _) (.iden hlc.1 (List.mem_cons_self ..))))
      (.orIntro2 (lcAt_openRec_swap hB φ 0 k hlc.1)
        (.impElim ((dψ.weaken _).weaken _) (.iden hlc.2 (List.mem_cons_self ..)))))
  | n + 1, _, _, A, B, hA, hB, hAB, hBA, k, .imp φ ψ, h, hf, hlc =>
    let hφB : LC (openRec k B φ) := lcAt_openRec_swap hB φ 0 k hlc.1
    let dφ' := JND.congrD n B A hB hA hBA hAB k φ (lt_of_bin_left h) hf.1 hφB
    let dψ := JND.congrD n A B hA hB hAB hBA k ψ (lt_of_bin_right h) hf.2 hlc.2
    .impIntro hlc (.impIntro hφB
      (.impElim ((dψ.weaken _).weaken _)
        (.impElim (.iden hlc (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
          (.impElim ((dφ'.weaken _).weaken _) (.iden hφB (List.mem_cons_self ..))))))
  | _ + 1, _, _, _, _, _, _, _, _, _, .circ _, _, hf, _ => hf.elim
  | n + 1, _, _, A, B, hA, hB, hAB, hBA, k, .all ψ, h, hf, hlc =>
    let hlcA : lcAt 1 (openRec (k + 1) A ψ) := hlc
    let hlcB : lcAt 1 (openRec (k + 1) B ψ) := lcAt_openRec_swap hB ψ 1 (k + 1) hlcA
    .impIntro hlc (.allIntro [] hlcB fun t _ =>
      .castF (openRec_comm (u := .fvar t) trivial hB ψ 0 (k + 1) (Nat.succ_ne_zero k).symm).symm
        (.impElim
          (JND.congrD n A B hA hB (hAB.weaken _) (hBA.weaken _) (k + 1) (openRec 0 (.fvar t) ψ)
            (by rw [size_openRec_fvar]; exact lt_of_un h) (circFree_openRec_fvar t 0 ψ hf)
            ((congrArg LC (openRec_comm (u := .fvar t) trivial hA ψ 0 (k + 1) (Nat.succ_ne_zero k).symm)).mp
              (lcAt_openRec _ 0 _ trivial hlcA)))
          (.allElim (χ := .fvar t) trivial (.iden hlc (List.mem_cons_self ..))
            (openRec_comm (u := .fvar t) trivial hA ψ 0 (k + 1) (Nat.succ_ne_zero k).symm).symm)))
  | n + 1, _, _, A, B, hA, hB, hAB, hBA, k, .allJ ψ, h, hf, hlc =>
    let hlcA : lcAt 1 (openRec (k + 1) A ψ) := hlc
    let hlcB : lcAt 1 (openRec (k + 1) B ψ) := lcAt_openRec_swap hB ψ 1 (k + 1) hlcA
    .impIntro hlc (.allJIntro [] hlcB fun t _ =>
      .castF (openRec_comm (u := .fvar t) trivial hB ψ 0 (k + 1) (Nat.succ_ne_zero k).symm).symm
        (.impElim
          (JND.congrD n A B hA hB
            ((hAB.weakenΘ IsJ.jmono fun _ hx => List.mem_cons_of_mem _ hx).weaken _)
            ((hBA.weakenΘ IsJ.jmono fun _ hx => List.mem_cons_of_mem _ hx).weaken _)
            (k + 1) (openRec 0 (.fvar t) ψ)
            (by rw [size_openRec_fvar]; exact lt_of_un h) (circFree_openRec_fvar t 0 ψ hf)
            ((congrArg LC (openRec_comm (u := .fvar t) trivial hA ψ 0 (k + 1) (Nat.succ_ne_zero k).symm)).mp
              (lcAt_openRec _ 0 _ trivial hlcA)))
          (.allJElim (χ := .fvar t) trivial (.var (List.mem_cons_self ..))
            (.iden hlc (List.mem_cons_self ..))
            (openRec_comm (u := .fvar t) trivial hA ψ 0 (k + 1) (Nat.succ_ne_zero k).symm).symm)))

/-! ## RTJ -/

/-- `◯°s` is a J-formula under any declarations (the `allJ` and `imp` clauses). -/
def isJ_circJ_fvar (Θ : List String) (s : String) : IsJ Θ (circJ (.fvar s)) :=
  .allJ [] fun t _ =>
    show IsJ (t :: Θ) (.imp (.imp (.fvar s) (.fvar t)) (.fvar t)) from
    .imp (.var (List.mem_cons_self ..))

theorem lc_guardJ (s : String) : LC (Fm.imp (circJ (.fvar s)) (.fvar s)) := ⟨lc_circJ trivial, trivial⟩

/-- `(∀°.ψ)*° = ∀p.((◯°p → p) → ψ*°)` is locally closed when its body is. -/
theorem lc_trAllJ {ψ : Fm} (h : lcAt 1 (toJ (rel ψ))) : LC (toJ (rel (.allJ ψ))) :=
  ⟨⟨(by decide : lcAt 1 (circJ (.bvar 0))), Nat.zero_lt_one⟩, h⟩

/-- The round trip on the guarded side, both directions, by induction on the
size of `φ`; `Θ` is generalised because `∀°I` declares its eigenvariable. -/
def rtjD : ∀ (n : Nat) (Θ : List String) (φ : Fm), size φ < n → LC φ → circFree φ →
    JND IsJ Θ [φ] (toJ (rel φ)) × JND IsJ Θ [toJ (rel φ)] φ
  | 0, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, _, .fvar _, _, _, _ =>
    (.iden trivial (List.mem_cons_self ..), .iden trivial (List.mem_cons_self ..))
  | _ + 1, _, .bvar k, _, hlc, _ => absurd hlc (Nat.not_lt_zero k)
  | _ + 1, _, .bot, _, _, _ =>
    (.iden trivial (List.mem_cons_self ..), .iden trivial (List.mem_cons_self ..))
  | n + 1, Θ, .and φ ψ, h, hlc, hf =>
    let dφ := rtjD n Θ φ (lt_of_bin_left h) hlc.1 hf.1
    let dψ := rtjD n Θ ψ (lt_of_bin_right h) hlc.2 hf.2
    (.andIntro
        (.cut1 dφ.1 hlc.1 (.andElim1 (.iden hlc (List.mem_cons_self ..))))
        (.cut1 dψ.1 hlc.2 (.andElim2 (.iden hlc (List.mem_cons_self ..)))),
     .andIntro
        (.cut1 dφ.2 (lc_tr hlc.1)
          (.andElim1 (.iden (⟨lc_tr hlc.1, lc_tr hlc.2⟩ : LC (toJ (rel (.and φ ψ))))
            (List.mem_cons_self ..))))
        (.cut1 dψ.2 (lc_tr hlc.2)
          (.andElim2 (.iden (⟨lc_tr hlc.1, lc_tr hlc.2⟩ : LC (toJ (rel (.and φ ψ))))
            (List.mem_cons_self ..)))))
  | n + 1, Θ, .or φ ψ, h, hlc, hf =>
    let dφ := rtjD n Θ φ (lt_of_bin_left h) hlc.1 hf.1
    let dψ := rtjD n Θ ψ (lt_of_bin_right h) hlc.2 hf.2
    (.orElim (.iden hlc (List.mem_cons_self ..))
        (.orIntro1 (lc_tr hlc.2) (.cut1 dφ.1 hlc.1 (.iden hlc.1 (List.mem_cons_self ..))))
        (.orIntro2 (lc_tr hlc.1) (.cut1 dψ.1 hlc.2 (.iden hlc.2 (List.mem_cons_self ..)))),
     .orElim (.iden (⟨lc_tr hlc.1, lc_tr hlc.2⟩ : LC (toJ (rel (.or φ ψ)))) (List.mem_cons_self ..))
        (.orIntro1 hlc.2 (.cut1 dφ.2 (lc_tr hlc.1) (.iden (lc_tr hlc.1) (List.mem_cons_self ..))))
        (.orIntro2 hlc.1 (.cut1 dψ.2 (lc_tr hlc.2) (.iden (lc_tr hlc.2) (List.mem_cons_self ..)))))
  | n + 1, Θ, .imp φ ψ, h, hlc, hf =>
    let dφ := rtjD n Θ φ (lt_of_bin_left h) hlc.1 hf.1
    let dψ := rtjD n Θ ψ (lt_of_bin_right h) hlc.2 hf.2
    (.impIntro (lc_tr hlc.1)
        (.cut1 dψ.1 hlc.2
          (.impElim (.iden hlc (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
            (.cut1 dφ.2 (lc_tr hlc.1) (.iden (lc_tr hlc.1) (List.mem_cons_self ..))))),
     .impIntro hlc.1
        (.cut1 dψ.2 (lc_tr hlc.2)
          (.impElim
            (.iden (⟨lc_tr hlc.1, lc_tr hlc.2⟩ : LC (toJ (rel (.imp φ ψ))))
              (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
            (.cut1 dφ.1 hlc.1 (.iden hlc.1 (List.mem_cons_self ..))))))
  | _ + 1, _, .circ _, _, _, hf => hf.elim
  | n + 1, Θ, .all ψ, h, hlc, hf =>
    let hψ : lcAt 1 ψ := hlc
    let hψ' : lcAt 1 (toJ (rel ψ)) := lcAt_toJ 1 _ (lcAt_rel 1 ψ hψ)
    (.allIntro [] hψ' fun s _ =>
        .castF (tr_opn_fvar ψ s)
          (.cut1 (rtjD n Θ (ψ.opn (.fvar s)) (by rw [size_opn_fvar]; exact lt_of_un h)
                (lc_opn _ trivial hψ) (circFree_opn_fvar s hf)).1
            (lc_opn _ trivial hψ)
            (.allElim (χ := .fvar s) trivial (.iden hlc (List.mem_cons_self ..)) rfl)),
     .allIntro [] hψ fun s _ =>
        .cut1 (rtjD n Θ (ψ.opn (.fvar s)) (by rw [size_opn_fvar]; exact lt_of_un h)
              (lc_opn _ trivial hψ) (circFree_opn_fvar s hf)).2
          (lc_tr (lc_opn _ trivial hψ))
          (.allElim (χ := .fvar s) trivial
            (.iden (hψ' : LC (toJ (rel (.all ψ)))) (List.mem_cons_self ..))
            (tr_opn_fvar ψ s)))
  | n + 1, Θ, .allJ ψ, h, hlc, hf =>
    let hψ : lcAt 1 ψ := hlc
    let hψ' : lcAt 1 (toJ (rel ψ)) := lcAt_toJ 1 _ (lcAt_rel 1 ψ hψ)
    (.allIntro [] (lc_trAllJ hψ') fun s _ =>
        show JND IsJ Θ [.allJ ψ]
          (.imp (.imp (circJ (.fvar s)) (.fvar s)) ((toJ (rel ψ)).opn (.fvar s))) from
        .impIntro (lc_guardJ s) <|
          .castF (tr_opn_fvar ψ s)
            (.cut1 (rtjD n Θ (ψ.opn (.fvar s)) (by rw [size_opn_fvar]; exact lt_of_un h)
                  (lc_opn _ trivial hψ) (circFree_opn_fvar s hf)).1
              (lc_opn _ trivial hψ)
              (.impElim
                (JND.congrD (size ψ + 1) (circJ (.fvar s)) (.fvar s) (lc_circJ trivial) trivial
                  (.iden (lc_guardJ s) (List.mem_cons_self ..))
                  (JND.OI IsJ.jmono _ trivial)
                  0 ψ (Nat.lt_succ_self _) hf (lc_opn _ (lc_circJ trivial) hψ))
                (.allJElim (χ := circJ (.fvar s)) (lc_circJ trivial) (isJ_circJ_fvar Θ s)
                  (.iden hlc (List.mem_cons_of_mem _ (List.mem_cons_self ..))) rfl))),
     .allJIntro [] hψ fun s _ =>
        .cut1 (rtjD n (s :: Θ) (ψ.opn (.fvar s)) (by rw [size_opn_fvar]; exact lt_of_un h)
              (lc_opn _ trivial hψ) (circFree_opn_fvar s hf)).2
          (lc_tr (lc_opn _ trivial hψ))
          (.castF (tr_opn_fvar ψ s).symm
            (.impElim
              (.allElim (χ := .fvar s)
                (θ := .imp (.imp (circJ (.fvar s)) (.fvar s)) ((toJ (rel ψ)).opn (.fvar s)))
                trivial
                (.iden (lc_trAllJ hψ') (List.mem_cons_self ..)) rfl)
              (.impIntro (lc_circJ trivial)
                (JND.circJ_collapse (.var (List.mem_cons_self ..)) trivial)))))

/-- **RTJ.** -/
theorem roundTripJ : RoundTripJ := fun Θ φ hlc hf =>
  let d := rtjD (size φ + 1) Θ φ (Nat.lt_succ_self _) hlc hf
  ⟨⟨d.1⟩, ⟨d.2⟩⟩

end P2LL

/-! ## Pins (upper bounds; first run at `[]`, see `wip/p2ll-STATUS.md` §9) -/

#axioms_within P2LL.size_openRec_fvar []
#axioms_within P2LL.allJFree_openRec_fvar []
#axioms_within P2LL.circFree_openRec_fvar []
#axioms_within P2LL.rel_shiftAt []
#axioms_within P2LL.rel_circJ []
#axioms_within P2LL.rt_opn_fvar [propext]
#axioms_within P2LL.tr_opn_fvar [propext]
#axioms_within P2LL.LaxND2.cut1 [propext]
#axioms_within P2LL.JND.cut1 [propext]
#axioms_within P2LL.rtpD [propext]
#axioms_within P2LL.roundTripP2LL [propext]
#axioms_within P2LL.openRec_comm [propext]
#axioms_within P2LL.lcAt_openRec_swap []
#axioms_within P2LL.JND.congrD [propext]
#axioms_within P2LL.isJ_circJ_fvar []
#axioms_within P2LL.lc_trAllJ []
#axioms_within P2LL.rtjD [propext]
#axioms_within P2LL.roundTripJ [propext]
