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
