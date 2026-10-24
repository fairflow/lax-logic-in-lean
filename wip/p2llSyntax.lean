import Meta.Audit

/-!
# P2LL and the guarded calculus: syntax, binders, translations

File 1 of the P2LL definability campaign (`wip/p2ll-STATUS.md`; design in
`docs/pll2-plan.md` §6).  One locally nameless formula type carries both

* **P2LL** (second-order propositional lax logic): atoms, `⊥ ∧ ∨ →`, a
  primitive nucleus `◯`, an impredicative `∀`;
* **the guarded calculus**: the same without `◯`, with a second binder `∀°`
  whose instances are restricted to the J-formulas of `wip/p2llJND.lean`.

P2LL formulas are the `allJ`-free ones (`allJFree`), the guarded calculus's the
`circ`-free ones (`circFree`); each calculus has no rule for the other's
connective, which is inert in it.  One type saves duplicating the binder layer;
this module is kept small so that a switch to two types is cheap.

Binders are locally nameless (plan §6.1): `fvar s` is a named free variable,
`bvar n` a de Bruijn index, and `ψ.opn u` opens the outermost binder of the body
`ψ` with `u`.  Local closure is the bounded `lcAt k` of `LaxLogic/QLL/Lc.lean`
(no loose index at or above `k`), so `openRec_lcAt` needs no fresh-name supply;
nor does anything else here: the calculi carry local closure as a side condition
wherever a rule's conclusion does not inherit it from the premises
(`wip/p2llND.lean`), so no fresh name is ever chosen.  (A fresh-name supply over
`String` would be classical: core's `String.length_*` lemmas go through the
UTF-8 decoder and `Classical.propDecidable`.)

The one place a binder is ADDED to an existing formula is the defined modality
`◯°φ := ∀°q.((φ → q) → q)`: the body `φ` moves under a new binder, so its loose
indices are raised by `shiftAt 0`.  For a locally closed `φ` the shift is the
identity (`shiftAt_lcAt`), and `(rpBody φ).opn u = (φ → u) → u` (`rpBody_opn`).
-/

namespace P2LL

/-- Formulas, shared by P2LL (`allJ`-free) and the guarded calculus (`circ`-free). -/
inductive Fm where
  | fvar (s : String)
  | bvar (n : Nat)
  | bot
  | and (φ ψ : Fm)
  | or (φ ψ : Fm)
  | imp (φ ψ : Fm)
  | circ (φ : Fm)
  | all (ψ : Fm)
  | allJ (ψ : Fm)
  deriving DecidableEq, Repr, Inhabited

namespace Fm

/-- `⊤ := ⊥ → ⊥`, as `PLLFormula.truePLL`. -/
abbrev top : Fm := .imp .bot .bot

/-! ## Opening, shifting, local closure -/

/-- Replace the bound variable `k` by `u`; the index rises under each binder. -/
def openRec (k : Nat) (u : Fm) : Fm → Fm
  | .fvar s => .fvar s
  | .bvar n => if n = k then u else .bvar n
  | .bot => .bot
  | .and φ ψ => .and (openRec k u φ) (openRec k u ψ)
  | .or φ ψ => .or (openRec k u φ) (openRec k u ψ)
  | .imp φ ψ => .imp (openRec k u φ) (openRec k u ψ)
  | .circ φ => .circ (openRec k u φ)
  | .all ψ => .all (openRec (k + 1) u ψ)
  | .allJ ψ => .allJ (openRec (k + 1) u ψ)

/-- The body `ψ` of a binder with its bound variable replaced by `u`
(`ψ^u` in the plan). -/
def opn (ψ u : Fm) : Fm := openRec 0 u ψ

/-- Raise every loose index at or above `d` by one: `φ` moves under a new binder. -/
def shiftAt (d : Nat) : Fm → Fm
  | .fvar s => .fvar s
  | .bvar n => if d ≤ n then .bvar (n + 1) else .bvar n
  | .bot => .bot
  | .and φ ψ => .and (shiftAt d φ) (shiftAt d ψ)
  | .or φ ψ => .or (shiftAt d φ) (shiftAt d ψ)
  | .imp φ ψ => .imp (shiftAt d φ) (shiftAt d ψ)
  | .circ φ => .circ (shiftAt d φ)
  | .all ψ => .all (shiftAt (d + 1) ψ)
  | .allJ ψ => .allJ (shiftAt (d + 1) ψ)

/-- No index at or above `k` occurs loose. -/
def lcAt (k : Nat) : Fm → Prop
  | .fvar _ => True
  | .bvar n => n < k
  | .bot => True
  | .and φ ψ => lcAt k φ ∧ lcAt k ψ
  | .or φ ψ => lcAt k φ ∧ lcAt k ψ
  | .imp φ ψ => lcAt k φ ∧ lcAt k ψ
  | .circ φ => lcAt k φ
  | .all ψ => lcAt (k + 1) ψ
  | .allJ ψ => lcAt (k + 1) ψ

/-- Locally closed: a formula of the object language. -/
abbrev LC (φ : Fm) : Prop := lcAt 0 φ

instance decLcAt : ∀ (k : Nat) (φ : Fm), Decidable (lcAt k φ)
  | _, .fvar _ => isTrue trivial
  | k, .bvar n => inferInstanceAs (Decidable (n < k))
  | _, .bot => isTrue trivial
  | k, .and φ ψ =>
      letI := decLcAt k φ
      letI := decLcAt k ψ
      inferInstanceAs (Decidable (lcAt k φ ∧ lcAt k ψ))
  | k, .or φ ψ =>
      letI := decLcAt k φ
      letI := decLcAt k ψ
      inferInstanceAs (Decidable (lcAt k φ ∧ lcAt k ψ))
  | k, .imp φ ψ =>
      letI := decLcAt k φ
      letI := decLcAt k ψ
      inferInstanceAs (Decidable (lcAt k φ ∧ lcAt k ψ))
  | k, .circ φ => decLcAt k φ
  | k, .all ψ => decLcAt (k + 1) ψ
  | k, .allJ ψ => decLcAt (k + 1) ψ

theorem lcAt_mono : ∀ {k k' : Nat}, k ≤ k' → ∀ φ : Fm, lcAt k φ → lcAt k' φ
  | _, _, _, .fvar _, _ => trivial
  | _, _, hk, .bvar _, h => Nat.lt_of_lt_of_le h hk
  | _, _, _, .bot, _ => trivial
  | _, _, hk, .and φ ψ, h => ⟨lcAt_mono hk φ h.1, lcAt_mono hk ψ h.2⟩
  | _, _, hk, .or φ ψ, h => ⟨lcAt_mono hk φ h.1, lcAt_mono hk ψ h.2⟩
  | _, _, hk, .imp φ ψ, h => ⟨lcAt_mono hk φ h.1, lcAt_mono hk ψ h.2⟩
  | _, _, hk, .circ φ, h => lcAt_mono hk φ h
  | _, _, hk, .all ψ, h => lcAt_mono (Nat.succ_le_succ hk) ψ h
  | _, _, hk, .allJ ψ, h => lcAt_mono (Nat.succ_le_succ hk) ψ h

/-- Opening at an index that does not occur loose changes nothing. -/
theorem openRec_lcAt (u : Fm) : ∀ (k : Nat) (φ : Fm), lcAt k φ → openRec k u φ = φ
  | _, .fvar _, _ => rfl
  | k, .bvar n, h => by
      have hn : n ≠ k := Nat.ne_of_lt h
      simp [openRec, hn]
  | _, .bot, _ => rfl
  | k, .and φ ψ, h => by
      simp only [openRec, openRec_lcAt u k φ h.1, openRec_lcAt u k ψ h.2]
  | k, .or φ ψ, h => by
      simp only [openRec, openRec_lcAt u k φ h.1, openRec_lcAt u k ψ h.2]
  | k, .imp φ ψ, h => by
      simp only [openRec, openRec_lcAt u k φ h.1, openRec_lcAt u k ψ h.2]
  | k, .circ φ, h => by simp only [openRec, openRec_lcAt u k φ h]
  | k, .all ψ, h => by simp only [openRec, openRec_lcAt u (k + 1) ψ h]
  | k, .allJ ψ, h => by simp only [openRec, openRec_lcAt u (k + 1) ψ h]

theorem opn_lc {φ : Fm} (u : Fm) (h : LC φ) : φ.opn u = φ := openRec_lcAt u 0 φ h

/-- Shifting a formula with no loose index at or above `d` changes nothing. -/
theorem shiftAt_lcAt : ∀ (d : Nat) (φ : Fm), lcAt d φ → shiftAt d φ = φ
  | _, .fvar _, _ => rfl
  | d, .bvar n, h => by
      have hn : ¬ d ≤ n := Nat.not_le_of_lt h
      simp [shiftAt, hn]
  | _, .bot, _ => rfl
  | d, .and φ ψ, h => by
      simp only [shiftAt, shiftAt_lcAt d φ h.1, shiftAt_lcAt d ψ h.2]
  | d, .or φ ψ, h => by
      simp only [shiftAt, shiftAt_lcAt d φ h.1, shiftAt_lcAt d ψ h.2]
  | d, .imp φ ψ, h => by
      simp only [shiftAt, shiftAt_lcAt d φ h.1, shiftAt_lcAt d ψ h.2]
  | d, .circ φ, h => by simp only [shiftAt, shiftAt_lcAt d φ h]
  | d, .all ψ, h => by simp only [shiftAt, shiftAt_lcAt (d + 1) ψ h]
  | d, .allJ ψ, h => by simp only [shiftAt, shiftAt_lcAt (d + 1) ψ h]

/-- Shifting raises the bound by one. -/
theorem lcAt_shiftAt : ∀ (d k : Nat) (φ : Fm), lcAt k φ → lcAt (k + 1) (shiftAt d φ)
  | _, _, .fvar _, _ => trivial
  | d, k, .bvar n, h => by
      have hn : n < k := h
      show lcAt (k + 1) (if d ≤ n then Fm.bvar (n + 1) else Fm.bvar n)
      split
      · exact Nat.succ_lt_succ hn
      · exact Nat.lt_succ_of_lt hn
  | _, _, .bot, _ => trivial
  | d, k, .and φ ψ, h => ⟨lcAt_shiftAt d k φ h.1, lcAt_shiftAt d k ψ h.2⟩
  | d, k, .or φ ψ, h => ⟨lcAt_shiftAt d k φ h.1, lcAt_shiftAt d k ψ h.2⟩
  | d, k, .imp φ ψ, h => ⟨lcAt_shiftAt d k φ h.1, lcAt_shiftAt d k ψ h.2⟩
  | d, k, .circ φ, h => lcAt_shiftAt d k φ h
  | d, k, .all ψ, h => lcAt_shiftAt (d + 1) (k + 1) ψ h
  | d, k, .allJ ψ, h => lcAt_shiftAt (d + 1) (k + 1) ψ h

/-- Opening then shifting is shifting then opening one index higher, for a `u`
with no loose index the shift could move. -/
theorem shiftAt_openRec : ∀ (d k : Nat) (u φ : Fm), d ≤ k → lcAt d u →
    shiftAt d (openRec k u φ) = openRec (k + 1) u (shiftAt d φ)
  | _, _, _, .fvar _, _, _ => rfl
  | d, k, u, .bvar n, hdk, hu => by
      by_cases hn : n = k
      · subst hn
        have h1 : openRec n u (Fm.bvar n) = u := by simp [openRec]
        have h2 : shiftAt d (Fm.bvar n) = Fm.bvar (n + 1) := by simp [shiftAt, hdk]
        rw [h1, h2, shiftAt_lcAt d u hu]
        simp [openRec]
      · have h1 : openRec k u (Fm.bvar n) = Fm.bvar n := by simp [openRec, hn]
        rw [h1]
        by_cases hd : d ≤ n
        · have h2 : shiftAt d (Fm.bvar n) = Fm.bvar (n + 1) := by simp [shiftAt, hd]
          rw [h2]
          simp [openRec, hn]
        · have h2 : shiftAt d (Fm.bvar n) = Fm.bvar n := by simp [shiftAt, hd]
          have hn' : n ≠ k + 1 := fun h => hd (h ▸ Nat.le_succ_of_le hdk)
          rw [h2]
          simp [openRec, hn']
  | _, _, _, .bot, _, _ => rfl
  | d, k, u, .and φ ψ, hdk, hu => by
      simp only [openRec, shiftAt, shiftAt_openRec d k u φ hdk hu, shiftAt_openRec d k u ψ hdk hu]
  | d, k, u, .or φ ψ, hdk, hu => by
      simp only [openRec, shiftAt, shiftAt_openRec d k u φ hdk hu, shiftAt_openRec d k u ψ hdk hu]
  | d, k, u, .imp φ ψ, hdk, hu => by
      simp only [openRec, shiftAt, shiftAt_openRec d k u φ hdk hu, shiftAt_openRec d k u ψ hdk hu]
  | d, k, u, .circ φ, hdk, hu => by
      simp only [openRec, shiftAt, shiftAt_openRec d k u φ hdk hu]
  | d, k, u, .all ψ, hdk, hu => by
      simp only [openRec, shiftAt,
        shiftAt_openRec (d + 1) (k + 1) u ψ (Nat.succ_le_succ hdk) (lcAt_mono (Nat.le_succ d) u hu)]
  | d, k, u, .allJ ψ, hdk, hu => by
      simp only [openRec, shiftAt,
        shiftAt_openRec (d + 1) (k + 1) u ψ (Nat.succ_le_succ hdk) (lcAt_mono (Nat.le_succ d) u hu)]

/-- Opening lowers the bound by one. -/
theorem lcAt_openRec : ∀ (φ : Fm) (k : Nat) (u : Fm), lcAt k u → lcAt (k + 1) φ →
    lcAt k (openRec k u φ)
  | .fvar _, _, _, _, _ => trivial
  | .bvar n, k, u, hu, h => by
      by_cases hn : n = k
      · subst hn
        simpa [openRec] using hu
      · have h' : n < k + 1 := h
        simp only [openRec, if_neg hn]
        exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h') hn
  | .bot, _, _, _, _ => trivial
  | .and φ ψ, k, u, hu, h => ⟨lcAt_openRec φ k u hu h.1, lcAt_openRec ψ k u hu h.2⟩
  | .or φ ψ, k, u, hu, h => ⟨lcAt_openRec φ k u hu h.1, lcAt_openRec ψ k u hu h.2⟩
  | .imp φ ψ, k, u, hu, h => ⟨lcAt_openRec φ k u hu h.1, lcAt_openRec ψ k u hu h.2⟩
  | .circ φ, k, u, hu, h => lcAt_openRec φ k u hu h
  | .all ψ, k, u, hu, h => lcAt_openRec ψ (k + 1) u (lcAt_mono (Nat.le_succ k) u hu) h
  | .allJ ψ, k, u, hu, h => lcAt_openRec ψ (k + 1) u (lcAt_mono (Nat.le_succ k) u hu) h

/-- The opened body of a locally closed binder is locally closed. -/
theorem lc_opn {ψ : Fm} (u : Fm) (hu : LC u) (h : lcAt 1 ψ) : LC (ψ.opn u) :=
  lcAt_openRec ψ 0 u hu h

/-- The converse: a body whose opening is closed at `k` was closed at `k + 1`
(for any `u`; the opened occurrences were exactly the index `k`).  This is why
the side condition `lcAt 1 ψ` on `∀I` is redundant given any one fresh name. -/
theorem lcAt_of_openRec : ∀ (k : Nat) (u φ : Fm), lcAt k (openRec k u φ) → lcAt (k + 1) φ
  | _, _, .fvar _, _ => trivial
  | k, u, .bvar n, h => by
      by_cases hn : n = k
      · subst hn
        exact Nat.lt_succ_self n
      · have h' : lcAt k (Fm.bvar n) := by simpa [openRec, hn] using h
        exact Nat.lt_succ_of_lt h'
  | _, _, .bot, _ => trivial
  | k, u, .and φ ψ, h => ⟨lcAt_of_openRec k u φ h.1, lcAt_of_openRec k u ψ h.2⟩
  | k, u, .or φ ψ, h => ⟨lcAt_of_openRec k u φ h.1, lcAt_of_openRec k u ψ h.2⟩
  | k, u, .imp φ ψ, h => ⟨lcAt_of_openRec k u φ h.1, lcAt_of_openRec k u ψ h.2⟩
  | k, u, .circ φ, h => lcAt_of_openRec k u φ h
  | k, u, .all ψ, h => lcAt_of_openRec (k + 1) u ψ h
  | k, u, .allJ ψ, h => lcAt_of_openRec (k + 1) u ψ h

/-! ## The modalities and the relativised quantifier

Written with the plan's names: `◯°` is the modality the guarded calculus
DEFINES, `RP` is Aczel's Russell–Prawitz modality (plain `∀`), `∀°` is the
relativised quantifier of P2LL (plan §1.6).  The letter J is reserved for the
J-formulas and the guarded calculus. -/

/-- `(φ → q) → q` as the body of a binder on `q`; `φ` moves under the binder. -/
def rpBody (φ : Fm) : Fm := .imp (.imp (shiftAt 0 φ) (.bvar 0)) (.bvar 0)

/-- The defined modality of the guarded calculus: `◯°φ := ∀°q.((φ → q) → q)`. -/
def circJ (φ : Fm) : Fm := .allJ (rpBody φ)

/-- Aczel's Russell–Prawitz modality, `RP(φ) := ∀q.((φ → q) → q)` with the plain
quantifier (survey §2.5(ii), plan §1.6). -/
def rp (φ : Fm) : Fm := .all (rpBody φ)

/-- The relativised quantifier of P2LL, `∀°p.ψ := ∀p.((◯p → p) → ψ)`; `ψ` is a
body with `bvar 0` for `p` (plan §1.6). -/
def allNuc (ψ : Fm) : Fm := .all (.imp (.imp (.circ (.bvar 0)) (.bvar 0)) ψ)

/-- `∀°p.((φ → p) → p)` in P2LL: the right-hand side of Proposition C. -/
def circNuc (φ : Fm) : Fm := allNuc (rpBody φ)

/-- For a locally closed `φ`, `(rpBody φ)^u = (φ → u) → u`. -/
theorem rpBody_opn {φ : Fm} (h : LC φ) (u : Fm) : (rpBody φ).opn u = .imp (.imp φ u) u := by
  simp [rpBody, opn, openRec, shiftAt_lcAt 0 φ h, openRec_lcAt u 0 φ h]

theorem lc_rpBody {φ : Fm} (h : LC φ) : lcAt 1 (rpBody φ) := by
  show (lcAt 1 (shiftAt 0 φ) ∧ 0 < 1) ∧ 0 < 1
  rw [shiftAt_lcAt 0 φ h]
  exact ⟨⟨lcAt_mono (Nat.zero_le 1) φ h, Nat.zero_lt_one⟩, Nat.zero_lt_one⟩

theorem lc_circJ {φ : Fm} (h : LC φ) : LC (circJ φ) := lc_rpBody h
theorem lc_rp {φ : Fm} (h : LC φ) : LC (rp φ) := lc_rpBody h
theorem lc_circNuc {φ : Fm} (h : LC φ) : LC (circNuc φ) :=
  ⟨⟨Nat.zero_lt_one, Nat.zero_lt_one⟩, lc_rpBody h⟩

/-! ## The two fragments and the two translations -/

/-- The formulas of the guarded calculus: no `◯`. -/
def circFree : Fm → Prop
  | .fvar _ => True
  | .bvar _ => True
  | .bot => True
  | .and φ ψ => circFree φ ∧ circFree ψ
  | .or φ ψ => circFree φ ∧ circFree ψ
  | .imp φ ψ => circFree φ ∧ circFree ψ
  | .circ _ => False
  | .all ψ => circFree ψ
  | .allJ ψ => circFree ψ

/-- The formulas of P2LL: no `∀°`. -/
def allJFree : Fm → Prop
  | .fvar _ => True
  | .bvar _ => True
  | .bot => True
  | .and φ ψ => allJFree φ ∧ allJFree ψ
  | .or φ ψ => allJFree φ ∧ allJFree ψ
  | .imp φ ψ => allJFree φ ∧ allJFree ψ
  | .circ φ => allJFree φ
  | .all ψ => allJFree ψ
  | .allJ _ => False

/-- `(−)°`: P2LL into the guarded calculus, `◯φ ↦ ◯°φ°`, homomorphic elsewhere. -/
def toJ : Fm → Fm
  | .fvar s => .fvar s
  | .bvar n => .bvar n
  | .bot => .bot
  | .and φ ψ => .and (toJ φ) (toJ ψ)
  | .or φ ψ => .or (toJ φ) (toJ ψ)
  | .imp φ ψ => .imp (toJ φ) (toJ ψ)
  | .circ φ => circJ (toJ φ)
  | .all ψ => .all (toJ ψ)
  | .allJ ψ => .allJ (toJ ψ)

/-- `(−)*`: the guarded calculus into P2LL, `∀°.ψ ↦ ∀.((◯q → q) → ψ*)`,
homomorphic elsewhere. -/
def rel : Fm → Fm
  | .fvar s => .fvar s
  | .bvar n => .bvar n
  | .bot => .bot
  | .and φ ψ => .and (rel φ) (rel ψ)
  | .or φ ψ => .or (rel φ) (rel ψ)
  | .imp φ ψ => .imp (rel φ) (rel ψ)
  | .circ φ => .circ (rel φ)
  | .all ψ => .all (rel ψ)
  | .allJ ψ => allNuc (rel ψ)

/-- The guards of the declared J-variables: `◯s → s` for every `s ∈ Θ`. -/
def guards (Θ : List String) : List Fm := Θ.map fun s => .imp (.circ (.fvar s)) (.fvar s)

/-! Validation (METHOD.md §3): each translation lands in the intended fragment
and is the identity on it. -/

theorem circFree_shiftAt : ∀ (d : Nat) (φ : Fm), circFree φ → circFree (shiftAt d φ)
  | _, .fvar _, _ => trivial
  | d, .bvar n, _ => by
      show circFree (if d ≤ n then Fm.bvar (n + 1) else Fm.bvar n)
      split <;> trivial
  | _, .bot, _ => trivial
  | d, .and φ ψ, h => ⟨circFree_shiftAt d φ h.1, circFree_shiftAt d ψ h.2⟩
  | d, .or φ ψ, h => ⟨circFree_shiftAt d φ h.1, circFree_shiftAt d ψ h.2⟩
  | d, .imp φ ψ, h => ⟨circFree_shiftAt d φ h.1, circFree_shiftAt d ψ h.2⟩
  | _, .circ _, h => h.elim
  | d, .all ψ, h => circFree_shiftAt (d + 1) ψ h
  | d, .allJ ψ, h => circFree_shiftAt (d + 1) ψ h

theorem circFree_toJ : ∀ φ : Fm, circFree (toJ φ)
  | .fvar _ => trivial
  | .bvar _ => trivial
  | .bot => trivial
  | .and φ ψ => ⟨circFree_toJ φ, circFree_toJ ψ⟩
  | .or φ ψ => ⟨circFree_toJ φ, circFree_toJ ψ⟩
  | .imp φ ψ => ⟨circFree_toJ φ, circFree_toJ ψ⟩
  | .circ φ => ⟨⟨circFree_shiftAt 0 (toJ φ) (circFree_toJ φ), trivial⟩, trivial⟩
  | .all ψ => circFree_toJ ψ
  | .allJ ψ => circFree_toJ ψ

theorem allJFree_rel : ∀ φ : Fm, allJFree (rel φ)
  | .fvar _ => trivial
  | .bvar _ => trivial
  | .bot => trivial
  | .and φ ψ => ⟨allJFree_rel φ, allJFree_rel ψ⟩
  | .or φ ψ => ⟨allJFree_rel φ, allJFree_rel ψ⟩
  | .imp φ ψ => ⟨allJFree_rel φ, allJFree_rel ψ⟩
  | .circ φ => allJFree_rel φ
  | .all ψ => allJFree_rel ψ
  | .allJ ψ => ⟨⟨trivial, trivial⟩, allJFree_rel ψ⟩

theorem toJ_eq_self_of_circFree : ∀ φ : Fm, circFree φ → toJ φ = φ
  | .fvar _, _ => rfl
  | .bvar _, _ => rfl
  | .bot, _ => rfl
  | .and φ ψ, h => by
      simp only [toJ, toJ_eq_self_of_circFree φ h.1, toJ_eq_self_of_circFree ψ h.2]
  | .or φ ψ, h => by
      simp only [toJ, toJ_eq_self_of_circFree φ h.1, toJ_eq_self_of_circFree ψ h.2]
  | .imp φ ψ, h => by
      simp only [toJ, toJ_eq_self_of_circFree φ h.1, toJ_eq_self_of_circFree ψ h.2]
  | .circ _, h => h.elim
  | .all ψ, h => by simp only [toJ, toJ_eq_self_of_circFree ψ h]
  | .allJ ψ, h => by simp only [toJ, toJ_eq_self_of_circFree ψ h]

theorem rel_eq_self_of_allJFree : ∀ φ : Fm, allJFree φ → rel φ = φ
  | .fvar _, _ => rfl
  | .bvar _, _ => rfl
  | .bot, _ => rfl
  | .and φ ψ, h => by
      simp only [rel, rel_eq_self_of_allJFree φ h.1, rel_eq_self_of_allJFree ψ h.2]
  | .or φ ψ, h => by
      simp only [rel, rel_eq_self_of_allJFree φ h.1, rel_eq_self_of_allJFree ψ h.2]
  | .imp φ ψ, h => by
      simp only [rel, rel_eq_self_of_allJFree φ h.1, rel_eq_self_of_allJFree ψ h.2]
  | .circ φ, h => by simp only [rel, rel_eq_self_of_allJFree φ h]
  | .all ψ, h => by simp only [rel, rel_eq_self_of_allJFree ψ h]
  | .allJ _, h => h.elim

/-! ## The translations preserve local closure and commute with opening

These are the four facts the interpretation theorems need at the quantifier
cases (`wip/p2llStatements.lean`): `(ψ^χ)* = ψ*^χ*` unconditionally, and
`(ψ^χ)° = ψ°^χ°` for locally closed `χ` (the `◯` case shifts, `shiftAt_openRec`).
The equalities are proved with `simp only`: plain `simp` decides `0 = k + 1` by
`Nat.right_eq_add`, whose proof is classical. -/

theorem lcAt_toJ : ∀ (k : Nat) (φ : Fm), lcAt k φ → lcAt k (toJ φ)
  | _, .fvar _, _ => trivial
  | _, .bvar _, h => h
  | _, .bot, _ => trivial
  | k, .and φ ψ, h => ⟨lcAt_toJ k φ h.1, lcAt_toJ k ψ h.2⟩
  | k, .or φ ψ, h => ⟨lcAt_toJ k φ h.1, lcAt_toJ k ψ h.2⟩
  | k, .imp φ ψ, h => ⟨lcAt_toJ k φ h.1, lcAt_toJ k ψ h.2⟩
  | k, .circ φ, h =>
      ⟨⟨lcAt_shiftAt 0 k (toJ φ) (lcAt_toJ k φ h), Nat.succ_pos k⟩, Nat.succ_pos k⟩
  | k, .all ψ, h => lcAt_toJ (k + 1) ψ h
  | k, .allJ ψ, h => lcAt_toJ (k + 1) ψ h

theorem lc_toJ {φ : Fm} (h : LC φ) : LC (toJ φ) := lcAt_toJ 0 φ h

theorem lcAt_rel : ∀ (k : Nat) (φ : Fm), lcAt k φ → lcAt k (rel φ)
  | _, .fvar _, _ => trivial
  | _, .bvar _, h => h
  | _, .bot, _ => trivial
  | k, .and φ ψ, h => ⟨lcAt_rel k φ h.1, lcAt_rel k ψ h.2⟩
  | k, .or φ ψ, h => ⟨lcAt_rel k φ h.1, lcAt_rel k ψ h.2⟩
  | k, .imp φ ψ, h => ⟨lcAt_rel k φ h.1, lcAt_rel k ψ h.2⟩
  | k, .circ φ, h => lcAt_rel k φ h
  | k, .all ψ, h => lcAt_rel (k + 1) ψ h
  | k, .allJ ψ, h => ⟨⟨Nat.succ_pos k, Nat.succ_pos k⟩, lcAt_rel (k + 1) ψ h⟩

theorem lc_rel {φ : Fm} (h : LC φ) : LC (rel φ) := lcAt_rel 0 φ h

theorem rel_openRec : ∀ (k : Nat) (u ψ : Fm), rel (openRec k u ψ) = openRec k (rel u) (rel ψ)
  | _, _, .fvar _ => rfl
  | k, u, .bvar n => by
      by_cases hn : n = k
      · subst hn
        simp [openRec, rel]
      · simp [openRec, rel, hn]
  | _, _, .bot => rfl
  | k, u, .and φ ψ => by simp only [openRec, rel, rel_openRec k u φ, rel_openRec k u ψ]
  | k, u, .or φ ψ => by simp only [openRec, rel, rel_openRec k u φ, rel_openRec k u ψ]
  | k, u, .imp φ ψ => by simp only [openRec, rel, rel_openRec k u φ, rel_openRec k u ψ]
  | k, u, .circ φ => by simp only [openRec, rel, rel_openRec k u φ]
  | k, u, .all ψ => by simp only [openRec, rel, rel_openRec (k + 1) u ψ]
  | k, u, .allJ ψ => by
      have h0 : (0 : Nat) ≠ k + 1 := (Nat.succ_ne_zero k).symm
      simp only [openRec, rel, allNuc, rel_openRec (k + 1) u ψ, if_neg h0]

theorem rel_opn (ψ u : Fm) : rel (ψ.opn u) = (rel ψ).opn (rel u) := rel_openRec 0 u ψ

theorem toJ_openRec : ∀ (k : Nat) (u ψ : Fm), LC u →
    toJ (openRec k u ψ) = openRec k (toJ u) (toJ ψ)
  | _, _, .fvar _, _ => rfl
  | k, u, .bvar n, _ => by
      by_cases hn : n = k
      · subst hn
        simp [openRec, toJ]
      · simp [openRec, toJ, hn]
  | _, _, .bot, _ => rfl
  | k, u, .and φ ψ, hu => by
      simp only [openRec, toJ, toJ_openRec k u φ hu, toJ_openRec k u ψ hu]
  | k, u, .or φ ψ, hu => by
      simp only [openRec, toJ, toJ_openRec k u φ hu, toJ_openRec k u ψ hu]
  | k, u, .imp φ ψ, hu => by
      simp only [openRec, toJ, toJ_openRec k u φ hu, toJ_openRec k u ψ hu]
  | k, u, .circ φ, hu => by
      have h0 : (0 : Nat) ≠ k + 1 := (Nat.succ_ne_zero k).symm
      simp only [openRec, toJ, toJ_openRec k u φ hu, circJ, rpBody, if_neg h0,
        shiftAt_openRec 0 k (toJ u) (toJ φ) (Nat.zero_le k) (lc_toJ hu)]
  | k, u, .all ψ, hu => by simp only [openRec, toJ, toJ_openRec (k + 1) u ψ hu]
  | k, u, .allJ ψ, hu => by simp only [openRec, toJ, toJ_openRec (k + 1) u ψ hu]

theorem toJ_opn {u : Fm} (ψ : Fm) (hu : LC u) : toJ (ψ.opn u) = (toJ ψ).opn (toJ u) :=
  toJ_openRec 0 u ψ hu

end Fm

end P2LL

/-! ## Pins (upper bounds; each first run at `[]` to watch it fail, see
`wip/p2ll-STATUS.md`) -/

#axioms_within P2LL.Fm.openRec_lcAt [propext]
#axioms_within P2LL.Fm.shiftAt_lcAt [propext]
#axioms_within P2LL.Fm.lcAt_openRec [propext]
#axioms_within P2LL.Fm.rpBody_opn [propext]
#axioms_within P2LL.Fm.lc_rpBody [propext]
#axioms_within P2LL.Fm.circFree_toJ []
#axioms_within P2LL.Fm.allJFree_rel []
#axioms_within P2LL.Fm.toJ_eq_self_of_circFree [propext]
#axioms_within P2LL.Fm.rel_eq_self_of_allJFree [propext]
#axioms_within P2LL.Fm.lcAt_shiftAt []
#axioms_within P2LL.Fm.shiftAt_openRec [propext]
#axioms_within P2LL.Fm.lcAt_of_openRec [propext]
#axioms_within P2LL.Fm.lcAt_toJ []
#axioms_within P2LL.Fm.lcAt_rel []
#axioms_within P2LL.Fm.rel_openRec [propext]
#axioms_within P2LL.Fm.toJ_openRec [propext]
