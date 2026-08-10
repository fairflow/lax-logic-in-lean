/-!
# LJF◯: the lax-flagged focused calculus, and uniform interpolation for PLL

The ◯-extension of `LaxLogic/LJF.lean` (which stays green beside this file as
the IPC control), per `docs/ljfo-plan.md`.  Zero imports, deliberately: the
auditability property — no other calculus can carry any part of the proof —
is preserved from the IPC campaign.

Design (settled by `PLLFocused.lean` and the blocker exercise, corrected by
the paper pass):

* `Neg` gains `circ : Pos → Neg`; nothing else in the syntax.
* A flag `JD ::= tru | lax` on all four judgments.  Three rules are
  flag-specific: `circL` (left focus on a box, lax only — the modal
  content), `laxOf` (the truth-to-lax coercion at the stable judgment —
  `PLLFocused` lacks it and thereby misses `◯φ` for provable implicational
  `φ`; found by the identity port, recorded as plan §3-results (f)), and
  `circR` *sets* its premise to lax.  `impR`/`andR` are tru-only (at lax
  they would assert the converse of K, refuted in-repo).  `impL` proves its
  argument truly.  Everything else threads the flag.
* Contexts are persistent (`lfoc` selects by membership): the G4iLL
  contraction failure cannot arise, machine-checked at the blocker.
* The lax goal is definable (`Γ ⊢lax P` iff `Γ ⊢tru ↓◯P`-wise), so the
  interpolant recursion of Part 2 carries **no flag** — only the
  derivation traversals do.

Part 1 (this stage): syntax, judgments, weakening, identity, weights.
-/

namespace LJFO

/-! ## Polarised syntax -/

mutual
/-- Positive (synchronous) propositions — unchanged from `LJF`. -/
inductive Pos where
  | atom : String → Pos
  | fls  : Pos
  | or   : Pos → Pos → Pos
  | down : Neg → Pos
  deriving DecidableEq
/-- Negative (asynchronous) propositions; `circ` is the lax modality, with a
positive body (its right rule enters the lax phase, its left rule is the
lax-only focus). -/
inductive Neg where
  | up   : Pos → Neg
  | imp  : Pos → Neg → Neg
  | and  : Neg → Neg → Neg
  | circ : Pos → Neg
  deriving DecidableEq
end

/-- The judgment flag: `tru` for truth, `lax` for the lax judgment. -/
inductive JD where
  | tru : JD
  | lax : JD
  deriving DecidableEq

/-! ## The calculus -/

mutual

/-- A **stable sequent** at judgment `j`: focus right, focus on a
hypothesis, or — the coercion `laxOf` — establish a lax goal by proving it
truly.  `laxOf` is Pfenning–Davies `laxIntro` in focused form, placed at
the stable judgment, where phase transitions belong. -/
inductive Stab : List Neg → JD → Pos → Type
  | rfoc {Γ j P} : RFocus Γ j P → Stab Γ j P
  | lfoc {Γ j P N} (h : N ∈ Γ) : LFoc Γ N j P → Stab Γ j P
  | laxOf {Γ P} : Stab Γ .tru P → Stab Γ .lax P

/-- **Right focus** on a positive goal; every rule threads the flag. -/
inductive RFocus : List Neg → JD → Pos → Type
  | init {Γ j a} (h : Neg.up (Pos.atom a) ∈ Γ) : RFocus Γ j (.atom a)
  | or1 {Γ j P Q} : RFocus Γ j P → RFocus Γ j (.or P Q)
  | or2 {Γ j P Q} : RFocus Γ j Q → RFocus Γ j (.or P Q)
  | rel {Γ j N} : Inv Γ [] j N → RFocus Γ j (.down N)

/-- **Left focus** on a negative hypothesis.  `impL` proves its argument
truly; `circL` — the only rule with modal *content* — opens a box, at a
lax goal only.  This is `SC`'s "succedent must be `◯`-shaped", as a phase
condition. -/
inductive LFoc : List Neg → Neg → JD → Pos → Type
  | rel {Γ j Q P} : Inv Γ [Q] j (.up P) → LFoc Γ (.up Q) j P
  | impL {Γ j Q N P} : Stab Γ .tru Q → LFoc Γ N j P → LFoc Γ (.imp Q N) j P
  | and1 {Γ j M N P} : LFoc Γ M j P → LFoc Γ (.and M N) j P
  | and2 {Γ j M N P} : LFoc Γ N j P → LFoc Γ (.and M N) j P
  | circL {Γ Q P} : Inv Γ [Q] .lax (.up P) → LFoc Γ (.circ Q) .lax P

/-- **Inversion.**  The right rules for `⊃` and `∧` are tru-only (at lax
they would assert the converse of K); `circR` sets its premise to lax from
either flag; the `Ω`-processing rules thread the flag. -/
inductive Inv : List Neg → List Pos → JD → Neg → Type
  | impR {Γ Ω Q N} : Inv Γ (Q :: Ω) .tru N → Inv Γ Ω .tru (.imp Q N)
  | andR {Γ Ω M N} : Inv Γ Ω .tru M → Inv Γ Ω .tru N → Inv Γ Ω .tru (.and M N)
  | circR {Γ Ω j P} : Inv Γ Ω .lax (.up P) → Inv Γ Ω j (.circ P)
  | stable {Γ j P} : Stab Γ j P → Inv Γ [] j (.up P)
  | orL {Γ Ω j P Q N} : Inv Γ (P :: Ω) j N → Inv Γ (Q :: Ω) j N →
      Inv Γ (.or P Q :: Ω) j N
  | flsL {Γ Ω j N} : Inv Γ (.fls :: Ω) j N
  | downL {Γ Ω j M N} : Inv (M :: Γ) Ω j N → Inv Γ (.down M :: Ω) j N
  | atomL {Γ Ω j a N} : Inv (.up (.atom a) :: Γ) Ω j N →
      Inv Γ (.atom a :: Ω) j N

end

/-! ## Contexts: the subset relation -/

/-- `Γ'` contains everything in `Γ`. -/
def Sub (Γ Γ' : List Neg) : Prop := ∀ N, N ∈ Γ → N ∈ Γ'

namespace Sub

theorem refl (Γ : List Neg) : Sub Γ Γ := fun _ h => h

theorem trans {Γ Γ' Γ'' : List Neg} (h₁ : Sub Γ Γ') (h₂ : Sub Γ' Γ'') :
    Sub Γ Γ'' := fun N h => h₂ N (h₁ N h)

/-- Extending both sides by the same hypothesis. -/
theorem cons {Γ Γ' : List Neg} (X : Neg) (h : Sub Γ Γ') :
    Sub (X :: Γ) (X :: Γ') := by
  intro N hN
  rcases List.mem_cons.mp hN with rfl | hN
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (h N hN)

/-- Extending the target. -/
theorem grow {Γ : List Neg} (X : Neg) : Sub Γ (X :: Γ) :=
  fun _ h => List.mem_cons_of_mem _ h

end Sub

/-! ## Weakening -/

mutual

/-- Weakening of a stable sequent. -/
def Stab.wk : {Γ Γ' : List Neg} → {j : JD} → {P : Pos} →
    Sub Γ Γ' → Stab Γ j P → Stab Γ' j P
  | _, _, _, _, H, .rfoc d   => .rfoc (RFocus.wk H d)
  | _, _, _, _, H, .lfoc h d => .lfoc (H _ h) (LFoc.wk H d)
  | _, _, _, _, H, .laxOf d  => .laxOf (Stab.wk H d)

/-- Weakening under right focus. -/
def RFocus.wk : {Γ Γ' : List Neg} → {j : JD} → {P : Pos} →
    Sub Γ Γ' → RFocus Γ j P → RFocus Γ' j P
  | _, _, _, _, H, .init h => .init (H _ h)
  | _, _, _, _, H, .or1 d  => .or1 (RFocus.wk H d)
  | _, _, _, _, H, .or2 d  => .or2 (RFocus.wk H d)
  | _, _, _, _, H, .rel d  => .rel (Inv.wk H d)

/-- Weakening under left focus. -/
def LFoc.wk : {Γ Γ' : List Neg} → {N : Neg} → {j : JD} → {P : Pos} →
    Sub Γ Γ' → LFoc Γ N j P → LFoc Γ' N j P
  | _, _, _, _, _, H, .rel d    => .rel (Inv.wk H d)
  | _, _, _, _, _, H, .impL a d => .impL (Stab.wk H a) (LFoc.wk H d)
  | _, _, _, _, _, H, .and1 d   => .and1 (LFoc.wk H d)
  | _, _, _, _, _, H, .and2 d   => .and2 (LFoc.wk H d)
  | _, _, _, _, _, H, .circL d  => .circL (Inv.wk H d)

/-- Weakening of an inversion sequent. -/
def Inv.wk : {Γ Γ' : List Neg} → {Ω : List Pos} → {j : JD} → {N : Neg} →
    Sub Γ Γ' → Inv Γ Ω j N → Inv Γ' Ω j N
  | _, _, _, _, _, H, .impR d   => .impR (Inv.wk H d)
  | _, _, _, _, _, H, .andR d e => .andR (Inv.wk H d) (Inv.wk H e)
  | _, _, _, _, _, H, .circR d  => .circR (Inv.wk H d)
  | _, _, _, _, _, H, .stable d => .stable (Stab.wk H d)
  | _, _, _, _, _, H, .orL d e  => .orL (Inv.wk H d) (Inv.wk H e)
  | _, _, _, _, _, _, .flsL     => .flsL
  | _, _, _, _, _, H, .downL d  => .downL (Inv.wk (Sub.cons _ H) d)
  | _, _, _, _, _, H, .atomL d  => .atomL (Inv.wk (Sub.cons _ H) d)

end

/-- A tru-stable sequent serves at either judgment (`laxOf` when needed). -/
def Stab.ofTru : {Γ : List Neg} → {P : Pos} → (j : JD) →
    Stab Γ .tru P → Stab Γ j P
  | _, _, .tru, s => s
  | _, _, .lax, s => .laxOf s

/-! ## Size -/

mutual
/-- Size of a positive. -/
def sizePos : Pos → Nat
  | .atom _  => 1
  | .fls     => 1
  | .or P Q  => sizePos P + sizePos Q + 1
  | .down N  => sizeNeg N + 1
/-- Size of a negative.  `circ` costs one, like a shift. -/
def sizeNeg : Neg → Nat
  | .up P    => sizePos P + 1
  | .imp P N => sizePos P + sizeNeg N + 1
  | .and M N => sizeNeg M + sizeNeg N + 1
  | .circ P  => sizePos P + 1
end

theorem sizePos_pos (P : Pos) : 0 < sizePos P := by
  cases P <;> simp [sizePos] <;> omega

theorem sizeNeg_pos (N : Neg) : 0 < sizeNeg N := by
  cases N <;> simp [sizeNeg] <;> omega

/-! ## Identity expansion

As in `LJF`, with one refinement forced by the flags: the right focus a
`posRestore` continuation receives is always **tru** (identity's own right
focus never needs the lax phase), while the judgment of the sequent being
built is free — the leaves coerce with `Stab.ofTru`.  `idNegK`/`idNeg` are
tru-only (`impR` is), which is no loss: lax goals are positive. -/

mutual

/-- **Left inversion of a positive returns it on the right**, at any
judgment, the returned focus at `tru`. -/
def posRestore (Q : Pos) (Γ : List Neg) (Ω : List Pos) {j : JD} (N : Neg)
    (k : ∀ Γ', Sub Γ Γ' → RFocus Γ' .tru Q → Inv Γ' Ω j N) :
    Inv Γ (Q :: Ω) j N :=
  match Q, k with
  | .atom a, k =>
      .atomL (k (.up (.atom a) :: Γ) (Sub.grow _) (.init (List.mem_cons_self ..)))
  | .fls, _ => .flsL
  | .down M, k =>
      .downL (k (M :: Γ) (Sub.grow _)
        (.rel (idNegK M (M :: Γ)
          (fun _ _ _ hs lf => .lfoc (hs _ (List.mem_cons_self ..)) lf))))
  | .or P₁ P₂, k =>
      .orL (posRestore P₁ Γ Ω N (fun Γ' hs r => k Γ' hs (.or1 r)))
           (posRestore P₂ Γ Ω N (fun Γ' hs r => k Γ' hs (.or2 r)))
termination_by sizePos Q
decreasing_by
  all_goals simp_wf
  all_goals simp only [sizePos]
  all_goals omega

/-- **A usable negative is a provable negative** — truly.  The continuation
turns a left focus on `N` *at any judgment* into a stable sequent: the flag
generality is forced by the `circ` case, whose left focus (`circL`) exists
only at lax.  That case is the one genuinely new clause: to prove `◯P`,
enter the lax phase (`circR`), left-focus the usable `◯P` through the
continuation, and restore the returned `P` — coercing the leaf with
`laxOf`. -/
def idNegK (N : Neg) (Γ : List Neg)
    (k : ∀ Γ' (j : JD) P, Sub Γ Γ' → LFoc Γ' N j P → Stab Γ' j P) :
    Inv Γ [] .tru N :=
  match N, k with
  | .up P, k =>
      .stable (k Γ .tru P (Sub.refl Γ)
        (.rel (posRestore P Γ [] (.up P) (fun _ _ r => .stable (.rfoc r)))))
  | .imp Q M, k =>
      .impR (posRestore Q Γ [] M (fun Γ' hs r =>
        idNegK M Γ' (fun Γ'' j P hs' lf =>
          k Γ'' j P (Sub.trans hs hs') (.impL (.rfoc (RFocus.wk hs' r)) lf))))
  | .and M₁ M₂, k =>
      .andR (idNegK M₁ Γ (fun Γ' j P hs lf => k Γ' j P hs (.and1 lf)))
            (idNegK M₂ Γ (fun Γ' j P hs lf => k Γ' j P hs (.and2 lf)))
  | .circ P, k =>
      .circR (.stable (k Γ .lax P (Sub.refl Γ)
        (.circL (posRestore P Γ [] (.up P)
          (fun _ _ r => .stable (.laxOf (.rfoc r)))))))
termination_by sizeNeg N
decreasing_by
  all_goals simp_wf
  all_goals simp only [sizeNeg]
  all_goals omega

end

/-- **Identity, negative form**: every hypothesis proves itself, truly. -/
def idNeg (N : Neg) (Γ : List Neg) (h : N ∈ Γ) : Inv Γ [] .tru N :=
  idNegK N Γ (fun _ _ _ hs lf => .lfoc (hs _ h) lf)

/-- **Identity, positive form**: `P ⇒ P` at any judgment, `P` inverted on
the left and focused (truly) on the right. -/
def idPos (P : Pos) (Γ : List Neg) (j : JD) : Inv Γ [P] j (.up P) :=
  posRestore P Γ [] (.up P) (fun _ _ r => .stable (Stab.ofTru j (.rfoc r)))

/-! ## The weight -/

mutual
/-- Weight of a positive — unchanged from `LJF`. -/
def wPos : Pos → Nat
  | .atom _ => 1
  | .fls    => 1
  | .or P Q => wPos P + wPos Q + 1
  | .down M => wNeg M + 1
/-- Weight of a negative.  `circ` costs `+1`: opening a box moves
`3^{wP+1}` out of the station and `2·3^{wP}` into the pending side, and
`2·3^w < 3^{w+1}` — the same inequality that pays for the atom fire. -/
def wNeg : Neg → Nat
  | .up P    => wPos P
  | .imp Q N => wPos Q + wNeg N + 1
  | .and M N => wNeg M + wNeg N + 3
  | .circ P  => wPos P + 1
end

theorem wPos_pos (P : Pos) : 0 < wPos P := by
  cases P <;> simp [wPos] <;> omega

theorem wNeg_pos (N : Neg) : 0 < wNeg N := by
  cases N with
  | up P => simpa [wNeg] using wPos_pos P
  | imp Q N => simp only [wNeg]; omega
  | and M N => simp only [wNeg]; omega
  | circ P => simpa [wNeg] using wPos_pos P


theorem p3_pos (n : Nat) : 0 < 3 ^ n := Nat.pow_pos (by omega)

theorem p3_mono {a b : Nat} (h : a ≤ b) : 3 ^ a ≤ 3 ^ b :=
  Nat.pow_le_pow_right (by omega) h

theorem p3_strict {a b : Nat} (h : a < b) : 3 ^ a < 3 ^ b := by
  calc 3 ^ a < 3 ^ a * 3 := by have := p3_pos a; omega
    _ = 3 ^ (a + 1) := by rw [Nat.pow_succ]
    _ ≤ 3 ^ b := p3_mono (by omega)

/-- Two summands strictly under the bound: `3^a + 3^b < 3^c` when `a,b < c`. -/
theorem p3_add {a b c : Nat} (ha : a < c) (hb : b < c) :
    3 ^ a + 3 ^ b < 3 ^ c := by
  have h1 : 3 ^ a ≤ 3 ^ (c - 1) := p3_mono (by omega)
  have h2 : 3 ^ b ≤ 3 ^ (c - 1) := p3_mono (by omega)
  have h3 : 3 ^ c = 3 ^ (c - 1) * 3 := by
    rw [← Nat.pow_succ]; congr 1; omega
  have := p3_pos (c - 1)
  omega

/-- `2·3^a < 3^c` when `a < c`. -/
theorem p3_2 {a c : Nat} (ha : a + 1 ≤ c) : 2 * 3 ^ a < 3 ^ c := by
  have h1 : 3 ^ a ≤ 3 ^ (c - 1) := p3_mono (by omega)
  have h3 : 3 ^ c = 3 ^ (c - 1) * 3 := by
    rw [← Nat.pow_succ]; congr 1; omega
  have := p3_pos (c - 1)
  omega

/-- `2·3^a + 3^b < 3^c` when `a + 2 ≤ c` and `b + 1 ≤ c`. -/
theorem p3_21 {a b c : Nat} (ha : a + 2 ≤ c) (hb : b + 1 ≤ c) :
    2 * 3 ^ a + 3 ^ b < 3 ^ c := by
  have h1 : 3 ^ a ≤ 3 ^ (c - 2) := p3_mono (by omega)
  have h2 : 3 ^ b ≤ 3 ^ (c - 2) * 3 := by
    have : 3 ^ b ≤ 3 ^ (c - 1) := p3_mono (by omega)
    have e : 3 ^ (c - 1) = 3 ^ (c - 2) * 3 := by
      rw [← Nat.pow_succ]; congr 1; omega
    omega
  have h3 : 3 ^ c = 3 ^ (c - 2) * 3 * 3 := by
    rw [← Nat.pow_succ, ← Nat.pow_succ]; congr 1; omega
  have := p3_pos (c - 2)
  omega

/-! ## Context measure -/

/-- `Σ 3^(weight)` over a context. -/
def sum3 : List Neg → Nat
  | []     => 0
  | N :: Γ => 3 ^ wNeg N + sum3 Γ

theorem sum3_append (Γ Δ : List Neg) :
    sum3 (Γ ++ Δ) = sum3 Γ + sum3 Δ := by
  induction Γ with
  | nil => simp [sum3]
  | cons N Γ ih => simp [sum3, ih]; omega

/-! ## Inversion of a positive, as data

`invertPos Q` is the list of **branches** produced by fully inverting `Q` on
the left; each branch is the list of stable hypotheses it contributes.
`⊥` has no branches; `∨` concatenates; an atom or a shift is one branch with
one hypothesis. -/

def invertPos : Pos → List (List Neg)
  | .atom a  => [[.up (.atom a)]]
  | .fls     => []
  | .or P Q  => invertPos P ++ invertPos Q
  | .down M  => [[M]]

/-- Each branch weighs no more than the positive it came from. -/
theorem invertPos_le : ∀ (P : Pos), ∀ b ∈ invertPos P, sum3 b ≤ 3 ^ wPos P
  | .atom a, b, hb => by
      simp only [invertPos, List.mem_singleton] at hb; subst hb
      simp [sum3, wNeg, wPos]
  | .fls, b, hb => by simp [invertPos] at hb
  | .or P Q, b, hb => by
      simp only [invertPos, List.mem_append] at hb
      rcases hb with hb | hb
      · exact Nat.le_trans (invertPos_le P b hb)
          (p3_mono (by simp only [wPos]; omega))
      · exact Nat.le_trans (invertPos_le Q b hb)
          (p3_mono (by simp only [wPos]; omega))
  | .down M, b, hb => by
      simp only [invertPos, List.mem_singleton] at hb; subst hb
      simp only [sum3, wPos]
      have := p3_strict (a := wNeg M) (b := wNeg M + 1) (by omega)
      omega
termination_by P => sizePos P
decreasing_by all_goals (simp_wf; simp only [sizePos]; omega)

/-- For a non-atomic positive the inequality is strict — this is what makes
moving a hypothesis's branches into the context a descent. -/
theorem invertPos_lt {P : Pos} (h : ∀ a, P ≠ .atom a) :
    ∀ b ∈ invertPos P, sum3 b < 3 ^ wPos P := by
  cases P with
  | atom a => exact absurd rfl (h a)
  | fls => intro b hb; simp [invertPos] at hb
  | or P Q =>
      intro b hb
      simp only [invertPos, List.mem_append] at hb
      rcases hb with hb | hb
      · exact Nat.lt_of_le_of_lt (invertPos_le P b hb)
          (p3_strict (by simp only [wPos]; have := wPos_pos Q; omega))
      · exact Nat.lt_of_le_of_lt (invertPos_le Q b hb)
          (p3_strict (by simp only [wPos]; have := wPos_pos P; omega))
  | down M =>
      intro b hb; simp [invertPos] at hb; subst hb
      simp only [sum3, wPos]
      have := p3_strict (a := wNeg M) (b := wNeg M + 1) (by omega)
      omega

/-! ## Positional splits

`splits Γ` lists each member of `Γ` together with the rest of the context —
the tool by which the saturated clauses consume a hypothesis without needing
decidable equality on formulas. -/

def splits : List Neg → List (Neg × List Neg)
  | []     => []
  | X :: Γ => (X, Γ) :: (splits Γ).map (fun ⟨Y, rest⟩ => (Y, X :: rest))

theorem splits_sum {Γ : List Neg} :
    ∀ {X rest}, (X, rest) ∈ splits Γ → sum3 Γ = 3 ^ wNeg X + sum3 rest := by
  induction Γ with
  | nil => intro X rest h; simp [splits] at h
  | cons Y Γ ih =>
      intro X rest h
      simp only [splits, List.mem_cons, List.mem_map] at h
      rcases h with h | ⟨⟨Z, rest'⟩, hZ, hEq⟩
      · cases h; rfl
      · cases hEq
        simp only [sum3, ih hZ]; omega

theorem splits_mem {Γ : List Neg} :
    ∀ {X rest}, (X, rest) ∈ splits Γ → X ∈ Γ := by
  induction Γ with
  | nil => intro X rest h; simp [splits] at h
  | cons Y Γ ih =>
      intro X rest h
      simp only [splits, List.mem_cons, List.mem_map] at h
      rcases h with h | ⟨⟨Z, rest'⟩, hZ, hEq⟩
      · cases h; exact List.mem_cons_self ..
      · cases hEq; exact List.mem_cons_of_mem _ (ih hZ)



/-! ## Interpolant connectives

The interpolant is a formula of `LJF` itself, carried as a `Neg` (hypotheses
are negative).  Disjunction of negatives goes through the shifts. -/

/-- `⊤` as a negative: `⊥ ⊃ ⊥`. -/
def nTop : Neg := .imp .fls (.up .fls)
/-- `⊥` as a negative. -/
def nBot : Neg := .up .fls
/-- Conjunction of interpolants. -/
def nAnd (M N : Neg) : Neg := .and M N
/-- Disjunction of interpolants: `↑(↓M ∨ ↓N)`. -/
def nOr (M N : Neg) : Neg := .up (.or (.down M) (.down N))
/-- Conjunction of a list, unit `⊤`. -/
def nAndAll : List Neg → Neg := fun l => l.foldr nAnd nTop
/-- Disjunction of a list, unit `⊥`. -/
def nOrAll : List Neg → Neg := fun l => l.foldr nOr nBot

/-- `p`-guard: the unit `C` when the atom is `p`, else `D`.  A named helper
so the aggregate match-arms stay opaque applications, which keeps the
functional-induction cases clean. -/
def pGuard (p a : String) (C D : Neg) : Neg := if a = p then C else D

/-- The head disjunct of an atomic goal: nothing if the atom is `p`. -/
def atomHead (p q : String) : List Neg := if q = p then [] else [.up (.atom q)]

/-- Is the atom `a` a hypothesis (as `↑a`)? -/
def atomMem (a : String) (Γ : List Neg) : Bool :=
  Γ.any (fun | .up (.atom b) => a == b | _ => false)

/-! ## The fire scan

A parked implication `a ⊃ N` fires as soon as its atom is present.  The scan
walks the positional splits and returns the first firable one. -/

def findFire (full : List Neg) : List (Neg × List Neg) → Option (String × Neg × List Neg)
  | [] => none
  | (X, rest) :: more =>
    match X with
    | .imp (.atom a) N =>
        if atomMem a full then some (a, N, rest) else findFire full more
    | _ => findFire full more

theorem findFire_mem {full : List Neg} :
    ∀ {l : List (Neg × List Neg)} {a N rest},
      findFire full l = some (a, N, rest) → (Neg.imp (.atom a) N, rest) ∈ l := by
  intro l
  induction l with
  | nil => intro a N rest h; simp [findFire] at h
  | cons XR more ih =>
      intro a N rest h
      obtain ⟨X, R⟩ := XR
      match X, h with
      | .imp (.atom b) N', h => ?_
      | .up P, h => exact List.mem_cons_of_mem _ (ih h)
      | .imp .fls N', h => exact List.mem_cons_of_mem _ (ih h)
      | .imp (.or Q₁ Q₂) N', h => exact List.mem_cons_of_mem _ (ih h)
      | .imp (.down M) N', h => exact List.mem_cons_of_mem _ (ih h)
      | .and M₁ M₂, h => exact List.mem_cons_of_mem _ (ih h)
      | .circ P, h => exact List.mem_cons_of_mem _ (ih h)
      simp only [findFire] at h
      by_cases hM : atomMem b full
      · simp [hM] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact List.mem_cons_self ..
      · simp [hM] at h
        exact List.mem_cons_of_mem _ (ih h)

/-- Goal component of the measure. -/
def goalW : Option Neg → Nat
  | none   => 0
  | some G => 3 ^ wNeg G

/-! ## The descent lemmas

One lemma per clause of the recursion below, each stating its measure descent
in exactly the shape the termination checker asks for.  Together they are the
spent form of the weight inequalities. -/

theorem dec_park {t d e : Nat} : 2 * t + (3 ^ e + d) < 2 * (3 ^ e + t) + d := by
  have := p3_pos e; omega

theorem dec_drop {t e : Nat} : t < 3 ^ e + t := by
  have := p3_pos e; omega

theorem dec_shift1 {m t : Nat} : 3 ^ m + t < 3 ^ (m + 1) + t := by
  have := p3_strict (a := m) (b := m + 1) (by omega); omega

theorem dec_and {m n t : Nat} :
    3 ^ m + (3 ^ n + t) < 3 ^ (m + n + 3) + t := by
  have := p3_add (a := m) (b := n) (c := m + n + 3) (by omega) (by omega)
  omega

theorem dec_impor {a b n t : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    3 ^ (a + n + 1) + (3 ^ (b + n + 1) + t) < 3 ^ (a + b + 1 + n + 1) + t := by
  have := p3_add (a := a + n + 1) (b := b + n + 1) (c := a + b + 1 + n + 1)
    (by omega) (by omega)
  omega

theorem dec_stripshift {x n t : Nat} :
    3 ^ (x + n + 1) + t < 3 ^ (x + 1 + n + 1) + t := by
  have := p3_strict (a := x + n + 1) (b := x + 1 + n + 1) (by omega); omega

theorem dec_curry {m₁ m₂ n t : Nat} :
    3 ^ (m₁ + 1 + (m₂ + 1 + n + 1) + 1) + t <
      3 ^ (m₁ + m₂ + 3 + 1 + n + 1) + t := by
  have := p3_strict (a := m₁ + 1 + (m₂ + 1 + n + 1) + 1)
    (b := m₁ + m₂ + 3 + 1 + n + 1) (by omega)
  omega

theorem dec_orctx {P Q : Pos} {b : List Neg} {t : Nat}
    (hb : b ∈ invertPos (Pos.or P Q)) :
    sum3 b + t < 3 ^ (wPos P + wPos Q + 1) + t := by
  have h := invertPos_lt (P := Pos.or P Q) (by intro a h; nomatch h) b hb
  simp only [wPos] at h; omega

theorem dec_fire {done rest : List Neg} {a : String} {N : Neg}
    (hf : findFire done (splits done) = some (a, N, rest)) :
    2 * (3 ^ wNeg N + 0) + sum3 rest < 2 * 0 + sum3 done := by
  have hs := splits_sum (findFire_mem hf)
  simp only [wNeg, wPos] at hs
  have := p3_2 (a := wNeg N) (c := 1 + wNeg N + 1) (by omega)
  omega

/-- Box conjunct: opening a parked box pays with the box's own weight
(`2·3^w < 3^{w+1}`, the fire inequality one level up). -/
theorem dec_boxE {done rest : List Neg} {Q : Pos}
    (h : (Neg.circ Q, rest) ∈ splits done) :
    2 * (3 ^ wPos Q + 0) + sum3 rest < 2 * 0 + sum3 done := by
  have hs := splits_sum h
  simp only [wNeg] at hs
  have := p3_2 (a := wPos Q) (c := wPos Q + 1) (by omega)
  omega

/-- Modal pair, `∀p`-component: `A(rest ⇒ ◯Q′)` from the station. -/
theorem dec_cimp1 {done rest : List Neg} {Q' : Pos} {N : Neg}
    (h : (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done) :
    sum3 rest + 3 ^ (wPos Q' + 1) < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have := p3_strict (a := wPos Q' + 1) (b := wPos Q' + 1 + 1 + wNeg N + 1) (by omega)
  omega

/-- Modal pair, fire component: `E(N :: rest)`. -/
theorem dec_cimp2 {done rest : List Neg} {Q' : Pos} {N : Neg}
    (h : (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done) :
    2 * (3 ^ wNeg N + 0) + sum3 rest < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have := p3_2 (a := wNeg N) (c := wPos Q' + 1 + 1 + wNeg N + 1) (by omega)
  omega

/-- Any member removal shrinks the station (the E-res component). -/
theorem dec_cimp3 {done rest : List Neg} {X : Neg}
    (h : (X, rest) ∈ splits done) : sum3 rest < sum3 done := by
  have hs := splits_sum h
  have := p3_pos (wNeg X)
  omega

/-- `dec_cimp1`, at an arbitrary goal weight (the `_g` discipline: state
the goal exactly so the farm's `exact` instantiates `g` without omega ever
meeting two power atoms — the pow-drop defect strikes otherwise). -/
theorem dec_cimp1_g {done rest : List Neg} {Q' : Pos} {N : Neg} {g : Nat}
    (h : (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done) :
    2 * 0 + sum3 rest + 3 ^ (wPos Q' + 1) < 2 * 0 + sum3 done + g := by
  have := dec_cimp1 h; omega

/-- The box-opening attack, body component: shared goal weight. -/
theorem dec_boxA_g {done rest : List Neg} {R : Pos} {g : Nat}
    (h : (Neg.circ R, rest) ∈ splits done) :
    2 * (3 ^ wPos R + 0) + sum3 rest + g < 2 * 0 + sum3 done + g := by
  have := dec_boxE h; omega

/-- The box-opening attack, guard component: the goal drops to `none`. -/
theorem dec_boxE_g {done rest : List Neg} {R : Pos} {g : Nat}
    (h : (Neg.circ R, rest) ∈ splits done) :
    2 * (3 ^ wPos R + 0) + sum3 rest + 0 < 2 * 0 + sum3 done + g := by
  have := dec_boxE h; omega

/-- The modal pair's fire component, at a shared goal weight. -/
theorem dec_cimp2_g {done rest : List Neg} {Q' : Pos} {N : Neg} {g : Nat}
    (h : (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done) :
    2 * (3 ^ wNeg N + 0) + sum3 rest + g < 2 * 0 + sum3 done + g := by
  have := dec_cimp2 h; omega

/-- The `◯`-goal direct row: prove the body truly, one modal cost less. -/
theorem dec_circDirect {d : Nat} {Q : Pos} :
    d + 3 ^ wPos Q < d + 3 ^ (wPos Q + 1) := by
  have := p3_strict (a := wPos Q) (b := wPos Q + 1) (by omega)
  omega

theorem dec_qimp {done rest : List Neg} {a : String} {N : Neg}
    (h : (Neg.imp (Pos.atom a) N, rest) ∈ splits done) :
    2 * (3 ^ wNeg N + 0) + sum3 rest < 2 * 0 + sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have := p3_2 (a := wNeg N) (c := 1 + wNeg N + 1) (by omega)
  omega

theorem dec_qimp_g {done rest : List Neg} {a : String} {N : Neg} {g : Nat}
    (h : (Neg.imp (Pos.atom a) N, rest) ∈ splits done) :
    2 * (3 ^ wNeg N + 0) + sum3 rest < 2 * 0 + sum3 done + g :=
  Nat.lt_of_lt_of_le (dec_qimp h) (by omega)

theorem dec_dyk1 {done rest : List Neg} {Q' : Pos} {N' N : Neg}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * (3 ^ (wNeg N' + 1 + wNeg N + 1) + 0) + sum3 rest +
        3 ^ (wPos Q' + wNeg N' + 1) <
      2 * 0 + sum3 done + 0 := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have := p3_21 (a := wNeg N' + 1 + wNeg N + 1) (b := wPos Q' + wNeg N' + 1)
    (c := wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1)
    (by have := wPos_pos Q'; omega) (by have := wNeg_pos N; omega)
  omega

theorem dec_dyk1_g {done rest : List Neg} {Q' : Pos} {N' N : Neg} {g : Nat}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * (3 ^ (wNeg N' + 1 + wNeg N + 1) + 0) + sum3 rest +
        3 ^ (wPos Q' + wNeg N' + 1) <
      2 * 0 + sum3 done + g := by
  have := dec_dyk1 h; omega

theorem dec_dyk0 {done rest : List Neg} {Q' : Pos} {N' N : Neg}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * (3 ^ (wNeg N' + 1 + wNeg N + 1) + 0) + sum3 rest + 0 <
      2 * 0 + sum3 done + 0 := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have := p3_2 (a := wNeg N' + 1 + wNeg N + 1)
    (c := wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1)
    (by have := wPos_pos Q'; omega)
  omega

theorem dec_dyk2 {done rest : List Neg} {Q' : Pos} {N' N : Neg}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * (3 ^ wNeg N + 0) + sum3 rest < 2 * 0 + sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have := p3_2 (a := wNeg N) (c := wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1)
    (by have := wPos_pos Q'; have := wNeg_pos N'; omega)
  omega

theorem dec_dyk2_g {done rest : List Neg} {Q' : Pos} {N' N : Neg} {g : Nat}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * (3 ^ wNeg N + 0) + sum3 rest < 2 * 0 + sum3 done + g :=
  Nat.lt_of_lt_of_le (dec_dyk2 h) (by omega)

theorem dec_orA {P Q : Pos} {b todo : List Neg} {d g : Nat}
    (hb : b ∈ invertPos (Pos.or P Q)) :
    2 * (sum3 b + sum3 todo) + d + 0 <
      2 * (3 ^ (wPos P + wPos Q + 1) + sum3 todo) + d + g := by
  have h1 := invertPos_lt (P := Pos.or P Q) (fun a h => Pos.noConfusion h) b hb
  simp only [wPos] at h1
  omega

theorem dec_ainv0 {Q : Pos} {b : List Neg} {N : Neg} {d : Nat}
    (hb : b ∈ invertPos Q) :
    2 * sum3 b + d + 0 < 2 * 0 + d + 3 ^ (wPos Q + wNeg N + 1) := by
  have h1 := invertPos_le Q b hb
  have := p3_2 (a := wPos Q) (c := wPos Q + wNeg N + 1)
    (by have := wNeg_pos N; omega)
  omega

theorem dec_ainv {Q : Pos} {b : List Neg} {N : Neg} {d : Nat}
    (hb : b ∈ invertPos Q) :
    2 * sum3 b + d + 3 ^ wNeg N < 2 * 0 + d + 3 ^ (wPos Q + wNeg N + 1) := by
  have h1 := invertPos_le Q b hb
  have := p3_21 (a := wPos Q) (b := wNeg N) (c := wPos Q + wNeg N + 1)
    (by have := wNeg_pos N; omega) (by have := wPos_pos Q; omega)
  omega



/-! ## The uniform interpolant

One recursion computes both quantifiers.  `interp p todo done goal`:

* `goal = none` — **`∃p` mode**: the strongest `p`-free consequence of the
  context `todo ++ done`;
* `goal = some G` — **`∀p` mode**: the weakest `p`-free hypothesis that,
  beside the context, suffices for `G`.

`todo` is the unprocessed part of the context; `done` holds the parked
members, which come in exactly three shapes — atoms `↑a`, implications
`a ⊃ N` whose atom is not yet available, and the Dyckhoff implications
`↓(Q' ⊃ N') ⊃ N`.

The processing clauses consume the head of `todo` and replace it by strictly
lighter material (the residual): this is where each weight inequality is
spent, and each clause is annotated with its inequality.  The aggregate
clauses (at `todo = []`) first fire any parked implication whose atom has
arrived, then read the interpolant off the saturated context.

The measure is `2·sum3 todo + sum3 done + goalW goal`: parking moves a
hypothesis from the doubled side to the single side, so even the bookkeeping
steps are strict, and no lexicographic order is needed. -/

set_option maxHeartbeats 2000000 in
def interp (p : String) : (todo done : List Neg) → (goal : Option Neg) → Neg
  -- ── processing phase: consume the head of `todo` ──
  -- park an atom
  | .up (.atom a) :: todo, done, g =>
      interp p todo (.up (.atom a) :: done) g
  -- absurd hypothesis: `∨` over no branches is `⊥`, `∧` over none is `⊤`
  | .up .fls :: _, _, none => nBot
  | .up .fls :: _, _, some _ => nTop
  -- context split: `∨` of branch results in `∃p` mode, `∧` in `∀p` mode
  -- [sum3 b < 3^(w P∨Q), both branches]
  | .up (.or P Q) :: todo, done, none =>
      nOrAll ((invertPos (.or P Q)).attach.map
        (fun ⟨b, hb⟩ => interp p (b ++ todo) done none))
  -- context split in ∀p mode: each branch conjunct guarded by the branch's
  -- ∃p, for the same reason as the implication goal — minimality would
  -- otherwise demand deriving one branch's ∀p from another branch's ∃p.
  | .up (.or P Q) :: todo, done, some G =>
      nAndAll ((invertPos (.or P Q)).attach.map
        (fun ⟨b, hb⟩ =>
          .imp (.down (interp p (b ++ todo) done none))
            (interp p (b ++ todo) done (some G))))
  -- a shifted negative moves into the context  [w M < w ↑↓M = w M + 1]
  | .up (.down M) :: todo, done, g =>
      interp p (M :: todo) done g
  -- a conjunction splits  [3^wM + 3^wN < 3^(wM+wN+3)]
  | .and M N :: todo, done, g =>
      interp p (M :: N :: todo) done g
  -- `⊥ ⊃ N` is inert: drop it
  | .imp .fls _ :: todo, done, g =>
      interp p todo done g
  -- `a ⊃ N` parks until its atom arrives
  | .imp (.atom a) N :: todo, done, g =>
      interp p todo (.imp (.atom a) N :: done) g
  -- `(Q₁∨Q₂) ⊃ N` splits  [3^(wQ₁+wN+1) + 3^(wQ₂+wN+1) < 3^(wQ₁+wQ₂+1+wN+1)]
  | .imp (.or Q₁ Q₂) N :: todo, done, g =>
      interp p (.imp Q₁ N :: .imp Q₂ N :: todo) done g
  -- `↓↑P' ⊃ N` strips the double shift  [w drops by 1]
  | .imp (.down (.up P')) N :: todo, done, g =>
      interp p (.imp P' N :: todo) done g
  -- currying: `↓(M₁∧M₂) ⊃ N  ↝  ↓M₁ ⊃ (↓M₂ ⊃ N)`  [w: +5 vs +4 — the
  -- inequality that forces `∧` to cost 3]
  | .imp (.down (.and M₁ M₂)) N :: todo, done, g =>
      interp p (.imp (.down M₁) (.imp (.down M₂) N) :: todo) done g
  -- the Dyckhoff implication parks
  | .imp (.down (.imp Q' N')) N :: todo, done, g =>
      interp p todo (.imp (.down (.imp Q' N')) N :: done) g
  -- a box parks: not left-invertible, opened only under a lax goal
  | .circ Q :: todo, done, g =>
      interp p todo (.circ Q :: done) g
  -- the ◯-implication parks: the modal Dyckhoff shape
  | .imp (.down (.circ Q')) N :: todo, done, g =>
      interp p todo (.imp (.down (.circ Q')) N :: done) g
  -- ── aggregate phase: `todo` exhausted ──
  | [], done, g =>
    match hf : findFire done (splits done) with
    -- a parked `a ⊃ N` whose atom has arrived fires  [3^wN < 3^(wN+2)]
    | some (_, N, rest) => interp p [N] rest g
    | none =>
      match g with
      -- ∃p mode: conjunction over the saturated context
      | none =>
          nAndAll ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
            match X with
            -- a surviving atom is its own p-free content
            | .up (.atom a) => pGuard p a nTop (.up (.atom a))
            -- `a ⊃ N`, atom absent: guard the recursion by the atom
            | .imp (.atom a) N =>
                pGuard p a nTop (.imp (.atom a) (interp p [N] rest none))
            -- the Dyckhoff implication: what it yields, guarded by what
            -- the goal interpolant of its antecedent demands — PAIRED with
            -- the ∃p of the residual station, which the minimality
            -- dispatch projects (third clause the (ii) induction forced;
            -- sound because done ⊢ res via resSim)
            | .imp (.down (.imp Q' N')) N =>
                nAnd
                  (.imp (.down (interp p [.imp (.down N') N] rest
                                 (some (.imp Q' N'))))
                       (interp p [N] rest none))
                  (interp p [.imp (.down N') N] rest none)
            -- a parked box: everything the opened station yields, boxed
            -- [2·3^wQ + Σrest < 3^(wQ+1) + Σrest]
            | .circ Q =>
                .circ (.down (interp p [.up Q] rest none))
            -- the ◯-implication: the modal Dyckhoff pair — the fire guarded
            -- by the ∀p of (rest ⇒ ◯Q′), PAIRED with the ∃p of rest (the
            -- E-res component, forced as in the intuitionistic case).  No
            -- residual and no witness-box family: modal descent (plan
            -- §3-results (e)) handles self-uses inside the antecedent.
            | .imp (.down (.circ Q')) N =>
                nAnd
                  (.imp (.down (interp p [] rest (some (.circ Q'))))
                       (interp p [N] rest none))
                  (interp p [] rest none)
            -- unreachable shapes park nothing
            | _ => nTop))
      -- ∀p mode: by the goal
      | some G =>
        match G with
        -- goal inversion  [2·sum3 b + 3^wN < 3^(wQ+wN+1)]
        -- ∀p at an implication goal: each branch conjunct is GUARDED by the
        -- branch's ∃p — without the guard, minimality fails (it would demand
        -- E(Γ) ⊢ E(Γ+b), which is false); with it, soundness still closes
        -- because eSound supplies the guard.  This is the clause the (ii)
        -- induction forces.
        | .imp Q N =>
            nAndAll ((invertPos Q).attach.map
              (fun ⟨b, hb⟩ =>
                .imp (.down (interp p b done none))
                  (interp p b done (some N))))
        | .and M N =>
            nAnd (interp p [] done (some M)) (interp p [] done (some N))
        -- context attacks: ways the saturated context can advance any goal;
        -- inlined per goal shape so each aggregate case is self-contained
        | .up (.atom q) =>
            if atomMem q done then nTop
            else nOrAll (atomHead p q ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up (Pos.atom q)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up (Pos.atom q))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.up (Pos.atom q))))
              | _, _ => nBot))
        | .up .fls =>
            nOrAll ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up Pos.fls))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up Pos.fls)))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.up Pos.fls)))
              | _, _ => nBot))
        | .up (.or P₁ P₂) =>
            nOrAll ([interp p [] done (some (.up P₁)),
                     interp p [] done (some (.up P₂))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up (Pos.or P₁ P₂)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up (Pos.or P₁ P₂))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.up (Pos.or P₁ P₂))))
              | _, _ => nBot))
        | .up (.down M) =>
            nOrAll ([interp p [] done (some M)] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up (Pos.down M)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up (Pos.down M))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.up (Pos.down M))))
              | _, _ => nBot))
        | .circ (.atom q) =>
            nOrAll ([interp p [] done (some (.up (.atom q)))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.atom q)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.atom q))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ (.atom q))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.atom q))))
              | _, _ => nBot))
        | .circ .fls =>
            nOrAll ([interp p [] done (some (.up .fls))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ .fls))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ .fls)))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ .fls)))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ .fls)))
              | _, _ => nBot))
        | .circ (.or P₁ P₂) =>
            nOrAll ([interp p [] done (some (.circ P₁)),
                     interp p [] done (some (.circ P₂)),
                     interp p [] done (some (.up (.or P₁ P₂)))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.or P₁ P₂)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.or P₁ P₂))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ (.or P₁ P₂))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.or P₁ P₂))))
              | _, _ => nBot))
        | .circ (.down (.up P')) =>
            nOrAll ([interp p [] done (some (.circ P'))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.down (.up P'))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.down (.up P')))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ (.down (.up P')))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.down (.up P')))))
              | _, _ => nBot))
        | .circ (.down (.circ P')) =>
            nOrAll ([interp p [] done (some (.circ P'))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.down (.circ P'))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.down (.circ P')))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ (.down (.circ P')))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.down (.circ P')))))
              | _, _ => nBot))
        | .circ (.down (.and M₁ M₂)) =>
            nOrAll ([interp p [] done (some (.up (.down (.and M₁ M₂))))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.down (.and M₁ M₂))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.down (.and M₁ M₂)))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ (.down (.and M₁ M₂)))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.down (.and M₁ M₂)))))
              | _, _ => nBot))
        | .circ (.down (.imp Q₀ N₀)) =>
            nOrAll ([interp p [] done (some (.up (.down (.imp Q₀ N₀))))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.down (.imp Q₀ N₀))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.down (.imp Q₀ N₀)))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ (.down (.imp Q₀ N₀)))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.down (.imp Q₀ N₀)))))
              | _, _ => nBot))
  termination_by todo done goal => 2 * sum3 todo + sum3 done + goalW goal
  decreasing_by
    all_goals simp_wf
    all_goals try simp only [sum3, sum3_append, goalW, wNeg, wPos]
    all_goals first
      | exact dec_dyk0 (by assumption)
      | exact dec_park
      | exact dec_drop
      | exact dec_shift1
      | exact dec_and
      | exact dec_curry
      | exact dec_stripshift
      | exact p3_strict (by first
          | omega
          | (have := wPos_pos P₁; have := wPos_pos P₂; omega)
          | (have := wNeg_pos M; have := wNeg_pos N; omega))
      | exact dec_impor (wPos_pos _) (wPos_pos _)
      | exact dec_orctx (by assumption)
      | (have h1 := invertPos_lt (P := Pos.or _ _)
           (by intro a h; nomatch h) _ (by assumption)
         simp only [wPos] at h1; omega)
      | exact dec_fire (by assumption)
      | exact dec_qimp (by assumption)
      | exact dec_qimp_g (by assumption)
      | exact dec_dyk1 (by assumption)
      | (have h1 := dec_dyk1 (by assumption); omega)
      | exact dec_dyk1_g (by assumption)
      | exact dec_dyk2 (by assumption)
      | exact dec_dyk2_g (by assumption)
      | exact dec_ainv (by assumption)
      | exact dec_ainv0 (by assumption)
      | exact dec_orA (by assumption)
      | exact Nat.lt_of_lt_of_le (dec_orA (by assumption)) (by omega)
      | exact dec_boxE (by assumption)
      | exact dec_cimp1 (by assumption)
      | exact dec_cimp1_g (by assumption)
      | exact dec_boxA_g (by assumption)
      | exact dec_boxE_g (by assumption)
      | exact dec_cimp2_g (by assumption)
      | exact dec_cimp2 (by assumption)
      | exact dec_cimp3 (by assumption)
      | exact dec_circDirect
      | (have h1 := dec_boxE (by assumption); omega)
      | (have h1 := dec_cimp1 (by assumption); omega)
      | (have h1 := dec_cimp2 (by assumption); omega)
      | (have h1 := dec_cimp3 (by assumption); omega)


/-! ## `p`-freeness -/

mutual
/-- The atom `p` does not occur (positives). -/
def PFreeP (p : String) : Pos → Prop
  | .atom a  => a ≠ p
  | .fls     => True
  | .or P Q  => PFreeP p P ∧ PFreeP p Q
  | .down M  => PFreeN p M
/-- The atom `p` does not occur (negatives). -/
def PFreeN (p : String) : Neg → Prop
  | .up P    => PFreeP p P
  | .imp Q N => PFreeP p Q ∧ PFreeN p N
  | .and M N => PFreeN p M ∧ PFreeN p N
  | .circ Q => PFreeP p Q
end

theorem pfree_nTop {p : String} : PFreeN p nTop := by
  simp [nTop, PFreeN, PFreeP]

theorem pfree_nBot {p : String} : PFreeN p nBot := by
  simp [nBot, PFreeN, PFreeP]

theorem pfree_nAnd {p : String} {M N : Neg}
    (hM : PFreeN p M) (hN : PFreeN p N) : PFreeN p (nAnd M N) :=
  ⟨hM, hN⟩

theorem pfree_nOr {p : String} {M N : Neg}
    (hM : PFreeN p M) (hN : PFreeN p N) : PFreeN p (nOr M N) :=
  ⟨hM, hN⟩

theorem pfree_nAndAll {p : String} {l : List Neg}
    (h : ∀ x ∈ l, PFreeN p x) : PFreeN p (nAndAll l) := by
  induction l with
  | nil => exact pfree_nTop
  | cons x l ih =>
      exact pfree_nAnd (h x (List.mem_cons_self ..))
        (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem pfree_nOrAll {p : String} {l : List Neg}
    (h : ∀ x ∈ l, PFreeN p x) : PFreeN p (nOrAll l) := by
  induction l with
  | nil => exact pfree_nBot
  | cons x l ih =>
      exact pfree_nOr (h x (List.mem_cons_self ..))
        (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem pfree_pGuard {p a : String} {C D : Neg}
    (hC : PFreeN p C) (hD : a ≠ p → PFreeN p D) : PFreeN p (pGuard p a C D) := by
  unfold pGuard; split
  · exact hC
  · exact hD (by assumption)

theorem pfree_atomHead {p q : String} : ∀ x ∈ atomHead p q, PFreeN p x := by
  unfold atomHead; split
  · intro x hx; exact absurd hx (List.not_mem_nil)
  · intro x hx
    rcases List.mem_singleton.mp hx with rfl
    rename_i h
    simpa only [PFreeN, PFreeP] using h

set_option maxHeartbeats 4000000 in
/-- **The interpolant never mentions `p`.**  Every clause either keeps
`p` out by construction, or is guarded by the `a == p` test that replaces
the would-be conjunct or disjunct by its unit.  The proof is farm-style —
no positional case names: every case of the recursion falls through the
alternative scripts until arity and shape match — so it survives clause
insertion and reordering. -/
theorem interp_pfree (p : String) :
    ∀ (todo done : List Neg) (g : Option Neg), PFreeN p (interp p todo done g) := by
  intro todo done g
  fun_induction interp p todo done g <;>
    first
    | assumption
    | exact pfree_nBot
    | exact pfree_nTop
    | exact ⟨by assumption, by assumption⟩
    | (rename_i ih
       apply pfree_nOrAll
       intro x hx
       simp only [List.mem_map, List.mem_attach, true_and] at hx
       obtain ⟨⟨b, hb⟩, rfl⟩ := hx
       exact ih b hb)
    | (rename_i ih2 ih1
       apply pfree_nAndAll
       intro x hx
       simp only [List.mem_map, List.mem_attach, true_and] at hx
       obtain ⟨⟨b, hb⟩, rfl⟩ := hx
       refine ⟨?_, ?_⟩ <;>
         first | exact ih1 b hb | exact ih2 b | exact ih1 b | exact ih2 b hb)
    | -- ∃p aggregate: qimp, dyk triple, box, modal triple — 8 ihs
      (rename_i ih8 ih7 ih6 ih5 ih4 ih3 ih2 ih1
       apply pfree_nAndAll
       intro x hx
       simp only [List.mem_map, List.mem_attach, true_and] at hx
       obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
       cases X with
       | up P =>
           cases P with
           | atom a =>
               exact pfree_pGuard pfree_nTop
                 (fun h => by simpa only [PFreeN, PFreeP] using h)
           | fls => exact pfree_nTop
           | or _ _ => exact pfree_nTop
           | down _ => exact pfree_nTop
       | imp Q N =>
           cases Q with
           | atom a =>
               exact pfree_pGuard pfree_nTop (fun h => ⟨h, by
                 first
                 | exact ih8 rest a N hXr | exact ih7 rest a N hXr
                 | exact ih6 rest a N hXr | exact ih5 rest a N hXr
                 | exact ih4 rest a N hXr | exact ih3 rest a N hXr
                 | exact ih2 rest a N hXr | exact ih1 rest a N hXr⟩)
           | fls => exact pfree_nTop
           | or _ _ => exact pfree_nTop
           | down M =>
               cases M with
               | up _ => exact pfree_nTop
               | and _ _ => exact pfree_nTop
               | imp Q' N' =>
                   refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
                     first
                     | exact ih8 rest Q' N' N hXr | exact ih7 rest Q' N' N hXr
                     | exact ih6 rest Q' N' N hXr | exact ih5 rest Q' N' N hXr
                     | exact ih4 rest Q' N' N hXr | exact ih3 rest Q' N' N hXr
                     | exact ih2 rest Q' N' N hXr | exact ih1 rest Q' N' N hXr
               | circ Q' =>
                   refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
                     first
                     | exact ih8 rest Q' N hXr | exact ih7 rest Q' N hXr
                     | exact ih6 rest Q' N hXr | exact ih5 rest Q' N hXr
                     | exact ih4 rest Q' N hXr | exact ih3 rest Q' N hXr
                     | exact ih2 rest Q' N hXr | exact ih1 rest Q' N hXr
       | and _ _ => exact pfree_nTop
       | circ Q =>
           first
           | exact ih8 rest Q hXr | exact ih7 rest Q hXr
           | exact ih6 rest Q hXr | exact ih5 rest Q hXr
           | exact ih4 rest Q hXr | exact ih3 rest Q hXr
           | exact ih2 rest Q hXr | exact ih1 rest Q hXr)
    | -- atom-goal attack aggregate (if-false): q hq + 5 ihs
      (rename_i q hq ih5 ih4 ih3 ih2 ih1
       apply pfree_nOrAll
       intro x hx
       rcases List.mem_append.mp hx with hx | hx
       · exact pfree_atomHead x hx
       · simp only [List.mem_map, List.mem_attach, true_and] at hx
         obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
         cases X with
         | up P => cases P <;> exact pfree_nBot
         | imp Q N =>
             cases Q with
             | atom a =>
                 exact pfree_pGuard pfree_nBot (fun h => pfree_nAnd h (by
                   first
                   | exact ih5 rest a N hXr | exact ih4 rest a N hXr
                   | exact ih3 rest a N hXr | exact ih2 rest a N hXr
                   | exact ih1 rest a N hXr))
             | fls => exact pfree_nBot
             | or _ _ => exact pfree_nBot
             | down M =>
                 cases M with
                 | up _ => exact pfree_nBot
                 | and _ _ => exact pfree_nBot
                 | imp Q' N' =>
                     refine pfree_nAnd ?_ ?_ <;>
                       first
                       | exact ih5 rest Q' N' N hXr | exact ih4 rest Q' N' N hXr
                       | exact ih3 rest Q' N' N hXr | exact ih2 rest Q' N' N hXr
                       | exact ih1 rest Q' N' N hXr
                 | circ Q' =>
                     refine pfree_nAnd ?_ ?_ <;>
                       first
                       | exact ih5 rest Q' N hXr | exact ih4 rest Q' N hXr
                       | exact ih3 rest Q' N hXr | exact ih2 rest Q' N hXr
                       | exact ih1 rest Q' N hXr
         | and _ _ => exact pfree_nBot
         | circ _ => exact pfree_nBot)
    | -- fls-goal attack aggregate: 5 ihs
      (rename_i ih5 ih4 ih3 ih2 ih1
       apply pfree_nOrAll
       intro x hx
       simp only [List.mem_map, List.mem_attach, true_and] at hx
       obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
       cases X with
       | up P => cases P <;> exact pfree_nBot
       | imp Q N =>
           cases Q with
           | atom a =>
               exact pfree_pGuard pfree_nBot (fun h => pfree_nAnd h (by
                 first
                 | exact ih5 rest a N hXr | exact ih4 rest a N hXr
                 | exact ih3 rest a N hXr | exact ih2 rest a N hXr
                 | exact ih1 rest a N hXr))
           | fls => exact pfree_nBot
           | or _ _ => exact pfree_nBot
           | down M =>
               cases M with
               | up _ => exact pfree_nBot
               | and _ _ => exact pfree_nBot
               | imp Q' N' =>
                   refine pfree_nAnd ?_ ?_ <;>
                     first
                     | exact ih5 rest Q' N' N hXr | exact ih4 rest Q' N' N hXr
                     | exact ih3 rest Q' N' N hXr | exact ih2 rest Q' N' N hXr
                     | exact ih1 rest Q' N' N hXr
               | circ Q' =>
                   refine pfree_nAnd ?_ ?_ <;>
                     first
                     | exact ih5 rest Q' N hXr | exact ih4 rest Q' N hXr
                     | exact ih3 rest Q' N hXr | exact ih2 rest Q' N hXr
                     | exact ih1 rest Q' N hXr
       | and _ _ => exact pfree_nBot
       | circ _ => exact pfree_nBot)
    | -- or-goal attack aggregate: ihP ihQ + 5 ihs
      (rename_i ihP ihQ ih5 ih4 ih3 ih2 ih1
       apply pfree_nOrAll
       intro x hx
       rcases List.mem_append.mp hx with hx | hx
       · rcases List.mem_cons.mp hx with rfl | hx
         · exact ihP
         · rcases List.mem_singleton.mp hx with rfl
           exact ihQ
       · simp only [List.mem_map, List.mem_attach, true_and] at hx
         obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
         cases X with
         | up P => cases P <;> exact pfree_nBot
         | imp Q N =>
             cases Q with
             | atom a =>
                 exact pfree_pGuard pfree_nBot (fun h => pfree_nAnd h (by
                   first
                   | exact ih5 rest a N hXr | exact ih4 rest a N hXr
                   | exact ih3 rest a N hXr | exact ih2 rest a N hXr
                   | exact ih1 rest a N hXr))
             | fls => exact pfree_nBot
             | or _ _ => exact pfree_nBot
             | down M =>
                 cases M with
                 | up _ => exact pfree_nBot
                 | and _ _ => exact pfree_nBot
                 | imp Q' N' =>
                     refine pfree_nAnd ?_ ?_ <;>
                       first
                       | exact ih5 rest Q' N' N hXr | exact ih4 rest Q' N' N hXr
                       | exact ih3 rest Q' N' N hXr | exact ih2 rest Q' N' N hXr
                       | exact ih1 rest Q' N' N hXr
                 | circ Q' =>
                     refine pfree_nAnd ?_ ?_ <;>
                       first
                       | exact ih5 rest Q' N hXr | exact ih4 rest Q' N hXr
                       | exact ih3 rest Q' N hXr | exact ih2 rest Q' N hXr
                       | exact ih1 rest Q' N hXr
         | and _ _ => exact pfree_nBot
         | circ _ => exact pfree_nBot)
    | -- down-goal attack aggregate: ihM + 5 ihs
      (rename_i ihM ih5 ih4 ih3 ih2 ih1
       apply pfree_nOrAll
       intro x hx
       rcases List.mem_append.mp hx with hx | hx
       · rcases List.mem_singleton.mp hx with rfl
         exact ihM
       · simp only [List.mem_map, List.mem_attach, true_and] at hx
         obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
         cases X with
         | up P => cases P <;> exact pfree_nBot
         | imp Q N =>
             cases Q with
             | atom a =>
                 exact pfree_pGuard pfree_nBot (fun h => pfree_nAnd h (by
                   first
                   | exact ih5 rest a N hXr | exact ih4 rest a N hXr
                   | exact ih3 rest a N hXr | exact ih2 rest a N hXr
                   | exact ih1 rest a N hXr))
             | fls => exact pfree_nBot
             | or _ _ => exact pfree_nBot
             | down M =>
                 cases M with
                 | up _ => exact pfree_nBot
                 | and _ _ => exact pfree_nBot
                 | imp Q' N' =>
                     refine pfree_nAnd ?_ ?_ <;>
                       first
                       | exact ih5 rest Q' N' N hXr | exact ih4 rest Q' N' N hXr
                       | exact ih3 rest Q' N' N hXr | exact ih2 rest Q' N' N hXr
                       | exact ih1 rest Q' N' N hXr
                 | circ Q' =>
                     refine pfree_nAnd ?_ ?_ <;>
                       first
                       | exact ih5 rest Q' N hXr | exact ih4 rest Q' N hXr
                       | exact ih3 rest Q' N hXr | exact ih2 rest Q' N hXr
                       | exact ih1 rest Q' N hXr
         | and _ _ => exact pfree_nBot
         | circ _ => exact pfree_nBot)
    | -- the ◯-∨ aggregate: three lax goal-inversion rows + stations — 10 ihs
      (rename_i ihP1 ihP2 ihP3 ih7 ih6 ih5 ih4 ih3 ih2 ih1
       apply pfree_nOrAll
       intro x hx
       rcases List.mem_append.mp hx with hx | hx
       · rcases List.mem_cons.mp hx with rfl | hx
         · exact ihP1
         · rcases List.mem_cons.mp hx with rfl | hx
           · exact ihP2
           · rcases List.mem_singleton.mp hx with rfl
             exact ihP3
       · simp only [List.mem_map, List.mem_attach, true_and] at hx
         obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
         cases X with
         | up P => cases P <;> exact pfree_nBot
         | imp Q N =>
             cases Q with
             | atom a =>
                 exact pfree_pGuard pfree_nBot (fun h => pfree_nAnd h (by
                   first
                   | exact ih7 rest a N hXr | exact ih6 rest a N hXr
                   | exact ih5 rest a N hXr | exact ih4 rest a N hXr
                   | exact ih3 rest a N hXr | exact ih2 rest a N hXr
                   | exact ih1 rest a N hXr))
             | fls => exact pfree_nBot
             | or _ _ => exact pfree_nBot
             | down M =>
                 cases M with
                 | up _ => exact pfree_nBot
                 | and _ _ => exact pfree_nBot
                 | imp Q' N' =>
                     refine pfree_nAnd ?_ ?_ <;>
                       first
                       | exact ih7 rest Q' N' N hXr | exact ih6 rest Q' N' N hXr
                       | exact ih5 rest Q' N' N hXr | exact ih4 rest Q' N' N hXr
                       | exact ih3 rest Q' N' N hXr | exact ih2 rest Q' N' N hXr
                       | exact ih1 rest Q' N' N hXr
                 | circ Q' =>
                     refine pfree_nAnd ?_ ?_ <;>
                       first
                       | exact ih7 rest Q' N hXr | exact ih6 rest Q' N hXr
                       | exact ih5 rest Q' N hXr | exact ih4 rest Q' N hXr
                       | exact ih3 rest Q' N hXr | exact ih2 rest Q' N hXr
                       | exact ih1 rest Q' N hXr
         | and _ _ => exact pfree_nBot
         | circ R =>
             refine ⟨?_, ?_⟩ <;>
               first
               | exact ih7 rest R hXr | exact ih6 rest R hXr
               | exact ih5 rest R hXr | exact ih4 rest R hXr
               | exact ih3 rest R hXr | exact ih2 rest R hXr
               | exact ih1 rest R hXr)
        | -- ◯-goal attack aggregate: direct + qimp + dyk pair + modal pair + box pair — 8 ihs
      (rename_i ihD ih7 ih6 ih5 ih4 ih3 ih2 ih1
       apply pfree_nOrAll
       intro x hx
       rcases List.mem_append.mp hx with hx | hx
       · rcases List.mem_singleton.mp hx with rfl
         exact ihD
       · simp only [List.mem_map, List.mem_attach, true_and] at hx
         obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
         cases X with
         | up P => cases P <;> exact pfree_nBot
         | imp Q N =>
             cases Q with
             | atom a =>
                 exact pfree_pGuard pfree_nBot (fun h => pfree_nAnd h (by
                   first
                   | exact ih7 rest a N hXr | exact ih6 rest a N hXr
                   | exact ih5 rest a N hXr | exact ih4 rest a N hXr
                   | exact ih3 rest a N hXr | exact ih2 rest a N hXr
                   | exact ih1 rest a N hXr))
             | fls => exact pfree_nBot
             | or _ _ => exact pfree_nBot
             | down M =>
                 cases M with
                 | up _ => exact pfree_nBot
                 | and _ _ => exact pfree_nBot
                 | imp Q' N' =>
                     refine pfree_nAnd ?_ ?_ <;>
                       first
                       | exact ih7 rest Q' N' N hXr | exact ih6 rest Q' N' N hXr
                       | exact ih5 rest Q' N' N hXr | exact ih4 rest Q' N' N hXr
                       | exact ih3 rest Q' N' N hXr | exact ih2 rest Q' N' N hXr
                       | exact ih1 rest Q' N' N hXr
                 | circ Q' =>
                     refine pfree_nAnd ?_ ?_ <;>
                       first
                       | exact ih7 rest Q' N hXr | exact ih6 rest Q' N hXr
                       | exact ih5 rest Q' N hXr | exact ih4 rest Q' N hXr
                       | exact ih3 rest Q' N hXr | exact ih2 rest Q' N hXr
                       | exact ih1 rest Q' N hXr
         | and _ _ => exact pfree_nBot
         | circ R =>
             refine ⟨?_, ?_⟩ <;>
               first
               | exact ih7 rest R hXr | exact ih6 rest R hXr
               | exact ih5 rest R hXr | exact ih4 rest R hXr
               | exact ih3 rest R hXr | exact ih2 rest R hXr
               | exact ih1 rest R hXr)

/-! # Part 3: the cut-free toolkit (ported from LJF, flags threaded) -/

/-! ## Derivation heights

The flag makes structural recursion unavailable to the traversals (constant
`tru`/`lax` indices in premises, compound goal indices), so they recurse on
an explicit height instead. -/

mutual
/-- Height of a stable derivation. -/
def szS : ∀ {Γ : List Neg} {j : JD} {P : Pos}, Stab Γ j P → Nat
  | _, _, _, .rfoc r => szR r + 1
  | _, _, _, .lfoc _ lf => szL lf + 1
  | _, _, _, .laxOf s => szS s + 1
/-- Height of a right focus. -/
def szR : ∀ {Γ : List Neg} {j : JD} {P : Pos}, RFocus Γ j P → Nat
  | _, _, _, .init _ => 1
  | _, _, _, .or1 r => szR r + 1
  | _, _, _, .or2 r => szR r + 1
  | _, _, _, .rel d => szI d + 1
/-- Height of a left focus. -/
def szL : ∀ {Γ : List Neg} {N : Neg} {j : JD} {P : Pos}, LFoc Γ N j P → Nat
  | _, _, _, _, .rel d => szI d + 1
  | _, _, _, _, .impL s lf => szS s + szL lf + 1
  | _, _, _, _, .and1 lf => szL lf + 1
  | _, _, _, _, .and2 lf => szL lf + 1
  | _, _, _, _, .circL d => szI d + 1
/-- Height of an inversion. -/
def szI : ∀ {Γ : List Neg} {Ω : List Pos} {j : JD} {N : Neg}, Inv Γ Ω j N → Nat
  | _, _, _, _, .impR d => szI d + 1
  | _, _, _, _, .andR d e => szI d + szI e + 1
  | _, _, _, _, .circR d => szI d + 1
  | _, _, _, _, .stable s => szS s + 1
  | _, _, _, _, .orL d e => szI d + szI e + 1
  | _, _, _, _, .flsL => 1
  | _, _, _, _, .downL d => szI d + 1
  | _, _, _, _, .atomL d => szI d + 1
end

mutual

/-- Re-target a stable proof: any right focus on `P` is passed to `k`. -/
def routeStab {Δ₀ : List Neg} {P P₀ : Pos}
    (k : ∀ {Δ' : List Neg} {j : JD}, Sub Δ₀ Δ' → RFocus Δ' j P → Stab Δ' j P₀) :
    ∀ {Δ : List Neg} {j : JD}, Sub Δ₀ Δ → Stab Δ j P → Stab Δ j P₀
  | _, _, hs, .rfoc r => k hs r
  | _, _, hs, .lfoc h lf => .lfoc h (routeLFoc k hs lf)
  | _, _, hs, .laxOf s => .laxOf (routeStab k hs s)
termination_by Δ j hs s => szS s
decreasing_by all_goals (simp_wf; simp only [szS, szR, szL, szI]; omega)

/-- Re-target below a left focus. -/
def routeLFoc {Δ₀ : List Neg} {P P₀ : Pos}
    (k : ∀ {Δ' : List Neg} {j : JD}, Sub Δ₀ Δ' → RFocus Δ' j P → Stab Δ' j P₀) :
    ∀ {Δ : List Neg} {H : Neg} {j : JD}, Sub Δ₀ Δ → LFoc Δ H j P → LFoc Δ H j P₀
  | _, _, _, hs, .rel d => .rel (routeInv k hs d)
  | _, _, _, hs, .impL s lf => .impL s (routeLFoc k hs lf)
  | _, _, _, hs, .and1 lf => .and1 (routeLFoc k hs lf)
  | _, _, _, hs, .and2 lf => .and2 (routeLFoc k hs lf)
  | _, _, _, hs, .circL d => .circL (routeInv k hs d)
termination_by Δ H j hs lf => szL lf
decreasing_by all_goals (simp_wf; simp only [szS, szR, szL, szI]; omega)

/-- Re-target through the inversion of a released antecedent.  The goal is a
shift, so `impR`/`andR` cannot occur and the traversal is total. -/
def routeInv {Δ₀ : List Neg} {P P₀ : Pos}
    (k : ∀ {Δ' : List Neg} {j : JD}, Sub Δ₀ Δ' → RFocus Δ' j P → Stab Δ' j P₀) :
    ∀ {Δ : List Neg} {Ω : List Pos} {j : JD}, Sub Δ₀ Δ →
      Inv Δ Ω j (.up P) → Inv Δ Ω j (.up P₀)
  | _, _, _, hs, .stable s => .stable (routeStab k hs s)
  | _, _, _, hs, .orL d₁ d₂ => .orL (routeInv k hs d₁) (routeInv k hs d₂)
  | _, _, _, _, .flsL => .flsL
  | _, _, _, hs, .downL d => .downL (routeInv k (hs.trans (Sub.grow _)) d)
  | _, _, _, hs, .atomL d => .atomL (routeInv k (hs.trans (Sub.grow _)) d)
termination_by Δ Ω j hs d => szI d
decreasing_by all_goals (simp_wf; simp only [szS, szR, szL, szI]; omega)

end

/-- Disjunction introduction at the stable level, left side. -/
def stabOr1 {Δ : List Neg} {j : JD} {A B : Pos} (s : Stab Δ j A) : Stab Δ j (.or A B) :=
  routeStab (Δ₀ := Δ) (fun _ r => .rfoc (.or1 r)) (Sub.refl Δ) s

/-- Disjunction introduction at the stable level, right side. -/
def stabOr2 {Δ : List Neg} {j : JD} {A B : Pos} (s : Stab Δ j B) : Stab Δ j (.or A B) :=
  routeStab (Δ₀ := Δ) (fun _ r => .rfoc (.or2 r)) (Sub.refl Δ) s

/-! ## Forced-shape extractors -/

/-- An inversion with empty `Ω` and shifted goal must be `stable`. -/
def unStable {Δ : List Neg} {j : JD} {P : Pos} : Inv Δ [] j (.up P) → Stab Δ j P
  | .stable s => s

/-- A right focus on a shift must be `rel`. -/
def relOf {Δ : List Neg} {j : JD} {M : Neg} : RFocus Δ j (.down M) → Inv Δ [] j M
  | .rel d => d

/-- An inversion with empty `Ω` and implication goal must be `impR`. -/
def impROf {Δ : List Neg} {j : JD} {Q : Pos} {N : Neg} :
    Inv Δ [] j (.imp Q N) → Inv Δ [Q] .tru N
  | .impR d => d

/-- An inversion with empty `Ω` and conjunction goal must be `andR`: left. -/
def andROf1 {Δ : List Neg} {j : JD} {M N : Neg} : Inv Δ [] j (.and M N) → Inv Δ [] .tru M
  | .andR d _ => d

/-- Right. -/
def andROf2 {Δ : List Neg} {j : JD} {M N : Neg} : Inv Δ [] j (.and M N) → Inv Δ [] .tru N
  | .andR _ e => e

/-- An inversion with empty `Ω` and modal goal must be `circR`. -/
def circROf {Δ : List Neg} {j : JD} {P : Pos} :
    Inv Δ [] j (.circ P) → Inv Δ [] .lax (.up P)
  | .circR d => d

/-! ## Realising and replaying the inversion of a positive -/

/-- Branch derivations assemble into the inversion of the positive. -/
def invBranches {j : JD} : ∀ (R : Pos) {Γ : List Neg} {Ω : List Pos} {N : Neg},
    (∀ b ∈ invertPos R, Inv (b ++ Γ) Ω j N) → Inv Γ (R :: Ω) j N
  | .atom a, _, _, _, h =>
      .atomL (h [.up (.atom a)] (by simp [invertPos]))
  | .fls, _, _, _, _ => .flsL
  | .or P Q, _, _, _, h =>
      .orL (invBranches P (fun b hb =>
              h b (by simp only [invertPos, List.mem_append]; exact .inl hb)))
           (invBranches Q (fun b hb =>
              h b (by simp only [invertPos, List.mem_append]; exact .inr hb)))
  | .down M, _, _, _, h => .downL (h [M] (by simp [invertPos]))
termination_by R => sizePos R
decreasing_by all_goals (simp_wf; simp only [sizePos]; omega)

/-- **Replay along a branch.**  A pending positive anywhere in `Ω` can be
extracted along any one branch of its inversion — the inversion phase is
deterministic, so the derivation already contains that branch. -/
def extract : ∀ {Γ : List Neg} (Ω₁ : List Pos) {R : Pos} {Ω₂ : List Pos}
    {C : Neg} {j : JD}, Inv Γ (Ω₁ ++ R :: Ω₂) j C →
    ∀ b ∈ invertPos R, Inv (b ++ Γ) (Ω₁ ++ Ω₂) j C
  -- extraction point at the head
  | _, [], .atom a, _, _, _, .atomL d, b, hb => by
      simp only [invertPos, List.mem_singleton] at hb; subst hb; exact d
  | _, [], .fls, _, _, _, .flsL, b, hb => by simp [invertPos] at hb
  | _, [], .or P Q, _, _, _, .orL d₁ d₂, b, hb =>
      if hP : b ∈ invertPos P then extract [] d₁ b hP
      else extract [] d₂ b (by
        simp only [invertPos, List.mem_append] at hb
        exact hb.resolve_left hP)
  | _, [], .down M, _, _, _, .downL d, b, hb => by
      simp only [invertPos, List.mem_singleton] at hb; subst hb; exact d
  -- goal rules commute past the extraction point
  | _, [], _, _, _, _, .impR d, b, hb => .impR (extract [_] d b hb)
  | _, [], _, _, _, _, .andR d e, b, hb => .andR (extract [] d b hb) (extract [] e b hb)
  | _, [], _, _, _, _, .circR d, b, hb => .circR (extract [] d b hb)
  | _, S :: Ω₁, _, _, _, _, .impR d, b, hb => .impR (extract (_ :: S :: Ω₁) d b hb)
  | _, S :: Ω₁, _, _, _, _, .andR d e, b, hb =>
      .andR (extract (S :: Ω₁) d b hb) (extract (S :: Ω₁) e b hb)
  | _, S :: Ω₁, _, _, _, _, .circR d, b, hb => .circR (extract (S :: Ω₁) d b hb)
  -- left rules on the head of `Ω₁` are rebuilt
  | _, .or _ _ :: Ω₁, _, _, _, _, .orL d₁ d₂, b, hb =>
      .orL (extract (_ :: Ω₁) d₁ b hb) (extract (_ :: Ω₁) d₂ b hb)
  | _, .fls :: _, _, _, _, _, .flsL, _, _ => .flsL
  | _, .down M :: Ω₁, _, _, _, _, .downL d, b, hb =>
      (extract Ω₁ d b hb).wk (fun X hX => by
        rcases List.mem_append.mp hX with hX | hX
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ hX)
        · rcases List.mem_cons.mp hX with rfl | hX
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ hX))
      |> Inv.downL
  | _, .atom a :: Ω₁, _, _, _, _, .atomL d, b, hb =>
      (extract Ω₁ d b hb).wk (fun X hX => by
        rcases List.mem_append.mp hX with hX | hX
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ hX)
        · rcases List.mem_cons.mp hX with rfl | hX
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ hX))
      |> Inv.atomL
termination_by Γ Ω₁ R Ω₂ C j d b hb => szI d
decreasing_by all_goals (simp_wf; simp only [szS, szR, szL, szI]; omega)



/-! ## Firing a shifted hypothesis, and merging its branches -/

/-- Fire `↑R ∈ Δ` at a stable sequent: stable continuations for every branch
of `R` assemble into one stable proof. -/
def stableFire {Δ : List Neg} {j : JD} {R : Pos} {P₀ : Pos} (h : Neg.up R ∈ Δ)
    (s : ∀ b ∈ invertPos R, Stab (b ++ Δ) j P₀) : Stab Δ j P₀ :=
  .lfoc h (.rel (invBranches R (fun b hb => .stable (s b hb))))

/-- **Eliminate a shifted hypothesis into a negative goal.**  By recursion on
the goal: implications invert their antecedent (`invBranches`) and push the
branch family through (`extract` + reordering), conjunctions project, and at
a shifted goal the hypothesis fires (`stableFire`).  This subsumes ex falso
(`R = ⊥`: the branch family is vacuous), disjunction elimination, and the
inversion of a shifted hypothesis. -/
def upMerge : ∀ (G : Neg) {Γ : List Neg} {R : Pos}, Neg.up R ∈ Γ →
    (∀ b ∈ invertPos R, Inv (b ++ Γ) [] .tru G) → Inv Γ [] .tru G
  | .imp Q N, Γ, R, h, D =>
      .impR (invBranches Q (fun c hc =>
        upMerge N (List.mem_append_right c h) (fun b hb =>
          (extract [] (impROf (D b hb)) c hc).wk (fun X hX => by
            rcases List.mem_append.mp hX with hX | hX
            · exact List.mem_append_right _ (List.mem_append_left _ hX)
            · rcases List.mem_append.mp hX with hX | hX
              · exact List.mem_append_left _ hX
              · exact List.mem_append_right _ (List.mem_append_right _ hX)))))
  | .and M N, _, _, h, D =>
      .andR (upMerge M h (fun b hb => andROf1 (D b hb)))
            (upMerge N h (fun b hb => andROf2 (D b hb)))
  | .up P, _, _, h, D =>
      .stable (stableFire h (fun b hb => unStable (D b hb)))
  | .circ P, _, _, h, D =>
      .circR (.stable (stableFire h (fun b hb => unStable (circROf (D b hb)))))

/-! ## Hypothesis simulation

Replace every use of one hypothesis `H` by material manufactured on the
target side.  A use is either a left focus on `H` — handled by `fl` — or, for
atomic `H`, an `init`; the latter reduces to the former through `idPos`, so
`fl` alone suffices. -/

theorem memBoth {H M : Neg} {Γ Δ : List Neg}
    (hm : ∀ X, X ∈ Γ → X = H ∨ X ∈ Δ) :
    ∀ X, X ∈ M :: Γ → X = H ∨ X ∈ M :: Δ := by
  intro X hX
  rcases List.mem_cons.mp hX with rfl | hX
  · exact .inr (List.mem_cons_self ..)
  · exact (hm X hX).imp id (List.mem_cons_of_mem _)

mutual

/-- Simulation at a stable sequent. -/
def simStab {H : Neg} {Δ₀ : List Neg}
    (fl : ∀ {Δ' : List Neg} {j : JD} {P : Pos}, Sub Δ₀ Δ' → LFoc Δ' H j P → Stab Δ' j P) :
    ∀ {Γ Δ : List Neg} {j : JD} {P : Pos}, (∀ X, X ∈ Γ → X = H ∨ X ∈ Δ) →
      Sub Δ₀ Δ → Stab Γ j P → Stab Δ j P
  | _, _, _, _, hm, hs, .rfoc r => simRFocus fl hm hs r
  | _, _, _, _, hm, hs, .laxOf s => .laxOf (simStab fl hm hs s)
  | _, _, _, _, hm, hs, @Stab.lfoc _ _ _ N h lf =>
      if e : N = H then fl hs (e ▸ simLFoc fl hm hs lf)
      else .lfoc ((hm _ h).resolve_left e) (simLFoc fl hm hs lf)
termination_by Γ Δ j P hm hs s => szS s
decreasing_by all_goals (simp_wf; simp only [szS, szR, szL, szI]; omega)

/-- Simulation under right focus.  Returns a stable proof, because an `init`
use of an atomic `H` must be re-routed through `fl` (via `idPos`), and that
produces a stable proof, not a focus. -/
def simRFocus {H : Neg} {Δ₀ : List Neg}
    (fl : ∀ {Δ' : List Neg} {j : JD} {P : Pos}, Sub Δ₀ Δ' → LFoc Δ' H j P → Stab Δ' j P) :
    ∀ {Γ Δ : List Neg} {j : JD} {P : Pos}, (∀ X, X ∈ Γ → X = H ∨ X ∈ Δ) →
      Sub Δ₀ Δ → RFocus Γ j P → Stab Δ j P
  | _, _, _, _, hm, hs, @RFocus.init _ _ a h =>
      if e : Neg.up (.atom a) = H then fl hs (e ▸ LFoc.rel (idPos (.atom a) _ _))
      else .rfoc (.init ((hm _ h).resolve_left e))
  | _, _, _, _, hm, hs, .or1 r => stabOr1 (simRFocus fl hm hs r)
  | _, _, _, _, hm, hs, .or2 r => stabOr2 (simRFocus fl hm hs r)
  | _, _, _, _, hm, hs, .rel d => .rfoc (.rel (simInv fl hm hs d))
termination_by Γ Δ j P hm hs r => szR r
decreasing_by all_goals (simp_wf; simp only [szS, szR, szL, szI]; omega)

/-- Simulation under a left focus on some other hypothesis. -/
def simLFoc {H : Neg} {Δ₀ : List Neg}
    (fl : ∀ {Δ' : List Neg} {j : JD} {P : Pos}, Sub Δ₀ Δ' → LFoc Δ' H j P → Stab Δ' j P) :
    ∀ {Γ Δ : List Neg} {H' : Neg} {j : JD} {P : Pos}, (∀ X, X ∈ Γ → X = H ∨ X ∈ Δ) →
      Sub Δ₀ Δ → LFoc Γ H' j P → LFoc Δ H' j P
  | _, _, _, _, _, hm, hs, .rel d => .rel (simInv fl hm hs d)
  | _, _, _, _, _, hm, hs, .impL s lf =>
      .impL (simStab fl hm hs s) (simLFoc fl hm hs lf)
  | _, _, _, _, _, hm, hs, .and1 lf => .and1 (simLFoc fl hm hs lf)
  | _, _, _, _, _, hm, hs, .and2 lf => .and2 (simLFoc fl hm hs lf)
  | _, _, _, _, _, hm, hs, .circL d => .circL (simInv fl hm hs d)
termination_by Γ Δ H' j P hm hs lf => szL lf
decreasing_by all_goals (simp_wf; simp only [szS, szR, szL, szI]; omega)

/-- Simulation through inversion. -/
def simInv {H : Neg} {Δ₀ : List Neg}
    (fl : ∀ {Δ' : List Neg} {j : JD} {P : Pos}, Sub Δ₀ Δ' → LFoc Δ' H j P → Stab Δ' j P) :
    ∀ {Γ Δ : List Neg} {Ω : List Pos} {j : JD} {C : Neg},
      (∀ X, X ∈ Γ → X = H ∨ X ∈ Δ) → Sub Δ₀ Δ → Inv Γ Ω j C → Inv Δ Ω j C
  | _, _, _, _, _, hm, hs, .impR d => .impR (simInv fl hm hs d)
  | _, _, _, _, _, hm, hs, .andR d e =>
      .andR (simInv fl hm hs d) (simInv fl hm hs e)
  | _, _, _, _, _, hm, hs, .circR d => .circR (simInv fl hm hs d)
  | _, _, _, _, _, hm, hs, .stable s => .stable (simStab fl hm hs s)
  | _, _, _, _, _, hm, hs, .orL d₁ d₂ =>
      .orL (simInv fl hm hs d₁) (simInv fl hm hs d₂)
  | _, _, _, _, _, _, _, .flsL => .flsL
  | _, _, _, _, _, hm, hs, .downL d =>
      .downL (simInv fl (memBoth hm) (hs.trans (Sub.grow _)) d)
  | _, _, _, _, _, hm, hs, .atomL d =>
      .atomL (simInv fl (memBoth hm) (hs.trans (Sub.grow _)) d)
termination_by Γ Δ Ω j C hm hs d => szI d
decreasing_by all_goals (simp_wf; simp only [szS, szR, szL, szI]; omega)

end

/-- The common instantiation: strip the head hypothesis, simulating its
uses. -/
def simHyp {H : Neg} {Γ Δ₀ : List Neg} {j : JD} {C : Neg}
    (fl : ∀ {Δ' : List Neg} {j' : JD} {P : Pos}, Sub Δ₀ Δ' → LFoc Δ' H j' P → Stab Δ' j' P)
    (hΓ : Sub Γ Δ₀) (d : Inv (H :: Γ) [] j C) : Inv Δ₀ [] j C :=
  simInv fl (fun X hX => (List.mem_cons.mp hX).imp id (hΓ X)) (Sub.refl Δ₀) d

/-! ## Interpolant-connective introductions and eliminations -/

/-- `⊤` needs nothing. -/
def nTopIntro {Γ : List Neg} : Inv Γ [] .tru nTop := .impR .flsL

/-- Conjunction of a list, introduction. -/
def nAndAllIntro : ∀ {l : List Neg} {Γ : List Neg},
    (∀ x ∈ l, Inv Γ [] .tru x) → Inv Γ [] .tru (nAndAll l)
  | [], _, _ => nTopIntro
  | x :: l, _, h =>
      .andR (h x (List.mem_cons_self ..))
        (nAndAllIntro (fun y hy => h y (List.mem_cons_of_mem _ hy)))

/-- Focused projection out of a list conjunction. -/
def lfocAndAll {j : JD} : ∀ {l : List Neg} {x : Neg} {Δ : List Neg} {P : Pos},
    x ∈ l → LFoc Δ x j P → LFoc Δ (nAndAll l) j P
  | y :: l, x, _, _, hx, lf =>
      if e : x = y then .and1 (e ▸ lf)
      else .and2 (lfocAndAll (by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd rfl e
        · exact hx) lf)

/-- Disjunction of a list, introduction at a member. -/
def nOrAllIntro {j : JD} : ∀ {l : List Neg} {x : Neg} {Γ : List Neg},
    x ∈ l → Inv Γ [] j x → Inv Γ [] j (nOrAll l)
  | y :: l, x, _, hx, d =>
      if e : x = y then .stable (.rfoc (.or1 (.rel (e ▸ d))))
      else .stable (.rfoc (.or2 (.rel (nOrAllIntro (by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd rfl e
        · exact hx) d))))

/-- Disjunction of a list, elimination: a case per member. -/
def nOrAllElim : ∀ {l : List Neg} {Γ : List Neg} (G : Neg), nOrAll l ∈ Γ →
    (∀ x ∈ l, ∀ {Γ' : List Neg}, Sub Γ Γ' → Inv (x :: Γ') [] .tru G) → Inv Γ [] .tru G
  | [], _, G, h, _ =>
      upMerge G (R := .fls) h (fun b hb => by simp [invertPos] at hb)
  | x :: l, Γ, G, h, D =>
      upMerge G h (fun b hb =>
        if e : b = [x] then
          e ▸ (D x (List.mem_cons_self ..) (Sub.refl _) |>.wk
            (fun Y hY => by
              rcases List.mem_cons.mp hY with rfl | hY
              · exact List.mem_append_left _ (List.mem_cons_self ..)
              · exact List.mem_append_right _ hY))
        else by
          have hb' : b = [nOrAll l] := by
            simp only [invertPos, List.mem_append, List.mem_singleton] at hb
            exact hb.resolve_left e
          subst hb'
          exact nOrAllElim G (List.mem_append_left _ (List.mem_cons_self ..))
            (fun y hy _ hs => D y (List.mem_cons_of_mem _ hy)
              (fun Z hZ => hs Z (List.mem_cons_of_mem _ hZ))))

/-- A `true` `atomMem` is a membership. -/
theorem atomMem_mem {a : String} {Γ : List Neg} (h : atomMem a Γ = true) :
    Neg.up (.atom a) ∈ Γ := by
  simp only [atomMem, List.any_eq_true] at h
  obtain ⟨x, hx, he⟩ := h
  match x, he with
  | .up (.atom b), he =>
      have : a = b := by simpa [BEq.comm] using he
      subst this; exact hx



/-! # Part 4: soundness of both modes

`eSound`: the context proves its `∃p` interpolant.  `aSound`: the `∀p`
interpolant, beside the context, proves the goal.  Mutual, by the same
weighted recursion as `interp` itself.  This section: the support layer. -/

/-! ## Small membership lemmas -/

theorem subPark {X : Neg} {t d : List Neg} :
    Sub (t ++ X :: d) (X :: (t ++ d)) := by
  intro N h
  simp only [List.mem_append, List.mem_cons] at h ⊢
  rcases h with h | h | h
  · exact .inr (.inl h)
  · exact .inl h
  · exact .inr (.inr h)

theorem subParkInv {X : Neg} {t d : List Neg} :
    Sub (X :: (t ++ d)) (t ++ X :: d) := by
  intro N h
  simp only [List.mem_append, List.mem_cons] at h ⊢
  rcases h with h | h | h
  · exact .inr (.inl h)
  · exact .inl h
  · exact .inr (.inr h)

theorem splits_sub {Γ : List Neg} :
    ∀ {X rest}, (X, rest) ∈ splits Γ → Sub rest Γ := by
  induction Γ with
  | nil => intro X rest h; simp [splits] at h
  | cons Y Γ ih =>
      intro X rest h
      simp only [splits, List.mem_cons, List.mem_map] at h
      rcases h with h | ⟨⟨Z, rest'⟩, hZ, hEq⟩
      · cases h; exact Sub.grow Y
      · cases hEq; exact Sub.cons Y (ih hZ)

theorem findFire_atom {full : List Neg} :
    ∀ {l : List (Neg × List Neg)} {a N rest},
      findFire full l = some (a, N, rest) → atomMem a full = true := by
  intro l
  induction l with
  | nil => intro a N rest h; simp [findFire] at h
  | cons XR more ih =>
      intro a N rest h
      obtain ⟨X, R⟩ := XR
      match X, h with
      | .imp (.atom b) N', h => ?_
      | .up P, h => exact ih h
      | .imp .fls N', h => exact ih h
      | .imp (.or Q₁ Q₂) N', h => exact ih h
      | .imp (.down M) N', h => exact ih h
      | .and M₁ M₂, h => exact ih h
      | .circ P, h => exact ih h
      simp only [findFire] at h
      by_cases hM : atomMem b full
      · simp [hM] at h; obtain ⟨rfl, _, _⟩ := h; exact hM
      · simp [hM] at h; exact ih h

/-! ## The truth-rooted re-targeter

From a `tru` root the traversal never meets `laxOf` or `circL` (both are
index-impossible), so a `tru`-fixed variant exists whose continuation may
build `tru`-only material — which `resSim` needs. -/

mutual

/-- Re-target a tru-stable proof; the continuation may change judgment —
the spine is rebuilt at `j`, the walked argument stays tru. -/
def routeStabT {Δ₀ : List Neg} {j : JD} {P P₀ : Pos}
    (k : ∀ {Δ' : List Neg}, Sub Δ₀ Δ' → RFocus Δ' .tru P → Stab Δ' j P₀) :
    ∀ {Δ : List Neg}, Sub Δ₀ Δ → Stab Δ .tru P → Stab Δ j P₀
  | _, hs, .rfoc r => k hs r
  | _, hs, .lfoc h lf => .lfoc h (routeLFocT k hs lf)
termination_by Δ hs s => szS s
decreasing_by all_goals (simp_wf; simp only [szS, szR, szL, szI]; omega)

/-- Below a left focus, tru-rooted. -/
def routeLFocT {Δ₀ : List Neg} {j : JD} {P P₀ : Pos}
    (k : ∀ {Δ' : List Neg}, Sub Δ₀ Δ' → RFocus Δ' .tru P → Stab Δ' j P₀) :
    ∀ {Δ : List Neg} {H : Neg}, Sub Δ₀ Δ → LFoc Δ H .tru P → LFoc Δ H j P₀
  | _, _, hs, .rel d => .rel (routeInvT k hs d)
  | _, _, hs, .impL s lf => .impL s (routeLFocT k hs lf)
  | _, _, hs, .and1 lf => .and1 (routeLFocT k hs lf)
  | _, _, hs, .and2 lf => .and2 (routeLFocT k hs lf)
termination_by Δ H hs lf => szL lf
decreasing_by all_goals (simp_wf; simp only [szS, szR, szL, szI]; omega)

/-- Through inversion, tru-rooted. -/
def routeInvT {Δ₀ : List Neg} {j : JD} {P P₀ : Pos}
    (k : ∀ {Δ' : List Neg}, Sub Δ₀ Δ' → RFocus Δ' .tru P → Stab Δ' j P₀) :
    ∀ {Δ : List Neg} {Ω : List Pos}, Sub Δ₀ Δ →
      Inv Δ Ω .tru (.up P) → Inv Δ Ω j (.up P₀)
  | _, _, hs, .stable s => .stable (routeStabT k hs s)
  | _, _, hs, .orL d₁ d₂ => .orL (routeInvT k hs d₁) (routeInvT k hs d₂)
  | _, _, _, .flsL => .flsL
  | _, _, hs, .downL d => .downL (routeInvT k (hs.trans (Sub.grow _)) d)
  | _, _, hs, .atomL d => .atomL (routeInvT k (hs.trans (Sub.grow _)) d)
termination_by Δ Ω hs d => szI d
decreasing_by all_goals (simp_wf; simp only [szS, szR, szL, szI]; omega)

end

/-! ## The residual simulator

Uses of the residual `↓N′ ⊃ N` are manufactured from the Dyckhoff hypothesis
`↓(Q′ ⊃ N′) ⊃ N` itself: a use supplies a stable proof of `↓N′`; routing it
(`routeStab`) releases an inversion of `N′`, which — weakened under the
inversion of `Q′` — rebuilds the stronger antecedent `↓(Q′ ⊃ N′)`, and the
hypothesis fires.  This is the derivability of `(A⊃B)⊃C ⊢ B⊃C`, in focused
form, with no cut. -/

def resSim {Q' : Pos} {N' N : Neg} {Δ₀ : List Neg}
    (hX : Neg.imp (.down (.imp Q' N')) N ∈ Δ₀) :
    ∀ {Δ' : List Neg} {j : JD} {P : Pos}, Sub Δ₀ Δ' →
      LFoc Δ' (.imp (.down N') N) j P → Stab Δ' j P
  | _, _, _, hs, .impL s' lf'' =>
      routeStabT
        (k := fun {Δ''} hs' r =>
          .lfoc (hs' _ (hs _ hX))
            (.impL
              (.rfoc (.rel (.impR (invBranches Q' (fun c _ =>
                (relOf r).wk (fun Z hZ => List.mem_append_right c hZ))))))
              (lf''.wk hs')))
        (Sub.refl _) s'

/-! ## The attack handlers

Each attack disjunct of a `∀p` interpolant, once produced by `nOrAllElim`,
is consumed by one of these.  They take the interpolant premises as
arguments, so they sit outside the mutual recursion. -/

/-- Attack via `a ⊃ N ∈ Γ'`: the disjunct `↑a ∧ A″` supplies the atom (left
component) and the continuation interpolant (right component). -/
def atkQimp {j : JD} {a : String} {N A'' G : Neg} {rest Γ' : List Neg}
    (hx : Neg.and (.up (.atom a)) A'' ∈ Γ')
    (hX : Neg.imp (.atom a) N ∈ Γ')
    (hrest : Sub rest Γ')
    (DN : Inv (A'' :: N :: rest) [] j G) : Inv Γ' [] j G :=
  -- strip A″ (project the right component), then N (fire the implication,
  -- proving its atom from the left component)
  simHyp
    (fl := fun hs lf => .lfoc (hs _ hX)
      (.impL (.lfoc (hs _ hx) (.and1 (.rel (idPos (.atom a) _ _)))) lf))
    (Sub.refl Γ')
    (simHyp
      (fl := fun hs lf =>
        .lfoc (hs _ (List.mem_cons_of_mem _ hx)) (.and2 lf))
      (Sub.cons N hrest)
      DN)



/-- Attack via the Dyckhoff hypothesis: the disjunct `A₁ ∧ A₂` supplies the
antecedent interpolant (left component) and the continuation interpolant
(right component). -/
def atkDyk {j : JD} {Q' : Pos} {N' N A₁ A₂ G : Neg} {rest Γ' : List Neg}
    (hx : Neg.and A₁ A₂ ∈ Γ')
    (hX : Neg.imp (.down (.imp Q' N')) N ∈ Γ')
    (hrest : Sub rest Γ')
    (D₁ : Inv (A₁ :: .imp (.down N') N :: rest) [] .tru (.imp Q' N'))
    (D₂ : Inv (A₂ :: N :: rest) [] j G) : Inv Γ' [] j G :=
  -- the antecedent Q′ ⊃ N′, residual uses simulated from the hypothesis
  let dM' : Inv Γ' [] .tru (.imp Q' N') :=
    simHyp (fl := resSim hX) (Sub.refl Γ')
      (simHyp
        (fl := fun hs lf =>
          .lfoc (hs _ (List.mem_cons_of_mem _ hx)) (.and1 lf))
        (Sub.cons _ hrest)
        D₁)
  -- main line: strip A₂ (right component), then N (fire the hypothesis)
  simHyp
    (fl := fun hs lf => .lfoc (hs _ hX)
      (.impL (.rfoc (.rel (dM'.wk hs))) lf))
    (Sub.refl Γ')
    (simHyp
      (fl := fun hs lf =>
        .lfoc (hs _ (List.mem_cons_of_mem _ hx)) (.and2 lf))
      (Sub.cons N hrest)
      D₂)

/-- Attack via the modal implication: the disjunct `A₁ ∧ A₂` supplies the
`∀p` of the antecedent's `◯`-goal (left component) and the continuation
interpolant (right component).  No residual simulator: the antecedent is
rebuilt from `A₁` directly — modal descent needs no residual. -/
def atkCimp {j : JD} {Q' : Pos} {N A₁ A₂ G : Neg} {rest Γ' : List Neg}
    (hx : Neg.and A₁ A₂ ∈ Γ')
    (hX : Neg.imp (.down (.circ Q')) N ∈ Γ')
    (hrest : Sub rest Γ')
    (D₁ : Inv (A₁ :: rest) [] .tru (.circ Q'))
    (D₂ : Inv (A₂ :: N :: rest) [] j G) : Inv Γ' [] j G :=
  let dM' : Inv Γ' [] .tru (.circ Q') :=
    simHyp
      (fl := fun hs lf => .lfoc (hs _ hx) (.and1 lf))
      hrest
      D₁
  simHyp
    (fl := fun hs lf => .lfoc (hs _ hX)
      (.impL (.rfoc (.rel (dM'.wk hs))) lf))
    (Sub.refl Γ')
    (simHyp
      (fl := fun hs lf =>
        .lfoc (hs _ (List.mem_cons_of_mem _ hx)) (.and2 lf))
      (Sub.cons N hrest)
      D₂)

/-- Choice-free witness for membership in a mapped list: the witness is
*found* by scanning, since `∃`-elimination cannot target `Type`. -/
def memMapWitness {α β : Type} [DecidableEq β] (f : α → β) :
    ∀ (l : List α) (y : β), y ∈ l.map f → {a : α // a ∈ l ∧ f a = y}
  | a :: l, y, h =>
      if e : f a = y then ⟨a, List.mem_cons_self .., e⟩
      else
        have h' : y ∈ l.map f := by
          simp only [List.map_cons, List.mem_cons] at h
          exact h.resolve_left (fun hy => e hy.symm)
        let ⟨w, hw, he⟩ := memMapWitness f l y h'
        ⟨w, List.mem_cons_of_mem _ hw, he⟩



/-! ## Reusable context shuffles -/

theorem subBranch1 {b t d : List Neg} {X : Neg} :
    Sub ((b ++ t) ++ d) (b ++ (X :: (t ++ d))) := by
  intro Z hZ
  simp only [List.mem_append, List.mem_cons] at hZ ⊢
  rcases hZ with (hZ | hZ) | hZ
  · exact .inl hZ
  · exact .inr (.inr (.inl hZ))
  · exact .inr (.inr (.inr hZ))

theorem subBranch2 {b t d : List Neg} {X Y : Neg} :
    Sub ((b ++ t) ++ d) (b ++ (X :: Y :: (t ++ d))) := by
  intro Z hZ
  simp only [List.mem_append, List.mem_cons] at hZ ⊢
  rcases hZ with (hZ | hZ) | hZ
  · exact .inl hZ
  · exact .inr (.inr (.inr (.inl hZ)))
  · exact .inr (.inr (.inr (.inr hZ)))

/-- `⊥` as a hypothesis proves anything. -/
def nBotElim {Γ : List Neg} (G : Neg) (h : nBot ∈ Γ) : Inv Γ [] .tru G :=
  upMerge G (R := .fls) h (fun _ hb => by simp [invertPos] at hb)

/-- `upMerge`, flag-generically.  At `tru` it is `upMerge`; at `lax` the
goal can only be a shift or a box — `⊃` and `∧` have no lax right rules, so
those cases are refuted by the witness `w` — and both fire directly, since
`stableFire` is flag-generic. -/
def upMergeJ (G : Neg) {Γ Γ₀ : List Neg} {R : Pos} {j : JD} (h : Neg.up R ∈ Γ)
    (w : Inv Γ₀ [] j G)
    (D : ∀ b ∈ invertPos R, Inv (b ++ Γ) [] j G) : Inv Γ [] j G :=
  match j, w, D with
  | .tru, _, D => upMerge G h D
  | .lax, w, D =>
    match G, w, D with
    | .up _, _, D => .stable (stableFire h (fun b hb => unStable (D b hb)))
    | .circ _, _, D =>
        .circR (.stable (stableFire h (fun b hb => unStable (circROf (D b hb)))))

/-- `nBot` eliminates at either flag. -/
def nBotElimJ (G : Neg) {Γ Γ₀ : List Neg} {j : JD} (h : nBot ∈ Γ)
    (w : Inv Γ₀ [] j G) : Inv Γ [] j G :=
  upMergeJ G (R := .fls) h w (fun _ hb => by simp [invertPos] at hb)

/-- `nOrAllElim`, flag-generically, by the same recursion. -/
def nOrAllElimJ : ∀ {l : List Neg} {Γ Γ₀ : List Neg} (G : Neg) {j : JD}, nOrAll l ∈ Γ →
    Inv Γ₀ [] j G →
    (∀ x ∈ l, ∀ {Γ' : List Neg}, Sub Γ Γ' → Inv (x :: Γ') [] j G) → Inv Γ [] j G
  | [], _, _, G, _, h, w, _ =>
      upMergeJ G (R := .fls) h w (fun _ hb => by simp [invertPos] at hb)
  | x :: l, Γ, _, G, _, h, w, D =>
      upMergeJ G h w (fun b hb =>
        if e : b = [x] then
          e ▸ (D x (List.mem_cons_self ..) (Sub.refl _) |>.wk
            (fun Y hY => by
              rcases List.mem_cons.mp hY with rfl | hY
              · exact List.mem_append_left _ (List.mem_cons_self ..)
              · exact List.mem_append_right _ hY))
        else by
          have hb' : b = [nOrAll l] := by
            simp only [invertPos, List.mem_append, List.mem_singleton] at hb
            exact hb.resolve_left e
          subst hb'
          exact nOrAllElimJ G (List.mem_append_left _ (List.mem_cons_self ..)) w
            (fun y hy _ hs => D y (List.mem_cons_of_mem _ hy)
              (fun Z hZ => hs Z (List.mem_cons_of_mem _ hZ))))

/-- The fire step, as one equation for every mode: when a parked `a ⊃ N'`
fires, the interpolant at the station equals the interpolant at the residual
station, whatever the goal.  Stated by cases because the equation lemmas of
the well-founded `interp` are specialised per fused matcher alternative, so
an abstract goal matches none of them — `rw [interp]` fails on
`interp p [] done (some G)` with `G` a variable. -/
theorem interpFire_eq {p : String} {done : List Neg} {a : String} {N' : Neg}
    {rest : List Neg}
    (hf : findFire done (splits done) = some (a, N', rest)) :
    ∀ g, interp p [] done g = interp p [N'] rest g := by
  intro g
  match g with
  | none | some (.up (.atom _)) | some (.up .fls) | some (.up (.or _ _))
  | some (.up (.down _)) | some (.imp _ _) | some (.and _ _)
  | some (.circ (.atom _)) | some (.circ .fls) | some (.circ (.or _ _))
  | some (.circ (.down (.up _))) | some (.circ (.down (.circ _)))
  | some (.circ (.down (.and _ _))) | some (.circ (.down (.imp _ _))) =>
      rw [interp]; split
      all_goals rename_i heq
      · rw [hf] at heq; cases heq; rfl
      · rw [hf] at heq; cases heq

/-- The fire step of `aSound`, one term for every goal shape. -/
def fireASound {p : String} {done : List Neg} {a : String} {N' : Neg}
    {rest : List Neg} {G : Neg}
    (hf : findFire done (splits done) = some (a, N', rest))
    (rec : Inv (interp p [N'] rest (some G) :: ([N'] ++ rest)) [] .tru G) :
    Inv (interp p [N'] rest (some G) :: done) [] .tru G :=
  simHyp
    (fl := fun hs lf =>
      .lfoc (hs _ (List.mem_cons_of_mem _
          (splits_mem (findFire_mem hf))))
        (.impL (.rfoc (.init (hs _ (List.mem_cons_of_mem _
          (atomMem_mem (findFire_atom hf)))))) lf))
    (Sub.cons _ (splits_sub (findFire_mem hf)))
    (rec.wk (by
      intro Z hZ
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))

/-! # Part 4: soundness of both modes -/

set_option hygiene false in
/-- The decreasing farm of the soundness mutual (`eSound`/`aSound`). Hygiene is off so entries naming call-site variables resolve there. -/
macro "ljf_dec_sound" : tactic => `(tactic| (
    all_goals simp_wf
    all_goals try simp only [sum3, sum3_append, goalW, wNeg, wPos]
    all_goals first
      | exact dec_dyk0 (by assumption)
      | exact dec_park
      | exact dec_drop
      | exact dec_shift1
      | exact dec_and
      | exact dec_curry
      | exact dec_stripshift
      | exact p3_strict (by first
          | omega
          | (have := wPos_pos P₁; have := wPos_pos P₂; omega)
          | (have := wNeg_pos M; have := wNeg_pos N; omega))
      | exact dec_impor (wPos_pos _) (wPos_pos _)
      | exact dec_orctx (by assumption)
      | (have h1 := invertPos_lt (P := Pos.or _ _)
           (by intro a h; nomatch h) _ (by assumption)
         simp only [wPos] at h1; omega)
      | exact dec_fire (by assumption)
      | exact dec_qimp (by assumption)
      | exact dec_qimp_g (by assumption)
      | exact dec_dyk1 (by assumption)
      | (have h1 := dec_dyk1 (by assumption); omega)
      | exact dec_dyk1_g (by assumption)
      | exact dec_dyk2 (by assumption)
      | exact dec_dyk2_g (by assumption)
      | exact dec_ainv (by assumption)
      | exact dec_ainv0 (by assumption)
      | exact dec_orA (by assumption)
      | exact Nat.lt_of_lt_of_le (dec_orA (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_park) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_fire (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_qimp (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_qimp_g (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_dyk1 (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_dyk1_g (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_dyk2 (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_dyk2_g (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_ainv (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_ainv0 (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_orctx (by assumption)) (by omega)
      | exact dec_boxE (by assumption)
      | exact dec_boxE_g (by assumption)
      | exact dec_boxA_g (by assumption)
      | exact dec_cimp1 (by assumption)
      | exact dec_cimp1_g (by assumption)
      | exact dec_cimp2 (by assumption)
      | exact dec_cimp2_g (by assumption)
      | exact dec_cimp3 (by assumption)
      | exact dec_circDirect
      | (have h1 := dec_boxE (by assumption); omega)
      | (have h1 := dec_cimp1 (by assumption); omega)
      | (have h1 := dec_cimp2 (by assumption); omega)
      | (have h1 := dec_cimp3 (by assumption); omega)))

set_option hygiene false in
/-- The decreasing farm of the E-side traversal (`eMinF` and the `T*` family). One definition, eight uses; edit here to tune all farms. -/
macro "ljf_dec_e" : tactic => `(tactic| (
    all_goals simp_wf
    all_goals try simp only [sum3, sum3_append, goalW, wNeg, wPos]
    all_goals
      first
        | exact Nat.lt_succ_self _
        | omega
        | exact Nat.lt_of_lt_of_le
            (Nat.lt_of_le_of_lt (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
              (dec_dykC (Q' := Q') (N' := N') (N := N) hXr))
            (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
        | exact Nat.lt_of_lt_of_le
            (Nat.lt_of_le_of_lt (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
              (dec_dykC (Q' := Q') (N' := N') (N := N_d) hXr))
            (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
        | exact Nat.lt_of_lt_of_le
            (Nat.lt_of_le_of_lt (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
              (dec_dykC (Q' := Q') (N' := N') (N := N) hXr))
            (Nat.le_add_right _ _)
        | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N) hXr; omega)
        | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N_d) hXr; omega)
        | (have h1 := dec_fireS (a := c) (N := Nc) hXr; omega)
        | (have h1 := dec_ainvS (N := N) (by assumption); omega)
        | (have h1 := dec_fireS (by assumption); omega)
        | (have h1 := dec_fireS (findFire_mem (by assumption)); omega)
        | (have h1 := dec_dykC (by assumption); omega)
        | (simp_arith; done)
        | exact dec_fireT (by assumption)
        | exact dec_dykT (by assumption)
        | (have h := dec_fireT (findFire_mem (by assumption)); omega)
        | (have h := dec_fireT (by assumption); omega)
        | (have h := dec_dykT (by assumption); omega)
        | exact Nat.lt_of_lt_of_le (dec_fireT (by assumption)) (by omega)
        | exact Nat.lt_of_lt_of_le (dec_dykT (by assumption)) (by omega)
        | exact dec_dyk0 (by assumption)
        | exact dec_park
        | exact dec_drop
        | exact dec_shift1
        | exact dec_and
        | exact dec_curry
        | exact dec_stripshift
        | exact dec_impor (wPos_pos _) (wPos_pos _)
        | exact dec_orctx (by assumption)
        | (have h1 := invertPos_lt (P := Pos.or _ _)
             (by intro a h; nomatch h) _ (by assumption)
           simp only [wPos] at h1; omega)
        | exact Nat.lt_of_lt_of_le (dec_fire (by assumption)) (by omega)
        | exact Nat.lt_of_lt_of_le (dec_qimp (by assumption)) (by omega)
        | exact p3_strict (by first
            | omega
            | (have := wPos_pos P₁; have := wPos_pos P₂; omega)
            | (have := wNeg_pos M; have := wNeg_pos N; omega))
        | exact dec_qimp_g (by assumption)
        | exact dec_dyk1 (by assumption)
        | (have h1 := dec_dyk1 (by assumption); omega)
        | exact dec_dyk1_g (by assumption)
        | exact dec_dyk2 (by assumption)
        | exact dec_dyk2_g (by assumption)
        | exact dec_ainv (by assumption)
        | exact dec_ainv0 (by assumption)
        | exact dec_orA (by assumption)
        | exact Nat.lt_of_lt_of_le (dec_qimp_g (by assumption)) (by omega)
        | exact Nat.lt_of_lt_of_le (dec_dyk1 (by assumption)) (by omega)
        | exact Nat.lt_of_lt_of_le (dec_dyk1_g (by assumption)) (by omega)
        | exact Nat.lt_of_lt_of_le (dec_dyk2 (by assumption)) (by omega)
        | exact Nat.lt_of_lt_of_le (dec_dyk2_g (by assumption)) (by omega)
        | exact Nat.lt_of_lt_of_le (dec_ainv (by assumption)) (by omega)
        | exact Nat.lt_of_lt_of_le (dec_orA (by assumption)) (by omega)
        | exact Nat.lt_of_lt_of_le (dec_orctx (by assumption)) (by omega)
        | (have h1 := p3_pos (wNeg M); omega)
        | (have h1 := p3_strict (a := wNeg M) (b := wNeg M + 1) (by omega)
           omega)
        | (have h1 := dec_and (m := wNeg M) (n := wNeg N) (t := 0); omega)
        | (have h1 := dec_curry (m₁ := wNeg M₁) (m₂ := wNeg M₂) (n := wNeg N)
             (t := 0); omega)
        | (have h1 := dec_stripshift (x := wPos P') (n := wNeg N) (t := 0)
           omega)
        | (have h1 := dec_impor (a := wPos Q₁) (b := wPos Q₂) (n := wNeg N)
             (t := 0) (wPos_pos _) (wPos_pos _); omega)
        | (have h1 := p3_pos (1 + wNeg N + 1); omega)
        | (have h1 := p3_pos (wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1); omega)
        | (refine Prod.Lex.left _ _ ?_
           first
             | omega
             | exact Nat.lt_of_lt_of_le
                 (Nat.lt_of_le_of_lt
                   (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
                   (dec_dykC (Q' := Q') (N' := N') (N := N) hXr))
                 (Nat.le_trans (Nat.le_add_left _ _)
                   (Nat.le_trans (Nat.le_add_right _ _)
                     (Nat.le_add_right _ _)))
             | exact Nat.lt_of_lt_of_le
                 (Nat.lt_of_le_of_lt
                   (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
                   (dec_dykC (Q' := Q') (N' := N') (N := N_d) hXr))
                 (Nat.le_trans (Nat.le_add_left _ _)
                   (Nat.le_trans (Nat.le_add_right _ _)
                     (Nat.le_add_right _ _)))
             | (have h1 := dec_dykC (Q' := Q') (N' := N') (N := N) hXr; omega)
             | (have h1 := dec_dykC (Q' := Q') (N' := N') (N := N_d) hXr
                omega)
             | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N) hXr; omega)
             | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N_d) hXr
                omega)
             | (have h1 := dec_fireS (a := c) (N := Nc) hXr; omega)
             | (have h1 := dec_ainvS (N := N) (by assumption); omega)
             | (have h1 := dec_fireS (by assumption); omega)
             | (have h1 := dec_fireS (findFire_mem (by assumption)); omega)
             | (have h1 := dec_dykC (by assumption); omega))
        | decreasing_tactic))

set_option hygiene false in
/-- The decreasing farm of the A-side traversal (`aMinF`, `UEntry`, the `U*` family, `dykAntC`). One definition, nine uses. -/
macro "ljf_dec_a" : tactic => `(tactic| (
    all_goals simp_wf
    all_goals try simp only [sum3, sum3_append, goalW, wNeg, wPos]
    all_goals
      first
        | exact Nat.lt_succ_self _
        | omega
        | exact Nat.lt_of_lt_of_le
            (Nat.lt_of_le_of_lt (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
              (dec_dykC (Q' := Q') (N' := N') (N := N) hXr))
            (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
        | exact Nat.lt_of_lt_of_le
            (Nat.lt_of_le_of_lt (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
              (dec_dykC (Q' := Q') (N' := N') (N := N_d) hXr))
            (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
        | exact Nat.lt_of_lt_of_le
            (Nat.lt_of_le_of_lt (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
              (dec_dykC (Q' := Q') (N' := N') (N := N) hXr))
            (Nat.le_add_right _ _)
        | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N) hXr; omega)
        | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N_d) hXr; omega)
        | (have h1 := dec_fireS (a := c) (N := Nc) hXr; omega)
        | (have h1 := dec_ainvS (N := N) (by assumption); omega)
        | (have h1 := dec_fireS (by assumption); omega)
        | (have h1 := dec_fireS (findFire_mem (by assumption)); omega)
        | (have h1 := dec_dykC (by assumption); omega)
        | (simp_arith; done)
        | exact dec_fireT (by assumption)
        | exact dec_dykT (by assumption)
        | (have h := dec_fireT (findFire_mem (by assumption)); omega)
        | (have h := dec_fireT (by assumption); omega)
        | (have h := dec_dykT (by assumption); omega)
        | (have h := dec_fireS (findFire_mem (by assumption)); omega)
        | (have h := dec_fireS (by assumption); omega)
        | (have h := dec_dykC (by assumption); omega)
        | exact dec_dyk0 (by assumption)
        | exact dec_park
        | exact dec_drop
        | exact dec_shift1
        | exact dec_and
        | exact dec_curry
        | exact dec_stripshift
        | exact dec_impor (wPos_pos _) (wPos_pos _)
        | exact dec_orctx (by assumption)
        | (have h1 := invertPos_lt (P := Pos.or _ _)
             (by intro a h; nomatch h) _ (by assumption)
           simp only [wPos] at h1; omega)
        | exact Nat.lt_of_lt_of_le (dec_fire (by assumption)) (by omega)
        | exact Nat.lt_of_lt_of_le (dec_qimp (by assumption)) (by omega)
        | (have h1 := dec_dyk1 (by assumption); omega)
        | (have h1 := dec_ainv (by assumption); omega)
        | (have h1 := dec_ainvS (by assumption); omega)
        | (have h1 := dec_ainv0 (by assumption); omega)
        | (have h1 := dec_orA (by assumption); omega)
        | (have h1 := p3_pos (wNeg M); omega)
        | (have h1 := p3_strict (a := wNeg M) (b := wNeg M + 1) (by omega)
           omega)
        | (have h1 := dec_and (m := wNeg M) (n := wNeg N) (t := 0); omega)
        | (have h1 := dec_curry (m₁ := wNeg M₁) (m₂ := wNeg M₂) (n := wNeg N)
             (t := 0); omega)
        | (have h1 := dec_stripshift (x := wPos P') (n := wNeg N) (t := 0)
           omega)
        | (have h1 := dec_impor (a := wPos Q₁) (b := wPos Q₂) (n := wNeg N)
             (t := 0) (wPos_pos _) (wPos_pos _); omega)
        | (have h1 := p3_pos (1 + wNeg N + 1); omega)
        | (have h1 := p3_pos (wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1); omega)
        | (have h1 := p3_succ (wNeg M); have h2 := p3_pos (wNeg M); omega)
        | (have h1 := p3_pos (wPos P₀); omega)
        | (have h1 := p3_strict (a := wPos P₁) (b := wPos P₁ + wPos P₂ + 1)
             (by have := wPos_pos P₂; omega); omega)
        | (have h1 := p3_strict (a := wPos P₂) (b := wPos P₁ + wPos P₂ + 1)
             (by have := wPos_pos P₁; omega); omega)
        | (have h1 := p3_strict (a := wNeg M) (b := wNeg M + wNeg N + 3)
             (by omega); omega)
        | (have h1 := p3_strict (a := wNeg N) (b := wNeg M + wNeg N + 3)
             (by omega); omega)
        | (refine Prod.Lex.left _ _ ?_
           first
             | omega
             | exact Nat.lt_of_lt_of_le
                 (Nat.lt_of_le_of_lt
                   (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
                   (dec_dykC (Q' := Q') (N' := N') (N := N) hXr))
                 (Nat.le_trans (Nat.le_add_left _ _)
                   (Nat.le_trans (Nat.le_add_right _ _)
                     (Nat.le_add_right _ _)))
             | exact Nat.lt_of_lt_of_le
                 (Nat.lt_of_le_of_lt
                   (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
                   (dec_dykC (Q' := Q') (N' := N') (N := N_d) hXr))
                 (Nat.le_trans (Nat.le_add_left _ _)
                   (Nat.le_trans (Nat.le_add_right _ _)
                     (Nat.le_add_right _ _)))
             | (have h1 := dec_dykC (Q' := Q') (N' := N') (N := N) hXr; omega)
             | (have h1 := dec_dykC (Q' := Q') (N' := N') (N := N_d) hXr
                omega)
             | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N) hXr; omega)
             | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N_d) hXr
                omega)
             | (have h1 := dec_fireS (a := c) (N := Nc) hXr; omega)
             | (have h1 := dec_ainvS (N := N) (by assumption); omega)
             | (have h1 := dec_fireS (by assumption); omega)
             | (have h1 := dec_fireS (findFire_mem (by assumption)); omega)
             | (have h1 := dec_dykC (by assumption); omega))
        | decreasing_tactic))


set_option maxHeartbeats 12000000 in
mutual

def eSound (p : String) : ∀ (todo done : List Neg),
    Inv (todo ++ done) [] .tru (interp p todo done none)
  | .up (.atom a) :: todo, done => by
      rw [interp]
      exact (eSound p todo (.up (.atom a) :: done)).wk subPark
  | .up .fls :: todo, done => by
      rw [interp]
      exact .stable (.lfoc (List.mem_cons_self ..) (.rel .flsL))
  | .up (.or P Q) :: todo, done => by
      rw [interp]
      refine upMerge _ (List.mem_cons_self ..) ?_
      intro b hb
      refine nOrAllIntro
        (List.mem_map_of_mem (List.mem_attach _ ⟨b, hb⟩)) ?_
      exact (eSound p (b ++ todo) done).wk subBranch1
  | .up (.down M) :: todo, done => by
      rw [interp]
      refine upMerge _ (List.mem_cons_self ..) ?_
      intro b hb
      simp only [invertPos, List.mem_singleton] at hb
      subst hb
      exact (eSound p (M :: todo) done).wk (Sub.cons M (Sub.grow _))
  | .and M N :: todo, done => by
      rw [interp]
      exact simHyp
        (fl := fun hs lf => .lfoc (hs _ (List.mem_cons_self ..)) (.and2 lf))
        (Sub.refl _)
        (simHyp
          (fl := fun hs lf =>
            .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
              (.and1 lf))
          (Sub.cons N (Sub.grow _))
          (eSound p (M :: N :: todo) done))
  | .imp .fls N :: todo, done => by
      rw [interp]
      exact (eSound p todo done).wk (Sub.grow _)
  | .imp (.atom a) N :: todo, done => by
      rw [interp]
      exact (eSound p todo (.imp (.atom a) N :: done)).wk subPark
  | .circ Q :: todo, done => by
      rw [interp]
      exact (eSound p todo (.circ Q :: done)).wk subPark
  | .imp (.down (.circ Q')) N :: todo, done => by
      rw [interp]
      exact (eSound p todo (.imp (.down (.circ Q')) N :: done)).wk subPark
  | .imp (.or Q₁ Q₂) N :: todo, done => by
      rw [interp]
      exact simHyp (H := .imp Q₂ N)
        (fl := fun hs lf => match lf with
          | .impL s lf1 =>
              .lfoc (hs _ (List.mem_cons_self ..)) (.impL (stabOr2 s) lf1))
        (Sub.refl _)
        (simHyp (H := .imp Q₁ N)
          (fl := fun hs lf => match lf with
            | .impL s lf1 =>
                .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
                  (.impL (stabOr1 s) lf1))
          (Sub.cons _ (Sub.grow _))
          (eSound p (.imp Q₁ N :: .imp Q₂ N :: todo) done))
  | .imp (.down (.up P')) N :: todo, done => by
      rw [interp]
      exact simHyp (H := .imp P' N)
        (fl := fun hs lf => match lf with
          | .impL s lf1 =>
              .lfoc (hs _ (List.mem_cons_self ..))
                (.impL (.rfoc (.rel (.stable s))) lf1))
        (Sub.grow _)
        (eSound p (.imp P' N :: todo) done)
  | .imp (.down (.and M₁ M₂)) N :: todo, done => by
      rw [interp]
      exact simHyp (H := .imp (.down M₁) (.imp (.down M₂) N))
        (fl := fun {Δa} {_} {_} hs lf => match lf with
          | LFoc.impL s₁ (LFoc.impL s₂ lf2) =>
              routeStabT (Δ₀ := Δa)
                (k := fun {Δb} hsb r₁ =>
                  routeStabT (Δ₀ := Δb)
                    (k := fun {Δc} hsc r₂ =>
                      .lfoc (hsc _ (hsb _ (hs _ (List.mem_cons_self ..))))
                        (.impL
                          (.rfoc (.rel (.andR ((relOf r₁).wk hsc) (relOf r₂))))
                          (lf2.wk (fun Z hZ => hsc _ (hsb _ hZ)))))
                    (Sub.refl _) (s₂.wk hsb))
                (Sub.refl _) s₁)
        (Sub.grow _)
        (eSound p (.imp (.down M₁) (.imp (.down M₂) N) :: todo) done)
  | .imp (.down (.imp Q' N')) N :: todo, done => by
      rw [interp]
      exact (eSound p todo (.imp (.down (.imp Q' N')) N :: done)).wk subPark
  | [], done => by
      rw [interp]
      match hf : findFire done (splits done) with
      | some (a, N, rest) =>
          simp only [hf]
          exact simHyp
            (fl := fun hs lf =>
              .lfoc (hs _ (splits_mem (findFire_mem hf)))
                (.impL (.rfoc (.init (hs _ (atomMem_mem (findFire_atom hf)))))
                  lf))
            (splits_sub (findFire_mem hf))
            (eSound p [N] rest)
      | none =>
          simp only [hf]
          refine nAndAllIntro ?_
          intro x hx
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx
          subst hEq
          cases X with
          | up P0 =>
              cases P0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]; exact nTopIntro
                  · simp only [pGuard, if_neg hap]
                    exact .stable (.rfoc (.init (splits_mem hXr)))
              | fls => exact nTopIntro
              | or _ _ => exact nTopIntro
              | down _ => exact nTopIntro
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]; exact nTopIntro
                  · simp only [pGuard, if_neg hap]
                    refine .impR (.atomL ?_)
                    exact simHyp
                      (fl := fun hs lf =>
                        .lfoc (hs _ (List.mem_cons_of_mem _ (splits_mem hXr)))
                          (.impL (.rfoc (.init (hs _ (List.mem_cons_self ..))))
                            lf))
                      (fun Z hZ =>
                        List.mem_cons_of_mem _ (splits_sub hXr Z hZ))
                      (eSound p [N] rest)
              | fls => exact nTopIntro
              | or _ _ => exact nTopIntro
              | down M0 =>
                  cases M0 with
                  | up _ => exact nTopIntro
                  | and _ _ => exact nTopIntro

                  | circ Q' =>
                      -- the modal Dyckhoff pair: the fire guarded by the ∀p
                      -- of (rest ⇒ ◯Q′), PAIRED with the ∃p of rest; the
                      -- argument comes from aSound at the ◯-goal — the
                      -- E1/A1 interlock
                      refine .andR (.impR (.downL ?_))
                        ((eSound p [] rest).wk (splits_sub hXr))
                      have dArg : Inv (interp p [] rest (some (.circ Q')) ::
                          ([] ++ done)) [] .tru (.up (.down (.circ Q'))) :=
                        .stable (.rfoc (.rel
                          ((aSound p [] rest (.circ Q')).wk (by
                            intro Z hZ
                            rcases List.mem_cons.mp hZ with rfl | hZ
                            · exact List.mem_cons_self ..
                            · exact List.mem_cons_of_mem _
                                (splits_sub hXr Z hZ)))))
                      exact simHyp
                        (fl := fun hs lf =>
                          .lfoc (hs _ (List.mem_cons_of_mem _ (splits_mem hXr)))
                            (.impL (unStable (dArg.wk hs)) lf))
                        (fun Z hZ =>
                          List.mem_cons_of_mem _ (splits_sub hXr Z hZ))
                        (eSound p [N] rest)
                  | imp Q' N' =>
                      refine .andR (.impR (.downL ?_))
                        (simHyp (fl := resSim (splits_mem hXr))
                          (splits_sub hXr)
                          (eSound p [.imp (.down N') N] rest))
                      have hXd : Neg.imp (.down (.imp Q' N')) N ∈
                          (interp p [.imp (.down N') N] rest
                            (some (.imp Q' N')) :: ([] ++ done)) :=
                        List.mem_cons_of_mem _ (splits_mem hXr)
                      have dM' : Inv (interp p [.imp (.down N') N] rest
                          (some (.imp Q' N')) :: ([] ++ done)) []
                          .tru (.imp Q' N') :=
                        simHyp (fl := resSim hXd) (Sub.refl _)
                          ((aSound p [.imp (.down N') N] rest
                              (.imp Q' N')).wk (by
                            intro Z hZ
                            rcases List.mem_cons.mp hZ with rfl | hZ
                            · exact List.mem_cons_of_mem _
                                (List.mem_cons_self ..)
                            · rcases List.mem_cons.mp hZ with rfl | hZ
                              · exact List.mem_cons_self ..
                              · exact List.mem_cons_of_mem _
                                  (List.mem_cons_of_mem _
                                    (splits_sub hXr Z hZ))))
                      exact simHyp
                        (fl := fun hs lf =>
                          .lfoc (hs _ hXd)
                            (.impL (.rfoc (.rel (dM'.wk hs))) lf))
                        (fun Z hZ =>
                          List.mem_cons_of_mem _ (splits_sub hXr Z hZ))
                        (eSound p [N] rest)
          | and _ _ => exact nTopIntro
          | circ Q =>
              -- the box conjunct ◯(↓E(↑Q :: rest)): circR into the lax
              -- phase, open the parked box, invert per branch, laxOf at
              -- the leaf, and eSound at the opened station — uses of the
              -- whole ↑Q mediated by extract along the branch
              refine .circR (.stable (.lfoc (splits_mem hXr)
                (.circL (invBranches Q (fun b hb => ?_)))))
              refine .stable (.laxOf (.rfoc (.rel ?_)))
              exact simHyp (H := .up Q)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (fun Z hZ => List.mem_append_right b (splits_sub hXr Z hZ))
                (eSound p [.up Q] rest)

  termination_by todo done => 2 * sum3 todo + sum3 done
  decreasing_by ljf_dec_sound

def aSound (p : String) : ∀ (todo done : List Neg) (G : Neg),
    Inv (interp p todo done (some G) :: (todo ++ done)) [] .tru G
  | .up (.atom a) :: todo, done, G => by
      rw [interp]
      exact (aSound p todo (.up (.atom a) :: done) G).wk (Sub.cons _ subPark)
  | .up .fls :: todo, done, G => by
      rw [interp]
      exact upMerge G (R := .fls)
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        (fun _ hb => by simp [invertPos] at hb)
  | .up (.or P Q) :: todo, done, G => by
      rw [interp]
      refine upMerge G (R := .or P Q)
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ?_
      intro b hb
      exact simHyp
        (fl := fun hs lf =>
          .lfoc (hs _ (List.mem_append_right _ (List.mem_cons_self ..)))
            (lfocAndAll (List.mem_map_of_mem (List.mem_attach _ ⟨b, hb⟩))
              (.impL
                (.rfoc (.rel ((eSound p (b ++ todo) done).wk (fun Z hZ =>
                  hs _ (subBranch2 Z (by
                    rcases List.mem_append.mp hZ with hZ | hZ
                    · exact List.mem_append_left _ hZ
                    · exact List.mem_append_right _ hZ))))))
                lf)))
        (subBranch2)
        (aSound p (b ++ todo) done G)
  | .up (.down M) :: todo, done, G => by
      rw [interp]
      refine upMerge G (R := .down M)
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ?_
      intro b hb
      simp only [invertPos, List.mem_singleton] at hb
      subst hb
      exact (aSound p (M :: todo) done G).wk (by
        intro Z hZ
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ hZ)))
  | .and M N :: todo, done, G => by
      rw [interp]
      exact simHyp
        (fl := fun hs lf =>
          .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
            (.and2 lf))
        (Sub.refl _)
        (simHyp
          (fl := fun hs lf =>
            .lfoc (hs _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (.and1 lf))
          (Sub.cons N (Sub.cons _ (Sub.grow _)))
          ((aSound p (M :: N :: todo) done G).wk (by
            intro Z hZ
            rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_self ..))
            · rcases List.mem_cons.mp hZ with rfl | hZ
              · exact List.mem_cons_self ..
              · rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ hZ)))))
  | .imp .fls N :: todo, done, G => by
      rw [interp]
      exact (aSound p todo done G).wk (Sub.cons _ (Sub.grow _))
  | .imp (.atom a) N :: todo, done, G => by
      rw [interp]
      exact (aSound p todo (.imp (.atom a) N :: done) G).wk (Sub.cons _ subPark)
  | .circ Q :: todo, done, G => by
      rw [interp]
      exact (aSound p todo (.circ Q :: done) G).wk (Sub.cons _ subPark)
  | .imp (.down (.circ Q')) N :: todo, done, G => by
      rw [interp]
      exact (aSound p todo (.imp (.down (.circ Q')) N :: done) G).wk
        (Sub.cons _ subPark)
  | .imp (.or Q₁ Q₂) N :: todo, done, G => by
      rw [interp]
      exact simHyp (H := .imp Q₂ N)
        (fl := fun hs lf => match lf with
          | .impL s lf1 =>
              .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
                (.impL (stabOr2 s) lf1))
        (Sub.refl _)
        (simHyp (H := .imp Q₁ N)
          (fl := fun hs lf => match lf with
            | .impL s lf1 =>
                .lfoc (hs _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
                  (.impL (stabOr1 s) lf1))
          (Sub.cons _ (Sub.cons _ (Sub.grow _)))
          ((aSound p (.imp Q₁ N :: .imp Q₂ N :: todo) done G).wk (by
            intro Z hZ
            rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_self ..))
            · rcases List.mem_cons.mp hZ with rfl | hZ
              · exact List.mem_cons_self ..
              · rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ hZ)))))
  | .imp (.down (.up P')) N :: todo, done, G => by
      rw [interp]
      exact simHyp (H := .imp P' N)
        (fl := fun hs lf => match lf with
          | .impL s lf1 =>
              .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
                (.impL (.rfoc (.rel (.stable s))) lf1))
        (Sub.refl _)
        ((aSound p (.imp P' N :: todo) done G).wk (by
          intro Z hZ
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ hZ))))
  | .imp (.down (.and M₁ M₂)) N :: todo, done, G => by
      rw [interp]
      exact simHyp (H := .imp (.down M₁) (.imp (.down M₂) N))
        (fl := fun {Δa} {_} {_} hs lf => match lf with
          | LFoc.impL s₁ (LFoc.impL s₂ lf2) =>
              routeStabT (Δ₀ := Δa)
                (k := fun {Δb} hsb r₁ =>
                  routeStabT (Δ₀ := Δb)
                    (k := fun {Δc} hsc r₂ =>
                      .lfoc (hsc _ (hsb _ (hs _ (List.mem_cons_of_mem _
                          (List.mem_cons_self ..)))))
                        (.impL
                          (.rfoc (.rel (.andR ((relOf r₁).wk hsc) (relOf r₂))))
                          (lf2.wk (fun Z hZ => hsc _ (hsb _ hZ)))))
                    (Sub.refl _) (s₂.wk hsb))
                (Sub.refl _) s₁)
        (Sub.refl _)
        ((aSound p (.imp (.down M₁) (.imp (.down M₂) N) :: todo) done G).wk (by
          intro Z hZ
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ hZ))))
  | .imp (.down (.imp Q' N')) N :: todo, done, G => by
      rw [interp]
      exact (aSound p todo (.imp (.down (.imp Q' N')) N :: done) G).wk
        (Sub.cons _ subPark)
  | [], done, .imp Q N => by
      rw [interp]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASound hf (aSound p [N'] rest (.imp Q N))
      | none =>
          simp only [hf]
          refine .impR (invBranches Q ?_)
          intro b hb
          exact simHyp
            (fl := fun hs lf =>
              .lfoc (hs _ (List.mem_append_right _ (List.mem_cons_self ..)))
                (lfocAndAll
                  (List.mem_map_of_mem (List.mem_attach _ ⟨b, hb⟩))
                  (.impL
                    (.rfoc (.rel ((eSound p b done).wk (fun Z hZ => hs _ (by
                      rcases List.mem_append.mp hZ with hZ | hZ
                      · exact List.mem_append_left _ hZ
                      · exact List.mem_append_right _
                          (List.mem_cons_of_mem _ hZ))))))
                    lf)))
            (fun Z hZ => by
              rcases List.mem_append.mp hZ with hZ | hZ
              · exact List.mem_append_left _ hZ
              · exact List.mem_append_right _ (List.mem_cons_of_mem _
                  (List.mem_append_right _ hZ)))
            (aSound p b done N)
  | [], done, .and M N => by
      rw [interp]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASound hf (aSound p [N'] rest (.and M N))
      | none =>
          simp only [hf]
          refine .andR ?_ ?_
          · exact simHyp
              (fl := fun hs lf =>
                .lfoc (hs _ (List.mem_cons_self ..)) (.and1 lf))
              (Sub.grow _)
              (aSound p [] done M)
          · exact simHyp
              (fl := fun hs lf =>
                .lfoc (hs _ (List.mem_cons_self ..)) (.and2 lf))
              (Sub.grow _)
              (aSound p [] done N)
  | [], done, .up (.atom q) => by
      rw [interp]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASound hf (aSound p [N'] rest (.up (.atom q)))
      | none =>
          simp only [hf]
          by_cases hq : atomMem q done = true
          · simp only [hq, if_true]
            exact .stable (.rfoc (.init (List.mem_cons_of_mem _
              (atomMem_mem hq))))
          · simp only [hq, if_false]
            refine nOrAllElim _ (List.mem_cons_self ..) ?_
            intro x hx Γ' hsub
            if hx1 : x ∈ atomHead p q then
              by_cases hqp : q = p
              · simp [atomHead, hqp] at hx1
              · simp only [atomHead, if_neg hqp, List.mem_singleton] at hx1
                subst hx1
                exact .stable (.rfoc (.init (List.mem_cons_self ..)))
            else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                      (aSound p [N] rest (.up (.atom q)))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [.imp (.down N') N] rest (.imp Q' N'))
                        (aSound p [N] rest (.up (.atom q)))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [] rest (.circ Q'))
                        (aSound p [N] rest (.up (.atom q)))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ _ => exact nBotElim _ (List.mem_cons_self ..)
  | [], done, .up .fls => by
      rw [interp]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASound hf (aSound p [N'] rest (.up .fls))
      | none =>
          simp only [hf]
          refine nOrAllElim _ (List.mem_cons_self ..) ?_
          intro x hx Γ' hsub
          if hx1 : x ∈ ([] : List Neg) then
            exact absurd hx1 (List.not_mem_nil)
          else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                      (aSound p [N] rest (.up .fls))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [.imp (.down N') N] rest (.imp Q' N'))
                        (aSound p [N] rest (.up .fls))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [] rest (.circ Q'))
                        (aSound p [N] rest (.up .fls))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ _ => exact nBotElim _ (List.mem_cons_self ..)
  | [], done, .up (.or P₁ P₂) => by
      rw [interp]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASound hf (aSound p [N'] rest (.up (.or P₁ P₂)))
      | none =>
          simp only [hf]
          refine nOrAllElim _ (List.mem_cons_self ..) ?_
          intro x hx Γ' hsub
          if hx1 : x ∈ [interp p [] done (some (.up P₁)),
              interp p [] done (some (.up P₂))] then
            if e1 : x = interp p [] done (some (.up P₁)) then
              subst e1
              exact .stable (stabOr1 (unStable ((aSound p [] done
                (.up P₁)).wk (by
                  intro Z hZ
                  rcases List.mem_cons.mp hZ with rfl | hZ
                  · exact List.mem_cons_self ..
                  · exact List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ hZ))))))
            else
              have e2 : x = interp p [] done (some (.up P₂)) := by
                rcases List.mem_cons.mp hx1 with h | h
                · exact absurd h e1
                · exact List.mem_singleton.mp h
              subst e2
              exact .stable (stabOr2 (unStable ((aSound p [] done
                (.up P₂)).wk (by
                  intro Z hZ
                  rcases List.mem_cons.mp hZ with rfl | hZ
                  · exact List.mem_cons_self ..
                  · exact List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ hZ))))))
          else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                      (aSound p [N] rest (.up (.or P₁ P₂)))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [.imp (.down N') N] rest (.imp Q' N'))
                        (aSound p [N] rest (.up (.or P₁ P₂)))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [] rest (.circ Q'))
                        (aSound p [N] rest (.up (.or P₁ P₂)))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ _ => exact nBotElim _ (List.mem_cons_self ..)
  | [], done, .up (.down M) => by
      rw [interp]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASound hf (aSound p [N'] rest (.up (.down M)))
      | none =>
          simp only [hf]
          refine nOrAllElim _ (List.mem_cons_self ..) ?_
          intro x hx Γ' hsub
          if hx1 : x ∈ [interp p [] done (some M)] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .stable (.rfoc (.rel ((aSound p [] done M).wk (by
              intro Z hZ
              rcases List.mem_cons.mp hZ with rfl | hZ
              · exact List.mem_cons_self ..
              · exact List.mem_cons_of_mem _
                  (hsub _ (List.mem_cons_of_mem _ hZ))))))
          else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                      (aSound p [N] rest (.up (.down M)))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [.imp (.down N') N] rest (.imp Q' N'))
                        (aSound p [N] rest (.up (.down M)))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [] rest (.circ Q'))
                        (aSound p [N] rest (.up (.down M)))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ _ => exact nBotElim _ (List.mem_cons_self ..)

  | [], done, .circ (.atom q) => by
      rw [interp]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASound hf (aSound p [N'] rest (.circ (.atom q)))
      | none =>
          simp only [hf]
          refine nOrAllElim _ (List.mem_cons_self ..) ?_
          intro x hx Γ' hsub
          if hx1 : x ∈ [interp p [] done (some (.up (.atom q)))] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .circR (.stable (.laxOf (unStable
              ((aSound p [] done (.up (.atom q))).wk (by
                intro Z hZ
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _
                    (hsub _ (List.mem_cons_of_mem _ hZ)))))))
          else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                      (aSound p [N] rest (.circ (.atom q)))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [.imp (.down N') N] rest (.imp Q' N'))
                        (aSound p [N] rest (.circ (.atom q)))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [] rest (.circ Q'))
                        (aSound p [N] rest (.circ (.atom q)))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ R =>
              -- THE E-GUARDED BOX-OPENING ROW, x = ↓E(↑R::rest) ⊃ A(↑R::rest ⇒ ◯Q):
              -- circR into the lax phase; open the station box; per branch of R,
              -- derive E at the opened station (extract-mediated eSound), feed the
              -- row to get the opened-station ∀p, close ◯Q by aSound there, and
              -- re-enter the lax phase through circROf.
              refine .circR (.stable (.lfoc
                (List.mem_cons_of_mem _
                  (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                (.circL (invBranches R (fun b hb => ?_)))))
              -- dE: the opened-station ∃p, over the branch products
              have dE : Inv (b ++ (Neg.imp
                    (.down (interp p [.up R] rest none))
                    (interp p [.up R] rest (some (.circ (.atom q)))) :: Γ')) []
                  .tru (interp p [.up R] rest none) :=
                simHyp (H := .up R)
                  (fl := fun hs lf => match lf with
                    | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                        (List.mem_append.mp hZ).elim
                          (fun h => hs Z (List.mem_append_left _ h)) id)))
                  (fun Z hZ => List.mem_append_right b
                    (List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ)))))
                  (eSound p [.up R] rest)
              -- the opened-station ∀p beside the opened station closes ◯Q
              have D := (aSound p [.up R] rest (.circ (.atom q)))
              -- strip A (via the row fired with dE), then ↑R (via extract)
              refine .stable (unStable (simHyp (H := .up R)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (Sub.refl _)
                (simHyp (H := interp p [.up R] rest (some (.circ (.atom q))))
                  (fl := fun hs lf =>
                    .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_self ..))))
                      (.impL (.rfoc (.rel (dE.wk (fun Z hZ =>
                        hs Z (List.mem_cons_of_mem _ hZ))))) lf))
                  (fun Z hZ => by
                    rcases List.mem_cons.mp hZ with rfl | hZ
                    · exact List.mem_cons_self ..
                    · exact List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))))
                  (circROf D))))


  | [], done, .circ .fls => by
      rw [interp]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASound hf (aSound p [N'] rest (.circ .fls))
      | none =>
          simp only [hf]
          refine nOrAllElim _ (List.mem_cons_self ..) ?_
          intro x hx Γ' hsub
          if hx1 : x ∈ [interp p [] done (some (.up .fls))] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .circR (.stable (.laxOf (unStable
              ((aSound p [] done (.up .fls)).wk (by
                intro Z hZ
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _
                    (hsub _ (List.mem_cons_of_mem _ hZ)))))))
          else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                      (aSound p [N] rest (.circ .fls))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [.imp (.down N') N] rest (.imp Q' N'))
                        (aSound p [N] rest (.circ .fls))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [] rest (.circ Q'))
                        (aSound p [N] rest (.circ .fls))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ R =>
              -- THE E-GUARDED BOX-OPENING ROW, x = ↓E(↑R::rest) ⊃ A(↑R::rest ⇒ ◯Q):
              -- circR into the lax phase; open the station box; per branch of R,
              -- derive E at the opened station (extract-mediated eSound), feed the
              -- row to get the opened-station ∀p, close ◯Q by aSound there, and
              -- re-enter the lax phase through circROf.
              refine .circR (.stable (.lfoc
                (List.mem_cons_of_mem _
                  (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                (.circL (invBranches R (fun b hb => ?_)))))
              -- dE: the opened-station ∃p, over the branch products
              have dE : Inv (b ++ (Neg.imp
                    (.down (interp p [.up R] rest none))
                    (interp p [.up R] rest (some (.circ .fls))) :: Γ')) []
                  .tru (interp p [.up R] rest none) :=
                simHyp (H := .up R)
                  (fl := fun hs lf => match lf with
                    | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                        (List.mem_append.mp hZ).elim
                          (fun h => hs Z (List.mem_append_left _ h)) id)))
                  (fun Z hZ => List.mem_append_right b
                    (List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ)))))
                  (eSound p [.up R] rest)
              -- the opened-station ∀p beside the opened station closes ◯Q
              have D := (aSound p [.up R] rest (.circ .fls))
              -- strip A (via the row fired with dE), then ↑R (via extract)
              refine .stable (unStable (simHyp (H := .up R)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (Sub.refl _)
                (simHyp (H := interp p [.up R] rest (some (.circ .fls)))
                  (fl := fun hs lf =>
                    .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_self ..))))
                      (.impL (.rfoc (.rel (dE.wk (fun Z hZ =>
                        hs Z (List.mem_cons_of_mem _ hZ))))) lf))
                  (fun Z hZ => by
                    rcases List.mem_cons.mp hZ with rfl | hZ
                    · exact List.mem_cons_self ..
                    · exact List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))))
                  (circROf D))))


  | [], done, .circ (.or P₁ P₂) => by
      rw [interp]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASound hf (aSound p [N'] rest (.circ (.or P₁ P₂)))
      | none =>
          simp only [hf]
          refine nOrAllElim _ (List.mem_cons_self ..) ?_
          intro x hx Γ' hsub
          if he1 : x = interp p [] done (some (.circ P₁)) then
            subst he1
            exact .circR (.stable (stabOr1 (unStable (circROf
                ((aSound p [] done (.circ P₁)).wk (by
                intro Z hZ
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _
                    (hsub _ (List.mem_cons_of_mem _ hZ))))))))
          else if he2 : x = interp p [] done (some (.circ P₂)) then
            subst he2
            exact .circR (.stable (stabOr2 (unStable (circROf
                ((aSound p [] done (.circ P₂)).wk (by
                intro Z hZ
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _
                    (hsub _ (List.mem_cons_of_mem _ hZ))))))))
          else if he3 : x = interp p [] done (some (.up (.or P₁ P₂))) then
            subst he3
            exact .circR (.stable (.laxOf (unStable
              ((aSound p [] done (.up (.or P₁ P₂))).wk (by
                intro Z hZ
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _
                    (hsub _ (List.mem_cons_of_mem _ hZ)))))))
          else
          have hx2 := (List.mem_append.mp hx).resolve_left (by
            intro h
            rcases List.mem_cons.mp h with h | h
            · exact he1 h
            · rcases List.mem_cons.mp h with h | h
              · exact he2 h
              · exact he3 (List.mem_singleton.mp h))
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                      (aSound p [N] rest (.circ (.or P₁ P₂)))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [.imp (.down N') N] rest (.imp Q' N'))
                        (aSound p [N] rest (.circ (.or P₁ P₂)))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [] rest (.circ Q'))
                        (aSound p [N] rest (.circ (.or P₁ P₂)))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ R =>
              -- THE E-GUARDED BOX-OPENING ROW, x = ↓E(↑R::rest) ⊃ A(↑R::rest ⇒ ◯Q):
              -- circR into the lax phase; open the station box; per branch of R,
              -- derive E at the opened station (extract-mediated eSound), feed the
              -- row to get the opened-station ∀p, close ◯Q by aSound there, and
              -- re-enter the lax phase through circROf.
              refine .circR (.stable (.lfoc
                (List.mem_cons_of_mem _
                  (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                (.circL (invBranches R (fun b hb => ?_)))))
              -- dE: the opened-station ∃p, over the branch products
              have dE : Inv (b ++ (Neg.imp
                    (.down (interp p [.up R] rest none))
                    (interp p [.up R] rest (some (.circ (.or P₁ P₂)))) :: Γ')) []
                  .tru (interp p [.up R] rest none) :=
                simHyp (H := .up R)
                  (fl := fun hs lf => match lf with
                    | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                        (List.mem_append.mp hZ).elim
                          (fun h => hs Z (List.mem_append_left _ h)) id)))
                  (fun Z hZ => List.mem_append_right b
                    (List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ)))))
                  (eSound p [.up R] rest)
              -- the opened-station ∀p beside the opened station closes ◯Q
              have D := (aSound p [.up R] rest (.circ (.or P₁ P₂)))
              -- strip A (via the row fired with dE), then ↑R (via extract)
              refine .stable (unStable (simHyp (H := .up R)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (Sub.refl _)
                (simHyp (H := interp p [.up R] rest (some (.circ (.or P₁ P₂))))
                  (fl := fun hs lf =>
                    .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_self ..))))
                      (.impL (.rfoc (.rel (dE.wk (fun Z hZ =>
                        hs Z (List.mem_cons_of_mem _ hZ))))) lf))
                  (fun Z hZ => by
                    rcases List.mem_cons.mp hZ with rfl | hZ
                    · exact List.mem_cons_self ..
                    · exact List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))))
                  (circROf D))))


  | [], done, .circ (.down (.up P')) => by
      rw [interp]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASound hf (aSound p [N'] rest (.circ (.down (.up P'))))
      | none =>
          simp only [hf]
          refine nOrAllElim _ (List.mem_cons_self ..) ?_
          intro x hx Γ' hsub
          if hx1 : x ∈ [interp p [] done (some (.circ P'))] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .circR (.stable (.rfoc (.rel (circROf
              ((aSound p [] done (.circ P')).wk (by
                intro Z hZ
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _
                    (hsub _ (List.mem_cons_of_mem _ hZ))))))))
          else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                      (aSound p [N] rest (.circ (.down (.up P'))))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [.imp (.down N') N] rest (.imp Q' N'))
                        (aSound p [N] rest (.circ (.down (.up P'))))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [] rest (.circ Q'))
                        (aSound p [N] rest (.circ (.down (.up P'))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ R =>
              -- THE E-GUARDED BOX-OPENING ROW, x = ↓E(↑R::rest) ⊃ A(↑R::rest ⇒ ◯Q):
              -- circR into the lax phase; open the station box; per branch of R,
              -- derive E at the opened station (extract-mediated eSound), feed the
              -- row to get the opened-station ∀p, close ◯Q by aSound there, and
              -- re-enter the lax phase through circROf.
              refine .circR (.stable (.lfoc
                (List.mem_cons_of_mem _
                  (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                (.circL (invBranches R (fun b hb => ?_)))))
              -- dE: the opened-station ∃p, over the branch products
              have dE : Inv (b ++ (Neg.imp
                    (.down (interp p [.up R] rest none))
                    (interp p [.up R] rest (some (.circ (.down (.up P'))))) :: Γ')) []
                  .tru (interp p [.up R] rest none) :=
                simHyp (H := .up R)
                  (fl := fun hs lf => match lf with
                    | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                        (List.mem_append.mp hZ).elim
                          (fun h => hs Z (List.mem_append_left _ h)) id)))
                  (fun Z hZ => List.mem_append_right b
                    (List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ)))))
                  (eSound p [.up R] rest)
              -- the opened-station ∀p beside the opened station closes ◯Q
              have D := (aSound p [.up R] rest (.circ (.down (.up P'))))
              -- strip A (via the row fired with dE), then ↑R (via extract)
              refine .stable (unStable (simHyp (H := .up R)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (Sub.refl _)
                (simHyp (H := interp p [.up R] rest (some (.circ (.down (.up P')))))
                  (fl := fun hs lf =>
                    .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_self ..))))
                      (.impL (.rfoc (.rel (dE.wk (fun Z hZ =>
                        hs Z (List.mem_cons_of_mem _ hZ))))) lf))
                  (fun Z hZ => by
                    rcases List.mem_cons.mp hZ with rfl | hZ
                    · exact List.mem_cons_self ..
                    · exact List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))))
                  (circROf D))))


  | [], done, .circ (.down (.circ P')) => by
      rw [interp]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASound hf (aSound p [N'] rest (.circ (.down (.circ P'))))
      | none =>
          simp only [hf]
          refine nOrAllElim _ (List.mem_cons_self ..) ?_
          intro x hx Γ' hsub
          if hx1 : x ∈ [interp p [] done (some (.circ P'))] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .circR (.stable (.rfoc (.rel (.circR (circROf
              ((aSound p [] done (.circ P')).wk (by
                intro Z hZ
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _
                    (hsub _ (List.mem_cons_of_mem _ hZ)))))))))
          else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                      (aSound p [N] rest (.circ (.down (.circ P'))))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [.imp (.down N') N] rest (.imp Q' N'))
                        (aSound p [N] rest (.circ (.down (.circ P'))))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [] rest (.circ Q'))
                        (aSound p [N] rest (.circ (.down (.circ P'))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ R =>
              -- THE E-GUARDED BOX-OPENING ROW, x = ↓E(↑R::rest) ⊃ A(↑R::rest ⇒ ◯Q):
              -- circR into the lax phase; open the station box; per branch of R,
              -- derive E at the opened station (extract-mediated eSound), feed the
              -- row to get the opened-station ∀p, close ◯Q by aSound there, and
              -- re-enter the lax phase through circROf.
              refine .circR (.stable (.lfoc
                (List.mem_cons_of_mem _
                  (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                (.circL (invBranches R (fun b hb => ?_)))))
              -- dE: the opened-station ∃p, over the branch products
              have dE : Inv (b ++ (Neg.imp
                    (.down (interp p [.up R] rest none))
                    (interp p [.up R] rest (some (.circ (.down (.circ P'))))) :: Γ')) []
                  .tru (interp p [.up R] rest none) :=
                simHyp (H := .up R)
                  (fl := fun hs lf => match lf with
                    | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                        (List.mem_append.mp hZ).elim
                          (fun h => hs Z (List.mem_append_left _ h)) id)))
                  (fun Z hZ => List.mem_append_right b
                    (List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ)))))
                  (eSound p [.up R] rest)
              -- the opened-station ∀p beside the opened station closes ◯Q
              have D := (aSound p [.up R] rest (.circ (.down (.circ P'))))
              -- strip A (via the row fired with dE), then ↑R (via extract)
              refine .stable (unStable (simHyp (H := .up R)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (Sub.refl _)
                (simHyp (H := interp p [.up R] rest (some (.circ (.down (.circ P')))))
                  (fl := fun hs lf =>
                    .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_self ..))))
                      (.impL (.rfoc (.rel (dE.wk (fun Z hZ =>
                        hs Z (List.mem_cons_of_mem _ hZ))))) lf))
                  (fun Z hZ => by
                    rcases List.mem_cons.mp hZ with rfl | hZ
                    · exact List.mem_cons_self ..
                    · exact List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))))
                  (circROf D))))


  | [], done, .circ (.down (.and M₁ M₂)) => by
      rw [interp]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASound hf (aSound p [N'] rest (.circ (.down (.and M₁ M₂))))
      | none =>
          simp only [hf]
          refine nOrAllElim _ (List.mem_cons_self ..) ?_
          intro x hx Γ' hsub
          if hx1 : x ∈ [interp p [] done (some (.up (.down (.and M₁ M₂))))] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .circR (.stable (.laxOf (unStable
              ((aSound p [] done (.up (.down (.and M₁ M₂)))).wk (by
                intro Z hZ
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _
                    (hsub _ (List.mem_cons_of_mem _ hZ)))))))
          else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                      (aSound p [N] rest (.circ (.down (.and M₁ M₂))))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [.imp (.down N') N] rest (.imp Q' N'))
                        (aSound p [N] rest (.circ (.down (.and M₁ M₂))))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [] rest (.circ Q'))
                        (aSound p [N] rest (.circ (.down (.and M₁ M₂))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ R =>
              -- THE E-GUARDED BOX-OPENING ROW, x = ↓E(↑R::rest) ⊃ A(↑R::rest ⇒ ◯Q):
              -- circR into the lax phase; open the station box; per branch of R,
              -- derive E at the opened station (extract-mediated eSound), feed the
              -- row to get the opened-station ∀p, close ◯Q by aSound there, and
              -- re-enter the lax phase through circROf.
              refine .circR (.stable (.lfoc
                (List.mem_cons_of_mem _
                  (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                (.circL (invBranches R (fun b hb => ?_)))))
              -- dE: the opened-station ∃p, over the branch products
              have dE : Inv (b ++ (Neg.imp
                    (.down (interp p [.up R] rest none))
                    (interp p [.up R] rest (some (.circ (.down (.and M₁ M₂))))) :: Γ')) []
                  .tru (interp p [.up R] rest none) :=
                simHyp (H := .up R)
                  (fl := fun hs lf => match lf with
                    | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                        (List.mem_append.mp hZ).elim
                          (fun h => hs Z (List.mem_append_left _ h)) id)))
                  (fun Z hZ => List.mem_append_right b
                    (List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ)))))
                  (eSound p [.up R] rest)
              -- the opened-station ∀p beside the opened station closes ◯Q
              have D := (aSound p [.up R] rest (.circ (.down (.and M₁ M₂))))
              -- strip A (via the row fired with dE), then ↑R (via extract)
              refine .stable (unStable (simHyp (H := .up R)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (Sub.refl _)
                (simHyp (H := interp p [.up R] rest (some (.circ (.down (.and M₁ M₂)))))
                  (fl := fun hs lf =>
                    .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_self ..))))
                      (.impL (.rfoc (.rel (dE.wk (fun Z hZ =>
                        hs Z (List.mem_cons_of_mem _ hZ))))) lf))
                  (fun Z hZ => by
                    rcases List.mem_cons.mp hZ with rfl | hZ
                    · exact List.mem_cons_self ..
                    · exact List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))))
                  (circROf D))))


  | [], done, .circ (.down (.imp Q₀ N₀)) => by
      rw [interp]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASound hf (aSound p [N'] rest (.circ (.down (.imp Q₀ N₀))))
      | none =>
          simp only [hf]
          refine nOrAllElim _ (List.mem_cons_self ..) ?_
          intro x hx Γ' hsub
          if hx1 : x ∈ [interp p [] done (some (.up (.down (.imp Q₀ N₀))))] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .circR (.stable (.laxOf (unStable
              ((aSound p [] done (.up (.down (.imp Q₀ N₀)))).wk (by
                intro Z hZ
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _
                    (hsub _ (List.mem_cons_of_mem _ hZ)))))))
          else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                      (aSound p [N] rest (.circ (.down (.imp Q₀ N₀))))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [.imp (.down N') N] rest (.imp Q' N'))
                        (aSound p [N] rest (.circ (.down (.imp Q₀ N₀))))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [] rest (.circ Q'))
                        (aSound p [N] rest (.circ (.down (.imp Q₀ N₀))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ R =>
              -- THE E-GUARDED BOX-OPENING ROW, x = ↓E(↑R::rest) ⊃ A(↑R::rest ⇒ ◯Q):
              -- circR into the lax phase; open the station box; per branch of R,
              -- derive E at the opened station (extract-mediated eSound), feed the
              -- row to get the opened-station ∀p, close ◯Q by aSound there, and
              -- re-enter the lax phase through circROf.
              refine .circR (.stable (.lfoc
                (List.mem_cons_of_mem _
                  (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                (.circL (invBranches R (fun b hb => ?_)))))
              -- dE: the opened-station ∃p, over the branch products
              have dE : Inv (b ++ (Neg.imp
                    (.down (interp p [.up R] rest none))
                    (interp p [.up R] rest (some (.circ (.down (.imp Q₀ N₀))))) :: Γ')) []
                  .tru (interp p [.up R] rest none) :=
                simHyp (H := .up R)
                  (fl := fun hs lf => match lf with
                    | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                        (List.mem_append.mp hZ).elim
                          (fun h => hs Z (List.mem_append_left _ h)) id)))
                  (fun Z hZ => List.mem_append_right b
                    (List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ)))))
                  (eSound p [.up R] rest)
              -- the opened-station ∀p beside the opened station closes ◯Q
              have D := (aSound p [.up R] rest (.circ (.down (.imp Q₀ N₀))))
              -- strip A (via the row fired with dE), then ↑R (via extract)
              refine .stable (unStable (simHyp (H := .up R)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (Sub.refl _)
                (simHyp (H := interp p [.up R] rest (some (.circ (.down (.imp Q₀ N₀)))))
                  (fl := fun hs lf =>
                    .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_self ..))))
                      (.impL (.rfoc (.rel (dE.wk (fun Z hZ =>
                        hs Z (List.mem_cons_of_mem _ hZ))))) lf))
                  (fun Z hZ => by
                    rcases List.mem_cons.mp hZ with rfl | hZ
                    · exact List.mem_cons_self ..
                    · exact List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))))
                  (circROf D))))

  termination_by todo done G => 2 * sum3 todo + sum3 done + 3 ^ wNeg G
  decreasing_by ljf_dec_sound

end

/-! # Parts 5–6: minimality of both modes -/




end LJFO

namespace LJFO

/-! # Part 5: the inverse transformations and the saturated-case statements

Each processing clause of `interp` has an *inverse* transformation —
replacing uses of the consumed hypothesis by uses of its residual — proved
as a `simulate` instance.  The saturated case is *named* by the statements
`SatE2`/`SatA2` (and the Dyckhoff dispatch by `DykAnt`); Part 6's inner
induction discharges them unconditionally (`satE2`/`satA2`/`dykAnt` at the
end of the file).  The parametrised minimality functions `eMin`/`aMin`
that historically lived here are superseded by `eMinF`/`aMinF` and
preserved in `Archive/ljf-simp-round1-superseded.lean`.

## The inverse transformations -/

/-! Forced-shape analysers, top level so the index specialises. -/

/-- A left focus on a conjunction projects. -/
def lfocAnd {Δ : List Neg} {j : JD} {M N : Neg} {P : Pos} :
    LFoc Δ (.and M N) j P → LFoc Δ M j P ⊕ LFoc Δ N j P
  | .and1 lf => .inl lf
  | .and2 lf => .inr lf

/-- A left focus on an implication is `impL`. -/
def lfocImp {Δ : List Neg} {j : JD} {Q : Pos} {N : Neg} {P : Pos} :
    LFoc Δ (.imp Q N) j P → Stab Δ .tru Q × LFoc Δ N j P
  | .impL s lf => (s, lf)

/-- A left focus on a shift is `rel`. -/
def lfocUp {Δ : List Neg} {j : JD} {Q : Pos} {P : Pos} :
    LFoc Δ (.up Q) j P → Inv Δ [Q] j (.up P)
  | .rel d => d

/-- There is no right focus on `⊥`. -/
def rfocFls {Δ : List Neg} {j : JD} {A : Sort _} : RFocus Δ j .fls → A := nofun

/-- A right focus on a disjunction picks a side. -/
def rfocOr {Δ : List Neg} {j : JD} {A B : Pos} :
    RFocus Δ j (.or A B) → RFocus Δ j A ⊕ RFocus Δ j B
  | .or1 r => .inl r
  | .or2 r => .inr r

/-- Uses of `M ∧ N` become uses of `M` and `N`. -/
def invAndHyp {M N : Neg} {Γ : List Neg} {j : JD} {C : Neg}
    (d : Inv (.and M N :: Γ) [] j C) : Inv (M :: N :: Γ) [] j C :=
  simHyp (H := .and M N)
    (fl := fun hs lf => match lfocAnd lf with
      | .inl lf' => .lfoc (hs _ (List.mem_cons_self ..)) lf'
      | .inr lf' =>
          .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) lf')
    (fun Z hZ => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
    d

/-- Uses of `⊥ ⊃ N` are vacuous: the antecedent proof routes to nothing —
`RFocus _ ⊥` has no constructor. -/
def invImpFls {N : Neg} {Γ : List Neg} {j : JD} {C : Neg}
    (d : Inv (.imp .fls N :: Γ) [] j C) : Inv Γ [] j C :=
  simHyp (H := .imp .fls N)
    (fl := fun _ lf =>
      routeStabT (k := fun _ r => rfocFls r) (Sub.refl _) (lfocImp lf).1)
    (Sub.refl _)
    d

/-- Uses of `(Q₁∨Q₂) ⊃ N` route through the split residuals. -/
def invImpOr {Q₁ Q₂ : Pos} {N : Neg} {Γ : List Neg} {j : JD} {C : Neg}
    (d : Inv (.imp (.or Q₁ Q₂) N :: Γ) [] j C) :
    Inv (.imp Q₁ N :: .imp Q₂ N :: Γ) [] j C :=
  simHyp (H := .imp (.or Q₁ Q₂) N)
    (fl := fun hs lf =>
      routeStabT
        (k := fun hs' r => match rfocOr r with
          | .inl r₁ =>
              .lfoc (hs' _ (hs _ (List.mem_cons_self ..)))
                (.impL (.rfoc r₁) ((lfocImp lf).2.wk hs'))
          | .inr r₂ =>
              .lfoc (hs' _ (hs _ (List.mem_cons_of_mem _
                  (List.mem_cons_self ..))))
                (.impL (.rfoc r₂) ((lfocImp lf).2.wk hs')))
        (Sub.refl _) (lfocImp lf).1)
    (fun Z hZ => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
    d

/-- Uses of `↓↑P′ ⊃ N` strip the double shift. -/
def invStrip {P' : Pos} {N : Neg} {Γ : List Neg} {j : JD} {C : Neg}
    (d : Inv (.imp (.down (.up P')) N :: Γ) [] j C) :
    Inv (.imp P' N :: Γ) [] j C :=
  simHyp (H := .imp (.down (.up P')) N)
    (fl := fun hs lf =>
      routeStabT
        (k := fun hs' r =>
          .lfoc (hs' _ (hs _ (List.mem_cons_self ..)))
            (.impL (unStable (relOf r)) ((lfocImp lf).2.wk hs')))
        (Sub.refl _) (lfocImp lf).1)
    (fun Z hZ => List.mem_cons_of_mem _ hZ)
    d

/-- Uses of `↓(M₁∧M₂) ⊃ N` fire the curried residual twice. -/
def invCurry {M₁ M₂ N : Neg} {Γ : List Neg} {j : JD} {C : Neg}
    (d : Inv (.imp (.down (.and M₁ M₂)) N :: Γ) [] j C) :
    Inv (.imp (.down M₁) (.imp (.down M₂) N) :: Γ) [] j C :=
  simHyp (H := .imp (.down (.and M₁ M₂)) N)
    (fl := fun hs lf =>
      routeStabT
        (k := fun hs' r =>
          .lfoc (hs' _ (hs _ (List.mem_cons_self ..)))
            (.impL (.rfoc (.rel (andROf1 (relOf r))))
              (.impL (.rfoc (.rel (andROf2 (relOf r))))
                ((lfocImp lf).2.wk hs'))))
        (Sub.refl _) (lfocImp lf).1)
    (fun Z hZ => List.mem_cons_of_mem _ hZ)
    d

/-- Uses of a shifted hypothesis restrict to any one branch of its
inversion — the derivation already contains that branch (`extract`). -/
def invUp {R : Pos} {Γ : List Neg} {j : JD} {C : Neg}
    (d : Inv (.up R :: Γ) [] j C) (b : List Neg) (hb : b ∈ invertPos R) :
    Inv (b ++ Γ) [] j C :=
  simHyp (H := .up R)
    (fl := fun {Δ'} {_} {_} hs lf =>
      unStable ((extract [] (lfocUp lf) b hb).wk (fun Z hZ => by
        rcases List.mem_append.mp hZ with hZ | hZ
        · exact hs _ (List.mem_append_left _ hZ)
        · exact hZ)))
    (fun Z hZ => List.mem_append_right _ hZ)
    d

end LJFO

namespace LJFO

/-! ## Splitting a context member -/

theorem splits_mem_split {Γ : List Neg} :
    ∀ {X rest}, (X, rest) ∈ splits Γ → ∀ Z ∈ Γ, Z = X ∨ Z ∈ rest := by
  induction Γ with
  | nil => intro X rest h; simp [splits] at h
  | cons Y Γ ih =>
      intro X rest h Z hZ
      simp only [splits, List.mem_cons, List.mem_map] at h
      rcases h with h | ⟨⟨W, rest'⟩, hW, hEq⟩
      · cases h
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact .inl rfl
        · exact .inr hZ
      · cases hEq
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact .inr (List.mem_cons_self ..)
        · rcases ih hW Z hZ with e | hZ
          · exact .inl e
          · exact .inr (List.mem_cons_of_mem _ hZ)

/-- Uses of a fired implication become uses of its conclusion. -/
def invFireHyp {a : String} {N : Neg} {done rest Δext : List Neg} {j : JD}
    {C : Neg}
    (h : (Neg.imp (.atom a) N, rest) ∈ splits done)
    (d : Inv (done ++ Δext) [] j C) : Inv (N :: (rest ++ Δext)) [] j C :=
  simInv (H := .imp (.atom a) N)
    (fl := fun hs lf => .lfoc (hs _ (List.mem_cons_self ..)) (lfocImp lf).2)
    (fun Z hZ => by
      rcases List.mem_append.mp hZ with hZ | hZ
      · rcases splits_mem_split h Z hZ with e | hZ
        · exact .inl e
        · exact .inr (List.mem_cons_of_mem _ (List.mem_append_left _ hZ))
      · exact .inr (List.mem_cons_of_mem _ (List.mem_append_right _ hZ)))
    (Sub.refl _) d

/-! ## Context shuffles for the minimality reductions -/

theorem subParkOut {X : Neg} {t d Δ : List Neg} :
    Sub (((X :: t) ++ d) ++ Δ) ((t ++ X :: d) ++ Δ) := by
  intro Z hZ
  rcases List.mem_append.mp hZ with hZ | hZ
  · exact List.mem_append_left _ (subParkInv _ hZ)
  · exact List.mem_append_right _ hZ

theorem subHeadOut {X : Neg} {t d Δ : List Neg} :
    Sub (((X :: t) ++ d) ++ Δ) (X :: ((t ++ d) ++ Δ)) := by
  intro Z hZ
  rcases List.mem_append.mp hZ with hZ | hZ
  · rcases List.mem_cons.mp hZ with rfl | hZ
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ hZ)
  · exact List.mem_cons_of_mem _ (List.mem_append_right _ hZ)

theorem subChainIn {b t d Δ : List Neg} :
    Sub (b ++ ((t ++ d) ++ Δ)) (((b ++ t) ++ d) ++ Δ) := by
  intro Z hZ
  rcases List.mem_append.mp hZ with hZ | hZ
  · exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ hZ))
  · rcases List.mem_append.mp hZ with hZ | hZ
    · rcases List.mem_append.mp hZ with hZ | hZ
      · exact List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ hZ))
      · exact List.mem_append_left _ (List.mem_append_right _ hZ)
    · exact List.mem_append_right _ hZ

/-! ## The two open obligations, and minimality modulo them -/

/-- The context is `p`-free. -/
def PFreeCtx (p : String) (Δ : List Neg) : Prop := ∀ N ∈ Δ, PFreeN p N

/-- Saturation: no parked implication can fire. -/
def Saturated (done : List Neg) : Prop :=
  findFire done (splits done) = none

/-- Every member appears in `splits`. -/
theorem splits_of_mem {Γ : List Neg} {X : Neg} (h : X ∈ Γ) :
    ∃ rest, (X, rest) ∈ splits Γ := by
  induction Γ with
  | nil => simp at h
  | cons Y Γ ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨Γ, List.mem_cons_self ..⟩
      · obtain ⟨rest, hr⟩ := ih h
        exact ⟨Y :: rest, List.mem_cons_of_mem _
          (List.mem_map_of_mem (f := fun zr => (zr.1, Y :: zr.2)) hr)⟩

/-- The three shapes parking can produce.  `SatE2`/`SatA2` are FALSE without
this restriction (e.g. `done = [↑q ∧ ↑q]` is saturated but its `∃p`
interpolant is the default `⊤`, which does not prove `q`); the recursion
only ever reaches saturated contexts of these shapes, so the restriction
costs nothing. -/
inductive ParkedN : Neg → Prop
  | atom (a : String) : ParkedN (.up (.atom a))
  | qimp (a : String) (N : Neg) : ParkedN (.imp (.atom a) N)
  | dyk (Q' : Pos) (N' N : Neg) : ParkedN (.imp (.down (.imp Q' N')) N)
  | box (Q : Pos) : ParkedN (.circ Q)
  | cimp (Q' : Pos) (N : Neg) : ParkedN (.imp (.down (.circ Q')) N)

/-- Every member is a parked shape. -/
def ParkedCtx (done : List Neg) : Prop := ∀ X ∈ done, ParkedN X

theorem ParkedCtx.nil : ParkedCtx [] := fun _ h => absurd h (List.not_mem_nil)

theorem ParkedCtx.cons {X : Neg} {done : List Neg}
    (hX : ParkedN X) (h : ParkedCtx done) : ParkedCtx (X :: done) := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | hZ
  · exact hX
  · exact h Z hZ

theorem ParkedCtx.sub {done rest : List Neg}
    (hs : Sub rest done) (h : ParkedCtx done) : ParkedCtx rest :=
  fun Z hZ => h Z (hs Z hZ)

/-- What `findFire = none` says about each scanned pair. -/
theorem findFire_none_spec {full : List Neg} :
    ∀ {l : List (Neg × List Neg)}, findFire full l = none →
      ∀ {a N rest}, (Neg.imp (.atom a) N, rest) ∈ l →
        atomMem a full = false := by
  intro l
  induction l with
  | nil => intro _ a N rest h; simp at h
  | cons XR more ih =>
      intro hn a N rest h
      obtain ⟨X, R⟩ := XR
      rcases List.mem_cons.mp h with hEq | h
      · cases hEq
        simp only [findFire] at hn
        by_cases hM : atomMem a full
        · simp [hM] at hn
        · simpa using hM
      · refine ih ?_ h
        match X, hn with
        | .imp (.atom b) N', hn => ?_
        | .up P, hn => exact hn
        | .imp .fls N', hn => exact hn
        | .imp (.or Q₁ Q₂) N', hn => exact hn
        | .imp (.down M) N', hn => exact hn
        | .and M₁ M₂, hn => exact hn
        | .circ P, hn => exact hn
        simp only [findFire] at hn
        by_cases hM : atomMem b full
        · simp [hM] at hn
        · simpa [hM] using hn

/-- At a saturated context, a parked implication's atom is absent.  In
particular a `p ⊃ N` member excludes `↑p`. -/
theorem saturated_atom_absent {done : List Neg} (hsat : Saturated done)
    {a : String} {N : Neg} (h : Neg.imp (.atom a) N ∈ done) :
    atomMem a done = false := by
  obtain ⟨rest, hr⟩ := splits_of_mem h
  exact findFire_none_spec hsat hr

/-- `atomMem` is complete for membership. -/
theorem atomMem_of_mem {a : String} {Γ : List Neg}
    (h : Neg.up (.atom a) ∈ Γ) : atomMem a Γ = true := by
  simp only [atomMem, List.any_eq_true]
  exact ⟨_, h, by simp⟩

/-- The goal of a sequent, adjusted for its judgment: a lax sequent with a
shifted goal is interpolated at the `◯`-goal (the lax judgment is
definable), and `tru` sequents keep their goal. -/
def jGoal : JD → Neg → Neg
  | j, .up P => match j with | .tru => .up P | .lax => .circ P
  | _, G => G

theorem jGoal_tru : ∀ {G : Neg}, jGoal .tru G = G
  | .up _ => rfl
  | .imp _ _ => rfl
  | .and _ _ => rfl
  | .circ _ => rfl

/-- Minimality of `∃p` at a saturated context — the inner induction over
derivations at saturated sequents, the heart of Pitts' argument.
Discharged unconditionally by `satE2` at the end of the file. -/
def SatE2 (p : String) : Type :=
  ∀ (done Δ : List Neg) (ψ : Neg), Saturated done → ParkedCtx done →
    PFreeCtx p Δ → PFreeN p ψ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j ψ →
      Inv (interp p [] done none :: Δ) [] j ψ

/-- Minimality of `∀p` at a saturated context.  Discharged unconditionally
by `satA2` at the end of the file. -/
def SatA2 (p : String) : Type :=
  ∀ (done Δ : List Neg) (G : Neg), Saturated done → ParkedCtx done →
    PFreeCtx p Δ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j G →
    Inv (interp p [] done none :: Δ) [] .tru
      (interp p [] done (some (jGoal j G)))


end LJFO

namespace LJFO

/-! # Part 6: the saturated case — the inner induction

The plan, fixed by the analysis of 2026-08-09:

* One traversal over the four judgments, structural in the derivation, at a
  fixed saturated parked station `done`, with the context split as
  `done`-part plus a `p`-free kept part `K`.
* Uses of `done`-members are dispatched through the matching conjunct of the
  interpolant; the continuation after a fire is packaged as a derivation
  over the fired context (`d_cont`), cleaned of residual uses of the fired
  member, and handed to the minimality function at strictly smaller measure.
* Proofs of the atom `p` at the main line are eliminated by **composition**:
  `init` on `↑p` is impossible (saturation excludes `↑p` beside `p ⊃ M`;
  the kept side is `p`-free), so every such proof bottoms out in a fire
  whose body releases the `p`-material — and at that node all pieces exist
  to compose the outer `p ⊃ M` use with the inner fire directly.
* The single dispatch that does not close by these means is the Dyckhoff
  antecedent — deriving `∀p` of the antecedent at the residual station from
  a main-line stable proof of it.  It is isolated as `DykAnt`, one
  statement serving both modes.

## Preliminaries -/

/-- `p`-freeness for a pending list. -/
def PFreeΩ (p : String) (Ω : List Pos) : Prop := ∀ Q ∈ Ω, PFreeP p Q

theorem PFreeΩ.nil {p : String} : PFreeΩ p [] := fun _ h => absurd h (List.not_mem_nil)

theorem PFreeΩ.cons {p : String} {Q : Pos} {Ω : List Pos}
    (hQ : PFreeP p Q) (h : PFreeΩ p Ω) : PFreeΩ p (Q :: Ω) := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | hZ
  · exact hQ
  · exact h Z hZ

theorem PFreeΩ.head {p : String} {Q : Pos} {Ω : List Pos}
    (h : PFreeΩ p (Q :: Ω)) : PFreeP p Q := h Q (List.mem_cons_self ..)

theorem PFreeΩ.tail {p : String} {Q : Pos} {Ω : List Pos}
    (h : PFreeΩ p (Q :: Ω)) : PFreeΩ p Ω :=
  fun Z hZ => h Z (List.mem_cons_of_mem _ hZ)

/-- Locate a member's split, constructively. -/
def splitAt : (Γ : List Neg) → (X : Neg) → X ∈ Γ → {rest // (X, rest) ∈ splits Γ}
  | Y :: Γ, X, h =>
      if e : X = Y then
        ⟨Γ, by cases e; exact List.mem_cons_self ..⟩
      else
        have h' : X ∈ Γ := by
          rcases List.mem_cons.mp h with rfl | h'
          · exact absurd rfl e
          · exact h'
        let ⟨rest, hr⟩ := splitAt Γ X h'
        ⟨Y :: rest, List.mem_cons_of_mem _
          (List.mem_map_of_mem (f := fun zr => (zr.1, Y :: zr.2)) hr)⟩

/-- The `∃p` conjunct of a `q`-implication member, and its membership in the
interpolant's conjunction list. -/
theorem qimpConjMem {p : String} {done : List Neg} {a : String} {N : Neg}
    {rest : List Neg} (hXr : (Neg.imp (.atom a) N, rest) ∈ splits done) :
    pGuard p a nTop (.imp (.atom a) (interp p [N] rest none)) ∈
      ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
        match X with
        | .up (.atom a) => pGuard p a nTop (.up (.atom a))
        | .imp (.atom a) N =>
            pGuard p a nTop (.imp (.atom a) (interp p [N] rest none))
        | .imp (.down (.imp Q' N')) N =>
            nAnd
              (.imp (.down (interp p [.imp (.down N') N] rest
                             (some (.imp Q' N'))))
                   (interp p [N] rest none))
              (interp p [.imp (.down N') N] rest none)
        | .circ Q =>
            .circ (.down (interp p [.up Q] rest none))
        | .imp (.down (.circ Q')) N =>
            nAnd
              (.imp (.down (interp p [] rest (some (.circ Q'))))
                   (interp p [N] rest none))
              (interp p [] rest none)
        | _ => nTop)) :=
  List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hXr⟩)

/-- Likewise for a surviving atom. -/
theorem atomConjMem {p : String} {done : List Neg} {a : String}
    {rest : List Neg} (hXr : (Neg.up (.atom a), rest) ∈ splits done) :
    pGuard p a nTop (.up (.atom a)) ∈
      ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
        match X with
        | .up (.atom a) => pGuard p a nTop (.up (.atom a))
        | .imp (.atom a) N =>
            pGuard p a nTop (.imp (.atom a) (interp p [N] rest none))
        | .imp (.down (.imp Q' N')) N =>
            nAnd
              (.imp (.down (interp p [.imp (.down N') N] rest
                             (some (.imp Q' N'))))
                   (interp p [N] rest none))
              (interp p [.imp (.down N') N] rest none)
        | .circ Q =>
            .circ (.down (interp p [.up Q] rest none))
        | .imp (.down (.circ Q')) N =>
            nAnd
              (.imp (.down (interp p [] rest (some (.circ Q'))))
                   (interp p [N] rest none))
              (interp p [] rest none)
        | _ => nTop)) :=
  List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hXr⟩)

/-- And for a Dyckhoff member. -/
theorem dykConjMem {p : String} {done : List Neg} {Q' : Pos} {N' N : Neg}
    {rest : List Neg}
    (hXr : (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done) :
    nAnd
      (.imp (.down (interp p [.imp (.down N') N] rest (some (.imp Q' N'))))
           (interp p [N] rest none))
      (interp p [.imp (.down N') N] rest none) ∈
      ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
        match X with
        | .up (.atom a) => pGuard p a nTop (.up (.atom a))
        | .imp (.atom a) N =>
            pGuard p a nTop (.imp (.atom a) (interp p [N] rest none))
        | .imp (.down (.imp Q' N')) N =>
            nAnd
              (.imp (.down (interp p [.imp (.down N') N] rest
                             (some (.imp Q' N'))))
                   (interp p [N] rest none))
              (interp p [.imp (.down N') N] rest none)
        | .circ Q =>
            .circ (.down (interp p [.up Q] rest none))
        | .imp (.down (.circ Q')) N =>
            nAnd
              (.imp (.down (interp p [] rest (some (.circ Q'))))
                   (interp p [N] rest none))
              (interp p [] rest none)
        | _ => nTop)) :=
  List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hXr⟩)

/-- And for a parked box. -/
theorem boxConjMem {p : String} {done : List Neg} {Q : Pos}
    {rest : List Neg}
    (hXr : (Neg.circ Q, rest) ∈ splits done) :
    Neg.circ (.down (interp p [.up Q] rest none)) ∈
      ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
        match X with
        | .up (.atom a) => pGuard p a nTop (.up (.atom a))
        | .imp (.atom a) N =>
            pGuard p a nTop (.imp (.atom a) (interp p [N] rest none))
        | .imp (.down (.imp Q' N')) N =>
            nAnd
              (.imp (.down (interp p [.imp (.down N') N] rest
                             (some (.imp Q' N'))))
                   (interp p [N] rest none))
              (interp p [.imp (.down N') N] rest none)
        | .circ Q =>
            .circ (.down (interp p [.up Q] rest none))
        | .imp (.down (.circ Q')) N =>
            nAnd
              (.imp (.down (interp p [] rest (some (.circ Q'))))
                   (interp p [N] rest none))
              (interp p [] rest none)
        | _ => nTop)) :=
  List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hXr⟩)

/-- And for a `◯`-implication member. -/
theorem cimpConjMem {p : String} {done : List Neg} {Q' : Pos} {N : Neg}
    {rest : List Neg}
    (hXr : (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done) :
    nAnd
      (.imp (.down (interp p [] rest (some (.circ Q'))))
           (interp p [N] rest none))
      (interp p [] rest none) ∈
      ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
        match X with
        | .up (.atom a) => pGuard p a nTop (.up (.atom a))
        | .imp (.atom a) N =>
            pGuard p a nTop (.imp (.atom a) (interp p [N] rest none))
        | .imp (.down (.imp Q' N')) N =>
            nAnd
              (.imp (.down (interp p [.imp (.down N') N] rest
                             (some (.imp Q' N'))))
                   (interp p [N] rest none))
              (interp p [.imp (.down N') N] rest none)
        | .circ Q =>
            .circ (.down (interp p [.up Q] rest none))
        | .imp (.down (.circ Q')) N =>
            nAnd
              (.imp (.down (interp p [] rest (some (.circ Q'))))
                   (interp p [N] rest none))
              (interp p [] rest none)
        | _ => nTop)) :=
  List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hXr⟩)

/-- **The isolated obligation** — the Dyckhoff antecedent dispatch: from a
main-line stable proof of the antecedent `↓(Q′ ⊃ N′)`, derive the `∀p`
interpolant of the antecedent at the residual station, on the interpolant
side.  One statement serves both modes.  This is Pitts' hardest case
(the `(A⊃B)⊃C` commute), and everything else below is proved outright. -/
def DykAnt (p : String) : Type :=
  ∀ (done rest K Γ' : List Neg) (Q' : Pos) (N' N : Neg),
    Saturated done → ParkedCtx done →
    (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
    (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
    Stab Γ' .tru (.down (.imp Q' N')) →
    Inv (interp p [] done none :: K) [] .tru
        (interp p [.imp (.down N') N] rest (some (.imp Q' N')))

end LJFO

namespace LJFO

/-! ## Part 6b: the dispatch helpers

Each is a plain `simulate`/assembly instance — no recursion into the coming
mutual block, so they compile standalone. -/

variable {p : String}

/-- **Fired-context cleanup.**  After a fire of `Q₀ ⊃ N`, residual uses of
the fired implication are redundant: the body `N` is now a hypothesis, so
`impL`-uses drop their antecedent and use `N` directly. -/
def fireClean {Q₀ : Pos} {N : Neg} {Γ' rest K : List Neg} {j : JD} {C : Neg}
    (hsplit : ∀ Z ∈ Γ', Z = Neg.imp Q₀ N ∨ Z ∈ rest ∨ Z ∈ K)
    (d : Inv (N :: Γ') [] j C) : Inv ((N :: rest) ++ K) [] j C :=
  simInv (H := .imp Q₀ N)
    (fl := fun hs lf =>
      .lfoc (hs _ (List.mem_append_left _ (List.mem_cons_self ..)))
        (lfocImp lf).2)
    (fun Z hZ => by
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact .inr (List.mem_append_left _ (List.mem_cons_self ..))
      · rcases hsplit Z hZ with e | hZ | hZ
        · exact .inl e
        · exact .inr (List.mem_append_left _ (List.mem_cons_of_mem _ hZ))
        · exact .inr (List.mem_append_right _ hZ))
    (Sub.refl _) d

/-- **Opened-box cleanup.**  After a box `◯Q` is opened, residual `circL`
uses of the box re-derive their content from the released hypothesis `↑Q`
directly. -/
def boxClean {Q : Pos} {Γ' rest K : List Neg} {j : JD} {C : Neg}
    (hsplit : ∀ Z ∈ Γ', Z = Neg.circ Q ∨ Z ∈ rest ∨ Z ∈ K)
    (d : Inv (Neg.up Q :: Γ') [] j C) : Inv ((Neg.up Q :: rest) ++ K) [] j C :=
  simInv (H := .circ Q)
    (fl := fun hs lf =>
      match lf with
      | .circL dQ =>
          .lfoc (hs _ (List.mem_append_left _ (List.mem_cons_self ..)))
            (.rel dQ))
    (fun Z hZ => by
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact .inr (List.mem_append_left _ (List.mem_cons_self ..))
      · rcases hsplit Z hZ with e | hZ | hZ
        · exact .inl e
        · exact .inr (List.mem_append_left _ (List.mem_cons_of_mem _ hZ))
        · exact .inr (List.mem_append_right _ hZ))
    (Sub.refl _) d


/-- The saturated `∃p` aggregate, as an equation. -/
theorem interpE_eq {p : String} {done : List Neg} (hsat : Saturated done) :
    interp p [] done none = nAndAll ((splits done).attach.map
      (fun ⟨(X, rest), hXr⟩ =>
        match X with
        | .up (.atom a) => pGuard p a nTop (.up (.atom a))
        | .imp (.atom a) N =>
            pGuard p a nTop (.imp (.atom a) (interp p [N] rest none))
        | .imp (.down (.imp Q' N')) N =>
            nAnd
              (.imp (.down (interp p [.imp (.down N') N] rest
                             (some (.imp Q' N'))))
                   (interp p [N] rest none))
              (interp p [.imp (.down N') N] rest none)
        | .circ Q =>
            .circ (.down (interp p [.up Q] rest none))
        | .imp (.down (.circ Q')) N =>
            nAnd
              (.imp (.down (interp p [] rest (some (.circ Q'))))
                   (interp p [N] rest none))
              (interp p [] rest none)
        | _ => nTop)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

/-- Project a surviving atom from the interpolant. -/
def atomAssemble {done K : List Neg} {a : String} {L : List Neg}
    (hE : interp p [] done none = nAndAll L)
    (hmem : pGuard p a nTop (.up (.atom a)) ∈ L) (hap : ¬ a = p) :
    Stab (interp p [] done none :: K) .tru (.atom a) :=
  .lfoc (List.mem_cons_self ..)
    (hE.symm ▸ lfocAndAll hmem (by
      simp only [pGuard]; rw [if_neg hap]
      exact LFoc.rel (idPos (.atom a) _ _)))


/-- The context split after locating a member: `done`-side members are the
member itself or in its complement. -/
theorem splitHyp {done K Γ' rest : List Neg} {X : Neg}
    (hm : ∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K)
    (hXr : (X, rest) ∈ splits done) :
    ∀ Z ∈ Γ', Z = X ∨ Z ∈ rest ∨ Z ∈ K := by
  intro Z hZ
  rcases hm Z hZ with hd | hK
  · rcases splits_mem_split hXr Z hd with e | hr
    · exact .inl e
    · exact .inr (.inl hr)
  · exact .inr (.inr hK)

end LJFO

namespace LJFO

/-! ## Part 6c: the inner induction, `∃p` side

The mutual block: `eMinF` (minimality, as before, but with the saturated
case discharged inline) and the traversal components.  Structural in the
derivation at a fixed station; every station-crossing goes through `eMinF`
at strictly smaller measure, so the lexicographic pair `(μ, size)` carries
the whole block. -/


theorem hmConsDone {done K Γ' : List Neg} {M : Neg} (hMd : M ∈ done)
    (hm : ∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) :
    ∀ Z ∈ M :: Γ', Z ∈ done ∨ Z ∈ K := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | hZ
  · exact .inl hMd
  · exact hm Z hZ

theorem hmConsK {done K Γ' : List Neg} {M : Neg}
    (hm : ∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) :
    ∀ Z ∈ M :: Γ', Z ∈ done ∨ Z ∈ M :: K := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | hZ
  · exact .inr (List.mem_cons_self ..)
  · exact (hm Z hZ).imp id (List.mem_cons_of_mem _)

theorem PFreeCtx.cons {p : String} {K : List Neg} {M : Neg}
    (hM : PFreeN p M) (hK : PFreeCtx p K) : PFreeCtx p (M :: K) := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | hZ
  · exact hM
  · exact hK Z hZ

/-- The weight inequalities for the traversal's station crossings. -/
theorem dec_fireT {done rest : List Neg} {a : String} {N : Neg}
    (h : (Neg.imp (.atom a) N, rest) ∈ splits done) :
    2 * 3 ^ wNeg N + sum3 rest < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have := p3_2 (a := wNeg N) (c := 1 + wNeg N + 1) (by omega)
  omega

theorem dec_dykT {done rest : List Neg} {Q' : Pos} {N' N : Neg}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * 3 ^ wNeg N + sum3 rest < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have := p3_2 (a := wNeg N) (c := wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1)
    (by have := wPos_pos Q'; have := wNeg_pos N'; omega)
  omega



/-! ## Part 7: shift release and the Dyckhoff commute

`relStab`: CPS release of a stable proof of `↓M` — the continuation receives
an inversion of `M` at every point one is produced.  `negOfDownStab` closes
the loop into a plain derivation of `M`, by recursion on `M` (the mirror of
`upMerge`).  `dykCommute` then converts a mixed-context stable proof of the
Dyckhoff antecedent into a derivation over the residual station — uses of
the full hypothesis are manufactured from the residual, because under the
antecedent's own inversion the goal-branch is in context (Dyckhoff's
observation, in focused form). -/

mutual

/-- CPS release of a stable `↓M`-proof. -/
def relStab {Δ₀ : List Neg} {j : JD} {M : Neg} {P₀ : Pos}
    (k : ∀ {Δ' : List Neg}, Sub Δ₀ Δ' → Inv Δ' [] .tru M → Stab Δ' j P₀) :
    ∀ {Δ : List Neg}, Sub Δ₀ Δ → Stab Δ .tru (.down M) → Stab Δ j P₀
  | _, hs, .rfoc r => k hs (relOf r)
  | _, hs, .lfoc h lf => .lfoc h (relLF k hs lf)
termination_by Δ hs s => szS s
decreasing_by all_goals (simp_wf; simp only [szS, szR, szL, szI]; omega)

/-- Release below a left focus. -/
def relLF {Δ₀ : List Neg} {j : JD} {M : Neg} {P₀ : Pos}
    (k : ∀ {Δ' : List Neg}, Sub Δ₀ Δ' → Inv Δ' [] .tru M → Stab Δ' j P₀) :
    ∀ {Δ : List Neg} {H : Neg}, Sub Δ₀ Δ →
      LFoc Δ H .tru (.down M) → LFoc Δ H j P₀
  | _, _, hs, .rel d => .rel (relInv k hs d)
  | _, _, hs, .impL s lf => .impL s (relLF k hs lf)
  | _, _, hs, .and1 lf => .and1 (relLF k hs lf)
  | _, _, hs, .and2 lf => .and2 (relLF k hs lf)
termination_by Δ H hs lf => szL lf
decreasing_by all_goals (simp_wf; simp only [szS, szR, szL, szI]; omega)

/-- Release through inversion; the goal is a shift, so the traversal is
total. -/
def relInv {Δ₀ : List Neg} {j : JD} {M : Neg} {P₀ : Pos}
    (k : ∀ {Δ' : List Neg}, Sub Δ₀ Δ' → Inv Δ' [] .tru M → Stab Δ' j P₀) :
    ∀ {Δ : List Neg} {Ω : List Pos}, Sub Δ₀ Δ →
      Inv Δ Ω .tru (.up (.down M)) → Inv Δ Ω j (.up P₀)
  | _, _, hs, .stable s => .stable (relStab k hs s)
  | _, _, hs, .orL d₁ d₂ => .orL (relInv k hs d₁) (relInv k hs d₂)
  | _, _, _, .flsL => .flsL
  | _, _, hs, .downL d => .downL (relInv k (hs.trans (Sub.grow _)) d)
  | _, _, hs, .atomL d => .atomL (relInv k (hs.trans (Sub.grow _)) d)
termination_by Δ Ω hs d => szI d
decreasing_by all_goals (simp_wf; simp only [szS, szR, szL, szI]; omega)

end

/-- **A stable proof of `↓M` yields a derivation of `M`** — by recursion on
`M`, releasing at each stage. -/
def negOfDownStab : ∀ (M : Neg) {Δ : List Neg},
    Stab Δ .tru (.down M) → Inv Δ [] .tru M
  | .up P, _, s =>
      .stable (relStab (fun _ d => unStable d) (Sub.refl _) s)
  | .imp Q N, _, s =>
      .impR (invBranches Q (fun c hc =>
        negOfDownStab N (relStab
          (fun {Δ'} hs d =>
            .rfoc (.rel ((extract [] (impROf d) c hc).wk (fun Z hZ => by
              rcases List.mem_append.mp hZ with hZ | hZ
              · exact hs _ (List.mem_append_left _ hZ)
              · exact hZ))))
          (Sub.refl _)
          (s.wk (fun Z hZ => List.mem_append_right c hZ)))))
  | .and M₁ M₂, _, s =>
      .andR
        (negOfDownStab M₁ (relStab
          (fun _ d => .rfoc (.rel (andROf1 d))) (Sub.refl _) s))
        (negOfDownStab M₂ (relStab
          (fun _ d => .rfoc (.rel (andROf2 d))) (Sub.refl _) s))
  | .circ P, _, s =>
      .circR (.stable (relStab (fun _ d => unStable (circROf d))
        (Sub.refl _) s))

/-- **The Dyckhoff commute.**  A mixed-context stable proof of the antecedent
`↓(Q′ ⊃ N′)` becomes a derivation of `Q′ ⊃ N′` over the residual station:
uses of the full hypothesis `X = ↓(Q′⊃N′) ⊃ N` are replaced by fires of the
residual `↓N′ ⊃ N`, whose antecedent is recovered because the branch of `Q′`
currently in context closes the released implication (`extract`). -/
def dykCommute {p : String} {Q' : Pos} {N' N : Neg}
    {done rest K Γ' : List Neg}
    (hXr : (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done)
    (hm : ∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K)
    (s : Stab Γ' .tru (.down (.imp Q' N'))) :
    Inv ((Neg.imp (.down N') N :: rest) ++ K) [] .tru (.imp Q' N') :=
  .impR (invBranches Q' (fun b hb =>
    negOfDownStab N'
      (routeStabT
        (k := fun {Δ''} hs' r =>
          .rfoc (.rel ((extract [] (impROf (relOf r)) b hb).wk (fun Z hZ => by
            rcases List.mem_append.mp hZ with hZ | hZ
            · exact hs' _ (List.mem_append_left _ hZ)
            · exact hZ))))
        (Sub.refl _)
        (simStab (H := Neg.imp (.down (.imp Q' N')) N)
          (fl := fun {Δ'} {_} {_} hs lf =>
            .lfoc
              (hs _ (List.mem_append_right b (List.mem_append_left _
                (List.mem_cons_self ..))))
              (.impL
                (routeStabT
                  (k := fun {Δ''} hs' r =>
                    .rfoc (.rel ((extract [] (impROf (relOf r)) b hb).wk
                      (fun Z hZ => by
                        rcases List.mem_append.mp hZ with hZ | hZ
                        · exact hs' _ (hs _ (List.mem_append_left _ hZ))
                        · exact hZ))))
                  (Sub.refl _) (lfocImp lf).1)
                (lfocImp lf).2))
          (fun Z hZ => by
            rcases List.mem_append.mp hZ with hZ | hZ
            · exact .inr (List.mem_append_left _ hZ)
            · rcases hm Z hZ with hd | hk
              · rcases splits_mem_split hXr Z hd with e | hr
                · exact .inl e
                · exact .inr (List.mem_append_right b
                    (List.mem_append_left _ (List.mem_cons_of_mem _ hr)))
              · exact .inr (List.mem_append_right b
                  (List.mem_append_right _ hk)))
          (Sub.refl _)
          (s.wk (fun Z hZ => List.mem_append_right b hZ))))))



/-! ## Part 8: A-side prelude -/

/-- The positive under a list disjunction. -/
def orChain : List Neg → Pos
  | [] => .fls
  | x :: l => .or (.down x) (.down (nOrAll l))

theorem nOrAll_eq (L : List Neg) : nOrAll L = .up (orChain L) := by
  cases L <;> rfl

theorem p3_succ (m : Nat) : (3:Nat) ^ (m + 1) = 3 ^ m * 3 := Nat.pow_succ ..

/-- The station drop for the Dyckhoff pipeline, with generous slack. -/
theorem dec_dykC {done rest : List Neg} {Q' : Pos} {N' N : Neg}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * 3 ^ (wNeg N' + 1 + wNeg N + 1) + sum3 rest +
      3 ^ (wPos Q' + wNeg N' + 1) + 9 < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have h1 := p3_mono (a := wNeg N' + 1 + wNeg N + 1)
    (b := wPos Q' + wNeg N' + 1 + wNeg N) (by have := wPos_pos Q'; omega)
  have h2 := p3_mono (a := wPos Q' + wNeg N' + 1)
    (b := wPos Q' + wNeg N' + 1 + wNeg N) (by have := wNeg_pos N; omega)
  have h3 : (3:Nat) ^ (wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1) =
      3 ^ (wPos Q' + wNeg N' + 1 + wNeg N) * 3 * 3 := by
    rw [show wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1 =
        wPos Q' + wNeg N' + 1 + wNeg N + 1 + 1 from by omega,
      p3_succ, p3_succ]
  have h5 := p3_mono (a := 1) (b := wPos Q' + wNeg N' + 1 + wNeg N)
    (by have := wPos_pos Q'; omega)
  omega

/-- The fire drop, with slack. -/
theorem dec_fireS {done rest : List Neg} {a : String} {N : Neg}
    (h : (Neg.imp (.atom a) N, rest) ∈ splits done) :
    2 * 3 ^ wNeg N + sum3 rest + 9 < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  rw [show 1 + wNeg N + 1 = wNeg N + 1 + 1 from by omega] at hs
  have h1 := p3_succ (wNeg N)
  have h2 := p3_succ (wNeg N + 1)
  have h3 := p3_mono (a := 1) (b := wNeg N) (wNeg_pos N)
  omega

/-- The Dyckhoff-fire drop, with slack. -/
theorem dec_dykS {done rest : List Neg} {Q' : Pos} {N' N : Neg}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * 3 ^ wNeg N + sum3 rest + 9 < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have h1 := p3_mono (a := wNeg N + 1 + 1)
    (b := wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1)
    (by have := wPos_pos Q'; have := wNeg_pos N'; omega)
  have h2 := p3_succ (wNeg N)
  have h3 := p3_succ (wNeg N + 1)
  have h4 := p3_mono (a := 1) (b := wNeg N) (wNeg_pos N)
  omega

/-- The goal-inversion drop, with slack. -/
theorem dec_ainvS {Q : Pos} {b : List Neg} {N : Neg}
    (hb : b ∈ invertPos Q) :
    2 * sum3 b + 3 ^ wNeg N + 9 < 3 ^ (wPos Q + wNeg N + 1) := by
  have h1 := invertPos_le Q b hb
  have hD := p3_succ (wPos Q + wNeg N - 1)
  rw [show wPos Q + wNeg N - 1 + 1 = wPos Q + wNeg N from by
    have := wPos_pos Q; omega] at hD
  have hC := p3_succ (wPos Q + wNeg N)
  have hA := p3_mono (a := wPos Q) (b := wPos Q + wNeg N - 1)
    (by have := wNeg_pos N; omega)
  have hB := p3_mono (a := wNeg N) (b := wPos Q + wNeg N)
    (by have := wPos_pos Q; omega)
  have hDp := p3_mono (a := 1) (b := wPos Q + wNeg N - 1)
    (by have := wPos_pos Q; have := wNeg_pos N; omega)
  omega

variable {p : String}

/-- Fire the `q`-implication conjunct: the atom from `sa`, the recursively
interpolated body consumed through `δ`. -/
def qAssembleN {done rest K : List Neg} {a : String} {N : Neg} {C : Neg}
    {L : List Neg}
    (hE : interp p [] done none = nAndAll L)
    (hmem : pGuard p a nTop (.imp (.atom a) (interp p [N] rest none)) ∈ L)
    (hap : ¬ a = p)
    (sa : Stab (interp p [] done none :: K) .tru (.atom a))
    {j : JD} (δ : Inv (interp p [N] rest none :: K) [] j C) :
    Inv (interp p [] done none :: K) [] j C :=
  simHyp
    (fl := fun hs lf =>
      .lfoc (hs _ (List.mem_cons_self ..))
        (hE.symm ▸ lfocAndAll hmem (by
          simp only [pGuard]; rw [if_neg hap]
          exact LFoc.impL (sa.wk hs) lf)))
    (Sub.grow _) δ

/-- Fire the Dyckhoff conjunct: the antecedent interpolant from `sant`, the
recursively interpolated body consumed through `δ`. -/
def dykAssembleN {done rest K : List Neg} {Q' : Pos} {N' N : Neg} {C : Neg}
    {L : List Neg}
    (hE : interp p [] done none = nAndAll L)
    (hmem : nAnd
        (.imp (.down (interp p [.imp (.down N') N] rest (some (.imp Q' N'))))
             (interp p [N] rest none))
        (interp p [.imp (.down N') N] rest none) ∈ L)
    (sant : Inv (interp p [] done none :: K) [] .tru
      (interp p [.imp (.down N') N] rest (some (.imp Q' N'))))
    {j : JD} (δ : Inv (interp p [N] rest none :: K) [] j C) :
    Inv (interp p [] done none :: K) [] j C :=
  simHyp
    (fl := fun hs lf =>
      .lfoc (hs _ (List.mem_cons_self ..))
        (hE.symm ▸ lfocAndAll hmem
          (.and1 (.impL (.rfoc (.rel (sant.wk hs))) lf))))
    (Sub.grow _) δ

/-- Open the box conjunct: at a lax goal, `circL` on the boxed `∃p` of the
opened station puts that interpolant straight into context — no simulation
needed. -/
def boxAssembleN {done rest K : List Neg} {Q : Pos} {P : Pos}
    {L : List Neg}
    (hE : interp p [] done none = nAndAll L)
    (hmem : Neg.circ (.down (interp p [.up Q] rest none)) ∈ L)
    (δ : Inv (interp p [.up Q] rest none :: K) [] .lax (.up P)) :
    Stab (interp p [] done none :: K) .lax P :=
  .lfoc (List.mem_cons_self ..)
    (hE.symm ▸ lfocAndAll hmem
      (.circL (.downL (δ.wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))))))

/-- Fire the `◯`-implication conjunct: the antecedent's `∀p` from `sant`,
the recursively interpolated body consumed through `δ`. -/
def cimpAssembleN {done rest K : List Neg} {Q' : Pos} {N : Neg} {C : Neg}
    {L : List Neg}
    (hE : interp p [] done none = nAndAll L)
    (hmem : nAnd
        (.imp (.down (interp p [] rest (some (.circ Q'))))
             (interp p [N] rest none))
        (interp p [] rest none) ∈ L)
    (sant : Inv (interp p [] done none :: K) [] .tru
      (interp p [] rest (some (.circ Q'))))
    {j : JD} (δ : Inv (interp p [N] rest none :: K) [] j C) :
    Inv (interp p [] done none :: K) [] j C :=
  simHyp
    (fl := fun hs lf =>
      .lfoc (hs _ (List.mem_cons_self ..))
        (hE.symm ▸ lfocAndAll hmem
          (.and1 (.impL (.rfoc (.rel (sant.wk hs))) lf))))
    (Sub.grow _) δ


/-! The `∀p` aggregates as equations, at each goal shape (stated outside any
mutual block so the elaborator reuses `interp`'s own compiled matchers). -/

theorem interpA_atom_eq {p : String} {done : List Neg}
    (hsat : Saturated done) {q : String} (hq : ¬ atomMem q done = true) :
    interp p [] done (some (.up (.atom q))) =
      nOrAll (atomHead p q ++ (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up (.atom q)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up (.atom q))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.up (.atom q))))
              | _, _ => nBot)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · simp [hq]

theorem interpA_atomT_eq {p : String} {done : List Neg}
    (hsat : Saturated done) {q : String} (hq : atomMem q done = true) :
    interp p [] done (some (.up (.atom q))) = nTop := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · simp [hq]

theorem interpA_fls_eq {p : String} {done : List Neg}
    (hsat : Saturated done) :
    interp p [] done (some (.up .fls)) =
      nOrAll ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up .fls))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up .fls)))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.up .fls)))
              | _, _ => nBot)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_or_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (P₁ P₂ : Pos) :
    interp p [] done (some (.up (.or P₁ P₂))) =
      nOrAll ([interp p [] done (some (.up P₁)),
               interp p [] done (some (.up P₂))] ++ (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up (.or P₁ P₂)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up (.or P₁ P₂))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.up (.or P₁ P₂))))
              | _, _ => nBot)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_down_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (M : Neg) :
    interp p [] done (some (.up (.down M))) =
      nOrAll ([interp p [] done (some M)] ++ (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up (.down M)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up (.down M))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.up (.down M))))
              | _, _ => nBot)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_imp_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (Q : Pos) (N : Neg) :
    interp p [] done (some (.imp Q N)) =
      nAndAll ((invertPos Q).attach.map
        (fun ⟨b, hb⟩ =>
          .imp (.down (interp p b done none))
            (interp p b done (some N)))) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_and_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (M N : Neg) :
    interp p [] done (some (.and M N)) =
      nAnd (interp p [] done (some M)) (interp p [] done (some N)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl


variable {p : String}

theorem interpA_circAtom_eq {p : String} {done : List Neg}
    (hsat : Saturated done) {q : String} :
    interp p [] done (some (.circ (.atom q))) = nOrAll ([interp p [] done (some (.up (.atom q)))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.atom q)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.atom q))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ (.atom q))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.atom q))))
              | _, _ => nBot)) := by
  conv => lhs; rw [interp]
  split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_circFls_eq {p : String} {done : List Neg}
    (hsat : Saturated done) :
    interp p [] done (some (.circ .fls)) = nOrAll ([interp p [] done (some (.up .fls))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ .fls))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ .fls)))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ .fls)))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ .fls)))
              | _, _ => nBot)) := by
  conv => lhs; rw [interp]
  split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_circOr_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (P₁ P₂ : Pos) :
    interp p [] done (some (.circ (.or P₁ P₂))) = nOrAll ([interp p [] done (some (.circ P₁)),
                     interp p [] done (some (.circ P₂)),
                     interp p [] done (some (.up (.or P₁ P₂)))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.or P₁ P₂)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.or P₁ P₂))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ (.or P₁ P₂))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.or P₁ P₂))))
              | _, _ => nBot)) := by
  conv => lhs; rw [interp]
  split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_circDownUp_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (P' : Pos) :
    interp p [] done (some (.circ (.down (.up P')))) = nOrAll ([interp p [] done (some (.circ P'))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.down (.up P'))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.down (.up P')))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ (.down (.up P')))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.down (.up P')))))
              | _, _ => nBot)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_circDownCirc_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (P' : Pos) :
    interp p [] done (some (.circ (.down (.circ P')))) = nOrAll ([interp p [] done (some (.circ P'))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.down (.circ P'))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.down (.circ P')))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ (.down (.circ P')))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.down (.circ P')))))
              | _, _ => nBot)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_circDownAnd_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (M₁ M₂ : Neg) :
    interp p [] done (some (.circ (.down (.and M₁ M₂)))) = nOrAll ([interp p [] done (some (.up (.down (.and M₁ M₂))))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.down (.and M₁ M₂))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.down (.and M₁ M₂)))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ (.down (.and M₁ M₂)))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.down (.and M₁ M₂)))))
              | _, _ => nBot)) := by
  conv => lhs; rw [interp]
  split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_circDownImp_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (Q₀ : Pos) (N₀ : Neg) :
    interp p [] done (some (.circ (.down (.imp Q₀ N₀)))) = nOrAll ([interp p [] done (some (.up (.down (.imp Q₀ N₀))))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.down (.imp Q₀ N₀))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.down (.imp Q₀ N₀)))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ (.down (.imp Q₀ N₀)))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.down (.imp Q₀ N₀)))))
              | _, _ => nBot)) := by
  conv => lhs; rw [interp]
  split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

set_option maxHeartbeats 8000000 in
mutual

/-- Minimality of `∃p`, with the saturated case discharged inline —
conditional only on the Dyckhoff antecedent dispatch `dyk`. -/
def eMinF : ∀ (todo done Δ : List Neg) (ψ : Neg), ParkedCtx done →
    PFreeCtx p Δ → PFreeN p ψ → ∀ {j : JD},
    Inv ((todo ++ done) ++ Δ) [] j ψ →
    Inv (interp p todo done none :: Δ) [] j ψ
  | .up (.atom a) :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF todo (.up (.atom a) :: done) Δ ψ
        (ParkedCtx.cons (ParkedN.atom a) hP) hΔ hψ
        (d.wk subParkOut)
  | .up .fls :: todo, done, Δ, ψ, _, _, _, _, d => by
      rw [interp]
      exact nBotElimJ _ (List.mem_cons_self ..) d
  | .up (.or P Q) :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      refine nOrAllElimJ _ (List.mem_cons_self ..) d ?_
      intro x hx Γ' hsub
      obtain ⟨⟨b, hb⟩, hmem, hEq⟩ := memMapWitness _ _ x hx
      subst hEq
      refine ((eMinF (b ++ todo) done Δ ψ hP hΔ hψ
        ((invUp (d.wk subHeadOut) b hb).wk subChainIn)).wk ?_)
      intro Z hZ
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (hsub _ (List.mem_cons_of_mem _ hZ))
  | .up (.down M) :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF (M :: todo) done Δ ψ hP hΔ hψ
        (((invUp (d.wk subHeadOut) [M] (by simp [invertPos]))).wk subChainIn)
  | .and M N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF (M :: N :: todo) done Δ ψ hP hΔ hψ
        ((invAndHyp (d.wk subHeadOut)).wk (subChainIn (b := [M, N])))
  | .imp .fls N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF todo done Δ ψ hP hΔ hψ (invImpFls (d.wk subHeadOut))
  | .imp (.atom a) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF todo (.imp (.atom a) N :: done) Δ ψ
        (ParkedCtx.cons (ParkedN.qimp a N) hP) hΔ hψ
        (d.wk subParkOut)
  | .imp (.or Q₁ Q₂) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF (.imp Q₁ N :: .imp Q₂ N :: todo) done Δ ψ hP hΔ hψ
        ((invImpOr (d.wk subHeadOut)).wk
          (subChainIn (b := [.imp Q₁ N, .imp Q₂ N])))
  | .imp (.down (.up P')) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF (.imp P' N :: todo) done Δ ψ hP hΔ hψ
        ((invStrip (d.wk subHeadOut)).wk (subChainIn (b := [.imp P' N])))
  | .imp (.down (.and M₁ M₂)) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF (.imp (.down M₁) (.imp (.down M₂) N) :: todo) done Δ ψ
        hP hΔ hψ
        ((invCurry (d.wk subHeadOut)).wk
          (subChainIn (b := [.imp (.down M₁) (.imp (.down M₂) N)])))
  | .imp (.down (.imp Q' N')) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF todo (.imp (.down (.imp Q' N')) N :: done) Δ ψ
        (ParkedCtx.cons (ParkedN.dyk Q' N' N) hP) hΔ hψ
        (d.wk subParkOut)
  | .circ Q :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF todo (.circ Q :: done) Δ ψ
        (ParkedCtx.cons (ParkedN.box Q) hP) hΔ hψ
        (d.wk subParkOut)
  | .imp (.down (.circ Q')) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF todo (.imp (.down (.circ Q')) N :: done) Δ ψ
        (ParkedCtx.cons (ParkedN.cimp Q' N) hP) hΔ hψ
        (d.wk subParkOut)
  | [], done, Δ, ψ, hP, hΔ, hψ, _, d => by
      match hf : findFire done (splits done) with
      | some (a, N, rest) =>
          rw [interpFire_eq hf none]
          exact eMinF [N] rest Δ ψ
            (ParkedCtx.sub (splits_sub (findFire_mem hf)) hP) hΔ hψ (invFireHyp (findFire_mem hf) d)
      | none =>
          exact TInv done hf hP
            (fun Z hZ => List.mem_append.mp hZ)
            (fun Z hZ => List.mem_append_left _ hZ)
            hΔ (fun _ h => absurd h (List.not_mem_nil)) hψ d
  termination_by todo done Δ ψ hP hΔ hψ j d =>
    (2 * sum3 todo + sum3 done + 1, 0)
  decreasing_by ljf_dec_e


/-- Inversion-phase traversal. -/
def TInv (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {Ω : List Pos} {C : Neg} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeΩ p Ω → PFreeN p C →
      Inv Γ' Ω j C → Inv (interp p [] done none :: K) Ω j C
  | _, _, _, _, _, hm, hm2, hK, hΩ, hC, .impR d =>
      .impR (TInv done hsat hP hm hm2 hK (hΩ.cons hC.1) hC.2 d)
  | _, _, _, _, _, hm, hm2, hK, hΩ, hC, .andR d e =>
      .andR (TInv done hsat hP hm hm2 hK hΩ hC.1 d)
            (TInv done hsat hP hm hm2 hK hΩ hC.2 e)
  | _, _, _, _, _, hm, hm2, hK, hΩ, hC, .circR d =>
      .circR (TInv done hsat hP hm hm2 hK hΩ hC d)
  | _, _, _, _, _, hm, hm2, hK, _, hC, .stable s =>
      .stable (TStab done hsat hP hm hm2 hK hC s)
  | _, _, .or P₁ Q₁ :: _, _, _, hm, hm2, hK, hΩ, hC, .orL d₁ d₂ =>
      have hor : PFreeP p (.or P₁ Q₁) := hΩ.head
      .orL (TInv done hsat hP hm hm2 hK (hΩ.tail.cons hor.1) hC d₁)
           (TInv done hsat hP hm hm2 hK (hΩ.tail.cons hor.2) hC d₂)
  | _, _, _, _, _, _, _, _, _, _, .flsL => .flsL
  | _, _, .down M₀ :: _, _, _, hm, hm2, hK, hΩ, hC, .downL d =>
      have hM : PFreeN p M₀ := hΩ.head
      .downL (((TInv done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons hM hK) hΩ.tail hC d)).wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  | _, _, .atom a :: _, _, _, hm, hm2, hK, hΩ, hC, .atomL d =>
      .atomL (((TInv done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons (show PFreeN p (.up (.atom a)) from hΩ.head) hK)
          hΩ.tail hC d)).wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  termination_by Γ' K Ω C j hm hm2 hK hΩ hC d => (2 * sum3 [] + sum3 done, sizeOf d)
  decreasing_by ljf_dec_e


/-- Stable-phase traversal: the dispatch point. -/
def TStab (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {P : Pos} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeP p P →
      Stab Γ' j P → Stab (interp p [] done none :: K) j P
  | _, _, _, _, hm, hm2, hK, hp, .rfoc r => TRF done hsat hP hm hm2 hK hp r
  | _, _, _, _, hm, hm2, hK, hp, .laxOf s =>
      .laxOf (TStab done hsat hP hm hm2 hK hp s)
  | _, _, _, _, hm, hm2, hK, hp, @Stab.lfoc _ _ _ N₀ h lf =>
      if hd : N₀ ∈ done then
        match N₀, hP _ hd, hd, lf with
        | .up (.atom a), _, hd, .rel (.atomL (.stable s')) =>
            TStab done hsat hP (hmConsDone hd hm)
              (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ)) hK hp s'
        | .imp (.atom a) N, _, hd, .impL s_a lf' =>
            if hap : a = p then
              TpElim done hsat hP hm hm2 hK hp hap hap hd lf' s_a
            else
              let ⟨rest, hXr⟩ := splitAt done _ hd
              unStable (qAssembleN (interpE_eq hsat) (qimpConjMem hXr) hap
                (TStab done hsat hP hm hm2 hK hap s_a)
                (eMinF [N] rest _ (.up _) (hP.sub (splits_sub hXr)) hK hp
                  (fireClean (splitHyp hm hXr)
                    (.stable (.lfoc (List.mem_cons_self ..)
                      (lf'.wk (Sub.grow _)))))))
        | .circ Q, _, hd, .circL d =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            boxAssembleN (interpE_eq hsat) (boxConjMem hXr)
              (eMinF [.up Q] rest _ (.up _) (hP.sub (splits_sub hXr)) hK hp
                (boxClean (splitHyp hm hXr)
                  (.stable (.lfoc (List.mem_cons_self ..)
                    (.rel (d.wk (Sub.grow _)))))))
        | .imp (.down (.circ Q')) N, _, hd, .impL s_d lf' =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            unStable (cimpAssembleN (interpE_eq hsat) (cimpConjMem hXr)
              (cimpAntC done rest _ _ Q' N hsat hP hXr hm hm2 hK s_d)
              (eMinF [N] rest _ (.up _) (hP.sub (splits_sub hXr)) hK hp
                (fireClean (splitHyp hm hXr)
                  (.stable (.lfoc (List.mem_cons_self ..)
                    (lf'.wk (Sub.grow _)))))))
        | .imp (.down (.imp Q' N')) N, _, hd, .impL s_d lf' =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            unStable (dykAssembleN (interpE_eq hsat) (dykConjMem hXr)
              (dykAntC done rest _ _ Q' N' N hsat hP hXr hm hm2 hK s_d)
              (eMinF [N] rest _ (.up _) (hP.sub (splits_sub hXr)) hK hp
                (fireClean (splitHyp hm hXr)
                  (.stable (.lfoc (List.mem_cons_self ..)
                    (lf'.wk (Sub.grow _)))))))
        | .up .fls, hpk, _, _ => nomatch hpk
        | .up (.or _ _), hpk, _, _ => nomatch hpk
        | .up (.down _), hpk, _, _ => nomatch hpk
        | .imp .fls _, hpk, _, _ => nomatch hpk
        | .imp (.or _ _) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.up _)) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.and _ _)) _, hpk, _, _ => nomatch hpk
        | .and _ _, hpk, _, _ => nomatch hpk
      else
        .lfoc (List.mem_cons_of_mem _ ((hm _ h).resolve_left hd))
          (TLF done hsat hP hm hm2 hK
            (hK _ ((hm _ h).resolve_left hd)) hp lf)
  termination_by Γ' K P j hm hm2 hK hp s => (2 * sum3 [] + sum3 done, sizeOf s)
  decreasing_by ljf_dec_e


/-- Right-focus traversal. -/
def TRF (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {P : Pos} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeP p P →
      RFocus Γ' j P → Stab (interp p [] done none :: K) j P
  | _, _, .atom a, _, hm, _, hK, hp, .init h => by
      by_cases hd : Neg.up (.atom a) ∈ done
      · exact
          let w := splitAt done _ hd
          Stab.ofTru _ (atomAssemble (interpE_eq hsat) (atomConjMem w.2) hp)
      · exact .rfoc (.init (List.mem_cons_of_mem _
          ((hm _ h).resolve_left hd)))
  | _, _, _, _, hm, hm2, hK, hp, .or1 r =>
      stabOr1 (TRF done hsat hP hm hm2 hK hp.1 r)
  | _, _, _, _, hm, hm2, hK, hp, .or2 r =>
      stabOr2 (TRF done hsat hP hm hm2 hK hp.2 r)
  | _, _, _, _, hm, hm2, hK, hp, .rel d =>
      .rfoc (.rel (TInv done hsat hP hm hm2 hK
        (fun _ h => absurd h (List.not_mem_nil)) hp d))
  termination_by Γ' K P j hm hm2 hK hp r => (2 * sum3 [] + sum3 done, sizeOf r)
  decreasing_by ljf_dec_e


/-- Left-focus traversal on a kept hypothesis. -/
def TLF (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {H : Neg} {P : Pos} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeN p H → PFreeP p P →
      LFoc Γ' H j P → LFoc (interp p [] done none :: K) H j P
  | _, _, _, _, _, hm, hm2, hK, hH, hp, .rel d =>
      .rel (TInv done hsat hP hm hm2 hK
        (PFreeΩ.cons hH PFreeΩ.nil) hp d)
  | _, _, _, _, _, hm, hm2, hK, hH, hp, .circL d =>
      .circL (TInv done hsat hP hm hm2 hK
        (PFreeΩ.cons hH PFreeΩ.nil) hp d)
  | _, _, _, _, _, hm, hm2, hK, hH, hp, .impL s lf =>
      .impL (TStab done hsat hP hm hm2 hK hH.1 s)
            (TLF done hsat hP hm hm2 hK hH.2 hp lf)
  | _, _, _, _, _, hm, hm2, hK, hH, hp, .and1 lf =>
      .and1 (TLF done hsat hP hm hm2 hK hH.1 hp lf)
  | _, _, _, _, _, hm, hm2, hK, hH, hp, .and2 lf =>
      .and2 (TLF done hsat hP hm hm2 hK hH.2 hp lf)
  termination_by Γ' K H P j hm hm2 hK hH hp lf => (2 * sum3 [] + sum3 done, sizeOf lf)
  decreasing_by ljf_dec_e


/-- The `p`-fire eliminator: a main-line proof of the atom `p`, plus the
outer `p ⊃ M` package, yields the target directly — `init` on `↑p` is
impossible, kept chains rebuild, nested `p`-fires shortcut to their own
premise, and every other fire composes the package with the fire's body. -/
def TpElim (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {a b : String} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeP p P₀ → a = p → b = p →
      Neg.imp (.atom a) M ∈ done → LFoc Γ' M j P₀ →
      Stab Γ' .tru (.atom b) → Stab (interp p [] done none :: K) j P₀
  | _, _, _, _, _, _, _, hm, _, hK, _, ha, hb, hXpkg, _, .rfoc (.init h) =>
      False.elim (by
        rcases hm _ h with hd | hk
        · have h1 := atomMem_of_mem hd
          have h2 := saturated_atom_absent hsat hXpkg
          rw [hb.trans ha.symm] at h1
          rw [h1] at h2; cases h2
        · exact (hK _ hk) hb)
  | _, _, _, _, a, b, _, hm, hm2, hK, hpT, ha, hb, hXpkg, lfP, @Stab.lfoc _ _ _ N₀ h lf =>
      if hd : N₀ ∈ done then
        match N₀, hP _ hd, hd, lf with
        | .up (.atom c), _, hd, .rel (.atomL (.stable s')) =>
            TpElim done hsat hP (hmConsDone hd hm)
              (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ)) hK hpT ha hb
              hXpkg (lfP.wk (Sub.grow _)) s'
        | .imp (.atom c) N_b, _, hd, .impL s_b lf_b =>
            if hcp : c = p then
              TpElim done hsat hP hm hm2 hK hpT ha hcp hXpkg lfP s_b
            else
              let ⟨rest, hXr⟩ := splitAt done _ hd
              unStable (qAssembleN (interpE_eq hsat) (qimpConjMem hXr) hcp
                (TStab done hsat hP hm hm2 hK hcp s_b)
                (eMinF [N_b] rest _ (.up _) (hP.sub (splits_sub hXr)) hK hpT
                  (fireClean (splitHyp hm hXr) (.stable
                    (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                      (.impL
                        ((hb.trans ha.symm) ▸
                          Stab.lfoc (List.mem_cons_self ..)
                            (lf_b.wk (Sub.grow _)))
                        (lfP.wk (Sub.grow _))))))))
        | .imp (.down (.imp Q' N')) N_d, _, hd, .impL s_d lf_d =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            unStable (dykAssembleN (interpE_eq hsat) (dykConjMem hXr)
              (dykAntC done rest _ _ Q' N' N_d hsat hP hXr hm hm2 hK s_d)
              (eMinF [N_d] rest _ (.up _) (hP.sub (splits_sub hXr)) hK hpT
                (fireClean (splitHyp hm hXr) (.stable
                  (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                    (.impL
                      ((hb.trans ha.symm) ▸
                        Stab.lfoc (List.mem_cons_self ..)
                          (lf_d.wk (Sub.grow _)))
                      (lfP.wk (Sub.grow _))))))))
        | .imp (.down (.circ Q')) N_c, _, hd, .impL s_c lf_c =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            unStable (cimpAssembleN (interpE_eq hsat) (cimpConjMem hXr)
              (cimpAntC done rest _ _ Q' N_c hsat hP hXr hm hm2 hK s_c)
              (eMinF [N_c] rest _ (.up _) (hP.sub (splits_sub hXr)) hK hpT
                (fireClean (splitHyp hm hXr) (.stable
                  (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                    (.impL
                      ((hb.trans ha.symm) ▸
                        Stab.lfoc (List.mem_cons_self ..)
                          (lf_c.wk (Sub.grow _)))
                      (lfP.wk (Sub.grow _))))))))
        | .circ _, _, _, lf => nomatch lf
        | .up .fls, hpk, _, _ => nomatch hpk
        | .up (.or _ _), hpk, _, _ => nomatch hpk
        | .up (.down _), hpk, _, _ => nomatch hpk
        | .imp .fls _, hpk, _, _ => nomatch hpk
        | .imp (.or _ _) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.up _)) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.and _ _)) _, hpk, _, _ => nomatch hpk
        | .and _ _, hpk, _, _ => nomatch hpk
      else
        .lfoc (List.mem_cons_of_mem _ ((hm _ h).resolve_left hd))
          (TpLF done hsat hP hm hm2 hK
            (hK _ ((hm _ h).resolve_left hd)) hpT ha hb hXpkg lfP lf)
  termination_by Γ' K M P₀ a b j hm hm2 hK hpT ha hb hXpkg lfP s =>
    (2 * sum3 [] + sum3 done, sizeOf s)
  decreasing_by ljf_dec_e


/-- Left focus on a kept hypothesis, inside a `p`-proof. -/
def TpLF (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {H : Neg} {a b : String} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeN p H → PFreeP p P₀ → a = p → b = p →
      Neg.imp (.atom a) M ∈ done → LFoc Γ' M j P₀ →
      LFoc Γ' H .tru (.atom b) → LFoc (interp p [] done none :: K) H j P₀
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hH, hpT, ha, hb, hXpkg, lfP, .rel d =>
      .rel (TpInv done hsat hP hm hm2 hK
        (PFreeΩ.cons hH PFreeΩ.nil)
        hpT ha hb hXpkg lfP d)
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hH, hpT, ha, hb, hXpkg, lfP, .impL s lf =>
      .impL (TStab done hsat hP hm hm2 hK hH.1 s)
            (TpLF done hsat hP hm hm2 hK hH.2 hpT ha hb hXpkg lfP lf)
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hH, hpT, ha, hb, hXpkg, lfP, .and1 lf =>
      .and1 (TpLF done hsat hP hm hm2 hK hH.1 hpT ha hb hXpkg lfP lf)
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hH, hpT, ha, hb, hXpkg, lfP, .and2 lf =>
      .and2 (TpLF done hsat hP hm hm2 hK hH.2 hpT ha hb hXpkg lfP lf)
  termination_by Γ' K M P₀ H a b j hm hm2 hK hH hpT ha hb hXpkg lfP lf =>
    (2 * sum3 [] + sum3 done, sizeOf lf)
  decreasing_by ljf_dec_e


/-- Inversion inside a `p`-proof, with the goal re-targeted. -/
def TpInv (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {Ω : List Pos} {a b : String} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeΩ p Ω → PFreeP p P₀ → a = p → b = p →
      Neg.imp (.atom a) M ∈ done → LFoc Γ' M j P₀ →
      Inv Γ' Ω .tru (.up (.atom b)) → Inv (interp p [] done none :: K) Ω j (.up P₀)
  | _, _, _, _, _, _, _, _, hm, hm2, hK, _, hpT, ha, hb, hXpkg, lfP, .stable s =>
      .stable (TpElim done hsat hP hm hm2 hK hpT ha hb hXpkg lfP s)
  | _, _, _, _, .or P₁ Q₁ :: _, _, _, _, hm, hm2, hK, hΩ, hpT, ha, hb, hXpkg, lfP, .orL d₁ d₂ =>
      have hor : PFreeP p (.or P₁ Q₁) := hΩ.head
      .orL (TpInv done hsat hP hm hm2 hK (hΩ.tail.cons hor.1)
              hpT ha hb hXpkg lfP d₁)
           (TpInv done hsat hP hm hm2 hK (hΩ.tail.cons hor.2)
              hpT ha hb hXpkg lfP d₂)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .flsL => .flsL
  | _, _, _, _, .down M₀ :: _, _, _, _, hm, hm2, hK, hΩ, hpT, ha, hb, hXpkg, lfP, .downL d =>
      have hM : PFreeN p M₀ := hΩ.head
      .downL (((TpInv done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons hM hK) hΩ.tail hpT ha hb hXpkg
          (lfP.wk (Sub.grow _)) d)).wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  | _, _, _, _, .atom c :: _, _, _, _, hm, hm2, hK, hΩ, hpT, ha, hb, hXpkg, lfP, .atomL d =>
      .atomL (((TpInv done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons (show PFreeN p (.up (.atom c)) from hΩ.head) hK) hΩ.tail hpT ha hb hXpkg
          (lfP.wk (Sub.grow _)) d)).wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  termination_by Γ' K M P₀ Ω a b j hm hm2 hK hΩ hpT ha hb hXpkg lfP d =>
    (2 * sum3 [] + sum3 done, sizeOf d)
  decreasing_by ljf_dec_e


/-- Minimality of `∀p`, with the saturated case discharged inline. -/
def aMinF : ∀ (todo done Δ : List Neg) (G : Neg), ParkedCtx done →
    PFreeCtx p Δ → ∀ {j : JD},
    Inv ((todo ++ done) ++ Δ) [] j G →
    Inv (interp p todo done none :: Δ) [] .tru
      (interp p todo done (some (jGoal j G)))
  | .up (.atom a) :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF todo (.up (.atom a) :: done) Δ G
        (ParkedCtx.cons (ParkedN.atom a) hP) hΔ (d.wk subParkOut)
  | .up .fls :: todo, done, Δ, G, _, _, _, _ => by
      rw [interp, interp]
      exact nBotElim _ (List.mem_cons_self ..)
  | .up (.or P Q) :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      refine nAndAllIntro ?_
      intro x hx
      obtain ⟨⟨b, hb⟩, hmem, hEq⟩ := memMapWitness _ _ x hx
      subst hEq
      refine .impR (.downL ?_)
      refine ((aMinF (b ++ todo) done Δ G hP hΔ
        ((invUp (d.wk subHeadOut) b hb).wk subChainIn)).wk ?_)
      intro Z hZ
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)
  | .up (.down M) :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF (M :: todo) done Δ G hP hΔ
        (((invUp (d.wk subHeadOut) [M] (by simp [invertPos]))).wk subChainIn)
  | .and M N :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF (M :: N :: todo) done Δ G hP hΔ
        ((invAndHyp (d.wk subHeadOut)).wk (subChainIn (b := [M, N])))
  | .imp .fls N :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF todo done Δ G hP hΔ (invImpFls (d.wk subHeadOut))
  | .imp (.atom a) N :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF todo (.imp (.atom a) N :: done) Δ G
        (ParkedCtx.cons (ParkedN.qimp a N) hP) hΔ
        (d.wk subParkOut)
  | .imp (.or Q₁ Q₂) N :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF (.imp Q₁ N :: .imp Q₂ N :: todo) done Δ G hP hΔ
        ((invImpOr (d.wk subHeadOut)).wk
          (subChainIn (b := [.imp Q₁ N, .imp Q₂ N])))
  | .imp (.down (.up P')) N :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF (.imp P' N :: todo) done Δ G hP hΔ
        ((invStrip (d.wk subHeadOut)).wk (subChainIn (b := [.imp P' N])))
  | .imp (.down (.and M₁ M₂)) N :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF (.imp (.down M₁) (.imp (.down M₂) N) :: todo) done Δ G
        hP hΔ
        ((invCurry (d.wk subHeadOut)).wk
          (subChainIn (b := [.imp (.down M₁) (.imp (.down M₂) N)])))
  | .imp (.down (.imp Q' N')) N :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF todo (.imp (.down (.imp Q' N')) N :: done) Δ G
        (ParkedCtx.cons (ParkedN.dyk Q' N' N) hP) hΔ
        (d.wk subParkOut)
  | .circ Q :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF todo (.circ Q :: done) Δ G
        (ParkedCtx.cons (ParkedN.box Q) hP) hΔ
        (d.wk subParkOut)
  | .imp (.down (.circ Q')) N :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF todo (.imp (.down (.circ Q')) N :: done) Δ G
        (ParkedCtx.cons (ParkedN.cimp Q' N) hP) hΔ
        (d.wk subParkOut)
  | [], done, Δ, G, hP, hΔ, j, d => by
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          rw [interpFire_eq hf none, interpFire_eq hf (some (jGoal j G))]
          exact aMinF [N'] rest Δ G
            (ParkedCtx.sub (splits_sub (findFire_mem hf)) hP) hΔ (invFireHyp (findFire_mem hf) d)
      | none =>
          exact UEntry done hf hP
            (fun Z hZ => List.mem_append.mp hZ)
            (fun Z hZ => List.mem_append_left _ hZ)
            hΔ G d
  termination_by todo done Δ G hP hΔ j d =>
    (2 * sum3 todo + sum3 done + 3 ^ wNeg G + 4, 0)
  decreasing_by ljf_dec_a


/-- The `∀p` interpolant of any goal over a mixed saturated context. -/
def UEntry (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      ∀ (G : Neg) {j : JD}, Inv Γ' [] j G →
      Inv (interp p [] done none :: K) [] .tru
        (interp p [] done (some (jGoal j G)))
  | _, _, hm, hm2, hK, .imp Q N, _, .impR d₁ => by
      show Inv _ [] .tru (interp p [] done (some (.imp Q N)))
      rw [interpA_imp_eq hsat Q N]
      refine nAndAllIntro ?_
      intro x hx
      obtain ⟨w, hmem, hEq⟩ := memMapWitness _ _ x hx
      subst hEq
      have hb : w.1 ∈ invertPos Q := w.2
      refine .impR (.downL ?_)
      have haux := (aMinF w.1 done _ N hP hK
        ((extract [] d₁ w.1 hb).wk (fun Z hZ => by
          rcases List.mem_append.mp hZ with hZ | hZ
          · exact List.mem_append_left _ (List.mem_append_left _ hZ)
          · rcases hm Z hZ with hd | hk
            · exact List.mem_append_left _ (List.mem_append_right _ hd)
            · exact List.mem_append_right _ hk)))
      rw [jGoal_tru] at haux
      refine (haux.wk ?_)
      intro Z hZ
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)
  | _, _, hm, hm2, hK, .and M N, _, .andR d₁ d₂ => by
      show Inv _ [] .tru (interp p [] done (some (.and M N)))
      rw [interpA_and_eq hsat M N]
      have h₁ := UEntry done hsat hP hm hm2 hK M d₁
      have h₂ := UEntry done hsat hP hm hm2 hK N d₂
      rw [jGoal_tru] at h₁ h₂
      exact .andR h₁ h₂
  | _, _, hm, hm2, hK, .circ P, _, .circR d =>
      UEntry done hsat hP hm hm2 hK (.up P) d
  | _, _, hm, hm2, hK, .up (.atom q), .tru, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.up (.atom q))))
      by_cases hq : atomMem q done = true
      · rw [interpA_atomT_eq hsat hq]; exact nTopIntro
      · rw [interpA_atom_eq hsat hq]
        exact UStab done hsat hP hm hm2 hK (interpA_atom_eq hsat hq)
          (fun {c Nc rest} hsp =>
            List.mem_append_right _
              (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
          (fun {Q' N' N rest} hsp =>
            List.mem_append_right _
              (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
          (fun {Q' N rest} hsp =>
            List.mem_append_right _
              (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
          (fun hj => nomatch hj)
          s
  | _, _, hm, hm2, hK, .up .fls, .tru, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.up .fls)))
      rw [interpA_fls_eq hsat]
      exact UStab done hsat hP hm hm2 hK (interpA_fls_eq hsat)
        (fun {c Nc rest} hsp =>
          List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩))
        (fun {Q' N' N rest} hsp =>
          List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩))
        (fun {Q' N rest} hsp =>
          List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩))
        (fun hj => nomatch hj)
        s
  | _, _, hm, hm2, hK, .up (.or P₁ P₂), .tru, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.up (.or P₁ P₂))))
      rw [interpA_or_eq hsat P₁ P₂]
      exact UStab done hsat hP hm hm2 hK (interpA_or_eq hsat P₁ P₂)
        (fun {c Nc rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun hj => nomatch hj)
        s
  | _, _, hm, hm2, hK, .up (.down M), .tru, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.up (.down M))))
      rw [interpA_down_eq hsat M]
      exact UStab done hsat hP hm hm2 hK (interpA_down_eq hsat M)
        (fun {c Nc rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun hj => nomatch hj)
        s
  | _, _, hm, hm2, hK, .up (.atom q), .lax, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.atom q))))
      rw [interpA_circAtom_eq hsat]
      exact UStab done hsat hP hm hm2 hK (interpA_circAtom_eq hsat)
        (fun {c Nc rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun _ {R rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        s
  | _, _, hm, hm2, hK, .up .fls, .lax, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.circ .fls)))
      rw [interpA_circFls_eq hsat]
      exact UStab done hsat hP hm hm2 hK (interpA_circFls_eq hsat)
        (fun {c Nc rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun _ {R rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        s
  | _, _, hm, hm2, hK, .up (.or P₁ P₂), .lax, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.or P₁ P₂))))
      rw [interpA_circOr_eq hsat P₁ P₂]
      exact UStab done hsat hP hm hm2 hK (interpA_circOr_eq hsat P₁ P₂)
        (fun {c Nc rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun _ {R rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        s
  | _, _, hm, hm2, hK, .up (.down (.up P')), .lax, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.down (.up P')))))
      rw [interpA_circDownUp_eq hsat P']
      exact UStab done hsat hP hm hm2 hK (interpA_circDownUp_eq hsat P')
        (fun {c Nc rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun _ {R rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        s
  | _, _, hm, hm2, hK, .up (.down (.circ P')), .lax, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.down (.circ P')))))
      rw [interpA_circDownCirc_eq hsat P']
      exact UStab done hsat hP hm hm2 hK (interpA_circDownCirc_eq hsat P')
        (fun {c Nc rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun _ {R rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        s
  | _, _, hm, hm2, hK, .up (.down (.and M₁ M₂)), .lax, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.down (.and M₁ M₂)))))
      rw [interpA_circDownAnd_eq hsat M₁ M₂]
      exact UStab done hsat hP hm hm2 hK (interpA_circDownAnd_eq hsat M₁ M₂)
        (fun {c Nc rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun _ {R rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        s
  | _, _, hm, hm2, hK, .up (.down (.imp Q₀ N₀)), .lax, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.down (.imp Q₀ N₀)))))
      rw [interpA_circDownImp_eq hsat Q₀ N₀]
      exact UStab done hsat hP hm hm2 hK (interpA_circDownImp_eq hsat Q₀ N₀)
        (fun {c Nc rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun _ {R rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        s
  termination_by Γ' K hm hm2 hK G j d =>
    (2 * sum3 [] + sum3 done + 3 ^ wNeg G + 3, 0)
  decreasing_by ljf_dec_a


/-- Stable-phase `∀p` traversal: attack emission. -/
def UStab (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {P₀ : Pos} {j : JD} {L : List Neg},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      interp p [] done (some (jGoal j (.up P₀))) = nOrAll L →
      (∀ {c : String} {Nc : Neg} {rest : List Neg},
        (Neg.imp (.atom c) Nc, rest) ∈ splits done →
        pGuard p c nBot (nAnd (.up (.atom c))
          (interp p [Nc] rest (some (jGoal j (.up P₀))))) ∈ L) →
      (∀ {Q' : Pos} {N' N : Neg} {rest : List Neg},
        (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
        nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
             (interp p [N] rest (some (jGoal j (.up P₀)))) ∈ L) →
      (∀ {Q' : Pos} {N : Neg} {rest : List Neg},
        (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done →
        nAnd (interp p [] rest (some (.circ Q')))
             (interp p [N] rest (some (jGoal j (.up P₀)))) ∈ L) →
      (j = .lax → ∀ {R : Pos} {rest : List Neg},
        (Neg.circ R, rest) ∈ splits done →
        Neg.imp (.down (interp p [.up R] rest none))
          (interp p [.up R] rest (some (jGoal j (.up P₀)))) ∈ L) →
      Stab Γ' j P₀ → Inv (interp p [] done none :: K) [] .tru (nOrAll L)
  | _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, .rfoc r =>
      hV ▸ URF done hsat hP hm hm2 hK r
  | _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, @Stab.lfoc _ _ N₀ h lf =>
      if hd : N₀ ∈ done then
        match N₀, hP _ hd, hd, lf with
        | .up (.atom c), _, hd, .rel (.atomL (.stable s')) =>
            UStab done hsat hP (hmConsDone hd hm)
              (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ)) hK hV qmem dmem s'
        | .imp (.atom c) Nc, _, hd, .impL s_c lf' =>
            if hcp : c = p then
              UpElim done hsat hP hm hm2 hK hV qmem dmem hcp hcp hd lf' s_c
            else by
              obtain ⟨rest, hXr⟩ := splitAt done _ hd
              exact nOrAllIntro (qmem hXr) (by
                simp only [pGuard]; rw [if_neg hcp]
                refine .andR
                  (.stable (TStab done hsat hP hm hm2 hK hcp s_c)) ?_
                exact qAssembleN (interpE_eq hsat) (qimpConjMem hXr) hcp
                  (TStab done hsat hP hm hm2 hK hcp s_c)
                  (aMinF [Nc] rest _ (.up _)
                    (ParkedCtx.sub (splits_sub hXr) hP) hK
                    (fireClean (splitHyp hm hXr)
                      (.stable (.lfoc (List.mem_cons_self ..)
                        (lf'.wk (Sub.grow _)))))))
        | .imp (.down (.imp Q' N')) N, _, hd, .impL s_d lf' => by
            obtain ⟨rest, hXr⟩ := splitAt done _ hd
            exact nOrAllIntro (dmem hXr)
              (.andR
                (dykAntC done rest _ _ Q' N' N hsat hP hXr hm hm2 hK s_d)
                (dykAssembleN (interpE_eq hsat) (dykConjMem hXr)
                  (dykAntC done rest _ _ Q' N' N hsat hP hXr hm hm2 hK s_d)
                  (aMinF [N] rest _ (.up _)
                    (ParkedCtx.sub (splits_sub hXr) hP) hK
                    (fireClean (splitHyp hm hXr)
                      (.stable (.lfoc (List.mem_cons_self ..)
                        (lf'.wk (Sub.grow _))))))))
        | .up .fls, hpk, _, _ => nomatch hpk
        | .up (.or _ _), hpk, _, _ => nomatch hpk
        | .up (.down _), hpk, _, _ => nomatch hpk
        | .imp .fls _, hpk, _, _ => nomatch hpk
        | .imp (.or _ _) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.up _)) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.and _ _)) _, hpk, _, _ => nomatch hpk
        | .and _ _, hpk, _, _ => nomatch hpk
      else
        (nOrAll_eq _).symm ▸
          Inv.stable (.lfoc (List.mem_cons_of_mem _ ((hm _ h).resolve_left hd))
            (ULF done hsat hP hm hm2 hK hV qmem dmem
              (hK _ ((hm _ h).resolve_left hd)) lf))
  termination_by Γ' K P₀ j L hm hm2 hK hV qmem dmem cmem bmem s =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf s)
  decreasing_by
    all_goals simp_wf
    all_goals try simp only [sum3, sum3_append, goalW, wNeg, wPos]
    all_goals
      first
        | exact Nat.lt_succ_self _
        | omega
        | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N) hXr; omega)
        | (have h1 := dec_fireS (a := c) (N := Nc) hXr; omega)
        | (have h1 := dec_ainvS (N := N) (by assumption); omega)
        | (have h1 := dec_fireS (by assumption); omega)
        | (have h1 := dec_fireS (findFire_mem (by assumption)); omega)
        | (refine Prod.Lex.left _ _ ?_
           first
             | omega
             | exact Nat.lt_of_lt_of_le
                 (Nat.lt_of_le_of_lt
                   (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
                   (dec_dykC (Q' := Q') (N' := N') (N := N) hXr))
                 (Nat.le_trans (Nat.le_add_left _ _)
                   (Nat.le_trans (Nat.le_add_right _ _)
                     (Nat.le_add_right _ _)))
             | exact Nat.lt_of_lt_of_le
                 (Nat.lt_of_le_of_lt
                   (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
                   (dec_dykC (Q' := Q') (N' := N') (N := N_d) hXr))
                 (Nat.le_trans (Nat.le_add_left _ _)
                   (Nat.le_trans (Nat.le_add_right _ _)
                     (Nat.le_add_right _ _)))
             | (have h1 := dec_dykC (Q' := Q') (N' := N') (N := N) hXr; omega)
             | (have h1 := dec_dykC (Q' := Q') (N' := N') (N := N_d) hXr
                omega)
             | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N) hXr; omega)
             | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N_d) hXr
                omega)
             | (have h1 := dec_fireS (a := c) (N := Nc) hXr; omega)
             | (have h1 := dec_ainvS (N := N) (by assumption); omega)
             | (have h1 := dec_fireS (by assumption); omega)
             | (have h1 := dec_fireS (findFire_mem (by assumption)); omega)
             | (have h1 := dec_dykC (by assumption); omega))
        | decreasing_tactic


/-- Right-focus `∀p` traversal: the goal-driven disjuncts. -/
def URF (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {P₀ : Pos} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      RFocus Γ' j P₀ →
      Inv (interp p [] done none :: K) [] .tru
        (interp p [] done (some (jGoal j (.up P₀))))
  | _, _, .atom q, .tru, hm, hm2, hK, .init h => by
      show Inv _ [] .tru (interp p [] done (some (.up (.atom q))))
      by_cases hq : atomMem q done = true
      · rw [interpA_atomT_eq hsat hq]; exact nTopIntro
      · have hk : Neg.up (.atom q) ∈ _ :=
          (hm _ h).resolve_left (fun hd => hq (atomMem_of_mem hd))
        have hqp : ¬ q = p := fun e => (hK _ hk) e
        rw [interpA_atom_eq hsat hq]
        refine nOrAllIntro (List.mem_append_left _ ?_)
          (.stable (.rfoc (.init (List.mem_cons_of_mem _ hk))))
        rw [atomHead, if_neg hqp]
        exact List.mem_cons_self ..
  | _, _, .atom q, .lax, hm, hm2, hK, .init h => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.atom q))))
      rw [interpA_circAtom_eq hsat]
      refine nOrAllIntro (List.mem_append_left _ (List.mem_cons_self ..)) ?_
      by_cases hq : atomMem q done = true
      · rw [interpA_atomT_eq hsat hq]; exact nTopIntro
      · have hk : Neg.up (.atom q) ∈ _ :=
          (hm _ h).resolve_left (fun hd => hq (atomMem_of_mem hd))
        have hqp : ¬ q = p := fun e => (hK _ hk) e
        rw [interpA_atom_eq hsat hq]
        refine nOrAllIntro (List.mem_append_left _ ?_)
          (.stable (.rfoc (.init (List.mem_cons_of_mem _ hk))))
        rw [atomHead, if_neg hqp]
        exact List.mem_cons_self ..
  | _, _, .or P₁ P₂, .tru, hm, hm2, hK, .or1 r₁ => by
      show Inv _ [] .tru (interp p [] done (some (.up (.or P₁ P₂))))
      rw [interpA_or_eq hsat P₁ P₂]
      exact nOrAllIntro (List.mem_append_left _ (List.mem_cons_self ..))
        (URF done hsat hP hm hm2 hK r₁)
  | _, _, .or P₁ P₂, .lax, hm, hm2, hK, .or1 r₁ => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.or P₁ P₂))))
      rw [interpA_circOr_eq hsat P₁ P₂]
      exact nOrAllIntro (List.mem_append_left _ (List.mem_cons_self ..))
        (URF done hsat hP hm hm2 hK r₁)
  | _, _, .or P₁ P₂, .tru, hm, hm2, hK, .or2 r₂ => by
      show Inv _ [] .tru (interp p [] done (some (.up (.or P₁ P₂))))
      rw [interpA_or_eq hsat P₁ P₂]
      exact nOrAllIntro (List.mem_append_left _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        (URF done hsat hP hm hm2 hK r₂)
  | _, _, .or P₁ P₂, .lax, hm, hm2, hK, .or2 r₂ => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.or P₁ P₂))))
      rw [interpA_circOr_eq hsat P₁ P₂]
      exact nOrAllIntro (List.mem_append_left _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        (URF done hsat hP hm hm2 hK r₂)
  | _, _, .down M, .tru, hm, hm2, hK, .rel dI => by
      show Inv _ [] .tru (interp p [] done (some (.up (.down M))))
      rw [interpA_down_eq hsat M]
      have h₁ := UEntry done hsat hP hm hm2 hK M dI
      rw [jGoal_tru] at h₁
      exact nOrAllIntro (List.mem_append_left _ (List.mem_cons_self ..)) h₁
  | _, _, .down (.up P'), .lax, hm, hm2, hK, .rel dI => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.down (.up P')))))
      rw [interpA_circDownUp_eq hsat P']
      exact nOrAllIntro (List.mem_append_left _ (List.mem_cons_self ..))
        (UEntry done hsat hP hm hm2 hK (.up P') dI)
  | _, _, .down (.circ P'), .lax, hm, hm2, hK, .rel dI => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.down (.circ P')))))
      rw [interpA_circDownCirc_eq hsat P']
      exact nOrAllIntro (List.mem_append_left _ (List.mem_cons_self ..))
        (UEntry done hsat hP hm hm2 hK (.circ P') dI)
  | _, _, .down (.and _ _), .lax, _, _, _, .rel dI => nomatch dI
  | _, _, .down (.imp _ _), .lax, _, _, _, .rel dI => nomatch dI
  termination_by Γ' K P₀ j hm hm2 hK r =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf r)
  decreasing_by ljf_dec_a


/-- Left focus on a kept hypothesis, `∀p` mode. -/
def ULF (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {P₀ : Pos} {j : JD} {L : List Neg} {H : Neg},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      interp p [] done (some (jGoal j (.up P₀))) = nOrAll L →
      (∀ {c : String} {Nc : Neg} {rest : List Neg},
        (Neg.imp (.atom c) Nc, rest) ∈ splits done →
        pGuard p c nBot (nAnd (.up (.atom c))
          (interp p [Nc] rest (some (jGoal j (.up P₀))))) ∈ L) →
      (∀ {Q' : Pos} {N' N : Neg} {rest : List Neg},
        (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
        nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
             (interp p [N] rest (some (jGoal j (.up P₀)))) ∈ L) →
      (∀ {Q' : Pos} {N : Neg} {rest : List Neg},
        (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done →
        nAnd (interp p [] rest (some (.circ Q')))
             (interp p [N] rest (some (jGoal j (.up P₀)))) ∈ L) →
      (j = .lax → ∀ {R : Pos} {rest : List Neg},
        (Neg.circ R, rest) ∈ splits done →
        Neg.imp (.down (interp p [.up R] rest none))
          (interp p [.up R] rest (some (jGoal j (.up P₀)))) ∈ L) →
      PFreeN p H →
      LFoc Γ' H j P₀ → LFoc (interp p [] done none :: K) H j (orChain L)
  | _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hH, .rel d =>
      .rel (UInvG done hsat hP hm hm2 hK hV qmem dmem cmem bmem
        (PFreeΩ.cons hH PFreeΩ.nil) d)
  | _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hH, .circL d =>
      .circL (UInvG done hsat hP hm hm2 hK hV qmem dmem cmem bmem
        (PFreeΩ.cons hH PFreeΩ.nil) d)
  | _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hH, .impL s lf =>
      .impL (TStab done hsat hP hm hm2 hK hH.1 s)
            (ULF done hsat hP hm hm2 hK hV qmem dmem cmem bmem hH.2 lf)
  | _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hH, .and1 lf =>
      .and1 (ULF done hsat hP hm hm2 hK hV qmem dmem cmem bmem hH.1 lf)
  | _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hH, .and2 lf =>
      .and2 (ULF done hsat hP hm hm2 hK hV qmem dmem cmem bmem hH.2 lf)
  termination_by Γ' K P₀ j L H hm hm2 hK hV qmem dmem cmem bmem hH lf =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf lf)
  decreasing_by ljf_dec_a


/-- Inversion, `∀p` mode, goal re-targeted to the disjunction. -/
def UInvG (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {P₀ : Pos} {j : JD} {L : List Neg} {Ω : List Pos},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      interp p [] done (some (jGoal j (.up P₀))) = nOrAll L →
      (∀ {c : String} {Nc : Neg} {rest : List Neg},
        (Neg.imp (.atom c) Nc, rest) ∈ splits done →
        pGuard p c nBot (nAnd (.up (.atom c))
          (interp p [Nc] rest (some (jGoal j (.up P₀))))) ∈ L) →
      (∀ {Q' : Pos} {N' N : Neg} {rest : List Neg},
        (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
        nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
             (interp p [N] rest (some (jGoal j (.up P₀)))) ∈ L) →
      (∀ {Q' : Pos} {N : Neg} {rest : List Neg},
        (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done →
        nAnd (interp p [] rest (some (.circ Q')))
             (interp p [N] rest (some (jGoal j (.up P₀)))) ∈ L) →
      (j = .lax → ∀ {R : Pos} {rest : List Neg},
        (Neg.circ R, rest) ∈ splits done →
        Neg.imp (.down (interp p [.up R] rest none))
          (interp p [.up R] rest (some (jGoal j (.up P₀)))) ∈ L) →
      PFreeΩ p Ω →
      Inv Γ' Ω j (.up P₀) →
      Inv (interp p [] done none :: K) Ω j (.up (orChain L))
  | _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, _, .stable s =>
      nOrAll_eq _ ▸ UStab done hsat hP hm hm2 hK hV qmem dmem cmem bmem s
  | _, _, _, _, _, .or PA PB :: _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hΩ, .orL d₁ d₂ =>
      .orL (UInvG done hsat hP hm hm2 hK hV qmem dmem cmem bmem
              (hΩ.tail.cons hΩ.head.1) d₁)
           (UInvG done hsat hP hm hm2 hK hV qmem dmem cmem bmem
              (hΩ.tail.cons hΩ.head.2) d₂)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .flsL => .flsL
  | _, _, _, _, _, .down M₀ :: _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hΩ, .downL d =>
      .downL (((UInvG done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons hΩ.head hK) hV qmem dmem cmem bmem hΩ.tail d)).wk
        (fun Z hZ => by
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  | _, _, _, _, _, .atom a :: _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hΩ, .atomL d =>
      .atomL (((UInvG done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons (show PFreeN p (.up (.atom a)) from hΩ.head) hK)
          hV qmem dmem cmem bmem hΩ.tail d)).wk
        (fun Z hZ => by
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  termination_by Γ' K P₀ j L Ω hm hm2 hK hV qmem dmem cmem bmem hΩ d =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf d)
  decreasing_by ljf_dec_a


/-- The `p`-fire eliminator, `∀p` mode: same composition, attack emission. -/
def UpElim (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {L : List Neg} {a b : String},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      interp p [] done (some (.up P₀)) = nOrAll L →
      (∀ {c : String} {Nc : Neg} {rest : List Neg},
        (Neg.imp (.atom c) Nc, rest) ∈ splits done →
        pGuard p c nBot (nAnd (.up (.atom c))
          (interp p [Nc] rest (some (.up P₀)))) ∈ L) →
      (∀ {Q' : Pos} {N' N : Neg} {rest : List Neg},
        (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
        nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
             (interp p [N] rest (some (.up P₀))) ∈ L) →
      a = p → b = p → Neg.imp (.atom a) M ∈ done → LFoc Γ' M P₀ →
      Stab Γ' (.atom b) →
      Inv (interp p [] done none :: K) [] (nOrAll L)
  | _, _, _, _, _, a, b, hm, _, hK, _, _, _, ha, hb, hXpkg, _, .rfoc (.init h) =>
      False.elim (by
        rcases hm _ h with hd | hk
        · have h1 := atomMem_of_mem hd
          have h2 := saturated_atom_absent hsat hXpkg
          rw [hb.trans ha.symm] at h1
          rw [h1] at h2; cases h2
        · exact (hK _ hk) hb)
  | _, _, _, _, _, a, b, hm, hm2, hK, hV, qmem, dmem, ha, hb, hXpkg, lfP,
      @Stab.lfoc _ _ N₀ h lf =>
      if hd : N₀ ∈ done then
        match N₀, hP _ hd, hd, lf with
        | .up (.atom c), _, hd, .rel (.atomL (.stable s')) =>
            UpElim done hsat hP (hmConsDone hd hm)
              (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ)) hK hV qmem dmem
              ha hb hXpkg (lfP.wk (Sub.grow _)) s'
        | .imp (.atom c) Nc, _, hd, .impL s_c lf_c =>
            if hcp : c = p then
              UpElim done hsat hP hm hm2 hK hV qmem dmem ha hcp hXpkg lfP s_c
            else by
              obtain ⟨rest, hXr⟩ := splitAt done _ hd
              exact nOrAllIntro (qmem hXr) (by
                simp only [pGuard]; rw [if_neg hcp]
                refine .andR
                  (.stable (TStab done hsat hP hm hm2 hK hcp s_c)) ?_
                exact qAssembleN (interpE_eq hsat) (qimpConjMem hXr) hcp
                  (TStab done hsat hP hm hm2 hK hcp s_c)
                  (aMinF [Nc] rest _ (.up _)
                    (ParkedCtx.sub (splits_sub hXr) hP) hK
                    (fireClean (splitHyp hm hXr) (.stable
                      (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                        (.impL
                          ((hb.trans ha.symm) ▸
                            Stab.lfoc (List.mem_cons_self ..)
                              (lf_c.wk (Sub.grow _)))
                          (lfP.wk (Sub.grow _))))))))
        | .imp (.down (.imp Q' N')) N_d, _, hd, .impL s_d lf_d => by
            obtain ⟨rest, hXr⟩ := splitAt done _ hd
            exact nOrAllIntro (dmem hXr)
              (.andR
                (dykAntC done rest _ _ Q' N' N_d hsat hP hXr hm hm2 hK s_d)
                (dykAssembleN (interpE_eq hsat) (dykConjMem hXr)
                  (dykAntC done rest _ _ Q' N' N_d hsat hP hXr hm hm2 hK s_d)
                  (aMinF [N_d] rest _ (.up _)
                    (ParkedCtx.sub (splits_sub hXr) hP) hK
                    (fireClean (splitHyp hm hXr) (.stable
                      (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                        (.impL
                          ((hb.trans ha.symm) ▸
                            Stab.lfoc (List.mem_cons_self ..)
                              (lf_d.wk (Sub.grow _)))
                          (lfP.wk (Sub.grow _)))))))))
        | .up .fls, hpk, _, _ => nomatch hpk
        | .up (.or _ _), hpk, _, _ => nomatch hpk
        | .up (.down _), hpk, _, _ => nomatch hpk
        | .imp .fls _, hpk, _, _ => nomatch hpk
        | .imp (.or _ _) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.up _)) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.and _ _)) _, hpk, _, _ => nomatch hpk
        | .and _ _, hpk, _, _ => nomatch hpk
      else
        (nOrAll_eq _).symm ▸
          Inv.stable (.lfoc (List.mem_cons_of_mem _ ((hm _ h).resolve_left hd))
            (UpLF done hsat hP hm hm2 hK hV qmem dmem
              (hK _ ((hm _ h).resolve_left hd)) ha hb hXpkg lfP lf))
  termination_by Γ' K M P₀ L a b hm hm2 hK hV qmem dmem ha hb hXpkg lfP s =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf s)
  decreasing_by ljf_dec_a


/-- Left focus on a kept hypothesis, inside an `∀p`-mode `p`-proof. -/
def UpLF (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {L : List Neg} {H : Neg}
      {a b : String},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      interp p [] done (some (.up P₀)) = nOrAll L →
      (∀ {c : String} {Nc : Neg} {rest : List Neg},
        (Neg.imp (.atom c) Nc, rest) ∈ splits done →
        pGuard p c nBot (nAnd (.up (.atom c))
          (interp p [Nc] rest (some (.up P₀)))) ∈ L) →
      (∀ {Q' : Pos} {N' N : Neg} {rest : List Neg},
        (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
        nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
             (interp p [N] rest (some (.up P₀))) ∈ L) →
      PFreeN p H → a = p → b = p → Neg.imp (.atom a) M ∈ done →
      LFoc Γ' M P₀ →
      LFoc Γ' H (.atom b) → LFoc (interp p [] done none :: K) H (orChain L)
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, hH, ha, hb, hXpkg,
      lfP, .rel d =>
      .rel (UpInvG done hsat hP hm hm2 hK hV qmem dmem
        (PFreeΩ.cons hH PFreeΩ.nil) ha hb hXpkg lfP d)
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, hH, ha, hb, hXpkg,
      lfP, .impL s lf =>
      .impL (TStab done hsat hP hm hm2 hK hH.1 s)
            (UpLF done hsat hP hm hm2 hK hV qmem dmem hH.2 ha hb hXpkg lfP lf)
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, hH, ha, hb, hXpkg,
      lfP, .and1 lf =>
      .and1 (UpLF done hsat hP hm hm2 hK hV qmem dmem hH.1 ha hb hXpkg lfP lf)
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, hH, ha, hb, hXpkg,
      lfP, .and2 lf =>
      .and2 (UpLF done hsat hP hm hm2 hK hV qmem dmem hH.2 ha hb hXpkg lfP lf)
  termination_by Γ' K M P₀ L H a b hm hm2 hK hV qmem dmem hH ha hb hXpkg lfP lf =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf lf)
  decreasing_by ljf_dec_a


/-- Inversion inside an `∀p`-mode `p`-proof. -/
def UpInvG (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {L : List Neg} {Ω : List Pos}
      {a b : String},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      interp p [] done (some (.up P₀)) = nOrAll L →
      (∀ {c : String} {Nc : Neg} {rest : List Neg},
        (Neg.imp (.atom c) Nc, rest) ∈ splits done →
        pGuard p c nBot (nAnd (.up (.atom c))
          (interp p [Nc] rest (some (.up P₀)))) ∈ L) →
      (∀ {Q' : Pos} {N' N : Neg} {rest : List Neg},
        (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
        nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
             (interp p [N] rest (some (.up P₀))) ∈ L) →
      PFreeΩ p Ω → a = p → b = p → Neg.imp (.atom a) M ∈ done →
      LFoc Γ' M P₀ →
      Inv Γ' Ω (.up (.atom b)) →
      Inv (interp p [] done none :: K) Ω (.up (orChain L))
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, _, ha, hb, hXpkg,
      lfP, .stable s =>
      nOrAll_eq _ ▸
        UpElim done hsat hP hm hm2 hK hV qmem dmem ha hb hXpkg lfP s
  | _, _, _, _, _, .or PA PB :: _, _, _, hm, hm2, hK, hV, qmem, dmem, hΩ, ha, hb, hXpkg,
      lfP, .orL d₁ d₂ =>
      .orL (UpInvG done hsat hP hm hm2 hK hV qmem dmem
              (hΩ.tail.cons hΩ.head.1) ha hb hXpkg lfP d₁)
           (UpInvG done hsat hP hm hm2 hK hV qmem dmem
              (hΩ.tail.cons hΩ.head.2) ha hb hXpkg lfP d₂)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .flsL => .flsL
  | _, _, _, _, _, .down M₀ :: _, _, _, hm, hm2, hK, hV, qmem, dmem, hΩ, ha, hb, hXpkg,
      lfP, .downL d =>
      .downL (((UpInvG done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons hΩ.head hK) hV qmem dmem hΩ.tail ha hb hXpkg
          (lfP.wk (Sub.grow _)) d)).wk
        (fun Z hZ => by
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  | _, _, _, _, _, .atom c :: _, _, _, hm, hm2, hK, hV, qmem, dmem, hΩ, ha, hb, hXpkg,
      lfP, .atomL d =>
      .atomL (((UpInvG done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons (show PFreeN p (.up (.atom c)) from hΩ.head) hK)
          hV qmem dmem hΩ.tail ha hb hXpkg
          (lfP.wk (Sub.grow _)) d)).wk
        (fun Z hZ => by
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  termination_by Γ' K M P₀ L Ω a b hm hm2 hK hV qmem dmem hΩ ha hb hXpkg lfP d =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf d)
  decreasing_by ljf_dec_a


/-- The Dyckhoff antecedent dispatch, discharged: commute, interpolate at
the residual station, project the E-res conjunct. -/
def dykAntC : ∀ (done rest K Γ' : List Neg) (Q' : Pos) (N' N : Neg),
    Saturated done → ParkedCtx done →
    (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
    (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
    Stab Γ' .tru (.down (.imp Q' N')) →
    Inv (interp p [] done none :: K) [] .tru
        (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
  | done, rest, K, Γ', Q', N', N, hsat, hP, hXr, hm, hm2, hK, s =>
      simHyp
        (fl := fun hs lf =>
          .lfoc (hs _ (List.mem_cons_self ..))
            ((interpE_eq hsat).symm ▸ lfocAndAll (dykConjMem hXr) (.and2 lf)))
        (Sub.grow _)
        (aMinF [.imp (.down N') N] rest K (.imp Q' N')
          (ParkedCtx.sub (splits_sub hXr) hP) hK
          (dykCommute (p := p) hXr hm s))
  termination_by done rest K Γ' Q' N' N hsat hP hXr hm hm2 hK s =>
    (2 * sum3 [Neg.imp (Pos.down N') N] + sum3 rest +
      3 ^ wNeg (Neg.imp Q' N') + 5, 0)
  decreasing_by ljf_dec_a


end

/-- **SatE2, unconditional.** -/
def satE2 : SatE2 p := fun done Δ ψ hsat hP hΔ hψ d =>
  TInv done hsat hP (fun Z hZ => List.mem_append.mp hZ)
    (fun Z hZ => List.mem_append_left _ hZ) hΔ
    (fun _ h => absurd h (List.not_mem_nil)) hψ d

/-- **SatA2, unconditional.** -/
def satA2 : SatA2 p := fun done Δ G hsat hP hΔ d =>
  UEntry done hsat hP (fun Z hZ => List.mem_append.mp hZ)
    (fun Z hZ => List.mem_append_left _ hZ) hΔ G d

/-- **The Dyckhoff antecedent dispatch, as originally isolated.** -/
def dykAnt : DykAnt p :=
  fun done rest K Γ' Q' N' N hsat hP hXr hm hm2 hK s =>
    dykAntC done rest K Γ' Q' N' N hsat hP hXr hm hm2 hK s

end LJFO



/-! ## Standing test 1: the G4iLL blocker

`◯((◯p→r)→◯p), ◯p→r ⊢ r` — PLL-provable, G4iLL-unprovable — re-derived
inside LJF◯ itself, so every rebuild re-checks it.  Ported from
`wip/ljf-lax-blocker.lean` (which proved it for `PLLFocused`); the term is
unchanged: `laxOf` is never needed here, and the two left-focusings of
`◯p→r` are free because contexts are persistent. -/

namespace BlockerTest

variable (p r : String)

/-- `◯p`. -/
abbrev oP : Neg := .circ (.atom p)

/-- `◯p → r`. -/
abbrev hyp : Neg := .imp (.down (oP p)) (.up (.atom r))

/-- `(◯p→r) → ◯p`. -/
abbrev chi : Neg := .imp (.down (hyp p r)) (oP p)

/-- `◯((◯p→r)→◯p)`, as `◯(↓χ)`. -/
abbrev bchi : Neg := .circ (.down (chi p r))

/-- Continuation closing goal `r` once `↑r` is released from the focus. -/
def closeR {Γ : List Neg} {j : JD} : LFoc Γ (.up (.atom r)) j (.atom r) :=
  .rel (.atomL (.stable (.rfoc (.init (List.mem_cons_self ..)))))

/-- `Γ ⊢lax p` whenever `◯p ∈ Γ`. -/
def closeOP {Γ : List Neg} (h : oP p ∈ Γ) : Stab Γ .lax (.atom p) :=
  .lfoc h (.circL (.atomL (.stable (.rfoc (.init (List.mem_cons_self ..))))))

/-- `Γ ⊢tru ↓◯p` whenever `◯p ∈ Γ`. -/
def downOP {Γ : List Neg} (h : oP p ∈ Γ) : Stab Γ .tru (.down (oP p)) :=
  .rfoc (.rel (.circR (.stable (closeOP p h))))

/-- The inner sequent — the **second use** of `◯p→r`. -/
def innerR : Stab [oP p, chi p r, bchi p r, hyp p r] .tru (.atom r) :=
  .lfoc
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    (.impL (downOP p (List.mem_cons_self ..)) (closeR r))

/-- `χ, ◯χ′, ◯p→r ⊢tru ↓(◯p→r)`. -/
def argHyp : Stab [chi p r, bchi p r, hyp p r] .tru (.down (hyp p r)) :=
  .rfoc (.rel (.impR (.downL (.stable (innerR p r)))))

/-- The lax core `◯χ′, ◯p→r ⊢lax p`. -/
def laxCore : Stab [bchi p r, hyp p r] .lax (.atom p) :=
  .lfoc (List.mem_cons_self ..)
    (.circL (.downL (.stable
      (.lfoc (List.mem_cons_self ..)
        (.impL (argHyp p r)
          (.circL (.atomL (.stable (.rfoc (.init (List.mem_cons_self ..)))))))))))

/-- **The G4iLL blocker is LJF◯-derivable.** -/
def blocker : Stab [bchi p r, hyp p r] .tru (.atom r) :=
  .lfoc (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    (.impL (.rfoc (.rel (.circR (.stable (laxCore p r))))) (closeR r))

end BlockerTest

end LJFO

/-! ### Axiom audit -/

/-- info: 'LJFO.BlockerTest.blocker' does not depend on any axioms -/
#guard_msgs in
#print axioms LJFO.BlockerTest.blocker

/-- info: 'LJFO.idNeg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LJFO.idNeg

/-- info: 'LJFO.interp_pfree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LJFO.interp_pfree

/-- info: 'LJFO.eSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LJFO.eSound

/-- info: 'LJFO.aSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LJFO.aSound
