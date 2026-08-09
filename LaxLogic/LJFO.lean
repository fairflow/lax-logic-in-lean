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
        | .circ Q =>
            nOrAll ([interp p [] done (some (.up Q))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ Q))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ Q)))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ Q)))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ Q)))
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

/- **The interpolant never mentions `p`.**  Every clause either keeps `p` out
by construction, or is guarded by the `a == p` test that replaces the would-be
conjunct or disjunct by its unit.
TEMPORARILY DISABLED for the probe-file cycle: to be restored
with the modal cases once `interp` is frozen in the olean.
theorem interp_pfree (p : String) :
    ∀ (todo done : List Neg) (g : Option Neg), PFreeN p (interp p todo done g) := by
  intro todo done g
  fun_induction interp p todo done g with
  | case1 => assumption
  | case2 => exact pfree_nBot
  | case3 => exact pfree_nTop
  | case4 =>
      rename_i ih
      apply pfree_nOrAll
      intro x hx
      simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨b, hb⟩, rfl⟩ := hx
      exact ih b hb
  | case5 =>
      rename_i ih2 ih1
      apply pfree_nAndAll
      intro x hx
      simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨b, hb⟩, rfl⟩ := hx
      refine ⟨?_, ?_⟩ <;>
        first | exact ih1 b hb | exact ih2 b | exact ih1 b | exact ih2 b hb
  | case6 => assumption
  | case7 => assumption
  | case8 => assumption
  | case9 => assumption
  | case10 => assumption
  | case11 => assumption
  | case12 => assumption
  | case13 => assumption
  | case14 => assumption
  | case15 =>
      rename_i ih4 ih3 ih2 ih1
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
              exact pfree_pGuard pfree_nTop
                (fun h => ⟨h, by
                  first
                  | exact ih4 rest a N hXr
                  | exact ih3 rest a N hXr
                  | exact ih2 rest a N hXr
                  | exact ih1 rest a N hXr⟩)
          | fls => exact pfree_nTop
          | or _ _ => exact pfree_nTop
          | down M =>
              cases M with
              | up _ => exact pfree_nTop
              | and _ _ => exact pfree_nTop
              | imp Q' N' =>
                  refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
                    first
                    | exact ih1 rest Q' N' N hXr
                    | exact ih2 rest Q' N' N hXr
                    | exact ih3 rest Q' N' N hXr
                    | exact ih4 rest Q' N' N hXr
      | and _ _ => exact pfree_nTop
  | case16 =>
      rename_i ih2 ih1
      apply pfree_nAndAll
      intro x hx
      simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨b, hb⟩, rfl⟩ := hx
      refine ⟨?_, ?_⟩ <;>
        first | exact ih1 b hb | exact ih2 b | exact ih1 b | exact ih2 b hb
  | case17 => exact ⟨by assumption, by assumption⟩
  | case18 => exact pfree_nTop
  | case19 =>
      rename_i q hq ih3 ih2 ih1
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
                exact pfree_pGuard pfree_nBot
                  (fun h => pfree_nAnd h (ih3 rest a N hXr))
            | fls => exact pfree_nBot
            | or _ _ => exact pfree_nBot
            | down M =>
                cases M with
                | up _ => exact pfree_nBot
                | and _ _ => exact pfree_nBot
                | imp Q' N' =>
                    exact pfree_nAnd (ih2 rest Q' N' N hXr) (ih1 rest Q' N' N hXr)
        | and _ _ => exact pfree_nBot
  | case20 =>
      rename_i ih3 ih2 ih1
      apply pfree_nOrAll
      intro x hx
      simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
      cases X with
      | up P => cases P <;> exact pfree_nBot
      | imp Q N =>
          cases Q with
          | atom a =>
              exact pfree_pGuard pfree_nBot
                (fun h => pfree_nAnd h (ih3 rest a N hXr))
          | fls => exact pfree_nBot
          | or _ _ => exact pfree_nBot
          | down M =>
              cases M with
              | up _ => exact pfree_nBot
              | and _ _ => exact pfree_nBot
              | imp Q' N' =>
                  exact pfree_nAnd (ih2 rest Q' N' N hXr) (ih1 rest Q' N' N hXr)
      | and _ _ => exact pfree_nBot
  | case21 =>
      rename_i ihP ihQ ih3 ih2 ih1
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
                exact pfree_pGuard pfree_nBot
                  (fun h => pfree_nAnd h (ih3 rest a N hXr))
            | fls => exact pfree_nBot
            | or _ _ => exact pfree_nBot
            | down M =>
                cases M with
                | up _ => exact pfree_nBot
                | and _ _ => exact pfree_nBot
                | imp Q' N' =>
                    exact pfree_nAnd (ih2 rest Q' N' N hXr) (ih1 rest Q' N' N hXr)
        | and _ _ => exact pfree_nBot
  | case22 =>
      rename_i ihM ih3 ih2 ih1
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
                exact pfree_pGuard pfree_nBot
                  (fun h => pfree_nAnd h (ih3 rest a N hXr))
            | fls => exact pfree_nBot
            | or _ _ => exact pfree_nBot
            | down M =>
                cases M with
                | up _ => exact pfree_nBot
                | and _ _ => exact pfree_nBot
                | imp Q' N' =>
                    exact pfree_nAnd (ih2 rest Q' N' N hXr) (ih1 rest Q' N' N hXr)
        | and _ _ => exact pfree_nBot

/-! ## The contract that remains

With `interp` total and `interp_pfree` proved, the components of the Σ-type
are in place: the formula, built by the clauses, and its `p`-freeness.  The
characteristic properties are the remaining obligations, stated as the
contract for the next stretch — all four internal to `LJF`, none touching
another calculus:

* **(E1) soundness of `∃p`**:
  `Inv (todo ++ done) [] (interp p todo done none)`
* **(A1) soundness of `∀p`**:
  `Inv (interp p todo done (some G) :: todo ++ done) [] G`
* **(E2) minimality of `∃p`**: for `p`-free `Δ` and `ψ`,
  `Inv (todo ++ done ++ Δ) [] ψ  →  Inv (interp p todo done none :: Δ) [] ψ`
* **(A2) minimality of `∀p`**: for `p`-free `Δ`,
  `Inv (todo ++ done ++ Δ) [] G  →
     Inv (interp p todo done none :: Δ) [] (interp p todo done (some G))`

**Status (2026-08-09, final)**: E1 and A1 are `eSound`/`aSound`, proved
unconditionally in Part 4.  E2 and A2 are `eMinF`/`aMinF` in Part 6, proved
unconditionally — the saturated case is discharged inline, and the
statements `SatE2`/`SatA2` naming it are discharged as `satE2`/`satA2`.  The minimality analysis also
forced the E-guards on the two branching `∀p` clauses of `interp`.

The toolkit they need, also internal: a hypothesis-simulation traversal
(replace uses of one hypothesis by a derived simulator — powers E1/A1 and the
easy inversion directions of E2/A2), and branch extraction
(`Inv Δ (P :: Ω) C → ∀ b ∈ invertPos P, Inv (b ++ Δ) Ω C`, from the
determinism of the inversion phase).  The one expected mountain is the
`E2`/`A2` case for the Dyckhoff implication — the focused form of the
`(A⊃B)⊃C` argument; if it resists, it is to be carried as an explicit
hypothesis, never a `sorry`. -/​


/-! # Part 3: the toolkit for the characteristic properties

Six tools, each internal to `LJF`, each structural, none using cut:

* `routeStab` — CPS re-targeting of a stable proof of a positive `P`: every
  right focus on `P` is handed to a continuation, every left-focus chain and
  goal-side inversion is rebuilt with the new target.  Its instances do the
  work classically assigned to cut: shift release, disjunction routing,
  ex falso from a provable `⊥`.
* `invBranches` — realise `invertPos` on the left: branch derivations
  assemble into the inversion of the positive.
* `extract` — the converse, at any position of `Ω`: the inversion phase is
  deterministic, so a pending positive can be replayed along any one branch.
* `stableFire` — fire a shifted hypothesis `↑R` at a stable sequent, given
  stable continuations for every branch of `R`.
* `upMerge` — eliminate a shifted hypothesis into a negative goal, by
  recursion on the goal; the leaf case is `stableFire`.
* `simStab` — hypothesis simulation: replace every use of one hypothesis
  `H` by derivations manufactured on the other side.  The `init` uses of an
  atomic `H` reduce to left-focus uses via `idPos`, so one handler covers
  everything.
-/​

/-! ## Routing a positive conclusion -/​

-/

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
