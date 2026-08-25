/-
LJF◯ — height-indexed judgments (route (B) infrastructure, layer 1).

The first layer of the roadmap's item-1 discipline transposed to the
focused calculus: the four judgments indexed by a height bound, monotone
in the bound, and equivalent to the unindexed forms.  This is the
`G4sh`-analogue (`PLLG4Dec.lean`) for LJF◯; the pigeonhole/collapse layer
and the fuel-founded interpolant recursion build on it.  Purely additive:
imports the frozen core, touches nothing.
-/
import LJF.OCore

namespace LJFO

/-! ## The height-indexed calculus

Each constructor raises the bound by one; `H`-judgments at bound `n` embed
into every larger bound (`mono`), and the unindexed judgments are exactly
the union over bounds (`toH`/`ofH`).  Mirrors the `Stab`/`RFocus`/`LFoc`/
`Inv` mutual verbatim. -/

mutual

inductive StabH : Nat → List Neg → JD → Pos → Type
  | rfoc {n Γ j P} : RFocusH n Γ j P → StabH (n+1) Γ j P
  | lfoc {n Γ j P N} (h : N ∈ Γ) : LFocH n Γ N j P → StabH (n+1) Γ j P
  | laxOf {n Γ P} : StabH n Γ .tru P → StabH (n+1) Γ .lax P

inductive RFocusH : Nat → List Neg → JD → Pos → Type
  | init {n Γ j a} (h : Neg.up (Pos.atom a) ∈ Γ) : RFocusH (n+1) Γ j (.atom a)
  | or1 {n Γ j P Q} : RFocusH n Γ j P → RFocusH (n+1) Γ j (.or P Q)
  | or2 {n Γ j P Q} : RFocusH n Γ j Q → RFocusH (n+1) Γ j (.or P Q)
  | rel {n Γ j N} : InvH n Γ [] j N → RFocusH (n+1) Γ j (.down N)

inductive LFocH : Nat → List Neg → Neg → JD → Pos → Type
  | rel {n Γ j Q P} : InvH n Γ [Q] j (.up P) → LFocH (n+1) Γ (.up Q) j P
  | impL {n Γ j Q N P} : StabH n Γ .tru Q → LFocH n Γ N j P →
      LFocH (n+1) Γ (.imp Q N) j P
  | and1 {n Γ j M N P} : LFocH n Γ M j P → LFocH (n+1) Γ (.and M N) j P
  | and2 {n Γ j M N P} : LFocH n Γ N j P → LFocH (n+1) Γ (.and M N) j P
  | circL {n Γ Q P} : InvH n Γ [Q] .lax (.up P) → LFocH (n+1) Γ (.circ Q) .lax P

inductive InvH : Nat → List Neg → List Pos → JD → Neg → Type
  | impR {n Γ Ω Q N} : InvH n Γ (Q :: Ω) .tru N → InvH (n+1) Γ Ω .tru (.imp Q N)
  | andR {n Γ Ω M N} : InvH n Γ Ω .tru M → InvH n Γ Ω .tru N →
      InvH (n+1) Γ Ω .tru (.and M N)
  | circR {n Γ Ω j P} : InvH n Γ Ω .lax (.up P) → InvH (n+1) Γ Ω j (.circ P)
  | stable {n Γ j P} : StabH n Γ j P → InvH (n+1) Γ [] j (.up P)
  | orL {n Γ Ω j P Q N} : InvH n Γ (P :: Ω) j N → InvH n Γ (Q :: Ω) j N →
      InvH (n+1) Γ (.or P Q :: Ω) j N
  | flsL {n Γ Ω j N} : InvH (n+1) Γ (.fls :: Ω) j N
  | downL {n Γ Ω j M N} : InvH n (M :: Γ) Ω j N → InvH (n+1) Γ (.down M :: Ω) j N
  | atomL {n Γ Ω j a N} : InvH n (.up (.atom a) :: Γ) Ω j N →
      InvH (n+1) Γ (.atom a :: Ω) j N

end

/-! ## Monotonicity in the bound -/

mutual

def StabH.mono : ∀ {n m : Nat} {Γ j P}, n ≤ m → StabH n Γ j P → StabH m Γ j P
  | _, m+1, _, _, _, h, .rfoc r => .rfoc (r.mono (Nat.le_of_succ_le_succ h))
  | _, m+1, _, _, _, h, .lfoc hm lf => .lfoc hm (lf.mono (Nat.le_of_succ_le_succ h))
  | _, m+1, _, _, _, h, .laxOf s => .laxOf (s.mono (Nat.le_of_succ_le_succ h))
  | _, 0, _, _, _, h, .rfoc _ => absurd h (by omega)
  | _, 0, _, _, _, h, .lfoc _ _ => absurd h (by omega)
  | _, 0, _, _, _, h, .laxOf _ => absurd h (by omega)

def RFocusH.mono : ∀ {n m : Nat} {Γ j P}, n ≤ m → RFocusH n Γ j P → RFocusH m Γ j P
  | _, m+1, _, _, _, _, .init hm => .init hm
  | _, 0, _, _, _, h, .init _ => absurd h (by omega)
  | _, m+1, _, _, _, h, .or1 r => .or1 (r.mono (Nat.le_of_succ_le_succ h))
  | _, m+1, _, _, _, h, .or2 r => .or2 (r.mono (Nat.le_of_succ_le_succ h))
  | _, m+1, _, _, _, h, .rel d => .rel (d.mono (Nat.le_of_succ_le_succ h))
  | _, 0, _, _, _, h, .or1 _ => absurd h (by omega)
  | _, 0, _, _, _, h, .or2 _ => absurd h (by omega)
  | _, 0, _, _, _, h, .rel _ => absurd h (by omega)

def LFocH.mono : ∀ {n m : Nat} {Γ N j P}, n ≤ m → LFocH n Γ N j P → LFocH m Γ N j P
  | _, m+1, _, _, _, _, h, .rel d => .rel (d.mono (Nat.le_of_succ_le_succ h))
  | _, m+1, _, _, _, _, h, .impL s lf =>
      .impL (s.mono (Nat.le_of_succ_le_succ h)) (lf.mono (Nat.le_of_succ_le_succ h))
  | _, m+1, _, _, _, _, h, .and1 lf => .and1 (lf.mono (Nat.le_of_succ_le_succ h))
  | _, m+1, _, _, _, _, h, .and2 lf => .and2 (lf.mono (Nat.le_of_succ_le_succ h))
  | _, m+1, _, _, _, _, h, .circL d => .circL (d.mono (Nat.le_of_succ_le_succ h))
  | _, 0, _, _, _, _, h, .rel _ => absurd h (by omega)
  | _, 0, _, _, _, _, h, .impL _ _ => absurd h (by omega)
  | _, 0, _, _, _, _, h, .and1 _ => absurd h (by omega)
  | _, 0, _, _, _, _, h, .and2 _ => absurd h (by omega)
  | _, 0, _, _, _, _, h, .circL _ => absurd h (by omega)

def InvH.mono : ∀ {n m : Nat} {Γ Ω j C}, n ≤ m → InvH n Γ Ω j C → InvH m Γ Ω j C
  | _, m+1, _, _, _, _, h, .impR d => .impR (d.mono (Nat.le_of_succ_le_succ h))
  | _, m+1, _, _, _, _, h, .andR d e =>
      .andR (d.mono (Nat.le_of_succ_le_succ h)) (e.mono (Nat.le_of_succ_le_succ h))
  | _, m+1, _, _, _, _, h, .circR d => .circR (d.mono (Nat.le_of_succ_le_succ h))
  | _, m+1, _, _, _, _, h, .stable s => .stable (s.mono (Nat.le_of_succ_le_succ h))
  | _, m+1, _, _, _, _, h, .orL d e =>
      .orL (d.mono (Nat.le_of_succ_le_succ h)) (e.mono (Nat.le_of_succ_le_succ h))
  | _, m+1, _, _, _, _, _, .flsL => .flsL
  | _, 0, _, _, _, _, h, .flsL => absurd h (by omega)
  | _, m+1, _, _, _, _, h, .downL d => .downL (d.mono (Nat.le_of_succ_le_succ h))
  | _, m+1, _, _, _, _, h, .atomL d => .atomL (d.mono (Nat.le_of_succ_le_succ h))
  | _, 0, _, _, _, _, h, .impR _ => absurd h (by omega)
  | _, 0, _, _, _, _, h, .andR _ _ => absurd h (by omega)
  | _, 0, _, _, _, _, h, .circR _ => absurd h (by omega)
  | _, 0, _, _, _, _, h, .stable _ => absurd h (by omega)
  | _, 0, _, _, _, _, h, .orL _ _ => absurd h (by omega)
  | _, 0, _, _, _, _, h, .downL _ => absurd h (by omega)
  | _, 0, _, _, _, _, h, .atomL _ => absurd h (by omega)

end

/-! ## Equivalence with the unindexed calculus -/

mutual

def Stab.toH : ∀ {Γ j P}, Stab Γ j P → Σ' n, StabH n Γ j P
  | _, _, _, .rfoc r => let ⟨n, r'⟩ := r.toH; ⟨n+1, .rfoc r'⟩
  | _, _, _, .lfoc h lf => let ⟨n, lf'⟩ := lf.toH; ⟨n+1, .lfoc h lf'⟩
  | _, _, _, .laxOf s => let ⟨n, s'⟩ := s.toH; ⟨n+1, .laxOf s'⟩

def RFocus.toH : ∀ {Γ j P}, RFocus Γ j P → Σ' n, RFocusH n Γ j P
  | _, _, _, .init h => ⟨1, .init h⟩
  | _, _, _, .or1 r => let ⟨n, r'⟩ := r.toH; ⟨n+1, .or1 r'⟩
  | _, _, _, .or2 r => let ⟨n, r'⟩ := r.toH; ⟨n+1, .or2 r'⟩
  | _, _, _, .rel d => let ⟨n, d'⟩ := d.toH; ⟨n+1, .rel d'⟩

def LFoc.toH : ∀ {Γ N j P}, LFoc Γ N j P → Σ' n, LFocH n Γ N j P
  | _, _, _, _, .rel d => let ⟨n, d'⟩ := d.toH; ⟨n+1, .rel d'⟩
  | _, _, _, _, .impL s lf =>
      let ⟨n₁, s'⟩ := s.toH; let ⟨n₂, lf'⟩ := lf.toH
      ⟨(max n₁ n₂)+1, .impL (s'.mono (Nat.le_max_left ..)) (lf'.mono (Nat.le_max_right ..))⟩
  | _, _, _, _, .and1 lf => let ⟨n, lf'⟩ := lf.toH; ⟨n+1, .and1 lf'⟩
  | _, _, _, _, .and2 lf => let ⟨n, lf'⟩ := lf.toH; ⟨n+1, .and2 lf'⟩
  | _, _, _, _, .circL d => let ⟨n, d'⟩ := d.toH; ⟨n+1, .circL d'⟩

def Inv.toH : ∀ {Γ Ω j C}, Inv Γ Ω j C → Σ' n, InvH n Γ Ω j C
  | _, _, _, _, .impR d => let ⟨n, d'⟩ := d.toH; ⟨n+1, .impR d'⟩
  | _, _, _, _, .andR d e =>
      let ⟨n₁, d'⟩ := d.toH; let ⟨n₂, e'⟩ := e.toH
      ⟨(max n₁ n₂)+1, .andR (d'.mono (Nat.le_max_left ..)) (e'.mono (Nat.le_max_right ..))⟩
  | _, _, _, _, .circR d => let ⟨n, d'⟩ := d.toH; ⟨n+1, .circR d'⟩
  | _, _, _, _, .stable s => let ⟨n, s'⟩ := s.toH; ⟨n+1, .stable s'⟩
  | _, _, _, _, .orL d e =>
      let ⟨n₁, d'⟩ := d.toH; let ⟨n₂, e'⟩ := e.toH
      ⟨(max n₁ n₂)+1, .orL (d'.mono (Nat.le_max_left ..)) (e'.mono (Nat.le_max_right ..))⟩
  | _, _, _, _, .flsL => ⟨1, .flsL⟩
  | _, _, _, _, .downL d => let ⟨n, d'⟩ := d.toH; ⟨n+1, .downL d'⟩
  | _, _, _, _, .atomL d => let ⟨n, d'⟩ := d.toH; ⟨n+1, .atomL d'⟩

end

mutual

def StabH.ofH : ∀ {n Γ j P}, StabH n Γ j P → Stab Γ j P
  | _, _, _, _, .rfoc r => .rfoc r.ofH
  | _, _, _, _, .lfoc h lf => .lfoc h lf.ofH
  | _, _, _, _, .laxOf s => .laxOf s.ofH

def RFocusH.ofH : ∀ {n Γ j P}, RFocusH n Γ j P → RFocus Γ j P
  | _, _, _, _, .init h => .init h
  | _, _, _, _, .or1 r => .or1 r.ofH
  | _, _, _, _, .or2 r => .or2 r.ofH
  | _, _, _, _, .rel d => .rel d.ofH

def LFocH.ofH : ∀ {n Γ N j P}, LFocH n Γ N j P → LFoc Γ N j P
  | _, _, _, _, _, .rel d => .rel d.ofH
  | _, _, _, _, _, .impL s lf => .impL s.ofH lf.ofH
  | _, _, _, _, _, .and1 lf => .and1 lf.ofH
  | _, _, _, _, _, .and2 lf => .and2 lf.ofH
  | _, _, _, _, _, .circL d => .circL d.ofH

def InvH.ofH : ∀ {n Γ Ω j C}, InvH n Γ Ω j C → Inv Γ Ω j C
  | _, _, _, _, _, .impR d => .impR d.ofH
  | _, _, _, _, _, .andR d e => .andR d.ofH e.ofH
  | _, _, _, _, _, .circR d => .circR d.ofH
  | _, _, _, _, _, .stable s => .stable s.ofH
  | _, _, _, _, _, .orL d e => .orL d.ofH e.ofH
  | _, _, _, _, _, .flsL => .flsL
  | _, _, _, _, _, .downL d => .downL d.ofH
  | _, _, _, _, _, .atomL d => .atomL d.ofH

end

/-- The unindexed judgment is the union over bounds. -/
def stab_iff_h {Γ j P} : Stab Γ j P → Σ' n, StabH n Γ j P := Stab.toH

end LJFO
