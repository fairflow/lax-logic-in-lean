/-
LJF◯ — the backward search skeleton (route (B), layer 3a).

The sequent type covering the four judgments and the backward
rule-instance enumerator `succs`: for a goal sequent, the list of rule
instances with that conclusion, each given as its premise list.  Pure
definitions — the soundness/completeness round-trip (which yields the
pigeonhole height bound, as `PLLG4Dec` does for G4c) is the next layer.
Zero imports beyond the frozen core.
-/
import LaxLogic.LJFOCore
import LaxLogic.LJFOHeight

namespace LJFO

/-- A sequent of any of the four judgments. -/
inductive LSeq where
  | stab (Γ : List Neg) (j : JD) (P : Pos)
  | rfocus (Γ : List Neg) (j : JD) (P : Pos)
  | lfoc (Γ : List Neg) (N : Neg) (j : JD) (P : Pos)
  | inv (Γ : List Neg) (Ω : List Pos) (j : JD) (C : Neg)
deriving DecidableEq

namespace LSeq

/-- The truth-to-lax coercion instances. -/
def laxInsts (Γ : List Neg) (j : JD) (P : Pos) : List (List LSeq) :=
  match j with
  | .lax => [[stab Γ .tru P]]
  | .tru => []

/-- Backward rule instances for a stable sequent: right focus, a left
focus per context member, and the truth-to-lax coercion at `lax`. -/
def succsStab (Γ : List Neg) (j : JD) (P : Pos) : List (List LSeq) :=
  [[rfocus Γ j P]] ++ Γ.map (fun N => [lfoc Γ N j P]) ++ laxInsts Γ j P

/-- Backward rule instances under right focus, by the positive's shape. -/
def succsRFocus (Γ : List Neg) (j : JD) : Pos → List (List LSeq)
  | .atom a => if Neg.up (Pos.atom a) ∈ Γ then [[]] else []
  | .fls => []
  | .or P Q => [[rfocus Γ j P], [rfocus Γ j Q]]
  | .down N => [[inv Γ [] j N]]

/-- The lax-only box-opening instances. -/
def circInsts (Γ : List Neg) (Q : Pos) (j : JD) (P : Pos) : List (List LSeq) :=
  match j with
  | .lax => [[inv Γ [Q] .lax (.up P)]]
  | .tru => []

/-- Backward rule instances under left focus, by the hypothesis's shape. -/
def succsLFoc (Γ : List Neg) (j : JD) (P : Pos) : Neg → List (List LSeq)
  | .up Q => [[inv Γ [Q] j (.up P)]]
  | .imp Q N => [[stab Γ .tru Q, lfoc Γ N j P]]
  | .and M N => [[lfoc Γ M j P], [lfoc Γ N j P]]
  | .circ Q => circInsts Γ Q j P

/-- The goal-driven inversion instances. -/
def goalInsts (Γ : List Neg) (Ω : List Pos) (C : Neg) (j : JD) : List (List LSeq) :=
  match C, j with
  | .imp Q N, .tru => [[inv Γ (Q :: Ω) .tru N]]
  | .and M N, .tru => [[inv Γ Ω .tru M, inv Γ Ω .tru N]]
  | .circ P, _ => [[inv Γ Ω .lax (.up P)]]
  | _, _ => []

/-- The stable-transition instance. -/
def stableInsts (Γ : List Neg) (Ω : List Pos) (C : Neg) (j : JD) : List (List LSeq) :=
  match Ω, C with
  | [], .up P => [[stab Γ j P]]
  | _, _ => []

/-- The `Ω`-head instances. -/
def omegaInsts (Γ : List Neg) (Ω : List Pos) (C : Neg) (j : JD) : List (List LSeq) :=
  match Ω with
  | [] => []
  | X :: Ω' =>
      match X with
      | .or P Q => [[inv Γ (P :: Ω') j C, inv Γ (Q :: Ω') j C]]
      | .fls => [[]]
      | .down M => [[inv (M :: Γ) Ω' j C]]
      | .atom a => [[inv (Neg.up (Pos.atom a) :: Γ) Ω' j C]]

/-- Backward rule instances in inversion. -/
def succsInv (Γ : List Neg) (Ω : List Pos) (j : JD) (C : Neg) :
    List (List LSeq) :=
  goalInsts Γ Ω C j ++ stableInsts Γ Ω C j ++ omegaInsts Γ Ω C j

/-- The enumerator. -/
def succs : LSeq → List (List LSeq)
  | stab Γ j P => succsStab Γ j P
  | rfocus Γ j P => succsRFocus Γ j P
  | lfoc Γ N j P => succsLFoc Γ j P N
  | inv Γ Ω j C => succsInv Γ Ω j C

end LSeq

/-- Derivability of a sequent, uniformly over the four judgments — the
target of the search round-trip. -/
def LSeq.holds : LSeq → Type
  | .stab Γ j P => Stab Γ j P
  | .rfocus Γ j P => RFocus Γ j P
  | .lfoc Γ N j P => LFoc Γ N j P
  | .inv Γ Ω j C => Inv Γ Ω j C

end LJFO

namespace LJFO
namespace LSeq

/-! ## Soundness of the enumerator: each instance replays its rule -/

/-- Singleton-membership elimination (the shape every one-instance rule
family produces). -/
theorem memSingle {α : Type} {a b : α} (h : a ∈ [b]) : a = b :=
  (List.mem_cons.mp h).resolve_right (fun hc => absurd hc (List.not_mem_nil))

/-- Premise packages: a derivation for every premise of the instance. -/
def Prems (ps : List LSeq) : Type := ∀ p ∈ ps, p.holds

def prems_head {p : LSeq} {ps : List LSeq} (k : Prems (p :: ps)) : p.holds :=
  k p (List.mem_cons_self ..)

def prems_tail {p : LSeq} {ps : List LSeq} (k : Prems (p :: ps)) : Prems ps :=
  fun q hq => k q (List.mem_cons_of_mem _ hq)

/-- Goal-driven inversion instances, factored for clean motives. -/
def invGoalSound : ∀ (Γ : List Neg) (Ω : List Pos) (C : Neg) (j : JD)
    (ps : List LSeq),
    ps ∈ goalInsts Γ Ω C j →
    Prems ps → Inv Γ Ω j C
  | Γ, Ω, .imp Q N, .tru, ps, hg, k =>
      have h1 : ps = [inv Γ (Q :: Ω) .tru N] :=
        memSingle hg
      by subst h1; exact Inv.impR (prems_head k)
  | Γ, Ω, .and M N, .tru, ps, hg, k =>
      have h1 : ps = [inv Γ Ω .tru M, inv Γ Ω .tru N] :=
        memSingle hg
      by subst h1; exact Inv.andR (prems_head k) (prems_head (prems_tail k))
  | Γ, Ω, .circ P, j, ps, hg, k =>
      have h1 : ps = [inv Γ Ω .lax (.up P)] :=
        memSingle hg
      by subst h1; exact Inv.circR (prems_head k)
  | _, _, .imp _ _, .lax, _, hg, _ => absurd hg (List.not_mem_nil)
  | _, _, .and _ _, .lax, _, hg, _ => absurd hg (List.not_mem_nil)
  | _, _, .up _, _, _, hg, _ => absurd hg (List.not_mem_nil)

/-- The stable-transition instance, factored. -/
def invStableSound : ∀ (Γ : List Neg) (Ω : List Pos) (C : Neg) (j : JD)
    (ps : List LSeq),
    ps ∈ stableInsts Γ Ω C j →
    Prems ps → Inv Γ Ω j C
  | Γ, [], .up P, j, ps, hs, k =>
      have h1 : ps = [stab Γ j P] :=
        memSingle hs
      by subst h1; exact Inv.stable (prems_head k)
  | _, [], .imp _ _, _, _, hs, _ => absurd hs (List.not_mem_nil)
  | _, [], .and _ _, _, _, hs, _ => absurd hs (List.not_mem_nil)
  | _, [], .circ _, _, _, hs, _ => absurd hs (List.not_mem_nil)
  | _, _ :: _, _, _, _, hs, _ => absurd hs (List.not_mem_nil)

/-- The `Ω`-head instances, factored. -/
def invOmegaSound : ∀ (Γ : List Neg) (Ω : List Pos) (C : Neg) (j : JD)
    (ps : List LSeq),
    ps ∈ omegaInsts Γ Ω C j →
    Prems ps → Inv Γ Ω j C
  | _, [], _, _, _, h3, _ => absurd h3 (List.not_mem_nil)
  | Γ, .or P Q :: Ω', C, j, ps, h3, k =>
      have h1 : ps = [inv Γ (P :: Ω') j C, inv Γ (Q :: Ω') j C] :=
        memSingle h3
      by subst h1; exact Inv.orL (prems_head k) (prems_head (prems_tail k))
  | Γ, .fls :: Ω', C, j, ps, h3, k =>
      have h1 : ps = [] :=
        memSingle h3
      by subst h1; exact Inv.flsL
  | Γ, .down M :: Ω', C, j, ps, h3, k =>
      have h1 : ps = [inv (M :: Γ) Ω' j C] :=
        memSingle h3
      by subst h1; exact Inv.downL (prems_head k)
  | Γ, .atom a :: Ω', C, j, ps, h3, k =>
      have h1 : ps = [inv (Neg.up (Pos.atom a) :: Γ) Ω' j C] :=
        memSingle h3
      by subst h1; exact Inv.atomL (prems_head k)

/-- The lax-coercion instance of the stable dispatch, factored. -/
def stabLaxSound : ∀ (Γ : List Neg) (j : JD) (P : Pos) (ps : List LSeq),
    ps ∈ laxInsts Γ j P →
    Prems ps → Stab Γ j P
  | Γ, .lax, P, ps, h4, k =>
      have h5 : ps = [stab Γ .tru P] :=
        memSingle h4
      by subst h5; exact Stab.laxOf (prems_head k)
  | _, .tru, _, _, h4, _ => absurd h4 (List.not_mem_nil)

/-- The lax-only box opening under left focus, factored. -/
def lfocCircSound : ∀ (Γ : List Neg) (Q : Pos) (j : JD) (P : Pos) (ps : List LSeq),
    ps ∈ circInsts Γ Q j P →
    Prems ps → LFoc Γ (.circ Q) j P
  | Γ, Q, .lax, P, ps, h, k =>
      have h1 : ps = [inv Γ [Q] .lax (.up P)] :=
        memSingle h
      by subst h1; exact LFoc.circL (prems_head k)
  | _, _, .tru, _, _, h, _ => absurd h (List.not_mem_nil)

/-- Each enumerated instance, given derivations of its premises, yields a
derivation of the conclusion. -/
def succs_sound : ∀ (s : LSeq) (ps : List LSeq), ps ∈ succs s → Prems ps → s.holds
  | stab Γ j P, ps, h, k =>
      if h1 : ps = [rfocus Γ j P] then by
        subst h1; exact Stab.rfoc (prems_head k)
      else
        have h2 := (List.mem_cons.mp h).resolve_left h1
        if h3 : ps ∈ Γ.map (fun N => [lfoc Γ N j P]) then
          let ⟨N, hN, hEq⟩ := memMapWitness _ _ _ h3
          have h5 : ps = [lfoc Γ N j P] := hEq.symm
          by subst h5; exact Stab.lfoc hN (prems_head k)
        else
          stabLaxSound Γ j P ps ((List.mem_append.mp h2).resolve_left h3) k
  | rfocus Γ j P, ps, h, k =>
      match P, h with
      | .atom a, h =>
          if hmem : Neg.up (Pos.atom a) ∈ Γ then
            have h5 : ps = [] := by
              simp only [succs, succsRFocus, if_pos hmem] at h
              simpa using h
            by subst h5; exact RFocus.init hmem
          else
            absurd (by simpa [succs, succsRFocus, if_neg hmem] using h) not_false
      | .or P Q, h =>
          if h1 : ps = [rfocus Γ j P] then by
            subst h1; exact RFocus.or1 (prems_head k)
          else
            have h2 : ps = [rfocus Γ j Q] :=
              List.mem_singleton.mp ((List.mem_cons.mp h).resolve_left h1)
            by subst h2; exact RFocus.or2 (prems_head k)
      | .down N, h =>
          have h1 : ps = [inv Γ [] j N] :=
            memSingle h
          by subst h1; exact RFocus.rel (prems_head k)
      | .fls, h => absurd h (List.not_mem_nil)
  | lfoc Γ N j P, ps, h, k =>
      match N, h with
      | .up Q, h =>
          have h1 : ps = [inv Γ [Q] j (.up P)] :=
            memSingle h
          by subst h1; exact LFoc.rel (prems_head k)
      | .imp Q M, h =>
          have h1 : ps = [stab Γ .tru Q, lfoc Γ M j P] :=
            memSingle h
          by subst h1; exact LFoc.impL (prems_head k) (prems_head (prems_tail k))
      | .and M₁ M₂, h =>
          if h1 : ps = [lfoc Γ M₁ j P] then by
            subst h1; exact LFoc.and1 (prems_head k)
          else
            have h2 : ps = [lfoc Γ M₂ j P] :=
              List.mem_singleton.mp ((List.mem_cons.mp h).resolve_left h1)
            by subst h2; exact LFoc.and2 (prems_head k)
      | .circ Q, h => lfocCircSound Γ Q j P ps h k
  | inv Γ Ω j C, ps, h, k =>
      if hg : ps ∈ goalInsts Γ Ω C j then
        invGoalSound Γ Ω C j ps hg k
      else
        if hs : ps ∈ stableInsts Γ Ω C j then
          invStableSound Γ Ω C j ps hs k
        else
          invOmegaSound Γ Ω C j ps
            ((List.mem_append.mp h).resolve_left
              (fun hAB => (List.mem_append.mp hAB).elim
                (fun ha => hg ha) (fun hb => hs hb))) k

end LSeq
end LJFO

namespace LJFO
namespace LSeq

/-! ## Completeness of the enumerator: every derivation's root rule is
an enumerated instance with held premises -/

def prems0 : Prems [] := fun _ hp => absurd hp (List.not_mem_nil)

def prems1 {p : LSeq} (d : p.holds) : Prems [p] := fun q hq =>
  have h : q = p := List.mem_singleton.mp hq
  by subst h; exact d

def prems2 {p q : LSeq} (d : p.holds) (e : q.holds) : Prems [p, q] := fun r hr =>
  if h : r = p then by subst h; exact d
  else
    have h2 : r = q :=
      List.mem_singleton.mp ((List.mem_cons.mp hr).resolve_left h)
    by subst h2; exact e

/-- The instance package: a premise list, its membership, and its
derivations. -/
def Inst (s : LSeq) : Type := Σ' ps : List LSeq, (ps ∈ succs s) ×' Prems ps

def succs_complete : ∀ (s : LSeq), s.holds → Inst s
  | stab Γ j P, d =>
      match d with
      | .rfoc r => ⟨[rfocus Γ j P], List.mem_cons_self .., prems1 r⟩
      | @Stab.lfoc _ _ _ N hN lf =>
          ⟨[lfoc Γ N j P],
           List.mem_append_left _ (List.mem_cons_of_mem _
             (List.mem_map_of_mem hN)),
           prems1 lf⟩
      | .laxOf s' =>
          ⟨[stab Γ .tru P],
           List.mem_append_right _ (List.mem_cons_self ..),
           prems1 s'⟩
  | rfocus Γ j P, d =>
      match P, d with
      | .atom a, .init hm =>
          ⟨[], by simp [succs, succsRFocus, if_pos hm], prems0⟩
      | .or P Q, .or1 r => ⟨[rfocus Γ j P], List.mem_cons_self .., prems1 r⟩
      | .or P Q, .or2 r =>
          ⟨[rfocus Γ j Q],
           List.mem_cons_of_mem _ (List.mem_cons_self ..), prems1 r⟩
      | .down N, .rel dI => ⟨[inv Γ [] j N], List.mem_cons_self .., prems1 dI⟩
  | lfoc Γ N j P, d =>
      match N, d with
      | .up Q, .rel dI => ⟨[inv Γ [Q] j (.up P)], List.mem_cons_self .., prems1 dI⟩
      | .imp Q M, .impL s lf =>
          ⟨[stab Γ .tru Q, lfoc Γ M j P], List.mem_cons_self .., prems2 s lf⟩
      | .and M₁ M₂, .and1 lf => ⟨[lfoc Γ M₁ j P], List.mem_cons_self .., prems1 lf⟩
      | .and M₁ M₂, .and2 lf =>
          ⟨[lfoc Γ M₂ j P],
           List.mem_cons_of_mem _ (List.mem_cons_self ..), prems1 lf⟩
      | .circ Q, .circL dI =>
          ⟨[inv Γ [Q] .lax (.up P)], List.mem_cons_self .., prems1 dI⟩
  | inv Γ Ω j C, d =>
      match d with
      | .impR dI =>
          ⟨_, List.mem_append_left _ (List.mem_append_left _
            (List.mem_cons_self ..)), prems1 dI⟩
      | .andR d₁ d₂ =>
          ⟨_, List.mem_append_left _ (List.mem_append_left _
            (List.mem_cons_self ..)), prems2 d₁ d₂⟩
      | .circR dI =>
          ⟨_, List.mem_append_left _ (List.mem_append_left _
            (List.mem_cons_self ..)), prems1 dI⟩
      | .stable s =>
          ⟨_, List.mem_append_left _ (List.mem_append_right _
            (List.mem_cons_self ..)), prems1 s⟩
      | .orL d₁ d₂ =>
          ⟨_, List.mem_append_right _ (List.mem_cons_self ..), prems2 d₁ d₂⟩
      | .flsL =>
          ⟨[], List.mem_append_right _ (List.mem_cons_self ..), prems0⟩
      | .downL dI =>
          ⟨_, List.mem_append_right _ (List.mem_cons_self ..), prems1 dI⟩
      | .atomL dI =>
          ⟨_, List.mem_append_right _ (List.mem_cons_self ..), prems1 dI⟩

end LSeq
end LJFO

namespace LJFO
namespace LSeq

/-! ## The fueled backward search

Depth-fueled: `search n s` succeeds when some enumerated instance's
premises all succeed at fuel `n`.  Soundness holds at every fuel;
completeness at sufficient fuel is the pigeonhole layer.  (The
visited-set refinement is introduced with the space bound; plain depth
fuel suffices for the sound direction and for the fuel-monotone
interface the interpolant recursion consumes.) -/

def search : Nat → LSeq → Bool
  | 0, _ => false
  | n+1, s => (succs s).any (fun ps => ps.all (fun p => search n p))

/-- Computable witness extraction from a successful `any`. -/
def anyWitness : ∀ (l : List (List LSeq)) (f : List LSeq → Bool),
    l.any f = true → Σ' ps : List LSeq, (ps ∈ l) ×' f ps = true
  | ps :: l, f, h =>
      if hf : f ps = true then ⟨ps, List.mem_cons_self .., hf⟩
      else
        have h' : l.any f = true := by
          have hor : f ps = true ∨ l.any f = true := by
            simpa [List.any_cons] using h
          exact hor.resolve_left hf
        let ⟨qs, hq, hfq⟩ := anyWitness l f h'
        ⟨qs, List.mem_cons_of_mem _ hq, hfq⟩

/-- Search is sound: a successful search rebuilds a derivation. -/
def search_sound : ∀ (n : Nat) (s : LSeq), search n s = true → s.holds
  | 0, _, h => absurd h (by simp [search])
  | n+1, s, h =>
      let ⟨ps, hmem, hall⟩ := anyWitness (succs s)
        (fun ps => ps.all (fun p => search n p))
        (by simpa [search] using h)
      succs_sound s ps hmem (fun p hp =>
        search_sound n p (by
          have h2 : ps.all (fun p => search n p) = true := by simpa using hall
          have h3 := List.all_eq_true.mp h2 p hp
          simpa using h3))

/-- Search is monotone in fuel. -/
theorem search_mono : ∀ {n m : Nat}, n ≤ m → ∀ {s : LSeq},
    search n s = true → search m s = true := by
  intro n m hnm
  induction n generalizing m with
  | zero => intro s h; simp [search] at h
  | succ k ih =>
      intro s h
      match m, hnm with
      | m+1, hnm =>
          simp only [search, List.any_eq_true] at h ⊢
          obtain ⟨ps, hmem, hall⟩ := h
          exact ⟨ps, hmem, by
            simp only [List.all_eq_true] at hall ⊢
            exact fun p hp => ih (Nat.le_of_succ_le_succ hnm) (hall p hp)⟩

end LSeq
end LJFO

namespace LJFO
namespace LSeq

/-! ## Completeness at existential fuel

Fuel equal to the derivation height suffices: the height-indexed
judgments feed the induction directly — no pigeonhole is needed for the
existential form of the round-trip. -/

/-- The height-indexed uniform judgment. -/
def holdsH : Nat → LSeq → Type
  | n, .stab Γ j P => StabH n Γ j P
  | n, .rfocus Γ j P => RFocusH n Γ j P
  | n, .lfoc Γ N j P => LFocH n Γ N j P
  | n, .inv Γ Ω j C => InvH n Γ Ω j C

/-- Premise packagers for the height-indexed instances. -/
def premsH0 {n : Nat} : ∀ q ∈ ([] : List LSeq), holdsH n q :=
  fun _ hq => absurd hq (List.not_mem_nil)

def premsH1 {n : Nat} {p : LSeq} (d : holdsH n p) : ∀ q ∈ [p], holdsH n q :=
  fun q hq => by have h := memSingle hq; subst h; exact d

def premsH2 {n : Nat} {p q : LSeq} (d : holdsH n p) (e : holdsH n q) :
    ∀ r ∈ [p, q], holdsH n r :=
  fun r hr =>
    if h : r = p then by subst h; exact d
    else by
      have h2 := memSingle ((List.mem_cons.mp hr).resolve_left h)
      subst h2; exact e

/-- `succs_complete`, height-indexed: the root instance's premises hold
one level down. -/
def succs_completeH : ∀ (n : Nat) (s : LSeq), holdsH (n+1) s →
    Σ' ps : List LSeq, (ps ∈ succs s) ×' (∀ p ∈ ps, holdsH n p)
  | n, .stab Γ j P, d =>
      match d with
      | .rfoc r => ⟨[.rfocus Γ j P], List.mem_cons_self ..,
          premsH1 r⟩
      | @StabH.lfoc _ _ _ _ N hN lf =>
          ⟨[.lfoc Γ N j P],
           List.mem_append_left _ (List.mem_cons_of_mem _
             (List.mem_map_of_mem hN)),
           premsH1 lf⟩
      | .laxOf s' =>
          ⟨[.stab Γ .tru P],
           List.mem_append_right _ (List.mem_cons_self ..),
           fun p hp => by
             have h := List.mem_singleton.mp hp; subst h; exact s'⟩
  | n, .rfocus Γ j P, d =>
      match P, d with
      | .atom a, .init hm =>
          ⟨[], by simp [succs, succsRFocus, if_pos hm],
           premsH0⟩
      | .or P Q, .or1 r =>
          ⟨[.rfocus Γ j P], List.mem_cons_self ..,
           premsH1 r⟩
      | .or P Q, .or2 r =>
          ⟨[.rfocus Γ j Q], List.mem_cons_of_mem _ (List.mem_cons_self ..),
           premsH1 r⟩
      | .down N, .rel dI =>
          ⟨[.inv Γ [] j N], List.mem_cons_self ..,
           premsH1 dI⟩
  | n, .lfoc Γ N j P, d =>
      match N, d with
      | .up Q, .rel dI =>
          ⟨[.inv Γ [Q] j (.up P)], List.mem_cons_self ..,
           premsH1 dI⟩
      | .imp Q M, .impL s lf =>
          ⟨[.stab Γ .tru Q, .lfoc Γ M j P], List.mem_cons_self ..,
           premsH2 s lf⟩
      | .and M₁ M₂, .and1 lf =>
          ⟨[.lfoc Γ M₁ j P], List.mem_cons_self ..,
           premsH1 lf⟩
      | .and M₁ M₂, .and2 lf =>
          ⟨[.lfoc Γ M₂ j P], List.mem_cons_of_mem _ (List.mem_cons_self ..),
           premsH1 lf⟩
      | .circ Q, .circL dI =>
          ⟨[.inv Γ [Q] .lax (.up P)], List.mem_cons_self ..,
           premsH1 dI⟩
  | n, .inv Γ Ω j C, d =>
      match d with
      | .impR dI =>
          ⟨_, List.mem_append_left _ (List.mem_append_left _
            (List.mem_cons_self ..)),
           premsH1 dI⟩
      | @InvH.andR _ _ _ M N d₁ d₂ =>
          ⟨_, List.mem_append_left _ (List.mem_append_left _
            (List.mem_cons_self ..)),
           premsH2 d₁ d₂⟩
      | .circR dI =>
          ⟨_, List.mem_append_left _ (List.mem_append_left _
            (List.mem_cons_self ..)),
           premsH1 dI⟩
      | .stable s =>
          ⟨_, List.mem_append_left _ (List.mem_append_right _
            (List.mem_cons_self ..)),
           premsH1 s⟩
      | @InvH.orL _ _ Ω₀ _ P₀ Q₀ C₀ d₁ d₂ =>
          ⟨_, List.mem_append_right _ (List.mem_cons_self ..),
           premsH2 d₁ d₂⟩
      | .flsL =>
          ⟨[], List.mem_append_right _ (List.mem_cons_self ..),
           premsH0⟩
      | .downL dI =>
          ⟨_, List.mem_append_right _ (List.mem_cons_self ..),
           premsH1 dI⟩
      | .atomL dI =>
          ⟨_, List.mem_append_right _ (List.mem_cons_self ..),
           premsH1 dI⟩

/-- Completeness at fuel = height. -/
theorem search_complete_h : ∀ (n : Nat) (s : LSeq), holdsH n s →
    search n s = true := by
  intro n
  induction n with
  | zero =>
      intro s d
      cases s <;> exact nomatch d
  | succ k ih =>
      intro s d
      obtain ⟨ps, hmem, hprem⟩ := succs_completeH k s d
      simp only [search, List.any_eq_true]
      exact ⟨ps, hmem, by
        simp only [List.all_eq_true]
        exact fun p hp => ih p (hprem p hp)⟩

/-- The round-trip at existential fuel: derivable iff searchable. -/
def search_complete {s : LSeq} (d : s.holds) : Σ' n, search n s = true :=
  match s, d with
  | .stab _ _ _, d => let ⟨n, dh⟩ := Stab.toH d; ⟨n, search_complete_h n _ dh⟩
  | .rfocus _ _ _, d => let ⟨n, dh⟩ := RFocus.toH d; ⟨n, search_complete_h n _ dh⟩
  | .lfoc _ _ _ _, d => let ⟨n, dh⟩ := LFoc.toH d; ⟨n, search_complete_h n _ dh⟩
  | .inv _ _ _ _, d => let ⟨n, dh⟩ := Inv.toH d; ⟨n, search_complete_h n _ dh⟩

end LSeq
end LJFO
