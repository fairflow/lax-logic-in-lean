import LaxLogic.PLL.SubTab.Translate
import ProofTools.Explore.Certify
import ProofTools.Audit.FileBound

/-!
# The subframe tableau as a proof system of `ProofTools.Explore`

2026-11-19.  The generic proof explorer of `proof-tools` asks an instance
for a type of judgments, a type of moves and one function:

    STab.Judg = SSeq                    a signed sequent at one world
    STab.Move = Move                    the twelve rules, each named by its formulas
    STab.step m s                       the premises of the rule at `s`, or why it does not apply

Nothing of the tableau is changed.  A move is a constructor of `TCert`
without its subtrees, and `step` asks what `check` asks and leaves the
sequents `check` goes on to (`Move.rule`).

**The statements** (PROVED here, within `[propext, Quot.sound]`):

    (m.rule s).ok = true → Forall₂ (check · · = true) (m.rule s).prems cs →
      check s (m.cert cs) = true                                       (check_cert_of)
    STab.Sound (fun s => ∃ c, check s c = true)                        (sound)
    check s (cert d) = true                    for d : Der STab s      (check_cert)
    cert (ofCert c s h) = c                                            (cert_ofCert)
    Der.mapOut soundND d = derive_gl (cert d) s.isS s.ant s.suc (check_cert d)
                                                                        (mapOut_eq)
    Der STab ⟨false, [], [φ]⟩ → Holds φ                                (holds_of_der)
    (∃ ls, derives STab ⟨false, [], [φ]⟩ ls = true) ∨ (∃ m, no.check φ m = true)
                                                                        (complete_script)

and a definition, the moves' soundness for natural deduction as data (the
library's `SoundT`; `ND s` is `s.ant ⊢ gl s.isS s.suc`, the reading of `s`):

    soundND : STab.SoundT ND
            = ∀ m s ps, STab.step m s = .ok ps → Each ND ps → ND s

So a derivation in the explorer's sense and a closed tableau are the same
thing, each computed from the other (`cert`, `ofCert`).  A derivation gives
its natural-deduction derivation by the library's map out at `soundND`
(`derivation`, `term`): each move is a rule of `Translate.lean`, applied,
with no closed tableau in between; by `mapOut_eq` it is the derivation
`deriveOf` computes from the closed tableau, which is how `derivation` and
`term` were defined until 2026-11-22.  An attempt with open goals is, the
same way, a derived rule of natural deduction (`Att.mapOut soundND`).  And
a script is a certificate of provability, with the tableau's completeness
carried over: every formula has a script that `derives` accepts or a finite
subframe countermodel.

What the library then gives the tableau with no further proof: scripts and
`run`, the certifier whose certificate is a script, the combinators on
tactics, and the tactic `apply_move` (`ExploreTactic.lean` declares the
alias `subtab` and what the editor needs).
-/

open PLLFormula ProofTools

namespace PLLND
namespace SubTab

/-! ## Formulas as text -/

/-- A formula in the notation of `PLLND`, an atom by its name. -/
def showF : PLLFormula → String
  | .prop a => a
  | .falsePLL => "⊥"
  | .and A B => "(" ++ showF A ++ " ∧ " ++ showF B ++ ")"
  | .or A B => "(" ++ showF A ++ " ∨ " ++ showF B ++ ")"
  | .ifThen A B => "(" ++ showF A ++ " ↠ " ++ showF B ++ ")"
  | .somehow A => "◯" ++ showF A

/-! ## The moves -/

/-- **A move**: a rule of the tableau, named by its formulas.  The
constructors of `TCert`, without their subtrees. -/
inductive Move where
  | bot
  | ax (A : PLLFormula)
  | andL (A B : PLLFormula)
  | orL (A B : PLLFormula)
  | impL (A B : PLLFormula)
  | boxL (A : PLLFormula)
  | andR (A B : PLLFormula)
  | orR (A B : PLLFormula)
  | impLoc (A B : PLLFormula)
  | boxLoc (A : PLLFormula)
  | impR (A B : PLLFormula)
  | boxR (A : PLLFormula)
  deriving DecidableEq, Inhabited

/-- What a move asks of a sequent, the sequents it leaves, and what to say
when it does not apply. -/
structure Rule where
  ok : Bool
  prems : List SSeq
  why : String

/-- `X` is not among the true formulas. -/
def notT (X : PLLFormula) : String := showF X ++ " is not among the true formulas"
/-- `X` is not among the false formulas. -/
def notF (X : PLLFormula) : String := showF X ++ " is not among the false formulas"
/-- The world is not an S-point. -/
def notS : String := "the world is not an S-point"

/-- **The rule of a move at a sequent**: the conditions and the premises of
`check`, constructor by constructor. -/
def Move.rule (s : SSeq) : Move → Rule
  | .bot => ⟨mem .falsePLL s.ant, [], notT .falsePLL⟩
  | .ax A => ⟨mem A s.ant && mem A s.suc, [],
      if mem A s.ant then notF A else notT A⟩
  | .andL A B => ⟨mem (.and A B) s.ant, [⟨s.isS, s.ant ++ [A, B], s.suc⟩], notT (.and A B)⟩
  | .orL A B => ⟨mem (.or A B) s.ant,
      [⟨s.isS, s.ant ++ [A], s.suc⟩, ⟨s.isS, s.ant ++ [B], s.suc⟩], notT (.or A B)⟩
  | .impL A B => ⟨mem (.ifThen A B) s.ant,
      [⟨s.isS, s.ant, s.suc ++ [A]⟩, ⟨s.isS, s.ant ++ [B], s.suc⟩], notT (.ifThen A B)⟩
  | .boxL A => ⟨s.isS && mem (.somehow A) s.ant, [⟨s.isS, s.ant ++ [A], s.suc⟩],
      if s.isS then notT (.somehow A) else notS⟩
  | .andR A B => ⟨mem (.and A B) s.suc,
      [⟨s.isS, s.ant, s.suc ++ [A]⟩, ⟨s.isS, s.ant, s.suc ++ [B]⟩], notF (.and A B)⟩
  | .orR A B => ⟨mem (.or A B) s.suc, [⟨s.isS, s.ant, s.suc ++ [A, B]⟩], notF (.or A B)⟩
  | .impLoc A B => ⟨mem (.ifThen A B) s.suc && mem A s.ant, [⟨s.isS, s.ant, s.suc ++ [B]⟩],
      if mem (.ifThen A B) s.suc then notT A else notF (.ifThen A B)⟩
  | .boxLoc A => ⟨s.isS && mem (.somehow A) s.suc, [⟨s.isS, s.ant, s.suc ++ [A]⟩],
      if s.isS then notF (.somehow A) else notS⟩
  | .impR A B => ⟨mem (.ifThen A B) s.suc, [⟨false, s.ant ++ [A], [B]⟩], notF (.ifThen A B)⟩
  | .boxR A => ⟨mem (.somehow A) s.suc, [⟨true, s.ant, [A]⟩], notF (.somehow A)⟩

/-- **One step**: the premises of the move at the sequent, or why it does
not apply. -/
def step (m : Move) (s : SSeq) : Except String (List SSeq) :=
  if (m.rule s).ok then .ok (m.rule s).prems else .error (m.rule s).why

/-- **The subframe tableau as a proof system.**  An `abbrev`, so that
`STab.Judg` unfolds to `SSeq` where Lean looks for instances. -/
abbrev STab : Explore.ProofSystem where
  Judg := SSeq
  Move := Move
  step := step

theorem step_of {m : Move} {s : SSeq} (h : (m.rule s).ok = true) :
    STab.step m s = .ok (m.rule s).prems := by
  show step m s = _
  simp only [step, h, if_true]

theorem step_ok {m : Move} {s : SSeq} {ps : List SSeq} (h : STab.step m s = .ok ps) :
    (m.rule s).ok = true ∧ ps = (m.rule s).prems := by
  have h' : step m s = .ok ps := h
  unfold step at h'
  split at h'
  · next hok => exact ⟨hok, (Except.ok.inj h').symm⟩
  · cases h'

/-! ## Moves and closed tableaux -/

/-- The closed tableau a move makes of the closed tableaux of its premises. -/
def Move.cert : Move → List TCert → TCert
  | .bot, _ => .bot
  | .ax A, _ => .ax A
  | .andL A B, [c] => .andL A B c
  | .orL A B, [c₁, c₂] => .orL A B c₁ c₂
  | .impL A B, [c₁, c₂] => .impL A B c₁ c₂
  | .boxL A, [c] => .boxL A c
  | .andR A B, [c₁, c₂] => .andR A B c₁ c₂
  | .orR A B, [c] => .orR A B c
  | .impLoc A B, [c] => .impLoc A B c
  | .boxLoc A, [c] => .boxLoc A c
  | .impR A B, [c] => .impR A B c
  | .boxR A, [c] => .boxR A c
  | _, _ => .bot

/-- Each premise has its closed tableau. -/
abbrev Checks (ps : List SSeq) (cs : List TCert) : Prop :=
  List.Forall₂ (fun p c => check p c = true) ps cs

/-- **A move is a rule of the checker**: where the move applies and each of
its premises has a closed tableau, the move's tableau checks. -/
theorem check_cert_of {m : Move} {s : SSeq} {cs : List TCert}
    (hok : (m.rule s).ok = true) (hcs : Checks (m.rule s).prems cs) :
    check s (m.cert cs) = true := by
  cases m with
  | bot => simpa [Move.rule, Move.cert, check] using hok
  | ax A => simpa [Move.rule, Move.cert, check] using hok
  | andL A B =>
    cases hcs with | cons h₁ hr => cases hr; simp_all [Move.rule, Move.cert, check]
  | orL A B =>
    cases hcs with
    | cons h₁ hr => cases hr with | cons h₂ hr => cases hr; simp_all [Move.rule, Move.cert, check]
  | impL A B =>
    cases hcs with
    | cons h₁ hr => cases hr with | cons h₂ hr => cases hr; simp_all [Move.rule, Move.cert, check]
  | boxL A =>
    cases hcs with | cons h₁ hr => cases hr; simp_all [Move.rule, Move.cert, check]
  | andR A B =>
    cases hcs with
    | cons h₁ hr => cases hr with | cons h₂ hr => cases hr; simp_all [Move.rule, Move.cert, check]
  | orR A B =>
    cases hcs with | cons h₁ hr => cases hr; simp_all [Move.rule, Move.cert, check]
  | impLoc A B =>
    cases hcs with | cons h₁ hr => cases hr; simp_all [Move.rule, Move.cert, check]
  | boxLoc A =>
    cases hcs with | cons h₁ hr => cases hr; simp_all [Move.rule, Move.cert, check]
  | impR A B =>
    cases hcs with | cons h₁ hr => cases hr; simp_all [Move.rule, Move.cert, check]
  | boxR A =>
    cases hcs with | cons h₁ hr => cases hr; simp_all [Move.rule, Move.cert, check]

theorem checks_of_forall : ∀ {ps : List SSeq}, (∀ p ∈ ps, ∃ c, check p c = true) →
    ∃ cs, Checks ps cs
  | [], _ => ⟨[], .nil⟩
  | p :: ps, h => by
    obtain ⟨c, hc⟩ := h p List.mem_cons_self
    obtain ⟨cs, hcs⟩ := checks_of_forall fun q hq => h q (List.mem_cons_of_mem _ hq)
    exact ⟨c :: cs, .cons hc hcs⟩

/-- **The moves are sound** for having a closed tableau. -/
theorem sound : STab.Sound (fun s => ∃ c, check s c = true) := by
  intro m s ps h hps
  obtain ⟨hok, rfl⟩ := step_ok h
  obtain ⟨cs, hcs⟩ := checks_of_forall hps
  exact ⟨m.cert cs, check_cert_of hok hcs⟩

/-! ## Derivations and closed tableaux -/

mutual
/-- **The closed tableau of a derivation.**  (Of an attempt with open goals
it is not a closed tableau: an open goal is read as `bot`.) -/
def cert : {o : Bool} → {s : SSeq} → Explore.Att STab o s → TCert
  | _, _, .goal => .bot
  | _, _, .node m _ _ ds => m.cert (certs ds)
/-- `cert` on a list. -/
def certs : {o : Bool} → {ps : List SSeq} → Explore.Atts STab o ps → List TCert
  | _, _, .nil => []
  | _, _, .cons d ds => cert d :: certs ds
end

mutual
/-- `check_cert`, stated for every attempt so that the recursion is
structural: an attempt with no open goal allowed. -/
theorem check_cert_aux : {o : Bool} → {s : SSeq} → (d : Explore.Att STab o s) → o = false →
    check s (cert d) = true
  | _, _, .goal, ho => by cases ho
  | _, _, .node m _ h ds, ho => by
    obtain ⟨hok, hps⟩ := step_ok h
    have hcs := checks_certs_aux ds ho
    subst hps
    exact check_cert_of hok hcs
/-- `check_cert_aux` on a list. -/
theorem checks_certs_aux : {o : Bool} → {ps : List SSeq} → (ds : Explore.Atts STab o ps) →
    o = false → Checks ps (certs ds)
  | _, _, .nil, _ => .nil
  | _, _, .cons d ds, ho => .cons (check_cert_aux d ho) (checks_certs_aux ds ho)
end

/-- **The closed tableau of a derivation checks.** -/
theorem check_cert {s : SSeq} (d : Explore.Der STab s) : check s (cert d) = true :=
  check_cert_aux d rfl

theorem and_left {a b : Bool} (h : (a && b) = true) : a = true := (Bool.and_eq_true_iff.mp h).1
theorem and_right {a b : Bool} (h : (a && b) = true) : b = true := (Bool.and_eq_true_iff.mp h).2

/-- **The derivation of a closed tableau.** -/
def ofCert : (c : TCert) → (s : SSeq) → check s c = true → Explore.Der STab s
  | .bot, s, h => .node .bot _ (step_of (m := .bot) (s := s) h) .nil
  | .ax A, s, h => .node (.ax A) _ (step_of (m := .ax A) (s := s) h) .nil
  | .andL A B c, s, h =>
    .node (.andL A B) _ (step_of (m := .andL A B) (s := s) (and_left h))
      (.cons (ofCert c _ (and_right h)) .nil)
  | .orL A B c₁ c₂, s, h =>
    .node (.orL A B) _ (step_of (m := .orL A B) (s := s) (and_left (and_left h)))
      (.cons (ofCert c₁ _ (and_right (and_left h))) (.cons (ofCert c₂ _ (and_right h)) .nil))
  | .impL A B c₁ c₂, s, h =>
    .node (.impL A B) _ (step_of (m := .impL A B) (s := s) (and_left (and_left h)))
      (.cons (ofCert c₁ _ (and_right (and_left h))) (.cons (ofCert c₂ _ (and_right h)) .nil))
  | .boxL A c, s, h =>
    .node (.boxL A) _ (step_of (m := .boxL A) (s := s) (and_left h))
      (.cons (ofCert c _ (and_right h)) .nil)
  | .andR A B c₁ c₂, s, h =>
    .node (.andR A B) _ (step_of (m := .andR A B) (s := s) (and_left (and_left h)))
      (.cons (ofCert c₁ _ (and_right (and_left h))) (.cons (ofCert c₂ _ (and_right h)) .nil))
  | .orR A B c, s, h =>
    .node (.orR A B) _ (step_of (m := .orR A B) (s := s) (and_left h))
      (.cons (ofCert c _ (and_right h)) .nil)
  | .impLoc A B c, s, h =>
    .node (.impLoc A B) _ (step_of (m := .impLoc A B) (s := s) (and_left h))
      (.cons (ofCert c _ (and_right h)) .nil)
  | .boxLoc A c, s, h =>
    .node (.boxLoc A) _ (step_of (m := .boxLoc A) (s := s) (and_left h))
      (.cons (ofCert c _ (and_right h)) .nil)
  | .impR A B c, s, h =>
    .node (.impR A B) _ (step_of (m := .impR A B) (s := s) (and_left h))
      (.cons (ofCert c _ (and_right h)) .nil)
  | .boxR A c, s, h =>
    .node (.boxR A) _ (step_of (m := .boxR A) (s := s) (and_left h))
      (.cons (ofCert c _ (and_right h)) .nil)

/-- **A closed tableau is the tableau of its derivation.** -/
theorem cert_ofCert : ∀ (c : TCert) (s : SSeq) (h : check s c = true), cert (ofCert c s h) = c
  | .bot, _, _ => rfl
  | .ax _, _, _ => rfl
  | .andL A B c, s, h => by
    simp only [ofCert, cert, certs, Move.cert, cert_ofCert c]
  | .orL A B c₁ c₂, s, h => by
    simp only [ofCert, cert, certs, Move.cert, cert_ofCert c₁, cert_ofCert c₂]
  | .impL A B c₁ c₂, s, h => by
    simp only [ofCert, cert, certs, Move.cert, cert_ofCert c₁, cert_ofCert c₂]
  | .boxL A c, s, h => by
    simp only [ofCert, cert, certs, Move.cert, cert_ofCert c]
  | .andR A B c₁ c₂, s, h => by
    simp only [ofCert, cert, certs, Move.cert, cert_ofCert c₁, cert_ofCert c₂]
  | .orR A B c, s, h => by
    simp only [ofCert, cert, certs, Move.cert, cert_ofCert c]
  | .impLoc A B c, s, h => by
    simp only [ofCert, cert, certs, Move.cert, cert_ofCert c]
  | .boxLoc A c, s, h => by
    simp only [ofCert, cert, certs, Move.cert, cert_ofCert c]
  | .impR A B c, s, h => by
    simp only [ofCert, cert, certs, Move.cert, cert_ofCert c]
  | .boxR A c, s, h => by
    simp only [ofCert, cert, certs, Move.cert, cert_ofCert c]

/-! ## To natural deduction, and to provability

The moves are sound for natural deduction, as data (`soundND`): a move that
applies is a rule of the translation of `Translate.lean`, applied to the
derivations of its premises.  The library's map out then carries a
derivation of the explorer to its natural-deduction derivation, with no
closed tableau in between. -/

/-- What a sequent's derivation proves in natural deduction: the reading of
the sequent as the rules of `Translate.lean` state it (`⋁Δ`, or `◯⋁Δ` at an
S-point). -/
abbrev ND (s : SSeq) : Type := s.ant ⊢ gl s.isS s.suc

/-- **A move is a rule of the translation**: where the move applies, from
the natural-deduction derivations of its premises, by position, that of its
sequent. -/
def Move.nd : (m : Move) → (s : SSeq) → (m.rule s).ok = true →
    Explore.Each ND (m.rule s).prems → ND s
  | .bot, _, h, _ => r_bot (mem_of h)
  | .ax _, _, h, _ => r_ax (mem_of (and_left h)) (mem_of (and_right h))
  | .andL _ _, _, h, e => r_andL (mem_of h) e.1
  | .orL _ _, _, h, e => r_orL (mem_of h) e.1 e.2.1
  | .impL _ _, _, h, e => r_impL (mem_of h) e.1 e.2.1
  | .boxL _, ⟨true, _, _⟩, h, e => r_boxL (mem_of h) e.1
  | .boxL _, ⟨false, _, _⟩, h, _ => absurd h Bool.false_ne_true
  | .andR _ _, _, h, e => r_andR (mem_of h) e.1 e.2.1
  | .orR _ _, _, h, e => r_orR (mem_of h) e.1
  | .impLoc _ _, _, h, e => r_impLoc (mem_of (and_left h)) e.1
  | .boxLoc _, ⟨true, _, _⟩, h, e => r_boxLoc (mem_of h) e.1
  | .boxLoc _, ⟨false, _, _⟩, h, _ => absurd h Bool.false_ne_true
  | .impR _ _, _, h, e => r_impR (mem_of h) e.1
  | .boxR _, _, h, e => r_boxR (mem_of h) e.1

/-- **The moves are sound for natural deduction**, as data. -/
def soundND : STab.SoundT ND := fun m s _ h e =>
  m.nd s (step_ok h).1 ((step_ok h).2 ▸ e)

/-- **The natural-deduction derivation of a derivation**, of the reading of
its sequent (`⋁Δ`, or `◯⋁Δ` at an S-point): the library's map out at
`soundND`. -/
def derivation {s : SSeq} (d : Explore.Der STab s) : s.ant ⊢ s.goal :=
  goal_eq s ▸ Explore.Der.mapOut soundND d

/-- **The proof term of a derivation of `⊢ φ`.** -/
def term {φ : PLLFormula} (d : Explore.Der STab ⟨false, [], [φ]⟩) : [] ⊢ φ :=
  of_bigOr_one (Explore.Der.mapOut soundND d)

/-! ### The map out and the closed tableau

`Translate.lean` translates a closed tableau, constructor by constructor
(`derive_gl`); the map out translates a derivation, move by move
(`Move.nd`).  Both apply the same rules, and (PROVED) they give the same
natural-deduction derivation: -/

/-- `mapOut_eq`, by induction on a bound on the number of moves, for every
attempt with no open goal allowed. -/
theorem mapOut_eq_aux : (n : Nat) → {o : Bool} → {s : SSeq} → (d : Explore.Att STab o s) →
    d.size ≤ n → (ho : o = false) → (g : Explore.Each ND d.goals) →
    Explore.Att.mapOut soundND d g = derive_gl (cert d) s.isS s.ant s.suc (check_cert_aux d ho)
  | _, _, _, .goal, _, ho, _ => by cases ho
  | 0, _, _, .node _ _ _ _, hn, _, _ => by simp [Explore.Att.size] at hn
  | n + 1, o, ⟨b, Γ, Δ⟩, .node m ps h ds, hn, ho, g => by
    obtain ⟨hok, rfl⟩ := step_ok h
    -- one premise: the induction hypothesis at it
    have one : ∀ {p : SSeq} (d : Explore.Att STab o p) (g : Explore.Each ND (d.goals ++ [])),
        d.size + 0 + 1 ≤ n + 1 → Explore.Att.mapOut soundND d (Explore.Each.split d.goals g).1 =
          derive_gl (cert d) p.isS p.ant p.suc (check_cert_aux d ho) := fun d g hd =>
      mapOut_eq_aux n d (by omega) ho _
    -- two premises: the induction hypothesis at each
    have two₁ : ∀ {p q : SSeq} (d : Explore.Att STab o p) (e : Explore.Att STab o q)
        (g : Explore.Each ND (d.goals ++ (e.goals ++ []))), d.size + (e.size + 0) + 1 ≤ n + 1 →
        Explore.Att.mapOut soundND d (Explore.Each.split d.goals g).1 =
          derive_gl (cert d) p.isS p.ant p.suc (check_cert_aux d ho) := fun d _ g hd =>
      mapOut_eq_aux n d (by omega) ho _
    have two₂ : ∀ {p q : SSeq} (d : Explore.Att STab o p) (e : Explore.Att STab o q)
        (g : Explore.Each ND (d.goals ++ (e.goals ++ []))), d.size + (e.size + 0) + 1 ≤ n + 1 →
        Explore.Att.mapOut soundND e
            (Explore.Each.split e.goals (Explore.Each.split d.goals g).2).1 =
          derive_gl (cert e) q.isS q.ant q.suc (check_cert_aux e ho) := fun _ e g hd =>
      mapOut_eq_aux n e (by omega) ho _
    cases m with
    | bot => match ds, g with | .nil, _ => rfl
    | ax A => match ds, g with | .nil, _ => rfl
    | andL A B =>
      match ds, hn, g with
      | .cons d .nil, hn, g => exact congrArg (r_andL _) (one d g hn)
    | orL A B =>
      match ds, hn, g with
      | .cons d (.cons e .nil), hn, g => exact congrArg₂ (r_orL _) (two₁ d e g hn) (two₂ d e g hn)
    | impL A B =>
      match ds, hn, g with
      | .cons d (.cons e .nil), hn, g => exact congrArg₂ (r_impL (mem_of hok)) (two₁ d e g hn) (two₂ d e g hn)
    | boxL A =>
      cases b with
      | false => exact absurd hok Bool.false_ne_true
      | true =>
        match ds, hn, g with
        | .cons d .nil, hn, g => exact congrArg (r_boxL _) (one d g hn)
    | andR A B =>
      match ds, hn, g with
      | .cons d (.cons e .nil), hn, g => exact congrArg₂ (r_andR _) (two₁ d e g hn) (two₂ d e g hn)
    | orR A B =>
      match ds, hn, g with
      | .cons d .nil, hn, g => exact congrArg (r_orR _) (one d g hn)
    | impLoc A B =>
      match ds, hn, g with
      | .cons d .nil, hn, g => exact congrArg (r_impLoc _) (one d g hn)
    | boxLoc A =>
      cases b with
      | false => exact absurd hok Bool.false_ne_true
      | true =>
        match ds, hn, g with
        | .cons d .nil, hn, g => exact congrArg (r_boxLoc _) (one d g hn)
    | impR A B =>
      match ds, hn, g with
      | .cons d .nil, hn, g => exact congrArg (r_impR _) (one d g hn)
    | boxR A =>
      match ds, hn, g with
      | .cons d .nil, hn, g => exact congrArg (r_boxR _) (one d g hn)

/-- **The map out is the translation of the closed tableau**: the
natural-deduction derivation the library computes from a derivation, move by
move, is the one `derive_gl` computes from its closed tableau. -/
theorem mapOut_eq {s : SSeq} (d : Explore.Der STab s) :
    Explore.Der.mapOut soundND d = derive_gl (cert d) s.isS s.ant s.suc (check_cert d) :=
  mapOut_eq_aux d.size d (Nat.le_refl _) rfl _

/-- `derivation` is what it was before the map out: the translation of the
closed tableau. -/
theorem derivation_eq {s : SSeq} (d : Explore.Der STab s) :
    derivation d = deriveOf (cert d) s (check_cert d) := by
  obtain ⟨b, Γ, Δ⟩ := s
  simp only [derivation, deriveOf, mapOut_eq]

/-- `term` is what it was before the map out: the proof term of the closed
tableau. -/
theorem term_eq {φ : PLLFormula} (d : Explore.Der STab ⟨false, [], [φ]⟩) :
    term d = termOf φ (cert d) (check_cert d) :=
  congrArg of_bigOr_one (mapOut_eq d)

/-- **A derivation of `⊢ φ` proves `φ`**, by the tableau's own rules. -/
theorem holds_of_der {φ : PLLFormula} (d : Explore.Der STab ⟨false, [], [φ]⟩) : Holds φ :=
  ⟨term d⟩

/-! ## Scripts as certificates -/

/-- **The yes side by scripts**: a script that derives `⊢ φ` certifies
`Nonempty ([] ⊢ φ)`.  The kernel runs the script. -/
def yesScript : Certify.Certifier PLLFormula (Explore.Script STab) Holds where
  check φ ls := Explore.derives STab ⟨false, [], [φ]⟩ ls
  sound _ _ h :=
    let ⟨_, hc⟩ := Explore.derives_sound sound h
    holds_of_check' hc

/-- The script of a closed tableau for `⊢ φ`. -/
def scriptOf (φ : PLLFormula) (c : TCert) (h : check ⟨false, [], [φ]⟩ c = true) :
    Explore.Script STab :=
  (ofCert c ⟨false, [], [φ]⟩ h).script

/-- **Completeness, by scripts.**  Every formula has a script that derives
it or a finite subframe countermodel.  From `dichotomy`, which names
neither certifier of `Sound.lean`, so that this route, like `yes'`, reaches
no constant of FRJW. -/
theorem complete_script (φ : PLLFormula) :
    (∃ ls, yesScript.check φ ls = true) ∨ (∃ m, no.check φ m = true) := by
  rcases dichotomy φ with ⟨c, hc⟩ | ⟨m, hm⟩
  · exact .inl ⟨scriptOf φ c hc, Explore.derives_script (ofCert c ⟨false, [], [φ]⟩ hc)⟩
  · exact .inr ⟨m, hm⟩

end SubTab
end PLLND

-- The bound on the axioms of this file: an upper bound.
#axioms_within_file [propext, Quot.sound]
