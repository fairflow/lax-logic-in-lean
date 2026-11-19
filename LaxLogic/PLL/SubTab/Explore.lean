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
    Der STab ⟨false, [], [φ]⟩ → Holds φ                                (holds_of_der)
    (∃ ls, derives STab ⟨false, [], [φ]⟩ ls = true) ∨ (∃ m, no.check φ m = true)
                                                                        (complete_script)

So a derivation in the explorer's sense and a closed tableau are the same
thing, each computed from the other (`cert`, `ofCert`); a derivation gives
its natural-deduction derivation through `deriveOf` (`derivation`, `term`);
and a script is a certificate of provability, with the tableau's
completeness carried over: every formula has a script that `derives`
accepts or a finite subframe countermodel.

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

/-! ## To natural deduction, and to provability -/

/-- **The natural-deduction derivation of a derivation**, of the reading of
its sequent (`⋁Δ`, or `◯⋁Δ` at an S-point), through `deriveOf`. -/
def derivation {s : SSeq} (d : Explore.Der STab s) : s.ant ⊢ s.goal :=
  deriveOf (cert d) s (check_cert d)

/-- **The proof term of a derivation of `⊢ φ`.** -/
def term {φ : PLLFormula} (d : Explore.Der STab ⟨false, [], [φ]⟩) : [] ⊢ φ :=
  termOf φ (cert d) (check_cert d)

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
