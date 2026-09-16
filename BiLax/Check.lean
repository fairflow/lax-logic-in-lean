/-
BiLax round 2 — THE DECIDABLE BRANCH CHECKER (discover-then-pin).

`FinBranch` presents a Hintikka structure in fully finite data:
`Bool` relations over `Fin n` and `List BiForm` assignments.  `checkB`
decides every Hintikka condition and `toHintikka` turns a
`checkB = true` certificate into the structure, so the pipeline is

    (untrusted search)  →  FinBranch  →  `by decide`  →  Hintikka
                        →  not_laxND  [KERNEL-CHECKED]

— the repo's discover-then-pin doctrine: the searcher may be
arbitrary, the certificate is kernel-checked.

The saturation conditions are checked for the formulas actually
PRESENT in `LL x` / `RR x`, which is exactly what the truth lemma
consumes: a compound formula in the assignment is itself checked, and
its immediate parts are required to be present too.
-/
import BiLax.Refute

namespace BiLax

structure FinBranch where
  n : Nat
  riB : Fin n → Fin n → Bool
  rmB : Fin n → Fin n → Bool
  rcB : Fin n → Fin n → Bool
  falB : Fin n → Bool
  LL : Fin n → List BiForm
  RR : Fin n → List BiForm

namespace FinBranch

variable (B : FinBranch)

def ws : List (Fin B.n) := List.finRange B.n

theorem mem_ws (x : Fin B.n) : x ∈ B.ws := List.mem_finRange x

theorem ws_all {p : Fin B.n → Bool} (h : (B.ws.all p) = true) (x : Fin B.n) :
    p x = true := List.all_eq_true.mp h x (B.mem_ws x)

theorem lst_all {l : List BiForm} {p : BiForm → Bool} (h : l.all p = true)
    {A : BiForm} (ha : A ∈ l) : p A = true := List.all_eq_true.mp h A ha

/-! ### The conditions, one atomic check each -/

def cRefl : Bool := B.ws.all fun x => B.riB x x && B.rmB x x
def cTrans : Bool := B.ws.all fun x => B.ws.all fun y => B.ws.all fun z =>
  (!(B.riB x y) || !(B.riB y z) || B.riB x z) &&
  (!(B.rmB x y) || !(B.rmB y z) || B.rmB x z)
def cSub : Bool := B.ws.all fun x => B.ws.all fun y =>
  (!(B.rmB x y) || B.riB x y) && (!(B.falB x) || !(B.riB x y) || B.falB y)
def cSquare : Bool := B.ws.all fun w => B.ws.all fun u => B.ws.all fun v =>
  !(B.rcB w u) || !(B.riB u v) || B.ws.any fun w' => B.riB w w' && B.rcB w' v
def cCounit : Bool := B.ws.all fun w => B.ws.all fun u =>
  !(B.rcB w u) || B.ws.any fun v => B.riB w v &&
    B.ws.all fun y => !(B.rmB v y) || B.riB y u
def cSerial : Bool := B.ws.all fun v => B.ws.any fun u => B.rmB v u && B.rcB v u
def cOpen : Bool := B.ws.all fun x => (B.LL x).all fun A => !(decide (A ∈ B.RR x))
def cPropH : Bool := B.ws.all fun x => B.ws.all fun y => !(B.riB x y) ||
  (B.LL x).all fun A => match A with
    | .prop _ => decide (A ∈ B.LL y)
    | _ => true
def cFalR : Bool := B.ws.all fun x => !(B.falB x) || (B.RR x).all fun A =>
  match A with
  | .prop _ => false
  | .bot => false
  | _ => true
def cBotL : Bool := B.ws.all fun x => (B.LL x).all fun A =>
  match A with
  | .bot => B.falB x
  | _ => true
def cSatL : Bool := B.ws.all fun x => (B.LL x).all fun A =>
  match A with
  | .and P Q => decide (P ∈ B.LL x) && decide (Q ∈ B.LL x)
  | .or P Q => decide (P ∈ B.LL x) || decide (Q ∈ B.LL x)
  | .imp P Q => B.ws.all fun y =>
      !(B.riB x y) || decide (P ∈ B.RR y) || decide (Q ∈ B.LL y)
  | .coimp P Q => B.ws.any fun y =>
      B.riB y x && decide (P ∈ B.LL y) && decide (Q ∈ B.RR y)
  | .lax P => B.ws.all fun y =>
      !(B.riB x y) || B.ws.any fun u => B.rmB y u && decide (P ∈ B.LL u)
  | .colax P => B.ws.any fun u => B.rcB u x && decide (P ∈ B.LL u)
  | _ => true
def cSatR : Bool := B.ws.all fun x => (B.RR x).all fun A =>
  match A with
  | .and P Q => decide (P ∈ B.RR x) || decide (Q ∈ B.RR x)
  | .or P Q => decide (P ∈ B.RR x) && decide (Q ∈ B.RR x)
  | .imp P Q => B.ws.any fun y =>
      B.riB x y && decide (P ∈ B.LL y) && decide (Q ∈ B.RR y)
  | .coimp P Q => B.ws.all fun y =>
      !(B.riB y x) || decide (P ∈ B.RR y) || decide (Q ∈ B.LL y)
  | .lax P => B.ws.any fun y =>
      B.riB x y && B.ws.all fun u => !(B.rmB y u) || decide (P ∈ B.RR u)
  | .colax P => B.ws.all fun u => !(B.rcB u x) || decide (P ∈ B.RR u)
  | _ => true

def checkB : Bool :=
  B.cRefl && B.cTrans && B.cSub && B.cSquare && B.cCounit && B.cSerial &&
  B.cOpen && B.cPropH && B.cFalR && B.cBotL && B.cSatL && B.cSatR

/-! ### Soundness of the checker -/

section
variable {B}

theorem checkB_parts (h : B.checkB = true) :
    B.cRefl = true ∧ B.cTrans = true ∧ B.cSub = true ∧ B.cSquare = true ∧
    B.cCounit = true ∧ B.cSerial = true ∧ B.cOpen = true ∧ B.cPropH = true ∧
    B.cFalR = true ∧ B.cBotL = true ∧ B.cSatL = true ∧ B.cSatR = true := by
  simp only [checkB, Bool.and_eq_true] at h
  tauto

end

/-- **A `checkB = true` certificate IS a Hintikka structure.** -/
def toHintikka (h : B.checkB = true) : Hintikka :=
  let P := checkB_parts h
  { n := B.n
    ri := fun x y => B.riB x y = true
    rm := fun x y => B.rmB x y = true
    rc := fun x y => B.rcB x y = true
    fal := fun x => B.falB x = true
    L := fun x A => A ∈ B.LL x
    R := fun x A => A ∈ B.RR x
    ri_refl := fun x => by
      simpa using (Bool.and_eq_true .. |>.mp (B.ws_all P.1 x)).1
    rm_refl := fun x => by
      simpa using (Bool.and_eq_true .. |>.mp (B.ws_all P.1 x)).2
    ri_trans := by
      intro x y z h1 h2
      have := (Bool.and_eq_true .. |>.mp
        (B.ws_all (B.ws_all (B.ws_all P.2.1 x) y) z)).1
      simp only [h1, h2, Bool.not_true, Bool.false_or] at this
      exact this
    rm_trans := by
      intro x y z h1 h2
      have := (Bool.and_eq_true .. |>.mp
        (B.ws_all (B.ws_all (B.ws_all P.2.1 x) y) z)).2
      simp only [h1, h2, Bool.not_true, Bool.false_or] at this
      exact this
    sub_mi := by
      intro x y h1
      have := (Bool.and_eq_true .. |>.mp (B.ws_all (B.ws_all P.2.2.1 x) y)).1
      simp only [h1, Bool.not_true, Bool.false_or] at this
      exact this
    fal_hered := by
      intro x y h1 hx
      have := (Bool.and_eq_true .. |>.mp (B.ws_all (B.ws_all P.2.2.1 x) y)).2
      simp only [h1, hx, Bool.not_true, Bool.false_or] at this
      exact this
    square_c := by
      intro w u v h1 h2
      have := B.ws_all (B.ws_all (B.ws_all P.2.2.2.1 w) u) v
      simp only [h1, h2, Bool.not_true, Bool.false_or, List.any_eq_true,
        Bool.and_eq_true] at this
      obtain ⟨w', -, hw1, hw2⟩ := this
      exact ⟨w', hw1, hw2⟩
    counit_c := by
      intro w u h1
      have := B.ws_all (B.ws_all P.2.2.2.2.1 w) u
      simp only [h1, Bool.not_true, Bool.false_or, List.any_eq_true,
        Bool.and_eq_true] at this
      obtain ⟨v, -, hv1, hv2⟩ := this
      refine ⟨v, hv1, fun y hy => ?_⟩
      have := B.ws_all hv2 y
      simp only [hy, Bool.not_true, Bool.false_or] at this
      exact this
    serial_c := by
      intro v
      have := B.ws_all P.2.2.2.2.2.1 v
      simp only [List.any_eq_true, Bool.and_eq_true] at this
      obtain ⟨u, -, h1, h2⟩ := this
      exact ⟨u, h1, h2⟩
    open_lr := by
      intro x A hL hR
      have := lst_all (B.ws_all P.2.2.2.2.2.2.1 x) hL
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
      exact this hR
    prop_hered := by
      intro x y a hxy hL
      have := B.ws_all (B.ws_all P.2.2.2.2.2.2.2.1 x) y
      simp only [hxy, Bool.not_true, Bool.false_or] at this
      simpa using lst_all this hL
    fal_no_prop := by
      intro x a hx hR
      have := B.ws_all P.2.2.2.2.2.2.2.2.1 x
      simp only [hx, Bool.not_true, Bool.false_or] at this
      simpa using lst_all this hR
    fal_no_bot := by
      intro x hx hR
      have := B.ws_all P.2.2.2.2.2.2.2.2.1 x
      simp only [hx, Bool.not_true, Bool.false_or] at this
      simpa using lst_all this hR
    bot_left := by
      intro x hL
      simpa using lst_all (B.ws_all P.2.2.2.2.2.2.2.2.2.1 x) hL
    sat_andL := by
      intro x A Bf hL
      have := lst_all (B.ws_all P.2.2.2.2.2.2.2.2.2.2.1 x) hL
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this
    sat_orL := by
      intro x A Bf hL
      have := lst_all (B.ws_all P.2.2.2.2.2.2.2.2.2.2.1 x) hL
      simp only [Bool.or_eq_true, decide_eq_true_eq] at this
      exact this
    sat_impL := by
      intro x y A Bf hL hxy
      have := B.ws_all (lst_all (B.ws_all P.2.2.2.2.2.2.2.2.2.2.1 x) hL) y
      simp only [hxy, Bool.not_true, Bool.false_or, Bool.or_eq_true,
        decide_eq_true_eq] at this
      exact this
    sat_coimpL := by
      intro x A Bf hL
      have := lst_all (B.ws_all P.2.2.2.2.2.2.2.2.2.2.1 x) hL
      simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
      obtain ⟨y, -, ⟨hy, hA⟩, hB⟩ := this
      exact ⟨y, hy, hA, hB⟩
    sat_laxL := by
      intro x y A hL hxy
      have := B.ws_all (lst_all (B.ws_all P.2.2.2.2.2.2.2.2.2.2.1 x) hL) y
      simp only [hxy, Bool.not_true, Bool.false_or, List.any_eq_true,
        Bool.and_eq_true, decide_eq_true_eq] at this
      obtain ⟨u, -, hu1, hu2⟩ := this
      exact ⟨u, hu1, hu2⟩
    sat_colaxL := by
      intro x A hL
      have := lst_all (B.ws_all P.2.2.2.2.2.2.2.2.2.2.1 x) hL
      simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
      obtain ⟨u, -, hu1, hu2⟩ := this
      exact ⟨u, hu1, hu2⟩
    sat_andR := by
      intro x A Bf hR
      have := lst_all (B.ws_all P.2.2.2.2.2.2.2.2.2.2.2 x) hR
      simp only [Bool.or_eq_true, decide_eq_true_eq] at this
      exact this
    sat_orR := by
      intro x A Bf hR
      have := lst_all (B.ws_all P.2.2.2.2.2.2.2.2.2.2.2 x) hR
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this
    sat_impR := by
      intro x A Bf hR
      have := lst_all (B.ws_all P.2.2.2.2.2.2.2.2.2.2.2 x) hR
      simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
      obtain ⟨y, -, ⟨hy, hA⟩, hB⟩ := this
      exact ⟨y, hy, hA, hB⟩
    sat_coimpR := by
      intro x y A Bf hR hyx
      have := B.ws_all (lst_all (B.ws_all P.2.2.2.2.2.2.2.2.2.2.2 x) hR) y
      simp only [hyx, Bool.not_true, Bool.false_or, Bool.or_eq_true,
        decide_eq_true_eq] at this
      exact this
    sat_laxR := by
      intro x A hR
      have := lst_all (B.ws_all P.2.2.2.2.2.2.2.2.2.2.2 x) hR
      simp only [List.any_eq_true, Bool.and_eq_true] at this
      obtain ⟨y, -, hy, hall⟩ := this
      refine ⟨y, hy, fun u hu => ?_⟩
      have := B.ws_all hall u
      simp only [hu, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
      exact this
    sat_colaxR := by
      intro x u A hR hux
      have := B.ws_all (lst_all (B.ws_all P.2.2.2.2.2.2.2.2.2.2.2 x) hR) u
      simp only [hux, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
      exact this }

/-- **The pinning theorem**: a checked branch refutes the PLL sequent
it carries. -/
theorem not_laxND_of_check {Γ : List PLLFormula} {φ : PLLFormula}
    (h : B.checkB = true) (x : Fin B.n)
    (hΓ : ∀ ψ ∈ Γ, emb ψ ∈ B.LL x) (hφ : emb φ ∈ B.RR x) :
    ¬ Nonempty (PLLND.LaxND Γ φ) :=
  (B.toHintikka h).not_laxND x hΓ hφ

end FinBranch

end BiLax
