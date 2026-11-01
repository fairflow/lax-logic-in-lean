import Mathlib.SetTheory.ZFC.Basic
import wip.f0SigOnto
import Meta.Audit

/-!
# The nesting of the copies `σⁿ(F0)`, turned inside out

Matthew, 2026-11-01 (an experiment; `Classical.choice` is permitted in this
module, and the declarations that use it are listed in the pins at the end).

`σ = sig = subBot t3` (`t3 = ◯⊥ ∨ ¬◯⊥`) embeds F0 faithfully into `[t3, ⊤]`
(`wip/f0SelfSim.lean`: `sigN_faithful`, `sigN_bot_le`, `sigN_bot_strict`,
`copies_strict`), so the copies are strictly nested:

    F0 ⊋ σ(F0) ⊋ σ²(F0) ⊋ ⋯ ⊋ σ^ω(F0) := ⋂ₙ σⁿ(F0).

Under `⊋` this chain is well-founded, of type `ω + 1` with the limit last.
This file turns it inside out in ZF, by well-founded recursion along `<` on
`WithTop ℕ` (no anti-foundation): for `i ∈ ω + 1`,

    D(i) = { (0, D(j)) : j < i }
         ∪ { (1, x) : x a colour of level i }               the elements of σⁱ(F0)
         ∪ { (2, (c, S_c ∩ σⁱ(F0))) : c ∈ C }              one bag per colour
         ∪ { (3, T_c(ω)) : c a colour with a base a_c }      thread limits (level ω only)

with Mathlib's `ZFSet.pair` and the tags `tag 0, tag 1, …` (`tag 0 = ∅`,
`tag (k+1) = {tag k}`).  A colour is an F0 element, coded as the set of codes
of all closed formulas in its class (`classCode`).

## Part A: the generic decoration

`D lab` takes a family of labels `lab k i` (tag `k + 1`) and is defined by
`WellFounded.fix`:

    D lab i = range (j < i ↦ (tag 0, D lab j)) ∪ ⋃ₖ {tag (k+1)} × lab k i.

The brief's single-label form `D i = range (j < i ↦ (tag 0, D j)) ∪ {tag 1} × lab i`
is `D1 lab = D (single lab)`.

## Part B: the F0 instance

`inSig n x := ∃ y, atomFree y ∧ σⁿ y ⊣⊢ x`, `inLim x := ∀ n, inSig n x`.
A colouring `K` has colours `K.C` with an injective code, a `⊣⊢`-invariant
`K.S c`, and an optional base `K.base c` for a thread.  The labels of level
`i` are the colours of the level (tag 1), the bags `(c, S_c ∩ level i)`
(tag 2) and, at level `⊤` only, the thread limits `T_{a_c}(ω)` (tag 3).

The thread of a closed `a` is the generic `D` with one label per level:

    T_a(n) = { (0, T_a(m)) : m < n } ∪ { (1, σⁿ(a)) },     T_a(ω) = { (0, T_a(m)) : m < ω }.

## Part C: statements

Every statement is a `Prop` definition in `Stmt`, committed before its proof
(stage 1).  The theorems proving them carry the same names in lower case.

The example colouring `rb`: red `= {σᵐ⊥ : m ∈ ℕ}` with base `⊥`, blue
`= {◯σᵐ⊥ : m ∈ ℕ}` with base `◯⊥` (each colour is the orbit of its base,
since `σᵐ(◯⊥) = ◯σᵐ⊥`).
-/

open PLLFormula

namespace PLLND
namespace F0
namespace InsideOut

open SemUI Sig
open PLLND.LaxInfinite (atomFree)

/-! ## Part A. The generic decoration -/

/-- The tags: `tag 0 = ∅`, `tag (k + 1) = {tag k}`. -/
def tag : ℕ → ZFSet.{0}
  | 0 => ∅
  | k + 1 => {tag k}

theorem tag_succ_ne_zero (k : ℕ) : tag (k + 1) ≠ tag 0 := by
  intro h
  have h1 : tag k ∈ tag (k + 1) := ZFSet.mem_singleton.mpr rfl
  rw [h] at h1
  exact ZFSet.notMem_empty _ h1

/-- One step of the recursion: the order members `(tag 0, rec j)` for `j < i`
and the labels `(tag (k + 1), x)` for `x ∈ lab k i`. -/
noncomputable def Dstep (lab : ℕ → WithTop ℕ → ZFSet.{0}) (i : WithTop ℕ)
    (rec : (j : WithTop ℕ) → j < i → ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.range (fun j : {j : WithTop ℕ // j < i} => ZFSet.pair (tag 0) (rec j.1 j.2)) ∪
    ZFSet.iUnion (fun k : ℕ => ZFSet.prod {tag (k + 1)} (lab k i))

/-- **The decoration**, by well-founded recursion along `<` on `ω + 1 = WithTop ℕ`. -/
noncomputable def D (lab : ℕ → WithTop ℕ → ZFSet.{0}) : WithTop ℕ → ZFSet.{0} :=
  (wellFounded_lt (α := WithTop ℕ)).fix (Dstep lab)

/-- One label family, at tag 1. -/
def single (lab : WithTop ℕ → ZFSet.{0}) : ℕ → WithTop ℕ → ZFSet.{0}
  | 0 => lab
  | _ + 1 => fun _ => ∅

/-- The brief's single-label form. -/
noncomputable def D1 (lab : WithTop ℕ → ZFSet.{0}) : WithTop ℕ → ZFSet.{0} := D (single lab)

/-! ## Part B. The F0 instance -/

/-- `x ∈ σⁿ(F0)`, up to `⊣⊢`. -/
def inSig (n : ℕ) (x : PLLFormula) : Prop :=
  ∃ y, atomFree y = true ∧ Interd (sigN n y) x

/-- `x ∈ σ^ω(F0) = ⋂ₙ σⁿ(F0)`. -/
def inLim (x : PLLFormula) : Prop := ∀ n, inSig n x

/-- The level `i ∈ ω + 1`. -/
def inLevel : WithTop ℕ → PLLFormula → Prop
  | none => inLim
  | some n => inSig n

/-- The shell `Lₙ = σⁿ(F0) ∖ σⁿ⁺¹(F0)`. -/
def shell (n : ℕ) (x : PLLFormula) : Prop := inSig n x ∧ ¬ inSig (n + 1) x

/-! ### A structural code of formulas -/

/-- A list of numerals, as nested pairs ending in `∅`. -/
def natsCode : List ℕ → ZFSet.{0}
  | [] => ∅
  | n :: l => ZFSet.pair (tag n) (natsCode l)

/-- A string, through its characters' code points. -/
def strCode (s : String) : ZFSet.{0} := natsCode (s.toList.map Char.toNat)

/-- **The structural code of a formula** (injective, `code_injective`). -/
def code : PLLFormula → ZFSet.{0}
  | .prop a => ZFSet.pair (tag 0) (strCode a)
  | .falsePLL => ZFSet.pair (tag 1) ∅
  | .and A B => ZFSet.pair (tag 2) (ZFSet.pair (code A) (code B))
  | .or A B => ZFSet.pair (tag 3) (ZFSet.pair (code A) (code B))
  | .ifThen A B => ZFSet.pair (tag 4) (ZFSet.pair (code A) (code B))
  | .somehow A => ZFSet.pair (tag 5) (code A)

/-- **The class code**: the set of codes of all closed `y ⊣⊢ x`.  A colour is
this set, so it is an element of F0, not a formula. -/
noncomputable def classCode (x : PLLFormula) : ZFSet.{0} :=
  ZFSet.range (fun y : {y : PLLFormula // atomFree y = true ∧ Interd y x} => code y.1)

/-! ### Colourings -/

/-- **A colouring**: colours with an injective code, a `⊣⊢`-invariant set `S c`
for each colour, and an optional base `a_c` (closed) whose thread limit is
carried by `D(ω)`. -/
structure Colouring where
  C : Type
  ccode : C → ZFSet.{0}
  ccode_inj : Function.Injective ccode
  S : C → PLLFormula → Prop
  S_inv : ∀ c x x', Interd x x' → S c x → S c x'
  base : C → Option PLLFormula
  base_af : ∀ c a, base c = some a → atomFree a = true

/-- The colours of level `i`: the classes of the closed formulas of the level. -/
noncomputable def colLab (i : WithTop ℕ) : ZFSet.{0} :=
  ZFSet.range (fun x : {x : PLLFormula // atomFree x = true ∧ inLevel i x} => classCode x.1)

/-- The bag of colour `c` at level `i`: the classes of `S c ∩ level i`. -/
noncomputable def bagSet (K : Colouring) (c : K.C) (i : WithTop ℕ) : ZFSet.{0} :=
  ZFSet.range (fun x : {x : PLLFormula // atomFree x = true ∧ inLevel i x ∧ K.S c x} =>
    classCode x.1)

/-- The bags of level `i`, each paired with its colour's code. -/
noncomputable def bagLab (K : Colouring) (i : WithTop ℕ) : ZFSet.{0} :=
  ZFSet.range (fun c : K.C => ZFSet.pair (K.ccode c) (bagSet K c i))

/-! ### Threads -/

/-- The label of the thread of `a`: `{σⁿ(a)}` at level `n`, nothing at `ω`. -/
noncomputable def threadLab (a : PLLFormula) : WithTop ℕ → ZFSet.{0}
  | none => ∅
  | some n => {classCode (sigN n a)}

/-- **The thread of `a`**: `T_a(n) = {(0, T_a(m)) : m < n} ∪ {(1, σⁿ a)}`,
`T_a(ω) = {(0, T_a(m)) : m < ω}`. -/
noncomputable def thread (a : PLLFormula) : WithTop ℕ → ZFSet.{0} := D1 (threadLab a)

/-- The thread limits of the chosen bases, at level `ω` only. -/
noncomputable def thrLab (K : Colouring) : WithTop ℕ → ZFSet.{0}
  | none => ZFSet.range (fun p : {p : K.C × PLLFormula // K.base p.1 = some p.2} =>
      thread p.1.2 ⊤)
  | some _ => ∅

/-- The labels of the F0 decoration: colours (tag 1), bags (tag 2), thread
limits (tag 3). -/
noncomputable def lab (K : Colouring) : ℕ → WithTop ℕ → ZFSet.{0}
  | 0 => colLab
  | 1 => bagLab K
  | 2 => thrLab K
  | _ + 3 => fun _ => ∅

/-- **The F0 decoration** of the colouring `K`. -/
noncomputable def DF (K : Colouring) : WithTop ℕ → ZFSet.{0} := D (lab K)

/-! ### The example colouring: red and blue -/

/-- Two colours. -/
inductive RB where
  | red
  | blue

/-- Their codes. -/
def rbCode : RB → ZFSet.{0}
  | .red => tag 0
  | .blue => tag 1

/-- Red: the bases `{σᵐ⊥ : m ∈ ℕ}`; blue: `{◯σᵐ⊥ : m ∈ ℕ}`. -/
def rbS : RB → PLLFormula → Prop
  | .red, x => ∃ m, Interd x (sigN m .falsePLL)
  | .blue, x => ∃ m, Interd x (.somehow (sigN m .falsePLL))

/-- Their bases: `⊥` and `◯⊥`. -/
def rbBase : RB → Option PLLFormula
  | .red => some .falsePLL
  | .blue => some (.somehow .falsePLL)

theorem rbCode_inj : Function.Injective rbCode := by
  intro c d h
  cases c <;> cases d
  · rfl
  · exact absurd (show tag 0 = tag 1 from h).symm (tag_succ_ne_zero 0)
  · exact absurd (show tag 1 = tag 0 from h) (tag_succ_ne_zero 0)
  · rfl

theorem rbS_inv : ∀ c x x', Interd x x' → rbS c x → rbS c x'
  | .red, _, _, h, ⟨m, hm⟩ => ⟨m, Interd.trans h.symm hm⟩
  | .blue, _, _, h, ⟨m, hm⟩ => ⟨m, Interd.trans h.symm hm⟩

theorem rbBase_af : ∀ c a, rbBase c = some a → atomFree a = true
  | .red, _, h => by cases h; rfl
  | .blue, _, h => by cases h; rfl

/-- **The red/blue colouring.** -/
def rb : Colouring where
  C := RB
  ccode := rbCode
  ccode_inj := rbCode_inj
  S := rbS
  S_inv := rbS_inv
  base := rbBase
  base_af := rbBase_af

/-- `x` is a colour of `DF rb i`. -/
def IsColour (i : WithTop ℕ) (x : PLLFormula) : Prop :=
  ZFSet.pair (tag 1) (classCode x) ∈ DF rb i

/-- `x` is in the `c`-bag of `DF rb i`. -/
def InBag (c : RB) (i : WithTop ℕ) (x : PLLFormula) : Prop :=
  ∃ B, ZFSet.pair (tag 2) (ZFSet.pair (rbCode c) B) ∈ DF rb i ∧ classCode x ∈ B

/-! ## Part C. The statements (stage 1) -/

namespace Stmt

/-! ### Generic -/

/-- The unfolding equation. -/
def DUnfold : Prop := ∀ (lab : ℕ → WithTop ℕ → ZFSet.{0}) (i : WithTop ℕ),
  D lab i = ZFSet.range (fun j : {j : WithTop ℕ // j < i} => ZFSet.pair (tag 0) (D lab j.1)) ∪
    ZFSet.iUnion (fun k : ℕ => ZFSet.prod {tag (k + 1)} (lab k i))

/-- The unfolding equation of the single-label form. -/
def D1Unfold : Prop := ∀ (lab : WithTop ℕ → ZFSet.{0}) (i : WithTop ℕ),
  D1 lab i = ZFSet.range (fun j : {j : WithTop ℕ // j < i} => ZFSet.pair (tag 0) (D1 lab j.1)) ∪
    ZFSet.prod {tag 1} (lab i)

/-- Membership in `D lab i`. -/
def MemDIff : Prop := ∀ (lab : ℕ → WithTop ℕ → ZFSet.{0}) (i : WithTop ℕ) (z : ZFSet.{0}),
  z ∈ D lab i ↔ (∃ j, j < i ∧ z = ZFSet.pair (tag 0) (D lab j)) ∨
    ∃ k x, x ∈ lab k i ∧ z = ZFSet.pair (tag (k + 1)) x

/-- `D lab` is one-to-one. -/
def DInjective : Prop := ∀ lab : ℕ → WithTop ℕ → ZFSet.{0}, Function.Injective (D lab)

/-- The order is read off by membership. -/
def MemOrderIff : Prop := ∀ (lab : ℕ → WithTop ℕ → ZFSet.{0}) (i j : WithTop ℕ),
  ZFSet.pair (tag 0) (D lab j) ∈ D lab i ↔ j < i

/-- The labels are read off by membership. -/
def MemLabelIff : Prop := ∀ (lab : ℕ → WithTop ℕ → ZFSet.{0}) (i : WithTop ℕ) (k : ℕ)
  (x : ZFSet.{0}), ZFSet.pair (tag (k + 1)) x ∈ D lab i ↔ x ∈ lab k i

/-- Every finite level is a member of the top. -/
def MemTop : Prop := ∀ (lab : ℕ → WithTop ℕ → ZFSet.{0}) (n : ℕ),
  ZFSet.pair (tag 0) (D lab n) ∈ D lab ⊤

/-! ### The F0 instance -/

/-- The structural code is one-to-one. -/
def CodeInjective : Prop := Function.Injective code

/-- Class codes are equal exactly on `⊣⊢`-classes. -/
def ClassCodeEqIff : Prop := ∀ x x' : PLLFormula, atomFree x = true →
  (classCode x = classCode x' ↔ Interd x x')

/-- **Colour readback.** -/
def ColourIff : Prop := ∀ (K : Colouring) (i : WithTop ℕ) (x : PLLFormula), atomFree x = true →
  (ZFSet.pair (tag 1) (classCode x) ∈ DF K i ↔ inLevel i x)

/-- The `c`-bag of `DF K i` is unique. -/
def BagIff : Prop := ∀ (K : Colouring) (i : WithTop ℕ) (c : K.C) (B : ZFSet.{0}),
  ZFSet.pair (tag 2) (ZFSet.pair (K.ccode c) B) ∈ DF K i ↔ B = bagSet K c i

/-- **Bag readback**: `x ∈ S c ∩ σⁱ(F0)` iff its class is in the `c`-bag of `D i`. -/
def Readback : Prop := ∀ (K : Colouring) (i : WithTop ℕ) (c : K.C) (x : PLLFormula),
  atomFree x = true →
  ((K.S c x ∧ inLevel i x) ↔
    ∃ B, ZFSet.pair (tag 2) (ZFSet.pair (K.ccode c) B) ∈ DF K i ∧ classCode x ∈ B)

/-- **Thread limits determine their base**: `T_a(ω) = T_b(ω) → a ⊣⊢ b`. -/
def ThreadLimitInjective : Prop := ∀ a b : PLLFormula, atomFree a = true →
  thread a ⊤ = thread b ⊤ → Interd a b

/-- With the converse. -/
def ThreadLimitIff : Prop := ∀ a b : PLLFormula, atomFree a = true → atomFree b = true →
  (thread a ⊤ = thread b ⊤ ↔ Interd a b)

/-- **Thread readback**: `(3, T_a(ω)) ∈ D(ω)` iff `a` is a chosen base, up to `⊣⊢`. -/
def ThreadReadback : Prop := ∀ (K : Colouring) (a : PLLFormula), atomFree a = true →
  (ZFSet.pair (tag 3) (thread a ⊤) ∈ DF K ⊤ ↔ ∃ c a', K.base c = some a' ∧ Interd a' a)

/-- No thread limit at a finite level. -/
def ThreadsOnlyAtTop : Prop := ∀ (K : Colouring) (n : ℕ) (z : ZFSet.{0}),
  ZFSet.pair (tag 3) z ∉ DF K n

/-! ### F0 facts -/

/-- **`σ` maps the shell `Lₙ` one-to-one onto `Lₙ₊₁`.** -/
def ShellShift : Prop := ∀ n : ℕ,
  (∀ x, atomFree x = true → shell n x → shell (n + 1) (sig x)) ∧
  (∀ x x', atomFree x = true → atomFree x' = true → shell n x → shell n x' →
    Interd (sig x) (sig x') → Interd x x') ∧
  (∀ z, atomFree z = true → shell (n + 1) z →
    ∃ x, atomFree x = true ∧ shell n x ∧ Interd (sig x) z)

/-- **The limit is the top**: `σ^ω(F0) = {⊤}`. -/
def LimEqTop : Prop := ∀ x : PLLFormula, atomFree x = true → (inLim x ↔ Deriv [] x)

/-- **Orbits leave every non-top element's upset**: for closed `a` and `⊬ x`,
eventually `σⁿ a ⊬ x`. -/
def OrbitOrderLimit : Prop := ∀ a x : PLLFormula, atomFree a = true → ¬ Deriv [] x →
  ∃ N, ∀ n, N ≤ n → ¬ Deriv [sigN n a] x

/-- **Every non-top element is `σᵈ y` for a unique `d` and a `y ∈ L₀` unique up
to `⊣⊢`.** -/
def OrbitsVsL0 : Prop := ∀ x : PLLFormula, atomFree x = true → ¬ Deriv [] x →
  (∃ d y, atomFree y = true ∧ shell 0 y ∧ Interd (sigN d y) x) ∧
  (∀ d d' y y', atomFree y = true → atomFree y' = true → shell 0 y → shell 0 y' →
    Interd (sigN d y) x → Interd (sigN d' y') x → d = d' ∧ Interd y y')

/-! ### Designed cells (stage 2) -/

/-- `σ²⊥` is a colour of `D 0`, `D 1`, `D 2`, not of `D 3`. -/
def CellSig2Colour : Prop :=
  IsColour (0 : ℕ) (sigN 2 .falsePLL) ∧ IsColour (1 : ℕ) (sigN 2 .falsePLL) ∧
    IsColour (2 : ℕ) (sigN 2 .falsePLL) ∧ ¬ IsColour (3 : ℕ) (sigN 2 .falsePLL)

/-- `⊤` is a colour of every `D n` and of `D ⊤`. -/
def CellTopColour : Prop := (∀ n : ℕ, IsColour n truePLL) ∧ IsColour ⊤ truePLL

/-- `σ²⊥` is in the red bag of `D 1` and `D 2`, not of `D 3`. -/
def CellSig2Red : Prop :=
  InBag .red (1 : ℕ) (sigN 2 .falsePLL) ∧ InBag .red (2 : ℕ) (sigN 2 .falsePLL) ∧
    ¬ InBag .red (3 : ℕ) (sigN 2 .falsePLL)

/-- Negative control: `⊥` is a colour of `D 0` but NOT of `D 1`. -/
def CtrlBot : Prop := IsColour (0 : ℕ) .falsePLL ∧ ¬ IsColour (1 : ℕ) .falsePLL

/-- The orbits of `⊥` and `◯⊥` have different thread limits. -/
def CellThreadsDiffer : Prop := thread .falsePLL ⊤ ≠ thread (.somehow .falsePLL) ⊤

/-- The shift, at `a = ⊥`, `n = 0`: `T_{σ⊥}(0)` and `T_⊥(1)` carry the same
colour but differ, and so do their limits. -/
def CellThreadShift : Prop :=
  (∀ z, ZFSet.pair (tag 1) z ∈ thread (sig .falsePLL) (0 : ℕ) ↔
      ZFSet.pair (tag 1) z ∈ thread .falsePLL (1 : ℕ)) ∧
    thread (sig .falsePLL) (0 : ℕ) ≠ thread .falsePLL (1 : ℕ) ∧
    thread (sig .falsePLL) ⊤ ≠ thread .falsePLL ⊤

/-- Thread readback in `rb`: the limits of `⊥` and `◯⊥` are in `D(ω)`, that of
`σ⊥ = t3` is not. -/
def CellThreadReadback : Prop :=
  ZFSet.pair (tag 3) (thread .falsePLL ⊤) ∈ DF rb ⊤ ∧
    ZFSet.pair (tag 3) (thread (.somehow .falsePLL) ⊤) ∈ DF rb ⊤ ∧
    ZFSet.pair (tag 3) (thread (sig .falsePLL) ⊤) ∉ DF rb ⊤

end Stmt

end InsideOut
end F0
end PLLND

/-! ## Axiom pins -/

#axioms_within PLLND.F0.InsideOut.tag_succ_ne_zero [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.rbCode_inj [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.rbS_inv [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.rbBase_af [propext, Quot.sound]
