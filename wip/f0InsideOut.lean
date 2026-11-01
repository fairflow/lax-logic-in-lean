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
         ∪ { (3, T_{a_c}(ω)) : c a colour with a base a_c }  thread limits (level ω only)

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
(stage 1, `ec8fae2`).  Each is proved by the theorem of the snake-case name:
`Stmt.MemOrderIff` by `mem_order_iff`, `Stmt.LimEqTop` by `lim_eq_top`, and so
on (Parts D to G).

The example colouring `rb`: red `= {σᵐ⊥ : m ∈ ℕ}` with base `⊥`, blue
`= {◯σᵐ⊥ : m ∈ ℕ}` with base `◯⊥` (each colour is the orbit of its base,
since `σᵐ(◯⊥) = ◯σᵐ⊥`).

## Results (all PROVED, pins at the end)

Generic, for every label family `lab`:

    D lab i = range (j < i ↦ (0, D lab j)) ∪ ⋃ₖ {k+1} × lab k i       (d_unfold)
    (0, D lab j) ∈ D lab i  ⟺  j < i                                   (mem_order_iff)
    (k+1, x) ∈ D lab i  ⟺  x ∈ lab k i                                 (mem_label_iff)
    D lab i = D lab j  ⟹  i = j                                         (D_injective)
    (0, D lab n) ∈ D lab ⊤   for every n : ℕ                            (mem_top)

`D_injective` is foundation: `D i = D j` with `j < i` would put `D j` on an
`∈`-cycle of length three (`no_mem3`).

The F0 instance, for closed `x`, `a`, `b`:

    (1, classCode x) ∈ D i  ⟺  x ∈ σⁱ(F0)                               (colour_iff)
    x ∈ S c ∧ x ∈ σⁱ(F0)  ⟺  classCode x ∈ the c-bag of D i            (readback, bag_iff)
    T_a(ω) = T_b(ω)  ⟺  a ⊣⊢ b                                          (thread_limit_iff)
    (3, T_a(ω)) ∈ D(ω)  ⟺  a ⊣⊢ a_c for some chosen base a_c           (thread_readback)

F0 facts:

    σ maps Lₙ = σⁿ(F0) ∖ σⁿ⁺¹(F0) one-to-one onto Lₙ₊₁                (shell_shift)
    x ∈ σ^ω(F0)  ⟺  ⊢ x                                                 (lim_eq_top)
    ⊬ x  ⟹  ∃ N, ∀ n ≥ N, σⁿ a ⊬ x                                     (orbit_order_limit)
    ⊬ x  ⟹  x ⊣⊢ σᵈ y with y ∈ L₀, d unique, y unique up to ⊣⊢        (orbits_vs_L0)

**The fixpoint argument** (`bot_everywhere`).  On a finite subframe model
the truth sets `Uₙ` of `σⁿ⊥` increase (`sigN_bot_strict`), so `Uₙ = Uₙ₊₁`
for some `n` (`stabilise`, by counting).  Since

    σⁿ⁺¹⊥ = ◯σⁿ⊥ ∨ (◯σⁿ⊥ ↠ σⁿ⊥)                                         (sigN_succ_bot)

the fixed set `U` satisfies `j(U) ⊆ U`, so `j(U) ⇒ U` holds everywhere, and
so does `U`.  A finite countermodel of `x` (`SubTab.complete`) then refutes
`σⁿ⊥ ⊢ x`, hence `σⁿ a ⊢ x` (`sigN_bot_le`), from some `N` on
(`cm_eventually`); `lim_eq_top` and `orbit_order_limit` follow.

**Classical.choice.**  `ZFSet.range` (through `Quotient.out`) and
`ZFSet.mem_range`, `ZFSet.mem_prod` use it, so `D`, `classCode` and every
theorem about the decoration or its readback do; `code` also reaches it
through `String.toList` (Lean core v4.31).  `orbits_vs_L0` uses it through
excluded middle on `inSig` (`exists_last`).  `shell_shift`, `lim_eq_top`,
`orbit_order_limit` and the arithmetic of the fixpoint argument are
`[propext, Quot.sound]`.
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

/-! ## Part D. Proofs: the generic decoration -/

theorem tag_injective : Function.Injective tag := by
  intro m n h
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => rfl
      | succ n => exact absurd h.symm (tag_succ_ne_zero n)
  | succ m ih =>
      cases n with
      | zero => exact absurd h (tag_succ_ne_zero m)
      | succ n =>
          have h' : ({tag m} : ZFSet.{0}) = {tag n} := h
          exact congrArg (· + 1) (ih (ZFSet.singleton_injective h'))

theorem tag_inj {m n : ℕ} : tag m = tag n ↔ m = n :=
  ⟨fun h => tag_injective h, fun h => h ▸ rfl⟩

theorem pair_ne_empty (x y : ZFSet.{0}) : ZFSet.pair x y ≠ ∅ := by
  intro h
  have h1 : ({x} : ZFSet.{0}) ∈ ZFSet.pair x y := ZFSet.mem_pair.mpr (Or.inl rfl)
  rw [h] at h1
  exact ZFSet.notMem_empty _ h1

/-- No `∈`-cycle of length three (foundation, `ZFSet.inductionOn`). -/
theorem no_mem3 (a : ZFSet.{0}) : ∀ b c : ZFSet.{0}, a ∈ b → b ∈ c → c ∈ a → False :=
  ZFSet.inductionOn (p := fun a => ∀ b c : ZFSet.{0}, a ∈ b → b ∈ c → c ∈ a → False) a
    (fun _ ih b c hab hbc hca => ih c hca _ b hca hab hbc)

/-- **The unfolding equation.** -/
theorem d_unfold : Stmt.DUnfold := fun lab i => WellFounded.fix_eq _ (Dstep lab) i

/-- **Membership in `D lab i`.** -/
theorem mem_D_iff : Stmt.MemDIff := by
  intro lab i z
  rw [d_unfold, ZFSet.mem_union, ZFSet.mem_range, ZFSet.mem_iUnion]
  apply or_congr
  · constructor
    · rintro ⟨⟨j, hj⟩, rfl⟩
      exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
  · constructor
    · rintro ⟨k, hk⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp hk
      rw [ZFSet.mem_singleton.mp ha]
      exact ⟨k, b, hb, rfl⟩
    · rintro ⟨k, x, hx, rfl⟩
      exact ⟨k, ZFSet.mem_prod.mpr ⟨_, ZFSet.mem_singleton.mpr rfl, x, hx, rfl⟩⟩

theorem order_mem (lab : ℕ → WithTop ℕ → ZFSet.{0}) {i j : WithTop ℕ} (h : j < i) :
    ZFSet.pair (tag 0) (D lab j) ∈ D lab i :=
  (mem_D_iff lab i _).mpr (Or.inl ⟨j, h, rfl⟩)

theorem not_order_mem_self (lab : ℕ → WithTop ℕ → ZFSet.{0}) (i : WithTop ℕ) :
    ZFSet.pair (tag 0) (D lab i) ∉ D lab i := fun h =>
  no_mem3 (D lab i) {tag 0, D lab i} (ZFSet.pair (tag 0) (D lab i))
    (ZFSet.mem_pair.mpr (Or.inr rfl)) (ZFSet.mem_pair.mpr (Or.inr rfl)) h

/-- **`D lab` is one-to-one.** -/
theorem D_injective : Stmt.DInjective := by
  intro lab i j h
  rcases lt_trichotomy i j with hij | hij | hij
  · have hm := order_mem lab hij
    rw [h] at hm
    exact absurd hm (not_order_mem_self lab j)
  · exact hij
  · have hm := order_mem lab hij
    rw [← h] at hm
    exact absurd hm (not_order_mem_self lab i)

/-- **The order is read off by membership**: `(0, D j) ∈ D i ↔ j < i`. -/
theorem mem_order_iff : Stmt.MemOrderIff := by
  intro lab i j
  refine ⟨fun h => ?_, order_mem lab⟩
  rcases (mem_D_iff lab i _).mp h with ⟨k, hk, he⟩ | ⟨k, x, _, he⟩
  · rw [D_injective lab (ZFSet.pair_inj.mp he).2]
    exact hk
  · exact absurd (tag_inj.mp (ZFSet.pair_inj.mp he).1) (Nat.succ_ne_zero k).symm

/-- **The labels are read off by membership.** -/
theorem mem_label_iff : Stmt.MemLabelIff := by
  intro lab i k x
  refine ⟨fun h => ?_, fun h => (mem_D_iff lab i _).mpr (Or.inr ⟨k, x, h, rfl⟩)⟩
  rcases (mem_D_iff lab i _).mp h with ⟨j, _, he⟩ | ⟨k', x', hx', he⟩
  · exact absurd (tag_inj.mp (ZFSet.pair_inj.mp he).1) (Nat.succ_ne_zero k)
  · obtain ⟨h1, h2⟩ := ZFSet.pair_inj.mp he
    have hk : k = k' := by
      have := tag_inj.mp h1
      omega
    subst hk
    subst h2
    exact hx'

/-- **Every finite level is a member of the top.** -/
theorem mem_top : Stmt.MemTop := fun lab n => order_mem lab (WithTop.coe_lt_top n)

/-- **The single-label form.** -/
theorem d1_unfold : Stmt.D1Unfold := by
  intro lab i
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_union, ZFSet.mem_range, ZFSet.mem_prod]
  show z ∈ D (single lab) i ↔ _
  rw [mem_D_iff]
  apply or_congr
  · constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
    · rintro ⟨⟨j, hj⟩, rfl⟩
      exact ⟨j, hj, rfl⟩
  · constructor
    · rintro ⟨k, x, hx, rfl⟩
      cases k with
      | zero => exact ⟨_, ZFSet.mem_singleton.mpr rfl, x, hx, rfl⟩
      | succ k => exact absurd hx (ZFSet.notMem_empty x)
    · rintro ⟨a, ha, b, hb, rfl⟩
      rw [ZFSet.mem_singleton.mp ha]
      exact ⟨0, b, hb, rfl⟩

/-! ## Part E. Proofs: the F0 instance -/

theorem natsCode_injective : Function.Injective natsCode := by
  intro l
  induction l with
  | nil =>
      intro l' h
      cases l' with
      | nil => rfl
      | cons n l' =>
          exact absurd (show ZFSet.pair (tag n) (natsCode l') = ∅ from h.symm) (pair_ne_empty _ _)
  | cons n l ih =>
      intro l' h
      cases l' with
      | nil => exact absurd (show ZFSet.pair (tag n) (natsCode l) = ∅ from h) (pair_ne_empty _ _)
      | cons n' l' =>
          obtain ⟨h1, h2⟩ := ZFSet.pair_inj.mp
            (show ZFSet.pair (tag n) (natsCode l) = ZFSet.pair (tag n') (natsCode l') from h)
          rw [tag_injective h1, ih h2]

theorem strCode_injective : Function.Injective strCode := by
  intro s t h
  have h1 : s.toList.map Char.toNat = t.toList.map Char.toNat := natsCode_injective h
  have h2 : s.toList = t.toList :=
    List.map_injective_iff.mpr (fun _ _ e => Char.toNat_inj.mp e) h1
  exact String.toList_inj.mp h2

/-- **The structural code is one-to-one.** -/
theorem code_injective : Stmt.CodeInjective := by
  intro φ
  induction φ with
  | prop a =>
      intro ψ h
      cases ψ <;> first
        | exact congrArg PLLFormula.prop (strCode_injective (ZFSet.pair_inj.mp h).2)
        | simp [code, tag_inj] at h
  | falsePLL =>
      intro ψ h
      cases ψ <;> first
        | rfl
        | simp [code, tag_inj] at h
  | and A B ihA ihB =>
      intro ψ h
      cases ψ <;> first
        | exact congrArg₂ PLLFormula.and (ihA (ZFSet.pair_inj.mp (ZFSet.pair_inj.mp h).2).1)
            (ihB (ZFSet.pair_inj.mp (ZFSet.pair_inj.mp h).2).2)
        | simp [code, tag_inj] at h
  | or A B ihA ihB =>
      intro ψ h
      cases ψ <;> first
        | exact congrArg₂ PLLFormula.or (ihA (ZFSet.pair_inj.mp (ZFSet.pair_inj.mp h).2).1)
            (ihB (ZFSet.pair_inj.mp (ZFSet.pair_inj.mp h).2).2)
        | simp [code, tag_inj] at h
  | ifThen A B ihA ihB =>
      intro ψ h
      cases ψ <;> first
        | exact congrArg₂ PLLFormula.ifThen (ihA (ZFSet.pair_inj.mp (ZFSet.pair_inj.mp h).2).1)
            (ihB (ZFSet.pair_inj.mp (ZFSet.pair_inj.mp h).2).2)
        | simp [code, tag_inj] at h
  | somehow A ih =>
      intro ψ h
      cases ψ <;> first
        | exact congrArg PLLFormula.somehow (ih (ZFSet.pair_inj.mp h).2)
        | simp [code, tag_inj] at h

theorem mem_classCode {x : PLLFormula} {z : ZFSet.{0}} :
    z ∈ classCode x ↔ ∃ y, atomFree y = true ∧ Interd y x ∧ code y = z := by
  unfold classCode
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨⟨y, hy, hyx⟩, rfl⟩
    exact ⟨y, hy, hyx, rfl⟩
  · rintro ⟨y, hy, hyx, rfl⟩
    exact ⟨⟨y, hy, hyx⟩, rfl⟩

theorem classCode_eq_of_interd {x x' : PLLFormula} (h : Interd x x') :
    classCode x = classCode x' := by
  apply ZFSet.ext
  intro z
  rw [mem_classCode, mem_classCode]
  constructor
  · rintro ⟨y, hy, hyx, rfl⟩
    exact ⟨y, hy, hyx.trans h, rfl⟩
  · rintro ⟨y, hy, hyx, rfl⟩
    exact ⟨y, hy, hyx.trans h.symm, rfl⟩

theorem interd_of_classCode_eq {x x' : PLLFormula} (hx : atomFree x = true)
    (h : classCode x = classCode x') : Interd x x' := by
  have h1 : code x ∈ classCode x' := by
    rw [← h]
    exact mem_classCode.mpr ⟨x, hx, Interd.refl x, rfl⟩
  obtain ⟨y, _, hyx, hc⟩ := mem_classCode.mp h1
  rw [code_injective hc] at hyx
  exact hyx

/-- **Class codes are equal exactly on `⊣⊢`-classes.** -/
theorem classCode_eq_iff : Stmt.ClassCodeEqIff := fun _ _ hx =>
  ⟨interd_of_classCode_eq hx, classCode_eq_of_interd⟩

theorem inLevel_coe {n : ℕ} {x : PLLFormula} : inLevel (n : WithTop ℕ) x ↔ inSig n x := Iff.rfl

theorem inLevel_top {x : PLLFormula} : inLevel ⊤ x ↔ inLim x := Iff.rfl

theorem inSig_of {n : ℕ} {x : PLLFormula} (y : PLLFormula) (hy : atomFree y = true)
    (h : Interd (sigN n y) x) : inSig n x := ⟨y, hy, h⟩

theorem inSig_congr {n : ℕ} {x x' : PLLFormula} (h : Interd x x') (hx : inSig n x) :
    inSig n x' := by
  obtain ⟨y, hy, hi⟩ := hx
  exact ⟨y, hy, hi.trans h⟩

theorem inLevel_congr : ∀ {i : WithTop ℕ} {x x' : PLLFormula}, Interd x x' →
    inLevel i x → inLevel i x'
  | none, _, _, h, hx => fun n => inSig_congr h (hx n)
  | some _, _, _, h, hx => inSig_congr h hx

theorem mem_colLab {i : WithTop ℕ} {x : PLLFormula} (hx : atomFree x = true) :
    classCode x ∈ colLab i ↔ inLevel i x := by
  unfold colLab
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨⟨x', hx', hl⟩, he⟩
    exact inLevel_congr (interd_of_classCode_eq hx' he) hl
  · intro hl
    exact ⟨⟨x, hx, hl⟩, rfl⟩

/-- **Colour readback.** -/
theorem colour_iff : Stmt.ColourIff := fun K i x hx =>
  (mem_label_iff (lab K) i 0 (classCode x)).trans (mem_colLab hx)

theorem mem_bagLab {K : Colouring} {i : WithTop ℕ} {c : K.C} {B : ZFSet.{0}} :
    ZFSet.pair (K.ccode c) B ∈ bagLab K i ↔ B = bagSet K c i := by
  unfold bagLab
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨c', he⟩
    obtain ⟨h1, h2⟩ := ZFSet.pair_inj.mp he
    rw [K.ccode_inj h1] at h2
    exact h2.symm
  · rintro rfl
    exact ⟨c, rfl⟩

/-- **The `c`-bag of `DF K i` is unique.** -/
theorem bag_iff : Stmt.BagIff := fun K i _ _ =>
  (mem_label_iff (lab K) i 1 _).trans mem_bagLab

theorem mem_bagSet {K : Colouring} {c : K.C} {i : WithTop ℕ} {x : PLLFormula}
    (hx : atomFree x = true) : classCode x ∈ bagSet K c i ↔ K.S c x ∧ inLevel i x := by
  unfold bagSet
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨⟨x', hx', hl, hS⟩, he⟩
    have hi := interd_of_classCode_eq hx' he
    exact ⟨K.S_inv c x' x hi hS, inLevel_congr hi hl⟩
  · rintro ⟨hS, hl⟩
    exact ⟨⟨x, hx, hl, hS⟩, rfl⟩

/-- **Bag readback.** -/
theorem readback : Stmt.Readback := by
  intro K i c x hx
  rw [← mem_bagSet hx]
  constructor
  · intro h
    exact ⟨_, (bag_iff K i c _).mpr rfl, h⟩
  · rintro ⟨B, hB, hx'⟩
    rw [(bag_iff K i c B).mp hB] at hx'
    exact hx'

/-! ### Threads -/

theorem not_lt_coe_zero (j : WithTop ℕ) : ¬ j < ((0 : ℕ) : WithTop ℕ) := by
  cases j with
  | top => exact WithTop.not_top_lt _
  | coe m => exact fun h => Nat.not_lt_zero m (WithTop.coe_lt_coe.mp h)

theorem mem_thread_label {a : PLLFormula} {i : WithTop ℕ} {z : ZFSet.{0}} :
    ZFSet.pair (tag 1) z ∈ thread a i ↔ z ∈ threadLab a i :=
  mem_label_iff (single (threadLab a)) i 0 z

/-- `T_a(0)` has no order member. -/
theorem thread_zero_no_order (a : PLLFormula) (y : ZFSet.{0}) :
    ZFSet.pair (tag 0) y ∉ thread a ((0 : ℕ) : WithTop ℕ) := by
  intro h
  rcases (mem_D_iff _ _ _).mp h with ⟨j, hj, _⟩ | ⟨k, x, _, he⟩
  · exact not_lt_coe_zero j hj
  · exact absurd (tag_inj.mp (ZFSet.pair_inj.mp he).1) (Nat.succ_ne_zero k).symm

/-- **Thread limits determine their base**: `T_a(ω) = T_b(ω) → a ⊣⊢ b`. -/
theorem thread_limit_injective : Stmt.ThreadLimitInjective := by
  intro a b ha h
  have h0 : ZFSet.pair (tag 0) (thread a ((0 : ℕ) : WithTop ℕ)) ∈ thread b ⊤ := by
    rw [← h]
    exact mem_top (single (threadLab a)) 0
  rcases (mem_D_iff _ _ _).mp h0 with ⟨j, hj, he⟩ | ⟨k, x, _, he⟩
  · have hj' := (ZFSet.pair_inj.mp he).2
    cases j with
    | top => exact absurd hj (lt_irrefl _)
    | coe m =>
      cases m with
      | zero =>
          have h1 : ZFSet.pair (tag 1) (classCode a) ∈ thread b ((0 : ℕ) : WithTop ℕ) := by
            have h1' : ZFSet.pair (tag 1) (classCode a) ∈ thread a ((0 : ℕ) : WithTop ℕ) :=
              mem_thread_label.mpr (ZFSet.mem_singleton.mpr rfl)
            rw [hj'] at h1'
            exact h1'
          exact interd_of_classCode_eq ha (ZFSet.mem_singleton.mp (mem_thread_label.mp h1))
      | succ m =>
          have h2 : ZFSet.pair (tag 0) (thread b ((0 : ℕ) : WithTop ℕ)) ∈
              thread a ((0 : ℕ) : WithTop ℕ) := by
            rw [hj']
            exact order_mem _ (WithTop.coe_lt_coe.mpr (Nat.succ_pos m))
          exact (thread_zero_no_order a _ h2).elim
  · exact absurd (tag_inj.mp (ZFSet.pair_inj.mp he).1) (Nat.succ_ne_zero k).symm

theorem sigN_interd (n : ℕ) {a b : PLLFormula} (ha : atomFree a = true) (hb : atomFree b = true)
    (h : Interd a b) : Interd (sigN n a) (sigN n b) :=
  ⟨sigN_mono n ha hb h.1, sigN_mono n hb ha h.2⟩

theorem sig_interd {a b : PLLFormula} (ha : atomFree a = true) (hb : atomFree b = true)
    (h : Interd a b) : Interd (sig a) (sig b) :=
  ⟨sig_mono ha hb h.1, sig_mono hb ha h.2⟩

theorem interd_of_sigN (n : ℕ) {a b : PLLFormula} (h : Interd (sigN n a) (sigN n b)) :
    Interd a b :=
  ⟨sigN_reflects_ctx n h.1, sigN_reflects_ctx n h.2⟩

theorem threadLab_congr {a b : PLLFormula} (ha : atomFree a = true) (hb : atomFree b = true)
    (h : Interd a b) : threadLab a = threadLab b := by
  funext i
  cases i with
  | top => rfl
  | coe n =>
      show ({classCode (sigN n a)} : ZFSet.{0}) = {classCode (sigN n b)}
      rw [classCode_eq_of_interd (sigN_interd n ha hb h)]

/-- **With the converse.** -/
theorem thread_limit_iff : Stmt.ThreadLimitIff := fun a b ha hb =>
  ⟨thread_limit_injective a b ha, fun h => by
    show D1 (threadLab a) ⊤ = D1 (threadLab b) ⊤
    rw [threadLab_congr ha hb h]⟩

theorem mem_thrLab_top {K : Colouring} {a : PLLFormula} (ha : atomFree a = true) :
    thread a ⊤ ∈ thrLab K ⊤ ↔ ∃ c a', K.base c = some a' ∧ Interd a' a := by
  show thread a ⊤ ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨⟨⟨c, a'⟩, hc⟩, he⟩
    exact ⟨c, a', hc, thread_limit_injective a' a (K.base_af c a' hc) he⟩
  · rintro ⟨c, a', hc, hi⟩
    exact ⟨⟨⟨c, a'⟩, hc⟩, (thread_limit_iff a' a (K.base_af c a' hc) ha).mpr hi⟩

/-- **Thread readback.** -/
theorem thread_readback : Stmt.ThreadReadback := fun K _ ha =>
  (mem_label_iff (lab K) ⊤ 2 _).trans (mem_thrLab_top ha)

/-- **No thread limit at a finite level.** -/
theorem threads_only_at_top : Stmt.ThreadsOnlyAtTop := fun K n z h =>
  ZFSet.notMem_empty z ((mem_label_iff (lab K) n 2 z).mp h)

/-! ## Part F. Proofs: F0 facts -/

theorem sig_sigN : ∀ (n : ℕ) (φ : PLLFormula), sig (sigN n φ) = sigN n (sig φ)
  | 0, _ => rfl
  | n + 1, φ => sig_sigN n (sig φ)

theorem sigN_succ (n : ℕ) (φ : PLLFormula) : sigN (n + 1) φ = sig (sigN n φ) :=
  (sig_sigN n φ).symm

theorem sigN_add : ∀ (k m : ℕ) (φ : PLLFormula), sigN (m + k) φ = sigN m (sigN k φ)
  | 0, _, _ => rfl
  | k + 1, m, φ => sigN_add k m (sig φ)

theorem sigN_or : ∀ (n : ℕ) (A B : PLLFormula), sigN n (.or A B) = .or (sigN n A) (sigN n B)
  | 0, _, _ => rfl
  | n + 1, A, B => sigN_or n (sig A) (sig B)

theorem sigN_somehow : ∀ (n : ℕ) (A : PLLFormula), sigN n (.somehow A) = .somehow (sigN n A)
  | 0, _ => rfl
  | n + 1, A => sigN_somehow n (sig A)

/-- `σⁿ⁺¹⊥ = ◯σⁿ⊥ ∨ (◯σⁿ⊥ ↠ σⁿ⊥)`. -/
theorem sigN_succ_bot (n : ℕ) : sigN (n + 1) .falsePLL =
    .or (.somehow (sigN n .falsePLL)) (.ifThen (.somehow (sigN n .falsePLL)) (sigN n .falsePLL)) := by
  show sigN n (.or (.somehow .falsePLL) (.ifThen (.somehow .falsePLL) .falsePLL)) = _
  rw [sigN_or, sigN_imp, sigN_somehow]

theorem inSig_succ {n : ℕ} {x : PLLFormula} (h : inSig (n + 1) x) : inSig n x := by
  obtain ⟨y, hy, hi⟩ := h
  exact ⟨sig y, sig_vf hy, hi⟩

theorem inSig_sig {n : ℕ} {x : PLLFormula} (hx : atomFree x = true) (h : inSig n x) :
    inSig (n + 1) (sig x) := by
  obtain ⟨y, hy, hi⟩ := h
  refine ⟨y, hy, ?_⟩
  rw [sigN_succ]
  exact sig_interd (sigN_vf n hy) hx hi

theorem inSig_of_sig {n : ℕ} {x : PLLFormula} (h : inSig (n + 1) (sig x)) : inSig n x := by
  obtain ⟨y, hy, hi⟩ := h
  refine ⟨y, hy, ?_⟩
  rw [sigN_succ] at hi
  exact ⟨sig_reflects_ctx hi.1, sig_reflects_ctx hi.2⟩

/-- **`σ` maps the shell `Lₙ` one-to-one onto `Lₙ₊₁`.** -/
theorem shell_shift : Stmt.ShellShift := by
  intro n
  refine ⟨fun x hx ⟨h1, h2⟩ => ⟨inSig_sig hx h1, fun h3 => h2 (inSig_of_sig h3)⟩,
    fun x x' _ _ _ _ h => ⟨sig_reflects_ctx h.1, sig_reflects_ctx h.2⟩, ?_⟩
  intro z _ hz
  obtain ⟨⟨y, hy, hi⟩, h2⟩ := hz
  refine ⟨sigN n y, sigN_vf n hy, ⟨⟨y, hy, Interd.refl _⟩, fun h3 => h2 ?_⟩, ?_⟩
  · obtain ⟨y', hy', hi'⟩ := h3
    refine ⟨y', hy', ?_⟩
    rw [sigN_succ]
    refine Interd.trans (sig_interd (sigN_vf _ hy') (sigN_vf n hy) hi') ?_
    rw [← sigN_succ]
    exact hi
  · rw [← sigN_succ]
    exact hi

/-! ### The fixpoint argument on a finite model -/

/-- `true ↦ 1`, `false ↦ 0`. -/
def b2n : Bool → ℕ
  | true => 1
  | false => 0

/-- The number of `i < N` with `g i = true`. -/
def cnt (g : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | N + 1 => cnt g N + b2n (g N)

theorem b2n_le_one (b : Bool) : b2n b ≤ 1 := by
  cases b
  · exact Nat.zero_le 1
  · exact le_refl 1

theorem cnt_le (g : ℕ → Bool) : ∀ N, cnt g N ≤ N
  | 0 => le_refl 0
  | N + 1 => by
      have h1 := cnt_le g N
      have h2 := b2n_le_one (g N)
      show cnt g N + b2n (g N) ≤ N + 1
      omega

theorem b2n_mono {a b : Bool} (h : a = true → b = true) : b2n a ≤ b2n b := by
  cases a
  · exact Nat.zero_le _
  · rw [h rfl]

theorem cnt_mono {g h : ℕ → Bool} :
    ∀ N, (∀ i, i < N → g i = true → h i = true) → cnt g N ≤ cnt h N
  | 0, _ => le_refl 0
  | N + 1, H => by
      have ih := cnt_mono N (fun i hi => H i (Nat.lt_succ_of_lt hi))
      have key := b2n_mono (H N (Nat.lt_succ_self N))
      show cnt g N + b2n (g N) ≤ cnt h N + b2n (h N)
      omega

theorem cnt_lt {g h : ℕ → Bool} :
    ∀ N, (∀ i, i < N → g i = true → h i = true) →
      ∀ j, j < N → g j = false → h j = true → cnt g N < cnt h N
  | 0, _, j, hj, _, _ => absurd hj (Nat.not_lt_zero j)
  | N + 1, H, j, hj, hg, hh => by
      have hmono := cnt_mono N (fun i hi => H i (Nat.lt_succ_of_lt hi))
      have key := b2n_mono (H N (Nat.lt_succ_self N))
      show cnt g N + b2n (g N) < cnt h N + b2n (h N)
      rcases (by omega : j < N ∨ j = N) with hj' | hj'
      · have ih := cnt_lt N (fun i hi => H i (Nat.lt_succ_of_lt hi)) j hj' hg hh
        omega
      · subst hj'
        rw [hg, hh]
        simp only [b2n]
        omega

/-- `p i = true` for every `i < N`, as a Boolean. -/
def allBelow (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | N + 1 => allBelow p N && p N

theorem allBelow_true {p : ℕ → Bool} :
    ∀ {N : ℕ}, allBelow p N = true → ∀ i, i < N → p i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | N + 1, h, i, hi => by
      have h' : allBelow p N = true ∧ p N = true := by
        simp only [allBelow, Bool.and_eq_true] at h
        exact h
      rcases (by omega : i < N ∨ i = N) with hi' | hi'
      · exact allBelow_true h'.1 i hi'
      · rw [hi']
        exact h'.2

theorem allBelow_false {p : ℕ → Bool} :
    ∀ {N : ℕ}, allBelow p N = false → ∃ i, i < N ∧ p i = false
  | 0, h => absurd h (by simp [allBelow])
  | N + 1, h => by
      cases hN : p N with
      | false => exact ⟨N, Nat.lt_succ_self N, hN⟩
      | true =>
          have h' : allBelow p N = false := by
            have h2 : (allBelow p N && p N) = false := h
            rw [hN, Bool.and_true] at h2
            exact h2
          obtain ⟨i, hi, hp⟩ := allBelow_false h'
          exact ⟨i, Nat.lt_succ_of_lt hi, hp⟩

theorem stab_aux (f : ℕ → ℕ → Bool) (N : ℕ)
    (mono : ∀ n i, i < N → f n i = true → f (n + 1) i = true) :
    ∀ k, (∃ n, ∀ i, i < N → f (n + 1) i = true → f n i = true) ∨ k ≤ cnt (f k) N
  | 0 => Or.inr (Nat.zero_le _)
  | k + 1 => by
      rcases stab_aux f N mono k with h | h
      · exact Or.inl h
      · cases hq : allBelow (fun i => !(f (k + 1) i) || f k i) N with
        | true =>
            refine Or.inl ⟨k, fun i hi h1 => ?_⟩
            have h2 := allBelow_true hq i hi
            rw [h1] at h2
            exact h2
        | false =>
            obtain ⟨j, hj, hp⟩ := allBelow_false hq
            have hb : f (k + 1) j = true ∧ f k j = false := by
              revert hp
              cases f (k + 1) j <;> cases f k j <;> decide
            have := cnt_lt N (mono k) j hj hb.2 hb.1
            right
            omega

/-- **A monotone sequence of subsets of a finite set stabilises.** -/
theorem stabilise (f : ℕ → ℕ → Bool) (N : ℕ)
    (mono : ∀ n i, i < N → f n i = true → f (n + 1) i = true) :
    ∃ n, ∀ i, i < N → f (n + 1) i = true → f n i = true := by
  rcases stab_aux f N mono (N + 1) with h | h
  · exact h
  · exact absurd (h.trans (cnt_le _ N)) (Nat.not_succ_le_self N)

/-- **In a finite subframe model, `σᴺ⊥` eventually holds everywhere.**  The
truth sets of `σⁿ⊥` increase (`sigN_bot_strict`), so they stop at some `U`
with `j(U) ∪ (j(U) ⇒ U) = U`; then `j(U) ⊆ U`, so `j(U) ⇒ U` is everything,
and so is `U`. -/
theorem bot_everywhere (m : SubTab.SubCM) (hok : m.okB = true) :
    ∃ N, ∀ i, i < m.n → m.forceB i (sigN N .falsePLL) = true := by
  have fiff : ∀ (φ : PLLFormula) (i : ℕ) (hi : i < m.n),
      m.forceB i φ = true ↔ (m.toModel hok).force ⟨i, hi⟩ φ :=
    fun φ i hi => SubTab.SubCM.forceB_iff hok φ ⟨i, hi⟩
  have mono : ∀ n i, i < m.n → m.forceB i (sigN n .falsePLL) = true →
      m.forceB i (sigN (n + 1) .falsePLL) = true := by
    intro n i hi h
    obtain ⟨d⟩ := (sigN_bot_strict n).1
    exact (fiff _ i hi).mpr (SubframeModel.CF.soundness₁ d (m.toModel hok) ⟨i, hi⟩
      ((fiff _ i hi).mp h))
  obtain ⟨n, hn⟩ := stabilise (fun n i => m.forceB i (sigN n .falsePLL)) m.n mono
  refine ⟨n, fun i hi => (fiff _ i hi).mpr ?_⟩
  have back : ∀ w : (m.toModel hok).W, (m.toModel hok).force w (sigN (n + 1) .falsePLL) →
      (m.toModel hok).force w (sigN n .falsePLL) :=
    fun w hw => (fiff _ w.1 w.2).mp (hn w.1 w.2 ((fiff _ w.1 w.2).mpr hw))
  rw [sigN_succ_bot] at back
  have himp : ∀ w : (m.toModel hok).W, (m.toModel hok).force w
      (.ifThen (.somehow (sigN n .falsePLL)) (sigN n .falsePLL)) :=
    fun _ v _ hv => back v (Or.inl hv)
  exact back ⟨i, hi⟩ (Or.inr (himp ⟨i, hi⟩))

/-- **A finite countermodel of `x` refutes `σⁿ⊥ ⊢ x` from some `N` on.** -/
theorem cm_eventually {x : PLLFormula} {m : SubTab.SubCM} (hm : m.refutes x = true) :
    ∃ N, ∀ n, N ≤ n → ¬ Deriv [sigN n .falsePLL] x := by
  simp only [SubTab.SubCM.refutes, Bool.and_eq_true, Bool.not_eq_true'] at hm
  obtain ⟨hok, hroot⟩ := hm
  have hr := (SubTab.SubCM.ok_parts hok).1
  obtain ⟨N, hN⟩ := bot_everywhere m hok
  refine ⟨N, fun n hn hd => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hle : Deriv [sigN N .falsePLL] (sigN (N + k) .falsePLL) := by
    rw [sigN_add k N]
    exact sigN_bot_le N _ (sigN_vf k rfl)
  obtain ⟨d⟩ := Deriv.cutHead hle hd
  have hf := SubframeModel.CF.soundness₁ d (m.toModel hok) ⟨m.root, hr⟩
    ((SubTab.SubCM.forceB_iff hok _ ⟨m.root, hr⟩).mp (hN m.root hr))
  have hb := (SubTab.SubCM.forceB_iff hok x ⟨m.root, hr⟩).mpr hf
  rw [hroot] at hb
  exact Bool.false_ne_true hb

theorem inLim_of_deriv {x : PLLFormula} (h : Deriv [] x) : inLim x := by
  intro n
  refine ⟨truePLL, rfl, Deriv.rename (fun _ hχ => by cases hχ) h, ?_⟩
  have e : sigN n truePLL = .ifThen (sigN n .falsePLL) (sigN n .falsePLL) := sigN_imp n _ _
  rw [e]
  exact Deriv.impIntro (Deriv.iden (.head _))

/-- **The limit is the top**: `σ^ω(F0) = {⊤}`. -/
theorem lim_eq_top : Stmt.LimEqTop := by
  intro x _
  refine ⟨fun h => ?_, inLim_of_deriv⟩
  rcases SubTab.complete x with ⟨c, hc⟩ | ⟨m, hm⟩
  · exact SubTab.holds_of_check hc
  · have hm' : m.refutes x = true := hm
    obtain ⟨N, hN⟩ := cm_eventually hm'
    obtain ⟨y, hy, hi⟩ := h N
    exact absurd (Deriv.cutHead (sigN_bot_le N y hy) hi.1) (hN N le_rfl)

/-- **Orbits leave the upset of every non-top element.** -/
theorem orbit_order_limit : Stmt.OrbitOrderLimit := by
  intro a x ha hx
  rcases SubTab.complete x with ⟨c, hc⟩ | ⟨m, hm⟩
  · exact absurd (SubTab.holds_of_check hc) hx
  · have hm' : m.refutes x = true := hm
    obtain ⟨N, hN⟩ := cm_eventually hm'
    exact ⟨N, fun n hn hd => hN n hn (Deriv.cutHead (sigN_bot_le n a ha) hd)⟩

/-- The last level containing `x`, by excluded middle on `inSig`. -/
theorem exists_last {x : PLLFormula} (h0 : inSig 0 x) :
    ∀ N, ¬ inSig N x → ∃ d, inSig d x ∧ ¬ inSig (d + 1) x
  | 0, hN => absurd h0 hN
  | N + 1, hN => by
      by_cases h : inSig N x
      · exact ⟨N, h, hN⟩
      · exact exists_last h0 N h

/-- **Every non-top element of F0 is `σᵈ y` for a unique `d` and a `y ∈ L₀`
unique up to `⊣⊢`.** -/
theorem orbits_vs_L0 : Stmt.OrbitsVsL0 := by
  intro x hx hnd
  refine ⟨?_, ?_⟩
  · obtain ⟨N, hN⟩ := orbit_order_limit .falsePLL x rfl hnd
    have hnot : ¬ inSig N x := fun ⟨y, hy, hi⟩ =>
      hN N le_rfl (Deriv.cutHead (sigN_bot_le N y hy) hi.1)
    obtain ⟨d, ⟨z, hz, hzi⟩, hd⟩ := exists_last ⟨x, hx, Interd.refl x⟩ N hnot
    refine ⟨d, z, hz, ⟨⟨z, hz, Interd.refl z⟩, fun ⟨w, hw, hwi⟩ => hd ⟨w, hw, ?_⟩⟩, hzi⟩
    exact Interd.trans (sigN_interd d (sig_vf hw) hz hwi) hzi
  · intro d d' y y' hy hy' hs hs' h h'
    have key : ∀ {d d' : ℕ} {y y' : PLLFormula}, atomFree y' = true → shell 0 y →
        Interd (sigN d y) x → Interd (sigN d' y') x → ¬ d < d' := by
      intro d d' y y' hy' hs h h' hlt
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
      have e : sigN (d + k + 1) y' = sigN d (sigN (k + 1) y') := sigN_add (k + 1) d y'
      rw [e] at h'
      have hi : Interd y (sigN (k + 1) y') := interd_of_sigN d (h.trans h'.symm)
      refine hs.2 ⟨sigN k y', sigN_vf k hy', ?_⟩
      rw [show sigN 1 (sigN k y') = sigN (k + 1) y' from sig_sigN k y']
      exact hi.symm
    have hdd : d = d' := by
      rcases lt_trichotomy d d' with hlt | heq | hgt
      · exact absurd hlt (key hy' hs h h')
      · exact heq
      · exact absurd hgt (key hy hs' h' h)
    subst hdd
    exact ⟨rfl, interd_of_sigN d (h.trans h'.symm)⟩

/-! ## Part G. The designed cells -/

theorem isColour_iff {i : WithTop ℕ} {x : PLLFormula} (hx : atomFree x = true) :
    IsColour i x ↔ inLevel i x :=
  colour_iff rb i x hx

theorem inBag_iff {c : RB} {i : WithTop ℕ} {x : PLLFormula} (hx : atomFree x = true) :
    InBag c i x ↔ rbS c x ∧ inLevel i x :=
  (readback rb i c x hx).symm

theorem not_inSig3_sig2 : ¬ inSig 3 (sigN 2 .falsePLL) := fun ⟨y, hy, hi⟩ =>
  (sigN_bot_strict 2).2 (Deriv.cutHead (sigN_bot_le 3 y hy) hi.1)

/-- **`σ²⊥` is a colour of `D 0`, `D 1`, `D 2`, not of `D 3`.** -/
theorem cell_sig2_colour : Stmt.CellSig2Colour := by
  have hx : atomFree (sigN 2 .falsePLL) = true := sigN_vf 2 rfl
  exact ⟨(isColour_iff hx).mpr (inSig_of (sigN 2 .falsePLL) hx (Interd.refl _)),
    (isColour_iff hx).mpr (inSig_of (sigN 1 .falsePLL) (sigN_vf 1 rfl) (Interd.refl _)),
    (isColour_iff hx).mpr (inSig_of .falsePLL rfl (Interd.refl _)),
    fun h => not_inSig3_sig2 ((isColour_iff hx).mp h)⟩

/-- **`⊤` is a colour of every `D n` and of `D ⊤`.** -/
theorem cell_top_colour : Stmt.CellTopColour := by
  have hT : atomFree truePLL = true := rfl
  have hL : inLim truePLL := inLim_of_deriv (Deriv.impIntro (Deriv.iden (.head _)))
  exact ⟨fun n => (isColour_iff hT).mpr (hL n), (isColour_iff hT).mpr hL⟩

/-- **`σ²⊥` is in the red bag of `D 1` and `D 2`, not of `D 3`.** -/
theorem cell_sig2_red : Stmt.CellSig2Red := by
  have hx : atomFree (sigN 2 .falsePLL) = true := sigN_vf 2 rfl
  have hred : rbS .red (sigN 2 .falsePLL) :=
    (⟨2, Interd.refl _⟩ : ∃ m, Interd (sigN 2 .falsePLL) (sigN m .falsePLL))
  exact ⟨(inBag_iff hx).mpr ⟨hred, inSig_of (sigN 1 .falsePLL) (sigN_vf 1 rfl) (Interd.refl _)⟩,
    (inBag_iff hx).mpr ⟨hred, inSig_of .falsePLL rfl (Interd.refl _)⟩,
    fun h => not_inSig3_sig2 ((inBag_iff hx).mp h).2⟩

/-- **Negative control**: `⊥` is a colour of `D 0`, but not of `D 1`
(`σ y ⊣⊢ ⊥` would give `t3 = σ⊥ ⊢ σ y ⊢ ⊥`). -/
theorem ctrl_bot : Stmt.CtrlBot := by
  refine ⟨(isColour_iff (x := .falsePLL) rfl).mpr (inSig_of .falsePLL rfl (Interd.refl _)),
    fun h => ?_⟩
  obtain ⟨y, hy, hi⟩ := ((isColour_iff (x := .falsePLL) rfl).mp h : inSig 1 .falsePLL)
  exact nd_t3_bot (Deriv.cutHead (sigN_bot_le 1 y hy) hi.1)

/-- **The orbits of `⊥` and `◯⊥` have different thread limits.** -/
theorem cell_threads_differ : Stmt.CellThreadsDiffer := fun h =>
  nd_e_bot (thread_limit_injective _ _ rfl h).2

/-- **The shift at `a = ⊥`, `n = 0`.** -/
theorem cell_thread_shift : Stmt.CellThreadShift := by
  refine ⟨fun z => ?_, fun h => ?_, fun h => ?_⟩
  · rw [mem_thread_label, mem_thread_label]
    exact Iff.rfl
  · have h1 : ZFSet.pair (tag 0) (thread .falsePLL ((0 : ℕ) : WithTop ℕ)) ∈
        thread .falsePLL ((1 : ℕ) : WithTop ℕ) :=
      order_mem _ (WithTop.coe_lt_coe.mpr Nat.zero_lt_one)
    rw [← h] at h1
    exact thread_zero_no_order _ _ h1
  · exact nd_t3_bot (thread_limit_injective _ _ (sig_vf rfl) h).1

/-- **Thread readback in `rb`.** -/
theorem cell_thread_readback : Stmt.CellThreadReadback := by
  refine ⟨(thread_readback rb .falsePLL rfl).mpr ⟨RB.red, .falsePLL, rfl, Interd.refl _⟩,
    (thread_readback rb (.somehow .falsePLL) rfl).mpr
      ⟨RB.blue, .somehow .falsePLL, rfl, Interd.refl _⟩, fun h => ?_⟩
  obtain ⟨c, a', hc, hi⟩ := (thread_readback rb (sig .falsePLL) (sig_vf rfl)).mp h
  cases c with
  | red =>
      obtain rfl : a' = .falsePLL := (Option.some.inj hc).symm
      exact nd_t3_bot hi.2
  | blue =>
      obtain rfl : a' = .somehow .falsePLL := (Option.some.inj hc).symm
      exact nd_t3_e hi.2

/-! The negative control watched failing: the proof pattern of the positive
colour cells (a witness `y` with `σⁿ y ⊣⊢ x` by reflexivity) is rejected at
`x = ⊥`, `n = 1`. -/

/--
error: Application type mismatch: The argument
  Interd.refl ?m.12
has type
  Interd ?m.12 ?m.12
but is expected to have type
  Interd (sigN ↑1 ⊥) ⊥
in the application
  inSig_of ⊥ rfl (Interd.refl ?m.12)
-/
#guard_msgs in
example : IsColour ((1 : ℕ) : WithTop ℕ) .falsePLL :=
  (isColour_iff (x := .falsePLL) rfl).mpr (inSig_of .falsePLL rfl (Interd.refl _))


end InsideOut
end F0
end PLLND

/-! ## Axiom pins

The actual axiom sets (`#axioms_within` with the set `#print axioms`
reports).  `Classical.choice` marks the declarations that use it. -/

#axioms_within PLLND.F0.InsideOut.tag_succ_ne_zero [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.rbCode_inj [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.rbS_inv [propext]
#axioms_within PLLND.F0.InsideOut.rbBase_af []
#axioms_within PLLND.F0.InsideOut.tag_injective [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.tag_inj [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.pair_ne_empty [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.no_mem3 [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.d_unfold [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.mem_D_iff [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.order_mem [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.not_order_mem_self [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.D_injective [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.mem_order_iff [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.mem_label_iff [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.mem_top [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.d1_unfold [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.natsCode_injective [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.strCode_injective [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.code_injective [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.mem_classCode [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.classCode_eq_of_interd [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.interd_of_classCode_eq [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.classCode_eq_iff [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.inLevel_coe []
#axioms_within PLLND.F0.InsideOut.inLevel_top []
#axioms_within PLLND.F0.InsideOut.inSig_of []
#axioms_within PLLND.F0.InsideOut.inSig_congr [propext]
#axioms_within PLLND.F0.InsideOut.inLevel_congr [propext]
#axioms_within PLLND.F0.InsideOut.mem_colLab [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.colour_iff [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.mem_bagLab [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.bag_iff [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.mem_bagSet [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.readback [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.not_lt_coe_zero [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.mem_thread_label [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.thread_zero_no_order [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.thread_limit_injective [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.sigN_interd [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.sig_interd [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.interd_of_sigN [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.threadLab_congr [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.thread_limit_iff [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.mem_thrLab_top [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.thread_readback [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.threads_only_at_top [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.sig_sigN []
#axioms_within PLLND.F0.InsideOut.sigN_succ []
#axioms_within PLLND.F0.InsideOut.sigN_add []
#axioms_within PLLND.F0.InsideOut.sigN_or []
#axioms_within PLLND.F0.InsideOut.sigN_somehow []
#axioms_within PLLND.F0.InsideOut.sigN_succ_bot []
#axioms_within PLLND.F0.InsideOut.inSig_succ []
#axioms_within PLLND.F0.InsideOut.inSig_sig [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.inSig_of_sig [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.shell_shift [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.b2n_le_one []
#axioms_within PLLND.F0.InsideOut.cnt_le [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.b2n_mono []
#axioms_within PLLND.F0.InsideOut.cnt_mono [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.cnt_lt [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.allBelow_true [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.allBelow_false [propext]
#axioms_within PLLND.F0.InsideOut.stab_aux [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.stabilise [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.bot_everywhere [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.cm_eventually [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.inLim_of_deriv [propext]
#axioms_within PLLND.F0.InsideOut.lim_eq_top [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.orbit_order_limit [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.exists_last [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.orbits_vs_L0 [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.isColour_iff [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.inBag_iff [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.not_inSig3_sig2 [propext, Quot.sound]
#axioms_within PLLND.F0.InsideOut.cell_sig2_colour [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.cell_top_colour [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.cell_sig2_red [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.ctrl_bot [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.cell_threads_differ [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.cell_thread_shift [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.cell_thread_readback [propext, Classical.choice, Quot.sound]

#axioms_within PLLND.F0.InsideOut.D [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.D1 [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.code [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.classCode [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.thread [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.DF [propext, Classical.choice, Quot.sound]
#axioms_within PLLND.F0.InsideOut.rb [propext, Quot.sound]
