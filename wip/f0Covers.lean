import wip.embedNeg
import wip.ladder8
import LaxLogic.PLL.SubTab.Translate
import Meta.Audit

/-!
# F0 is not dense: the covers at the bottom

F0 is the Lindenbaum algebra of the variable-free PLL formulas (the
fragment RN(◯,{})).  Write `t n = rnSub n` (`wip/rnEmbed.lean`), the
Rieger–Nishimura rung `rn n` under `p := ◯⊥`:

    t0 = ⊥,  t1 = ◯⊥,  t2 = ¬◯⊥,  t3 = t1 ∨ t2,  t4 = t3 ↠ t1,  t5 = t3 ∨ t4.

Here they are the named formulas `bot, e, ne, t3, t4, t5` (`rnSub_0`, …,
`rnSub_5`, all `rfl`).

## The result (all PROVED, pins at the end)

A cover `u ⋖ v` (`Covers u v`) is `u ⊢ v`, `v ⊬ u`, and every variable-free
`x` with `u ⊢ x` and `x ⊢ v` satisfies `x ⊣⊢ u` or `x ⊣⊢ v`.  Then

    t0 ⋖ t1    t0 ⋖ t2    t1 ⋖ t3    t2 ⋖ t3    t1 ⋖ t4    t3 ⋖ t5    t4 ⋖ t5

(`cover_0_1`, …, `cover_4_5`), so F0 is NOT dense: these intervals contain
nothing.  Also (`low_trichotomy`), for every variable-free `x`,

    ◯⊥ ⊢ x   or   x ⊣⊢ ⊥   or   x ⊣⊢ ¬◯⊥.

## The method

**The reduction lemma** (`red_box`, `red_imp`, `red_or`, with `red_and`,
`red_bot`): for all `x, y, a`,

    ◯(x ∧ a) ∧ a   ⊣⊢  ◯x ∧ a
    (x ↠ y) ∧ a    ⊣⊢  ((x ∧ a) ↠ (y ∧ a)) ∧ a
    (x ∨ y) ∧ a    ⊣⊢  (x ∧ a) ∨ (y ∧ a).

**The finite-downset theorem** (`DownTable.classify`).  If a list `L`
contains `⊥` and `a`, every member entails `a`, and `L` is closed up to
`⊣⊢` under `∧`, `∨`, `l ↦ ◯l ∧ a` and `(l, l') ↦ (l ↠ l') ∧ a`
(`DownTable a L`, the closure passed as hypotheses), then every
variable-free `x` has `x ∧ a ⊣⊢ l` for some `l ∈ L`; so every
variable-free `x ⊢ a` is `⊣⊢` a member of `L` (`classify_below`).  The
proof is induction on `x`, one reduction lemma per connective.

**The five tables** (`D1_table`, …, `D5_table`):

    ↓t1 = {⊥, t1}   ↓t2 = {⊥, t2}   ↓t3 = {⊥, t1, t2, t3}
    ↓t4 = {⊥, t1, t4}   ↓t5 = {⊥, t1, t2, t3, t4, t5}

Every cell (224 `⊣⊢` cells, 17 `⊢` cells) is a pair of closed subframe
tableaux, re-checked by the kernel (`SubTab.check`, `decide +kernel`) and
translated into `LaxND` derivations by `SubTab.termOf`.  The cells were
found by the untrusted producer `SubTab.solve` (scratch generator,
2026-10-22); nothing in a cell is trusted but the kernel check.  The
pen facts behind the tables hold: `¬¬◯⊥` is ◯-closed (`D5_box_4`:
`◯t4 ∧ t5 ⊣⊢ t4`), `◯¬◯⊥ ∧ t5 ⊣⊢ t3` (`D5_box_2`), and
`◯¬◯⊥ ∧ t4 ⊣⊢ t1` (`pen_box_ne_t4`).

**Distinctness** (`D1_distinct`, …, `D5_distinct`): one four-world
constraint model `M3` (the ladder worlds `0, 1, 2` and a fallible top),
on which the truth sets of `⊥, t1, …, t5` on `{0,1,2}` are
`∅, {0}, {1}, {0,1}, {0,2}, {0,1,2}`, checked by
`FinCM.not_provable_of_check`.

**Fragment first** (CLAUDE.md rule 8).  The ◯-free instance of these
covers is the Rieger–Nishimura ladder, `covers9_eq` (`wip/ladder8.lean`):
`rn0 ⋖ rn1, rn2`, `rn1 ⋖ rn3, rn4`, `rn2 ⋖ rn3`, `rn3 ⋖ rn5`, `rn4 ⋖ rn5`
among the rungs.  The new content here is that no variable-free formula
with `◯` falls into these intervals either.
-/

open PLLFormula

namespace PLLND
namespace F0

open SemUI RNEmbed
open PLLND.LaxInfinite (atomFree)

/-! ## The formulas -/

/-- `t0 = ⊥`. -/
def bot : PLLFormula := .falsePLL
/-- `t1 = ◯⊥`. -/
def e : PLLFormula := .somehow .falsePLL
/-- `t2 = ¬◯⊥`. -/
def ne : PLLFormula := .ifThen e .falsePLL
/-- `t3 = ◯⊥ ∨ ¬◯⊥`. -/
def t3 : PLLFormula := .or e ne
/-- `t4 = t3 ↠ ◯⊥` (`⊣⊢ ¬¬◯⊥`, `rnSub_four_interd`). -/
def t4 : PLLFormula := .ifThen t3 e
/-- `t5 = t3 ∨ t4` (`⊣⊢ ¬◯⊥ ∨ ¬¬◯⊥`). -/
def t5 : PLLFormula := .or t3 t4

theorem rnSub_0 : rnSub 0 = bot := rfl
theorem rnSub_1 : rnSub 1 = e := rfl
theorem rnSub_2 : rnSub 2 = ne := rfl
theorem rnSub_3 : rnSub 3 = t3 := rfl
theorem rnSub_4 : rnSub 4 = t4 := rfl
theorem rnSub_5 : rnSub 5 = t5 := rfl

/-! ## A1. The reduction lemma -/

theorem red_bot (a : PLLFormula) : Interd (.and .falsePLL a) .falsePLL :=
  ⟨⟨.andElim1 (.iden (.head _))⟩, ⟨.falsoElim _ (.iden (.head _))⟩⟩

theorem red_and (x y a : PLLFormula) :
    Interd (.and (.and x y) a) (.and (.and x a) (.and y a)) :=
  ⟨⟨.andIntro
      (.andIntro (.andElim1 (.andElim1 (.iden (.head _)))) (.andElim2 (.iden (.head _))))
      (.andIntro (.andElim2 (.andElim1 (.iden (.head _)))) (.andElim2 (.iden (.head _))))⟩,
   ⟨.andIntro
      (.andIntro (.andElim1 (.andElim1 (.iden (.head _))))
        (.andElim1 (.andElim2 (.iden (.head _)))))
      (.andElim2 (.andElim1 (.iden (.head _))))⟩⟩

/-- `(x ∨ y) ∧ a ⊣⊢ (x ∧ a) ∨ (y ∧ a)`. -/
theorem red_or (x y a : PLLFormula) :
    Interd (.and (.or x y) a) (.or (.and x a) (.and y a)) :=
  ⟨⟨.orElim (.andElim1 (.iden (.head _)))
      (.orIntro1 (.andIntro (.iden (.head _)) (.andElim2 (.iden (.tail _ (.head _))))))
      (.orIntro2 (.andIntro (.iden (.head _)) (.andElim2 (.iden (.tail _ (.head _))))))⟩,
   ⟨.orElim (.iden (.head _))
      (.andIntro (.orIntro1 (.andElim1 (.iden (.head _)))) (.andElim2 (.iden (.head _))))
      (.andIntro (.orIntro2 (.andElim1 (.iden (.head _)))) (.andElim2 (.iden (.head _))))⟩⟩

/-- `(x ↠ y) ∧ a ⊣⊢ ((x ∧ a) ↠ (y ∧ a)) ∧ a`. -/
theorem red_imp (x y a : PLLFormula) :
    Interd (.and (.ifThen x y) a) (.and (.ifThen (.and x a) (.and y a)) a) :=
  ⟨⟨.andIntro
      (.impIntro (.andIntro
        (.impElim (.andElim1 (.iden (.tail _ (.head _)))) (.andElim1 (.iden (.head _))))
        (.andElim2 (.iden (.head _)))))
      (.andElim2 (.iden (.head _)))⟩,
   ⟨.andIntro
      (.impIntro (.andElim1 (.impElim (.andElim1 (.iden (.tail _ (.head _))))
        (.andIntro (.iden (.head _)) (.andElim2 (.iden (.tail _ (.head _))))))))
      (.andElim2 (.iden (.head _)))⟩⟩

/-- `◯(x ∧ a) ∧ a ⊣⊢ ◯x ∧ a`. -/
theorem red_box (x a : PLLFormula) :
    Interd (.and (.somehow (.and x a)) a) (.and (.somehow x) a) :=
  ⟨⟨.andIntro
      (.laxElim (.andElim1 (.iden (.head _))) (.laxIntro (.andElim1 (.iden (.head _)))))
      (.andElim2 (.iden (.head _)))⟩,
   ⟨.andIntro
      (.laxElim (.andElim1 (.iden (.head _)))
        (.laxIntro (.andIntro (.iden (.head _)) (.andElim2 (.iden (.tail _ (.head _)))))))
      (.andElim2 (.iden (.head _)))⟩⟩

/-- Below `a`, meeting with `a` changes nothing. -/
theorem absorb {x a : PLLFormula} (h : Deriv [x] a) : Interd x (.and x a) :=
  ⟨Deriv.andIntro (Deriv.iden (.head _)) h, Deriv.andElim1 (Deriv.iden (.head _))⟩

/-! ## A1. The finite-downset theorem -/

/-- **A finite table for the downset of `a`.**  `L` contains `⊥` and `a`,
lies below `a`, and is closed up to `⊣⊢` under `∧`, `∨`, `l ↦ ◯l ∧ a` and
`(l, l') ↦ (l ↠ l') ∧ a`.  Each closure hypothesis is a function returning,
for members of `L`, a member and the interderivability. -/
structure DownTable (a : PLLFormula) (L : List PLLFormula) : Prop where
  bot_mem : PLLFormula.falsePLL ∈ L
  top_mem : a ∈ L
  below : ∀ l ∈ L, Deriv [l] a
  and_cl : ∀ l ∈ L, ∀ l' ∈ L, ∃ m ∈ L, Interd (.and l l') m
  or_cl : ∀ l ∈ L, ∀ l' ∈ L, ∃ m ∈ L, Interd (.or l l') m
  box_cl : ∀ l ∈ L, ∃ m ∈ L, Interd (.and (.somehow l) a) m
  imp_cl : ∀ l ∈ L, ∀ l' ∈ L, ∃ m ∈ L, Interd (.and (.ifThen l l') a) m

/-- **The finite-downset theorem.**  Under a table for `a`, every
variable-free `x` has `x ∧ a ⊣⊢ l` for some member `l`.  Induction on `x`,
one reduction lemma per connective. -/
theorem DownTable.classify {a : PLLFormula} {L : List PLLFormula} (T : DownTable a L) :
    ∀ x : PLLFormula, atomFree x = true → ∃ l ∈ L, Interd (.and x a) l := by
  intro x
  induction x with
  | prop _ => intro h; simp [atomFree] at h
  | falsePLL => intro _; exact ⟨_, T.bot_mem, red_bot a⟩
  | and x y ihx ihy =>
      intro h
      have hxy : atomFree x = true ∧ atomFree y = true := by simpa [atomFree] using h
      obtain ⟨lx, hlx, ix⟩ := ihx hxy.1
      obtain ⟨ly, hly, iy⟩ := ihy hxy.2
      obtain ⟨m, hm, im⟩ := T.and_cl lx hlx ly hly
      exact ⟨m, hm, (red_and x y a).trans ((Interd.and_congr ix iy).trans im)⟩
  | or x y ihx ihy =>
      intro h
      have hxy : atomFree x = true ∧ atomFree y = true := by simpa [atomFree] using h
      obtain ⟨lx, hlx, ix⟩ := ihx hxy.1
      obtain ⟨ly, hly, iy⟩ := ihy hxy.2
      obtain ⟨m, hm, im⟩ := T.or_cl lx hlx ly hly
      exact ⟨m, hm, (red_or x y a).trans ((Interd.or_congr ix iy).trans im)⟩
  | ifThen x y ihx ihy =>
      intro h
      have hxy : atomFree x = true ∧ atomFree y = true := by simpa [atomFree] using h
      obtain ⟨lx, hlx, ix⟩ := ihx hxy.1
      obtain ⟨ly, hly, iy⟩ := ihy hxy.2
      obtain ⟨m, hm, im⟩ := T.imp_cl lx hlx ly hly
      exact ⟨m, hm, (red_imp x y a).trans
        ((Interd.and_congr (Interd.imp_congr ix iy) (Interd.refl a)).trans im)⟩
  | somehow x ihx =>
      intro h
      have hx : atomFree x = true := by simpa [atomFree] using h
      obtain ⟨lx, hlx, ix⟩ := ihx hx
      obtain ⟨m, hm, im⟩ := T.box_cl lx hlx
      exact ⟨m, hm, (red_box x a).symm.trans
        ((Interd.and_congr (Interd.box_congr ix) (Interd.refl a)).trans im)⟩

/-- **Every variable-free formula below `a` is a member of the table**, up
to `⊣⊢`. -/
theorem DownTable.classify_below {a : PLLFormula} {L : List PLLFormula}
    (T : DownTable a L) {x : PLLFormula} (hx : atomFree x = true)
    (hxa : Deriv [x] a) : ∃ l ∈ L, Interd x l := by
  obtain ⟨l, hl, i⟩ := T.classify x hx
  exact ⟨l, hl, (absorb hxa).trans i⟩

/-! ## Finite tables: plumbing -/

/-- `P` holds at every member, as nested data (so a table is a term). -/
inductive AllL (P : PLLFormula → Prop) : List PLLFormula → Prop
  | nil : AllL P []
  | cons {x : PLLFormula} {xs : List PLLFormula} : P x → AllL P xs → AllL P (x :: xs)

theorem allL_mem {P : PLLFormula → Prop} {L : List PLLFormula} (h : AllL P L) :
    ∀ l ∈ L, P l := by
  induction h with
  | nil => intro l hl; simp at hl
  | cons hx _ ih =>
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · exact hx
      · exact ih l hl

/-- A closed subframe tableau for `X ↠ Y` gives `X ⊢ Y` (`SubTab.termOf`). -/
theorem derivTab {X Y : PLLFormula} (c : SubTab.TCert)
    (h : SubTab.check ⟨false, [], [.ifThen X Y]⟩ c = true) : Deriv [X] Y :=
  ⟨.impElim ((SubTab.termOf _ c h).rename (fun _ hψ => by simp at hψ)) (.iden (.head _))⟩

/-- Two closed subframe tableaux give `X ⊣⊢ Y`. -/
theorem interdTab {X Y : PLLFormula} (c d : SubTab.TCert)
    (h₁ : SubTab.check ⟨false, [], [.ifThen X Y]⟩ c = true)
    (h₂ : SubTab.check ⟨false, [], [.ifThen Y X]⟩ d = true) : Interd X Y :=
  ⟨derivTab c h₁, derivTab d h₂⟩

/-! ## A2. The five tables

Generated (scratch generator `_out/gen.lean`, untrusted: `SubTab.solve`,
each certificate pre-checked by `check`), then re-checked here by the
kernel.  Cell names: `Dn_below_i : Ln[i] ⊢ a`, `Dn_and_i_j`, `Dn_or_i_j`,
`Dn_box_i`, `Dn_imp_i_j`, indices into the list. -/

set_option maxRecDepth 100000

abbrev D1_list : List PLLFormula := [bot, e]
theorem D1_mem_0 : bot ∈ D1_list := List.Mem.head _
theorem D1_mem_1 : e ∈ D1_list := List.Mem.tail _ (List.Mem.head _)

abbrev D2_list : List PLLFormula := [bot, ne]
theorem D2_mem_0 : bot ∈ D2_list := List.Mem.head _
theorem D2_mem_1 : ne ∈ D2_list := List.Mem.tail _ (List.Mem.head _)

abbrev D3_list : List PLLFormula := [bot, e, ne, t3]
theorem D3_mem_0 : bot ∈ D3_list := List.Mem.head _
theorem D3_mem_1 : e ∈ D3_list := List.Mem.tail _ (List.Mem.head _)
theorem D3_mem_2 : ne ∈ D3_list := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
theorem D3_mem_3 : t3 ∈ D3_list :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

abbrev D4_list : List PLLFormula := [bot, e, t4]
theorem D4_mem_0 : bot ∈ D4_list := List.Mem.head _
theorem D4_mem_1 : e ∈ D4_list := List.Mem.tail _ (List.Mem.head _)
theorem D4_mem_2 : t4 ∈ D4_list := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

abbrev D5_list : List PLLFormula := [bot, e, ne, t3, t4, t5]
theorem D5_mem_0 : bot ∈ D5_list := List.Mem.head _
theorem D5_mem_1 : e ∈ D5_list := List.Mem.tail _ (List.Mem.head _)
theorem D5_mem_2 : ne ∈ D5_list := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
theorem D5_mem_3 : t3 ∈ D5_list :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
theorem D5_mem_4 : t4 ∈ D5_list :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
theorem D5_mem_5 : t5 ∈ D5_list :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.head _)))))

/-! ### Table `D1`: the downset of `e`, `[bot, e]` -/

theorem D1_below_0 : Deriv [bot] e :=
  derivTab (.impR bot e .bot) (by decide +kernel)

theorem D1_below_1 : Deriv [e] e :=
  derivTab (.impR e e (.ax e)) (by decide +kernel)

theorem D1_box_0 : Interd (.and e e) e :=
  interdTab (.impR (.and e e) e (.andL e e (.ax e)))
    (.impR e (.and e e) (.andR e e (.ax e) (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D1_and_0_0 : Interd (.and bot bot) bot :=
  interdTab (.impR (.and bot bot) bot (.andL bot bot .bot))
    (.impR bot (.and bot bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D1_or_0_0 : Interd (.or bot bot) bot :=
  interdTab (.impR (.or bot bot) bot (.orL bot bot .bot .bot))
    (.impR bot (.or bot bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D1_imp_0_0 : Interd (.and (.ifThen bot bot) e) e :=
  interdTab (.impR (.and (.ifThen bot bot) e) e (.andL (.ifThen bot bot) e (.impL bot bot (.ax e) .bot)))
    (.impR e (.and (.ifThen bot bot) e) (.andR (.ifThen bot bot) e (.impR bot bot .bot) (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D1_and_0_1 : Interd (.and bot e) bot :=
  interdTab (.impR (.and bot e) bot (.andL bot e .bot))
    (.impR bot (.and bot e) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D1_or_0_1 : Interd (.or bot e) e :=
  interdTab (.impR (.or bot e) e (.orL bot e .bot (.ax e)))
    (.impR e (.or bot e) (.orR bot e (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D1_imp_0_1 : Interd (.and (.ifThen bot e) e) e :=
  interdTab (.impR (.and (.ifThen bot e) e) e (.andL (.ifThen bot e) e (.impL bot e (.ax e) (.ax e))))
    (.impR e (.and (.ifThen bot e) e) (.andR (.ifThen bot e) e (.impR bot e .bot) (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D1_box_1 : Interd (.and (.somehow e) e) e :=
  interdTab (.impR (.and (.somehow e) e) e (.andL (.somehow e) e (.ax e)))
    (.impR e (.and (.somehow e) e) (.andR (.somehow e) e (.boxR e (.boxL bot .bot)) (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D1_and_1_0 : Interd (.and e bot) bot :=
  interdTab (.impR (.and e bot) bot (.andL e bot .bot))
    (.impR bot (.and e bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D1_or_1_0 : Interd (.or e bot) e :=
  interdTab (.impR (.or e bot) e (.orL e bot (.ax e) .bot))
    (.impR e (.or e bot) (.orR e bot (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D1_imp_1_0 : Interd (.and ne e) bot :=
  interdTab (.impR (.and ne e) bot (.andL ne e (.impL e bot (.ax e) .bot)))
    (.impR bot (.and ne e) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D1_and_1_1 : Interd (.and e e) e :=
  interdTab (.impR (.and e e) e (.andL e e (.ax e)))
    (.impR e (.and e e) (.andR e e (.ax e) (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D1_or_1_1 : Interd (.or e e) e :=
  interdTab (.impR (.or e e) e (.orL e e (.ax e) (.ax e)))
    (.impR e (.or e e) (.orR e e (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D1_imp_1_1 : Interd (.and (.ifThen e e) e) e :=
  interdTab (.impR (.and (.ifThen e e) e) e (.andL (.ifThen e e) e (.impL e e (.ax e) (.ax e))))
    (.impR e (.and (.ifThen e e) e) (.andR (.ifThen e e) e (.impLoc e e (.ax e)) (.ax e)))
    (by decide +kernel) (by decide +kernel)

/-- The closure table of `D1`. -/
theorem D1_table : DownTable e D1_list where
  bot_mem := D1_mem_0
  top_mem := D1_mem_1
  below := allL_mem (.cons D1_below_0
      (.cons D1_below_1
      .nil))
  and_cl := allL_mem
    (.cons (allL_mem (.cons ⟨bot, D1_mem_0, D1_and_0_0⟩ (.cons ⟨bot, D1_mem_0, D1_and_0_1⟩ .nil)))
      (.cons (allL_mem (.cons ⟨bot, D1_mem_0, D1_and_1_0⟩ (.cons ⟨e, D1_mem_1, D1_and_1_1⟩ .nil)))
      .nil))
  or_cl := allL_mem
    (.cons (allL_mem (.cons ⟨bot, D1_mem_0, D1_or_0_0⟩ (.cons ⟨e, D1_mem_1, D1_or_0_1⟩ .nil)))
      (.cons (allL_mem (.cons ⟨e, D1_mem_1, D1_or_1_0⟩ (.cons ⟨e, D1_mem_1, D1_or_1_1⟩ .nil)))
      .nil))
  box_cl := allL_mem
    (.cons ⟨e, D1_mem_1, D1_box_0⟩
      (.cons ⟨e, D1_mem_1, D1_box_1⟩
      .nil))
  imp_cl := allL_mem
    (.cons (allL_mem (.cons ⟨e, D1_mem_1, D1_imp_0_0⟩ (.cons ⟨e, D1_mem_1, D1_imp_0_1⟩ .nil)))
      (.cons (allL_mem (.cons ⟨bot, D1_mem_0, D1_imp_1_0⟩ (.cons ⟨e, D1_mem_1, D1_imp_1_1⟩ .nil)))
      .nil))

/-! ### Table `D2`: the downset of `ne`, `[bot, ne]` -/

theorem D2_below_0 : Deriv [bot] ne :=
  derivTab (.impR bot ne .bot) (by decide +kernel)

theorem D2_below_1 : Deriv [ne] ne :=
  derivTab (.impR ne ne (.impL e bot (.ax ne) .bot)) (by decide +kernel)

theorem D2_box_0 : Interd (.and e ne) bot :=
  interdTab (.impR (.and e ne) bot (.andL e ne (.impL e bot (.ax e) .bot)))
    (.impR bot (.and e ne) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D2_and_0_0 : Interd (.and bot bot) bot :=
  interdTab (.impR (.and bot bot) bot (.andL bot bot .bot))
    (.impR bot (.and bot bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D2_or_0_0 : Interd (.or bot bot) bot :=
  interdTab (.impR (.or bot bot) bot (.orL bot bot .bot .bot))
    (.impR bot (.or bot bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D2_imp_0_0 : Interd (.and (.ifThen bot bot) ne) ne :=
  interdTab (.impR (.and (.ifThen bot bot) ne) ne (.andL (.ifThen bot bot) ne (.impL bot bot (.impL e bot (.ax ne) .bot) .bot)))
    (.impR ne (.and (.ifThen bot bot) ne) (.impL e bot (.andR (.ifThen bot bot) ne (.impR bot bot (.impL e bot .bot .bot)) (.ax ne)) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D2_and_0_1 : Interd (.and bot ne) bot :=
  interdTab (.impR (.and bot ne) bot (.andL bot ne .bot))
    (.impR bot (.and bot ne) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D2_or_0_1 : Interd (.or bot ne) ne :=
  interdTab (.impR (.or bot ne) ne (.orL bot ne .bot (.impL e bot (.ax ne) .bot)))
    (.impR ne (.or bot ne) (.impL e bot (.orR bot ne (.ax ne)) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D2_imp_0_1 : Interd (.and (.ifThen bot ne) ne) ne :=
  interdTab (.impR (.and (.ifThen bot ne) ne) ne (.andL (.ifThen bot ne) ne (.impL bot ne (.impL e bot (.ax ne) .bot) (.impL e bot (.ax ne) .bot))))
    (.impR ne (.and (.ifThen bot ne) ne) (.impL e bot (.andR (.ifThen bot ne) ne (.impR bot ne (.impL e bot .bot .bot)) (.ax ne)) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D2_box_1 : Interd (.and (.somehow ne) ne) ne :=
  interdTab (.impR (.and (.somehow ne) ne) ne (.andL (.somehow ne) ne (.impL e bot (.ax ne) .bot)))
    (.impR ne (.and (.somehow ne) ne) (.impL e bot (.andR (.somehow ne) ne (.boxR ne (.impL e bot (.boxLoc bot (.ax ne)) .bot)) (.ax ne)) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D2_and_1_0 : Interd (.and ne bot) bot :=
  interdTab (.impR (.and ne bot) bot (.andL ne bot (.impL e bot .bot .bot)))
    (.impR bot (.and ne bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D2_or_1_0 : Interd (.or ne bot) ne :=
  interdTab (.impR (.or ne bot) ne (.orL ne bot (.impL e bot (.ax ne) .bot) .bot))
    (.impR ne (.or ne bot) (.impL e bot (.orR ne bot (.ax ne)) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D2_imp_1_0 : Interd (.and (.ifThen ne bot) ne) bot :=
  interdTab (.impR (.and (.ifThen ne bot) ne) bot (.andL (.ifThen ne bot) ne (.impL ne bot (.impL e bot (.ax ne) .bot) .bot)))
    (.impR bot (.and (.ifThen ne bot) ne) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D2_and_1_1 : Interd (.and ne ne) ne :=
  interdTab (.impR (.and ne ne) ne (.andL ne ne (.impL e bot (.ax ne) .bot)))
    (.impR ne (.and ne ne) (.impL e bot (.andR ne ne (.ax ne) (.ax ne)) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D2_or_1_1 : Interd (.or ne ne) ne :=
  interdTab (.impR (.or ne ne) ne (.orL ne ne (.impL e bot (.ax ne) .bot) (.impL e bot (.ax ne) .bot)))
    (.impR ne (.or ne ne) (.impL e bot (.orR ne ne (.ax ne)) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D2_imp_1_1 : Interd (.and (.ifThen ne ne) ne) ne :=
  interdTab (.impR (.and (.ifThen ne ne) ne) ne (.andL (.ifThen ne ne) ne (.impL ne ne (.impL e bot (.ax ne) .bot) (.impL e bot (.ax ne) .bot))))
    (.impR ne (.and (.ifThen ne ne) ne) (.impL e bot (.andR (.ifThen ne ne) ne (.impLoc ne ne (.ax ne)) (.ax ne)) .bot))
    (by decide +kernel) (by decide +kernel)

/-- The closure table of `D2`. -/
theorem D2_table : DownTable ne D2_list where
  bot_mem := D2_mem_0
  top_mem := D2_mem_1
  below := allL_mem (.cons D2_below_0
      (.cons D2_below_1
      .nil))
  and_cl := allL_mem
    (.cons (allL_mem (.cons ⟨bot, D2_mem_0, D2_and_0_0⟩ (.cons ⟨bot, D2_mem_0, D2_and_0_1⟩ .nil)))
      (.cons (allL_mem (.cons ⟨bot, D2_mem_0, D2_and_1_0⟩ (.cons ⟨ne, D2_mem_1, D2_and_1_1⟩ .nil)))
      .nil))
  or_cl := allL_mem
    (.cons (allL_mem (.cons ⟨bot, D2_mem_0, D2_or_0_0⟩ (.cons ⟨ne, D2_mem_1, D2_or_0_1⟩ .nil)))
      (.cons (allL_mem (.cons ⟨ne, D2_mem_1, D2_or_1_0⟩ (.cons ⟨ne, D2_mem_1, D2_or_1_1⟩ .nil)))
      .nil))
  box_cl := allL_mem
    (.cons ⟨bot, D2_mem_0, D2_box_0⟩
      (.cons ⟨ne, D2_mem_1, D2_box_1⟩
      .nil))
  imp_cl := allL_mem
    (.cons (allL_mem (.cons ⟨ne, D2_mem_1, D2_imp_0_0⟩ (.cons ⟨ne, D2_mem_1, D2_imp_0_1⟩ .nil)))
      (.cons (allL_mem (.cons ⟨bot, D2_mem_0, D2_imp_1_0⟩ (.cons ⟨ne, D2_mem_1, D2_imp_1_1⟩ .nil)))
      .nil))

/-! ### Table `D3`: the downset of `t3`, `[bot, e, ne, t3]` -/

theorem D3_below_0 : Deriv [bot] t3 :=
  derivTab (.impR bot t3 .bot) (by decide +kernel)

theorem D3_below_1 : Deriv [e] t3 :=
  derivTab (.impR e t3 (.orR e ne (.ax e))) (by decide +kernel)

theorem D3_below_2 : Deriv [ne] t3 :=
  derivTab (.impR ne t3 (.impL e bot (.orR e ne (.ax ne)) .bot)) (by decide +kernel)

theorem D3_below_3 : Deriv [t3] t3 :=
  derivTab (.impR t3 t3 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot))) (by decide +kernel)

theorem D3_box_0 : Interd (.and e t3) e :=
  interdTab (.impR (.and e t3) e (.andL e t3 (.orL e ne (.ax e) (.impL e bot (.ax e) .bot))))
    (.impR e (.and e t3) (.andR e t3 (.ax e) (.orR e ne (.ax e))))
    (by decide +kernel) (by decide +kernel)

theorem D3_and_0_0 : Interd (.and bot bot) bot :=
  interdTab (.impR (.and bot bot) bot (.andL bot bot .bot))
    (.impR bot (.and bot bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D3_or_0_0 : Interd (.or bot bot) bot :=
  interdTab (.impR (.or bot bot) bot (.orL bot bot .bot .bot))
    (.impR bot (.or bot bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D3_imp_0_0 : Interd (.and (.ifThen bot bot) t3) t3 :=
  interdTab (.impR (.and (.ifThen bot bot) t3) t3 (.andL (.ifThen bot bot) t3 (.impL bot bot (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) .bot)))
    (.impR t3 (.and (.ifThen bot bot) t3) (.orL e ne (.andR (.ifThen bot bot) t3 (.impR bot bot (.orL e ne .bot (.impL e bot .bot .bot))) (.ax t3)) (.impL e bot (.andR (.ifThen bot bot) t3 (.impR bot bot (.impL e bot (.orL e ne .bot .bot) .bot)) (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D3_and_0_1 : Interd (.and bot e) bot :=
  interdTab (.impR (.and bot e) bot (.andL bot e .bot))
    (.impR bot (.and bot e) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D3_or_0_1 : Interd (.or bot e) e :=
  interdTab (.impR (.or bot e) e (.orL bot e .bot (.ax e)))
    (.impR e (.or bot e) (.orR bot e (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D3_imp_0_1 : Interd (.and (.ifThen bot e) t3) t3 :=
  interdTab (.impR (.and (.ifThen bot e) t3) t3 (.andL (.ifThen bot e) t3 (.impL bot e (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orL e ne (.ax t3) (.impL e bot (.ax e) .bot)))))
    (.impR t3 (.and (.ifThen bot e) t3) (.orL e ne (.andR (.ifThen bot e) t3 (.impR bot e (.orL e ne .bot (.impL e bot .bot .bot))) (.ax t3)) (.impL e bot (.andR (.ifThen bot e) t3 (.impR bot e (.impL e bot (.orL e ne .bot .bot) .bot)) (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D3_and_0_2 : Interd (.and bot ne) bot :=
  interdTab (.impR (.and bot ne) bot (.andL bot ne .bot))
    (.impR bot (.and bot ne) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D3_or_0_2 : Interd (.or bot ne) ne :=
  interdTab (.impR (.or bot ne) ne (.orL bot ne .bot (.impL e bot (.ax ne) .bot)))
    (.impR ne (.or bot ne) (.impL e bot (.orR bot ne (.ax ne)) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D3_imp_0_2 : Interd (.and (.ifThen bot ne) t3) t3 :=
  interdTab (.impR (.and (.ifThen bot ne) t3) t3 (.andL (.ifThen bot ne) t3 (.impL bot ne (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.impL e bot (.orL e ne (.ax e) (.ax t3)) .bot))))
    (.impR t3 (.and (.ifThen bot ne) t3) (.orL e ne (.andR (.ifThen bot ne) t3 (.impR bot ne (.orL e ne .bot (.impL e bot .bot .bot))) (.ax t3)) (.impL e bot (.andR (.ifThen bot ne) t3 (.impR bot ne (.impL e bot (.orL e ne .bot .bot) .bot)) (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D3_and_0_3 : Interd (.and bot t3) bot :=
  interdTab (.impR (.and bot t3) bot (.andL bot t3 .bot))
    (.impR bot (.and bot t3) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D3_or_0_3 : Interd (.or bot t3) t3 :=
  interdTab (.impR (.or bot t3) t3 (.orL bot t3 .bot (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot))))
    (.impR t3 (.or bot t3) (.orL e ne (.orR bot t3 (.ax t3)) (.impL e bot (.orR bot t3 (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D3_imp_0_3 : Interd (.and (.ifThen bot t3) t3) t3 :=
  interdTab (.impR (.and (.ifThen bot t3) t3) t3 (.andL (.ifThen bot t3) t3 (.impL bot t3 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)))))
    (.impR t3 (.and (.ifThen bot t3) t3) (.orL e ne (.andR (.ifThen bot t3) t3 (.impR bot t3 (.orL e ne .bot (.impL e bot .bot .bot))) (.ax t3)) (.impL e bot (.andR (.ifThen bot t3) t3 (.impR bot t3 (.impL e bot (.orL e ne .bot .bot) .bot)) (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D3_box_1 : Interd (.and (.somehow e) t3) e :=
  interdTab (.impR (.and (.somehow e) t3) e (.andL (.somehow e) t3 (.orL e ne (.ax e) (.impL e bot (.boxR bot (.boxL e (.boxL bot .bot))) .bot))))
    (.impR e (.and (.somehow e) t3) (.andR (.somehow e) t3 (.boxR e (.boxL bot .bot)) (.orR e ne (.ax e))))
    (by decide +kernel) (by decide +kernel)

theorem D3_and_1_0 : Interd (.and e bot) bot :=
  interdTab (.impR (.and e bot) bot (.andL e bot .bot))
    (.impR bot (.and e bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D3_or_1_0 : Interd (.or e bot) e :=
  interdTab (.impR (.or e bot) e (.orL e bot (.ax e) .bot))
    (.impR e (.or e bot) (.orR e bot (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D3_imp_1_0 : Interd (.and ne t3) ne :=
  interdTab (.impR (.and ne t3) ne (.andL ne t3 (.impL e bot (.orL e ne (.ax e) (.ax ne)) .bot)))
    (.impR ne (.and ne t3) (.impL e bot (.andR ne t3 (.ax ne) (.orR e ne (.ax ne))) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D3_and_1_1 : Interd (.and e e) e :=
  interdTab (.impR (.and e e) e (.andL e e (.ax e)))
    (.impR e (.and e e) (.andR e e (.ax e) (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D3_or_1_1 : Interd (.or e e) e :=
  interdTab (.impR (.or e e) e (.orL e e (.ax e) (.ax e)))
    (.impR e (.or e e) (.orR e e (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D3_imp_1_1 : Interd (.and (.ifThen e e) t3) t3 :=
  interdTab (.impR (.and (.ifThen e e) t3) t3 (.andL (.ifThen e e) t3 (.impL e e (.orL e ne (.ax e) (.impL e bot (.ax t3) .bot)) (.orL e ne (.ax t3) (.impL e bot (.ax e) .bot)))))
    (.impR t3 (.and (.ifThen e e) t3) (.orL e ne (.andR (.ifThen e e) t3 (.impLoc e e (.ax e)) (.ax t3)) (.impL e bot (.andR (.ifThen e e) t3 (.impR e e (.impL e bot (.orL e ne (.ax e) (.ax e)) .bot)) (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D3_and_1_2 : Interd (.and e ne) bot :=
  interdTab (.impR (.and e ne) bot (.andL e ne (.impL e bot (.ax e) .bot)))
    (.impR bot (.and e ne) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D3_or_1_2 : Interd (.or e ne) t3 :=
  interdTab (.impR t3 t3 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)))
    (.impR t3 t3 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D3_imp_1_2 : Interd (.and (.ifThen e ne) t3) ne :=
  interdTab (.impR (.and (.ifThen e ne) t3) ne (.andL (.ifThen e ne) t3 (.impL e ne (.orL e ne (.ax e) (.impL e bot (.ax ne) .bot)) (.impL e bot (.orL e ne (.ax e) (.ax ne)) .bot))))
    (.impR ne (.and (.ifThen e ne) t3) (.impL e bot (.andR (.ifThen e ne) t3 (.impR e ne (.impL e bot (.ax e) .bot)) (.orR e ne (.ax ne))) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D3_and_1_3 : Interd (.and e t3) e :=
  interdTab (.impR (.and e t3) e (.andL e t3 (.orL e ne (.ax e) (.impL e bot (.ax e) .bot))))
    (.impR e (.and e t3) (.andR e t3 (.ax e) (.orR e ne (.ax e))))
    (by decide +kernel) (by decide +kernel)

theorem D3_or_1_3 : Interd (.or e t3) t3 :=
  interdTab (.impR (.or e t3) t3 (.orL e t3 (.orR e ne (.ax e)) (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot))))
    (.impR t3 (.or e t3) (.orL e ne (.orR e t3 (.ax e)) (.impL e bot (.orR e t3 (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D3_imp_1_3 : Interd (.and (.ifThen e t3) t3) t3 :=
  interdTab (.impR (.and (.ifThen e t3) t3) t3 (.andL (.ifThen e t3) t3 (.impL e t3 (.orL e ne (.ax e) (.impL e bot (.ax t3) .bot)) (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)))))
    (.impR t3 (.and (.ifThen e t3) t3) (.orL e ne (.andR (.ifThen e t3) t3 (.impLoc e t3 (.ax t3)) (.ax t3)) (.impL e bot (.andR (.ifThen e t3) t3 (.impR e t3 (.impL e bot (.orL e ne (.ax e) (.ax e)) .bot)) (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D3_box_2 : Interd (.and (.somehow ne) t3) t3 :=
  interdTab (.impR (.and (.somehow ne) t3) t3 (.andL (.somehow ne) t3 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot))))
    (.impR t3 (.and (.somehow ne) t3) (.orL e ne (.andR (.somehow ne) t3 (.boxR ne (.boxL bot .bot)) (.ax t3)) (.impL e bot (.andR (.somehow ne) t3 (.boxR ne (.impL e bot (.orL e ne (.boxL bot .bot) (.boxLoc bot (.ax ne))) .bot)) (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D3_and_2_0 : Interd (.and ne bot) bot :=
  interdTab (.impR (.and ne bot) bot (.andL ne bot (.impL e bot .bot .bot)))
    (.impR bot (.and ne bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D3_or_2_0 : Interd (.or ne bot) ne :=
  interdTab (.impR (.or ne bot) ne (.orL ne bot (.impL e bot (.ax ne) .bot) .bot))
    (.impR ne (.or ne bot) (.impL e bot (.orR ne bot (.ax ne)) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D3_imp_2_0 : Interd (.and (.ifThen ne bot) t3) e :=
  interdTab (.impR (.and (.ifThen ne bot) t3) e (.andL (.ifThen ne bot) t3 (.impL ne bot (.orL e ne (.impLoc e bot (.ax e)) (.impL e bot (.ax ne) .bot)) .bot)))
    (.impR e (.and (.ifThen ne bot) t3) (.andR (.ifThen ne bot) t3 (.impR ne bot (.impL e bot (.ax e) .bot)) (.orR e ne (.ax e))))
    (by decide +kernel) (by decide +kernel)

theorem D3_and_2_1 : Interd (.and ne e) bot :=
  interdTab (.impR (.and ne e) bot (.andL ne e (.impL e bot (.ax e) .bot)))
    (.impR bot (.and ne e) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D3_or_2_1 : Interd (.or ne e) t3 :=
  interdTab (.impR (.or ne e) t3 (.orL ne e (.impL e bot (.orR e ne (.ax ne)) .bot) (.orR e ne (.ax e))))
    (.impR t3 (.or ne e) (.orL e ne (.orR ne e (.impLoc e bot (.ax e))) (.impL e bot (.orR ne e (.ax ne)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D3_imp_2_1 : Interd (.and (.ifThen ne e) t3) e :=
  interdTab (.impR (.and (.ifThen ne e) t3) e (.andL (.ifThen ne e) t3 (.impL ne e (.orL e ne (.impLoc e bot (.ax e)) (.impL e bot (.ax ne) .bot)) (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)))))
    (.impR e (.and (.ifThen ne e) t3) (.andR (.ifThen ne e) t3 (.impR ne e (.impL e bot (.ax e) .bot)) (.orR e ne (.ax e))))
    (by decide +kernel) (by decide +kernel)

theorem D3_and_2_2 : Interd (.and ne ne) ne :=
  interdTab (.impR (.and ne ne) ne (.andL ne ne (.impL e bot (.ax ne) .bot)))
    (.impR ne (.and ne ne) (.impL e bot (.andR ne ne (.ax ne) (.ax ne)) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D3_or_2_2 : Interd (.or ne ne) ne :=
  interdTab (.impR (.or ne ne) ne (.orL ne ne (.impL e bot (.ax ne) .bot) (.impL e bot (.ax ne) .bot)))
    (.impR ne (.or ne ne) (.impL e bot (.orR ne ne (.ax ne)) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D3_imp_2_2 : Interd (.and (.ifThen ne ne) t3) t3 :=
  interdTab (.impR (.and (.ifThen ne ne) t3) t3 (.andL (.ifThen ne ne) t3 (.impL ne ne (.orL e ne (.impLoc e bot (.ax t3)) (.impL e bot (.ax ne) .bot)) (.impL e bot (.orL e ne (.ax e) (.ax t3)) .bot))))
    (.impR t3 (.and (.ifThen ne ne) t3) (.orL e ne (.andR (.ifThen ne ne) t3 (.impR ne ne (.orL e ne (.impL e bot (.ax e) .bot) (.impL e bot (.ax e) .bot))) (.ax t3)) (.impL e bot (.andR (.ifThen ne ne) t3 (.impLoc ne ne (.ax ne)) (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D3_and_2_3 : Interd (.and ne t3) ne :=
  interdTab (.impR (.and ne t3) ne (.andL ne t3 (.impL e bot (.orL e ne (.ax e) (.ax ne)) .bot)))
    (.impR ne (.and ne t3) (.impL e bot (.andR ne t3 (.ax ne) (.orR e ne (.ax ne))) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D3_or_2_3 : Interd (.or ne t3) t3 :=
  interdTab (.impR (.or ne t3) t3 (.orL ne t3 (.impL e bot (.orR e ne (.ax ne)) .bot) (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot))))
    (.impR t3 (.or ne t3) (.orL e ne (.orR ne t3 (.impLoc e bot (.ax t3))) (.impL e bot (.orR ne t3 (.ax ne)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D3_imp_2_3 : Interd (.and (.ifThen ne t3) t3) t3 :=
  interdTab (.impR (.and (.ifThen ne t3) t3) t3 (.andL (.ifThen ne t3) t3 (.impL ne t3 (.orL e ne (.impLoc e bot (.ax t3)) (.impL e bot (.ax ne) .bot)) (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)))))
    (.impR t3 (.and (.ifThen ne t3) t3) (.orL e ne (.andR (.ifThen ne t3) t3 (.impR ne t3 (.orL e ne (.impL e bot (.ax e) .bot) (.impL e bot (.ax e) .bot))) (.ax t3)) (.impL e bot (.andR (.ifThen ne t3) t3 (.impLoc ne t3 (.ax t3)) (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D3_box_3 : Interd (.and (.somehow t3) t3) t3 :=
  interdTab (.impR (.and (.somehow t3) t3) t3 (.andL (.somehow t3) t3 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot))))
    (.impR t3 (.and (.somehow t3) t3) (.orL e ne (.andR (.somehow t3) t3 (.boxR t3 (.boxL bot .bot)) (.ax t3)) (.impL e bot (.andR (.somehow t3) t3 (.boxR t3 (.impL e bot (.orL e ne (.boxL bot .bot) (.boxLoc bot (.ax t3))) .bot)) (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D3_and_3_0 : Interd (.and t3 bot) bot :=
  interdTab (.impR (.and t3 bot) bot (.andL t3 bot (.orL e ne .bot (.impL e bot .bot .bot))))
    (.impR bot (.and t3 bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D3_or_3_0 : Interd (.or t3 bot) t3 :=
  interdTab (.impR (.or t3 bot) t3 (.orL t3 bot (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) .bot))
    (.impR t3 (.or t3 bot) (.orL e ne (.orR t3 bot (.ax t3)) (.impL e bot (.orR t3 bot (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D3_imp_3_0 : Interd (.and (.ifThen t3 bot) t3) bot :=
  interdTab (.impR (.and (.ifThen t3 bot) t3) bot (.andL (.ifThen t3 bot) t3 (.impL t3 bot (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) .bot)))
    (.impR bot (.and (.ifThen t3 bot) t3) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D3_and_3_1 : Interd (.and t3 e) e :=
  interdTab (.impR (.and t3 e) e (.andL t3 e (.orL e ne (.ax e) (.impL e bot (.ax e) .bot))))
    (.impR e (.and t3 e) (.andR t3 e (.orR e ne (.ax e)) (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D3_or_3_1 : Interd (.or t3 e) t3 :=
  interdTab (.impR (.or t3 e) t3 (.orL t3 e (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orR e ne (.ax e))))
    (.impR t3 (.or t3 e) (.orL e ne (.orR t3 e (.ax t3)) (.impL e bot (.orR t3 e (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D3_imp_3_1 : Interd (.and t4 t3) e :=
  interdTab (.impR (.and t4 t3) e (.andL t4 t3 (.impL t3 e (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)))))
    (.impR e (.and t4 t3) (.andR t4 t3 (.impR t3 e (.orL e ne (.ax e) (.impL e bot (.ax e) .bot))) (.orR e ne (.ax e))))
    (by decide +kernel) (by decide +kernel)

theorem D3_and_3_2 : Interd (.and t3 ne) ne :=
  interdTab (.impR (.and t3 ne) ne (.andL t3 ne (.orL e ne (.impL e bot (.ax e) .bot) (.impL e bot (.ax ne) .bot))))
    (.impR ne (.and t3 ne) (.impL e bot (.andR t3 ne (.orR e ne (.ax ne)) (.ax ne)) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D3_or_3_2 : Interd (.or t3 ne) t3 :=
  interdTab (.impR (.or t3 ne) t3 (.orL t3 ne (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.impL e bot (.orR e ne (.ax ne)) .bot)))
    (.impR t3 (.or t3 ne) (.orL e ne (.orR t3 ne (.ax t3)) (.impL e bot (.orR t3 ne (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D3_imp_3_2 : Interd (.and (.ifThen t3 ne) t3) ne :=
  interdTab (.impR (.and (.ifThen t3 ne) t3) ne (.andL (.ifThen t3 ne) t3 (.impL t3 ne (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.impL e bot (.orL e ne (.ax e) (.ax ne)) .bot))))
    (.impR ne (.and (.ifThen t3 ne) t3) (.impL e bot (.andR (.ifThen t3 ne) t3 (.impR t3 ne (.impL e bot (.orL e ne (.ax e) (.ax ne)) .bot)) (.orR e ne (.ax ne))) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D3_and_3_3 : Interd (.and t3 t3) t3 :=
  interdTab (.impR (.and t3 t3) t3 (.andL t3 t3 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot))))
    (.impR t3 (.and t3 t3) (.orL e ne (.andR t3 t3 (.ax t3) (.ax t3)) (.impL e bot (.andR t3 t3 (.ax t3) (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D3_or_3_3 : Interd (.or t3 t3) t3 :=
  interdTab (.impR (.or t3 t3) t3 (.orL t3 t3 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot))))
    (.impR t3 (.or t3 t3) (.orL e ne (.orR t3 t3 (.ax t3)) (.impL e bot (.orR t3 t3 (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D3_imp_3_3 : Interd (.and (.ifThen t3 t3) t3) t3 :=
  interdTab (.impR (.and (.ifThen t3 t3) t3) t3 (.andL (.ifThen t3 t3) t3 (.impL t3 t3 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)))))
    (.impR t3 (.and (.ifThen t3 t3) t3) (.orL e ne (.andR (.ifThen t3 t3) t3 (.impLoc t3 t3 (.ax t3)) (.ax t3)) (.impL e bot (.andR (.ifThen t3 t3) t3 (.impLoc t3 t3 (.ax t3)) (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

/-- The closure table of `D3`. -/
theorem D3_table : DownTable t3 D3_list where
  bot_mem := D3_mem_0
  top_mem := D3_mem_3
  below := allL_mem (.cons D3_below_0
      (.cons D3_below_1
      (.cons D3_below_2
      (.cons D3_below_3
      .nil))))
  and_cl := allL_mem
    (.cons (allL_mem (.cons ⟨bot, D3_mem_0, D3_and_0_0⟩ (.cons ⟨bot, D3_mem_0, D3_and_0_1⟩ (.cons ⟨bot, D3_mem_0, D3_and_0_2⟩ (.cons ⟨bot, D3_mem_0, D3_and_0_3⟩ .nil)))))
      (.cons (allL_mem (.cons ⟨bot, D3_mem_0, D3_and_1_0⟩ (.cons ⟨e, D3_mem_1, D3_and_1_1⟩ (.cons ⟨bot, D3_mem_0, D3_and_1_2⟩ (.cons ⟨e, D3_mem_1, D3_and_1_3⟩ .nil)))))
      (.cons (allL_mem (.cons ⟨bot, D3_mem_0, D3_and_2_0⟩ (.cons ⟨bot, D3_mem_0, D3_and_2_1⟩ (.cons ⟨ne, D3_mem_2, D3_and_2_2⟩ (.cons ⟨ne, D3_mem_2, D3_and_2_3⟩ .nil)))))
      (.cons (allL_mem (.cons ⟨bot, D3_mem_0, D3_and_3_0⟩ (.cons ⟨e, D3_mem_1, D3_and_3_1⟩ (.cons ⟨ne, D3_mem_2, D3_and_3_2⟩ (.cons ⟨t3, D3_mem_3, D3_and_3_3⟩ .nil)))))
      .nil))))
  or_cl := allL_mem
    (.cons (allL_mem (.cons ⟨bot, D3_mem_0, D3_or_0_0⟩ (.cons ⟨e, D3_mem_1, D3_or_0_1⟩ (.cons ⟨ne, D3_mem_2, D3_or_0_2⟩ (.cons ⟨t3, D3_mem_3, D3_or_0_3⟩ .nil)))))
      (.cons (allL_mem (.cons ⟨e, D3_mem_1, D3_or_1_0⟩ (.cons ⟨e, D3_mem_1, D3_or_1_1⟩ (.cons ⟨t3, D3_mem_3, D3_or_1_2⟩ (.cons ⟨t3, D3_mem_3, D3_or_1_3⟩ .nil)))))
      (.cons (allL_mem (.cons ⟨ne, D3_mem_2, D3_or_2_0⟩ (.cons ⟨t3, D3_mem_3, D3_or_2_1⟩ (.cons ⟨ne, D3_mem_2, D3_or_2_2⟩ (.cons ⟨t3, D3_mem_3, D3_or_2_3⟩ .nil)))))
      (.cons (allL_mem (.cons ⟨t3, D3_mem_3, D3_or_3_0⟩ (.cons ⟨t3, D3_mem_3, D3_or_3_1⟩ (.cons ⟨t3, D3_mem_3, D3_or_3_2⟩ (.cons ⟨t3, D3_mem_3, D3_or_3_3⟩ .nil)))))
      .nil))))
  box_cl := allL_mem
    (.cons ⟨e, D3_mem_1, D3_box_0⟩
      (.cons ⟨e, D3_mem_1, D3_box_1⟩
      (.cons ⟨t3, D3_mem_3, D3_box_2⟩
      (.cons ⟨t3, D3_mem_3, D3_box_3⟩
      .nil))))
  imp_cl := allL_mem
    (.cons (allL_mem (.cons ⟨t3, D3_mem_3, D3_imp_0_0⟩ (.cons ⟨t3, D3_mem_3, D3_imp_0_1⟩ (.cons ⟨t3, D3_mem_3, D3_imp_0_2⟩ (.cons ⟨t3, D3_mem_3, D3_imp_0_3⟩ .nil)))))
      (.cons (allL_mem (.cons ⟨ne, D3_mem_2, D3_imp_1_0⟩ (.cons ⟨t3, D3_mem_3, D3_imp_1_1⟩ (.cons ⟨ne, D3_mem_2, D3_imp_1_2⟩ (.cons ⟨t3, D3_mem_3, D3_imp_1_3⟩ .nil)))))
      (.cons (allL_mem (.cons ⟨e, D3_mem_1, D3_imp_2_0⟩ (.cons ⟨e, D3_mem_1, D3_imp_2_1⟩ (.cons ⟨t3, D3_mem_3, D3_imp_2_2⟩ (.cons ⟨t3, D3_mem_3, D3_imp_2_3⟩ .nil)))))
      (.cons (allL_mem (.cons ⟨bot, D3_mem_0, D3_imp_3_0⟩ (.cons ⟨e, D3_mem_1, D3_imp_3_1⟩ (.cons ⟨ne, D3_mem_2, D3_imp_3_2⟩ (.cons ⟨t3, D3_mem_3, D3_imp_3_3⟩ .nil)))))
      .nil))))

/-! ### Table `D4`: the downset of `t4`, `[bot, e, t4]` -/

theorem D4_below_0 : Deriv [bot] t4 :=
  derivTab (.impR bot t4 .bot) (by decide +kernel)

theorem D4_below_1 : Deriv [e] t4 :=
  derivTab (.impR e t4 (.impR t3 e (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)))) (by decide +kernel)

theorem D4_below_2 : Deriv [t4] t4 :=
  derivTab (.impR t4 t4 (.impL t3 e (.orR e ne (.ax t4)) (.ax t4))) (by decide +kernel)

theorem D4_box_0 : Interd (.and e t4) e :=
  interdTab (.impR (.and e t4) e (.andL e t4 (.ax e)))
    (.impR e (.and e t4) (.andR e t4 (.ax e) (.impR t3 e (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)))))
    (by decide +kernel) (by decide +kernel)

theorem D4_and_0_0 : Interd (.and bot bot) bot :=
  interdTab (.impR (.and bot bot) bot (.andL bot bot .bot))
    (.impR bot (.and bot bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D4_or_0_0 : Interd (.or bot bot) bot :=
  interdTab (.impR (.or bot bot) bot (.orL bot bot .bot .bot))
    (.impR bot (.or bot bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D4_imp_0_0 : Interd (.and (.ifThen bot bot) t4) t4 :=
  interdTab (.impR (.and (.ifThen bot bot) t4) t4 (.andL (.ifThen bot bot) t4 (.impL bot bot (.impL t3 e (.orR e ne (.ax t4)) (.ax t4)) .bot)))
    (.impR t4 (.and (.ifThen bot bot) t4) (.impL t3 e (.orR e ne (.andR (.ifThen bot bot) t4 (.impR bot bot (.impL t3 e .bot .bot)) (.ax t4))) (.andR (.ifThen bot bot) t4 (.impR bot bot .bot) (.ax t4))))
    (by decide +kernel) (by decide +kernel)

theorem D4_and_0_1 : Interd (.and bot e) bot :=
  interdTab (.impR (.and bot e) bot (.andL bot e .bot))
    (.impR bot (.and bot e) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D4_or_0_1 : Interd (.or bot e) e :=
  interdTab (.impR (.or bot e) e (.orL bot e .bot (.ax e)))
    (.impR e (.or bot e) (.orR bot e (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D4_imp_0_1 : Interd (.and (.ifThen bot e) t4) t4 :=
  interdTab (.impR (.and (.ifThen bot e) t4) t4 (.andL (.ifThen bot e) t4 (.impL bot e (.impL t3 e (.orR e ne (.ax t4)) (.ax t4)) (.ax t4))))
    (.impR t4 (.and (.ifThen bot e) t4) (.impL t3 e (.orR e ne (.andR (.ifThen bot e) t4 (.impR bot e (.impL t3 e .bot .bot)) (.ax t4))) (.andR (.ifThen bot e) t4 (.impR bot e .bot) (.ax t4))))
    (by decide +kernel) (by decide +kernel)

theorem D4_and_0_2 : Interd (.and bot t4) bot :=
  interdTab (.impR (.and bot t4) bot (.andL bot t4 .bot))
    (.impR bot (.and bot t4) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D4_or_0_2 : Interd (.or bot t4) t4 :=
  interdTab (.impR (.or bot t4) t4 (.orL bot t4 .bot (.impL t3 e (.orR e ne (.ax t4)) (.ax t4))))
    (.impR t4 (.or bot t4) (.impL t3 e (.orR e ne (.orR bot t4 (.ax t4))) (.orR bot t4 (.ax t4))))
    (by decide +kernel) (by decide +kernel)

theorem D4_imp_0_2 : Interd (.and (.ifThen bot t4) t4) t4 :=
  interdTab (.impR (.and (.ifThen bot t4) t4) t4 (.andL (.ifThen bot t4) t4 (.impL bot t4 (.impL t3 e (.orR e ne (.ax t4)) (.ax t4)) (.impL t3 e (.orR e ne (.ax t4)) (.ax t4)))))
    (.impR t4 (.and (.ifThen bot t4) t4) (.impL t3 e (.orR e ne (.andR (.ifThen bot t4) t4 (.impR bot t4 (.impL t3 e .bot .bot)) (.ax t4))) (.andR (.ifThen bot t4) t4 (.impR bot t4 .bot) (.ax t4))))
    (by decide +kernel) (by decide +kernel)

theorem D4_box_1 : Interd (.and (.somehow e) t4) e :=
  interdTab (.impR (.and (.somehow e) t4) e (.andL (.somehow e) t4 (.impL t3 e (.orR e ne (.boxR bot (.boxL e (.boxL bot .bot)))) (.ax e))))
    (.impR e (.and (.somehow e) t4) (.andR (.somehow e) t4 (.boxR e (.boxL bot .bot)) (.impR t3 e (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)))))
    (by decide +kernel) (by decide +kernel)

theorem D4_and_1_0 : Interd (.and e bot) bot :=
  interdTab (.impR (.and e bot) bot (.andL e bot .bot))
    (.impR bot (.and e bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D4_or_1_0 : Interd (.or e bot) e :=
  interdTab (.impR (.or e bot) e (.orL e bot (.ax e) .bot))
    (.impR e (.or e bot) (.orR e bot (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D4_imp_1_0 : Interd (.and ne t4) bot :=
  interdTab (.impR (.and ne t4) bot (.andL ne t4 (.impL e bot (.impL t3 e (.orR e ne (.ax ne)) (.ax e)) .bot)))
    (.impR bot (.and ne t4) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D4_and_1_1 : Interd (.and e e) e :=
  interdTab (.impR (.and e e) e (.andL e e (.ax e)))
    (.impR e (.and e e) (.andR e e (.ax e) (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D4_or_1_1 : Interd (.or e e) e :=
  interdTab (.impR (.or e e) e (.orL e e (.ax e) (.ax e)))
    (.impR e (.or e e) (.orR e e (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D4_imp_1_1 : Interd (.and (.ifThen e e) t4) t4 :=
  interdTab (.impR (.and (.ifThen e e) t4) t4 (.andL (.ifThen e e) t4 (.impL e e (.impL t3 e (.orR e ne (.ax t4)) (.ax e)) (.ax t4))))
    (.impR t4 (.and (.ifThen e e) t4) (.impL t3 e (.orR e ne (.andR (.ifThen e e) t4 (.impR e e (.impL t3 e (.orR e ne (.ax e)) (.ax e))) (.ax t4))) (.andR (.ifThen e e) t4 (.impLoc e e (.ax e)) (.ax t4))))
    (by decide +kernel) (by decide +kernel)

theorem D4_and_1_2 : Interd (.and e t4) e :=
  interdTab (.impR (.and e t4) e (.andL e t4 (.ax e)))
    (.impR e (.and e t4) (.andR e t4 (.ax e) (.impR t3 e (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)))))
    (by decide +kernel) (by decide +kernel)

theorem D4_or_1_2 : Interd (.or e t4) t4 :=
  interdTab (.impR (.or e t4) t4 (.orL e t4 (.impR t3 e (.orL e t4 (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)) (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)))) (.impL t3 e (.orR e ne (.ax t4)) (.ax t4))))
    (.impR t4 (.or e t4) (.impL t3 e (.orR e ne (.orR e t4 (.ax t4))) (.orR e t4 (.ax e))))
    (by decide +kernel) (by decide +kernel)

theorem D4_imp_1_2 : Interd (.and (.ifThen e t4) t4) t4 :=
  interdTab (.impR (.and (.ifThen e t4) t4) t4 (.andL (.ifThen e t4) t4 (.impL e t4 (.impL t3 e (.orR e ne (.ax t4)) (.ax e)) (.impL t3 e (.orR e ne (.ax t4)) (.ax t4)))))
    (.impR t4 (.and (.ifThen e t4) t4) (.impL t3 e (.orR e ne (.andR (.ifThen e t4) t4 (.impR e t4 (.impL t3 e (.orR e ne (.ax e)) (.ax t4))) (.ax t4))) (.andR (.ifThen e t4) t4 (.impLoc e t4 (.ax t4)) (.ax t4))))
    (by decide +kernel) (by decide +kernel)

theorem D4_box_2 : Interd (.and (.somehow t4) t4) t4 :=
  interdTab (.impR (.and (.somehow t4) t4) t4 (.andL (.somehow t4) t4 (.impL t3 e (.orR e ne (.ax t4)) (.ax t4))))
    (.impR t4 (.and (.somehow t4) t4) (.impL t3 e (.orR e ne (.andR (.somehow t4) t4 (.boxR t4 (.impL t3 e (.orR e ne (.boxLoc bot (.ax t4))) (.boxL bot .bot))) (.ax t4))) (.andR (.somehow t4) t4 (.boxR t4 (.boxL bot .bot)) (.ax t4))))
    (by decide +kernel) (by decide +kernel)

theorem D4_and_2_0 : Interd (.and t4 bot) bot :=
  interdTab (.impR (.and t4 bot) bot (.andL t4 bot (.impL t3 e .bot .bot)))
    (.impR bot (.and t4 bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D4_or_2_0 : Interd (.or t4 bot) t4 :=
  interdTab (.impR (.or t4 bot) t4 (.orL t4 bot (.impL t3 e (.orR e ne (.ax t4)) (.ax t4)) .bot))
    (.impR t4 (.or t4 bot) (.impL t3 e (.orR e ne (.orR t4 bot (.ax t4))) (.orR t4 bot (.ax t4))))
    (by decide +kernel) (by decide +kernel)

theorem D4_imp_2_0 : Interd (.and (.ifThen t4 bot) t4) bot :=
  interdTab (.impR (.and (.ifThen t4 bot) t4) bot (.andL (.ifThen t4 bot) t4 (.impL t4 bot (.impL t3 e (.orR e ne (.ax t4)) (.ax t4)) .bot)))
    (.impR bot (.and (.ifThen t4 bot) t4) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D4_and_2_1 : Interd (.and t4 e) e :=
  interdTab (.impR (.and t4 e) e (.andL t4 e (.impL t3 e (.orR e ne (.ax e)) (.ax e))))
    (.impR e (.and t4 e) (.andR t4 e (.impR t3 e (.orL e ne (.ax e) (.impL e bot (.ax e) .bot))) (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D4_or_2_1 : Interd (.or t4 e) t4 :=
  interdTab (.impR (.or t4 e) t4 (.orL t4 e (.impL t3 e (.orR e ne (.ax t4)) (.ax t4)) (.impR t3 e (.orL t4 e (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)) (.orL e ne (.ax e) (.impL e bot (.ax e) .bot))))))
    (.impR t4 (.or t4 e) (.impL t3 e (.orR e ne (.orR t4 e (.ax t4))) (.orR t4 e (.ax t4))))
    (by decide +kernel) (by decide +kernel)

theorem D4_imp_2_1 : Interd (.and (.ifThen t4 e) t4) e :=
  interdTab (.impR (.and (.ifThen t4 e) t4) e (.andL (.ifThen t4 e) t4 (.impL t4 e (.impL t3 e (.orR e ne (.ax t4)) (.ax t4)) (.ax e))))
    (.impR e (.and (.ifThen t4 e) t4) (.andR (.ifThen t4 e) t4 (.impR t4 e (.ax e)) (.impR t3 e (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)))))
    (by decide +kernel) (by decide +kernel)

theorem D4_and_2_2 : Interd (.and t4 t4) t4 :=
  interdTab (.impR (.and t4 t4) t4 (.andL t4 t4 (.impL t3 e (.orR e ne (.ax t4)) (.ax t4))))
    (.impR t4 (.and t4 t4) (.impL t3 e (.orR e ne (.andR t4 t4 (.ax t4) (.ax t4))) (.andR t4 t4 (.ax t4) (.ax t4))))
    (by decide +kernel) (by decide +kernel)

theorem D4_or_2_2 : Interd (.or t4 t4) t4 :=
  interdTab (.impR (.or t4 t4) t4 (.orL t4 t4 (.impL t3 e (.orR e ne (.ax t4)) (.ax t4)) (.impL t3 e (.orR e ne (.ax t4)) (.ax t4))))
    (.impR t4 (.or t4 t4) (.impL t3 e (.orR e ne (.orR t4 t4 (.ax t4))) (.orR t4 t4 (.ax t4))))
    (by decide +kernel) (by decide +kernel)

theorem D4_imp_2_2 : Interd (.and (.ifThen t4 t4) t4) t4 :=
  interdTab (.impR (.and (.ifThen t4 t4) t4) t4 (.andL (.ifThen t4 t4) t4 (.impL t4 t4 (.impL t3 e (.orR e ne (.ax t4)) (.ax t4)) (.impL t3 e (.orR e ne (.ax t4)) (.ax t4)))))
    (.impR t4 (.and (.ifThen t4 t4) t4) (.impL t3 e (.orR e ne (.andR (.ifThen t4 t4) t4 (.impLoc t4 t4 (.ax t4)) (.ax t4))) (.andR (.ifThen t4 t4) t4 (.impLoc t4 t4 (.ax t4)) (.ax t4))))
    (by decide +kernel) (by decide +kernel)

/-- The closure table of `D4`. -/
theorem D4_table : DownTable t4 D4_list where
  bot_mem := D4_mem_0
  top_mem := D4_mem_2
  below := allL_mem (.cons D4_below_0
      (.cons D4_below_1
      (.cons D4_below_2
      .nil)))
  and_cl := allL_mem
    (.cons (allL_mem (.cons ⟨bot, D4_mem_0, D4_and_0_0⟩ (.cons ⟨bot, D4_mem_0, D4_and_0_1⟩ (.cons ⟨bot, D4_mem_0, D4_and_0_2⟩ .nil))))
      (.cons (allL_mem (.cons ⟨bot, D4_mem_0, D4_and_1_0⟩ (.cons ⟨e, D4_mem_1, D4_and_1_1⟩ (.cons ⟨e, D4_mem_1, D4_and_1_2⟩ .nil))))
      (.cons (allL_mem (.cons ⟨bot, D4_mem_0, D4_and_2_0⟩ (.cons ⟨e, D4_mem_1, D4_and_2_1⟩ (.cons ⟨t4, D4_mem_2, D4_and_2_2⟩ .nil))))
      .nil)))
  or_cl := allL_mem
    (.cons (allL_mem (.cons ⟨bot, D4_mem_0, D4_or_0_0⟩ (.cons ⟨e, D4_mem_1, D4_or_0_1⟩ (.cons ⟨t4, D4_mem_2, D4_or_0_2⟩ .nil))))
      (.cons (allL_mem (.cons ⟨e, D4_mem_1, D4_or_1_0⟩ (.cons ⟨e, D4_mem_1, D4_or_1_1⟩ (.cons ⟨t4, D4_mem_2, D4_or_1_2⟩ .nil))))
      (.cons (allL_mem (.cons ⟨t4, D4_mem_2, D4_or_2_0⟩ (.cons ⟨t4, D4_mem_2, D4_or_2_1⟩ (.cons ⟨t4, D4_mem_2, D4_or_2_2⟩ .nil))))
      .nil)))
  box_cl := allL_mem
    (.cons ⟨e, D4_mem_1, D4_box_0⟩
      (.cons ⟨e, D4_mem_1, D4_box_1⟩
      (.cons ⟨t4, D4_mem_2, D4_box_2⟩
      .nil)))
  imp_cl := allL_mem
    (.cons (allL_mem (.cons ⟨t4, D4_mem_2, D4_imp_0_0⟩ (.cons ⟨t4, D4_mem_2, D4_imp_0_1⟩ (.cons ⟨t4, D4_mem_2, D4_imp_0_2⟩ .nil))))
      (.cons (allL_mem (.cons ⟨bot, D4_mem_0, D4_imp_1_0⟩ (.cons ⟨t4, D4_mem_2, D4_imp_1_1⟩ (.cons ⟨t4, D4_mem_2, D4_imp_1_2⟩ .nil))))
      (.cons (allL_mem (.cons ⟨bot, D4_mem_0, D4_imp_2_0⟩ (.cons ⟨e, D4_mem_1, D4_imp_2_1⟩ (.cons ⟨t4, D4_mem_2, D4_imp_2_2⟩ .nil))))
      .nil)))

/-! ### Table `D5`: the downset of `t5`, `[bot, e, ne, t3, t4, t5]` -/

theorem D5_below_0 : Deriv [bot] t5 :=
  derivTab (.impR bot t5 .bot) (by decide +kernel)

theorem D5_below_1 : Deriv [e] t5 :=
  derivTab (.impR e t5 (.orR t3 t4 (.orR e ne (.ax e)))) (by decide +kernel)

theorem D5_below_2 : Deriv [ne] t5 :=
  derivTab (.impR ne t5 (.impL e bot (.orR t3 t4 (.orR e ne (.ax ne))) .bot)) (by decide +kernel)

theorem D5_below_3 : Deriv [t3] t5 :=
  derivTab (.impR t3 t5 (.orL e ne (.orR t3 t4 (.ax t3)) (.impL e bot (.orR t3 t4 (.ax t3)) .bot))) (by decide +kernel)

theorem D5_below_4 : Deriv [t4] t5 :=
  derivTab (.impR t4 t5 (.impL t3 e (.orR e ne (.orR t3 t4 (.ax t4))) (.orR t3 t4 (.orR e ne (.ax e))))) (by decide +kernel)

theorem D5_below_5 : Deriv [t5] t5 :=
  derivTab (.impR t5 t5 (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5)))) (by decide +kernel)

theorem D5_box_0 : Interd (.and e t5) e :=
  interdTab (.impR (.and e t5) e (.andL e t5 (.orL t3 t4 (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)) (.ax e))))
    (.impR e (.and e t5) (.andR e t5 (.ax e) (.orR t3 t4 (.orR e ne (.ax e)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_0_0 : Interd (.and bot bot) bot :=
  interdTab (.impR (.and bot bot) bot (.andL bot bot .bot))
    (.impR bot (.and bot bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D5_or_0_0 : Interd (.or bot bot) bot :=
  interdTab (.impR (.or bot bot) bot (.orL bot bot .bot .bot))
    (.impR bot (.or bot bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_0_0 : Interd (.and (.ifThen bot bot) t5) t5 :=
  interdTab (.impR (.and (.ifThen bot bot) t5) t5 (.andL (.ifThen bot bot) t5 (.impL bot bot (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))) .bot)))
    (.impR t5 (.and (.ifThen bot bot) t5) (.orL t3 t4 (.orL e ne (.andR (.ifThen bot bot) t5 (.impR bot bot (.orL e ne (.orL t3 t4 .bot .bot) (.impL e bot (.orL t3 t4 .bot .bot) .bot))) (.ax t5)) (.impL e bot (.andR (.ifThen bot bot) t5 (.impR bot bot (.impL e bot (.orL e ne (.orL t3 t4 .bot .bot) (.orL t3 t4 .bot (.impL t3 e .bot .bot))) .bot)) (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.andR (.ifThen bot bot) t5 (.impR bot bot (.impL t3 e (.orL t3 t4 (.orL e ne .bot (.impL e bot .bot .bot)) .bot) (.orL t3 t4 (.orL e ne .bot (.impL e bot .bot .bot)) .bot))) (.ax t5))) (.andR (.ifThen bot bot) t5 (.impR bot bot (.orL t3 t4 (.orL e ne .bot (.impL e bot .bot .bot)) .bot)) (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_0_1 : Interd (.and bot e) bot :=
  interdTab (.impR (.and bot e) bot (.andL bot e .bot))
    (.impR bot (.and bot e) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D5_or_0_1 : Interd (.or bot e) e :=
  interdTab (.impR (.or bot e) e (.orL bot e .bot (.ax e)))
    (.impR e (.or bot e) (.orR bot e (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_0_1 : Interd (.and (.ifThen bot e) t5) t5 :=
  interdTab (.impR (.and (.ifThen bot e) t5) t5 (.andL (.ifThen bot e) t5 (.impL bot e (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))) (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax e) .bot)) (.ax t5)))))
    (.impR t5 (.and (.ifThen bot e) t5) (.orL t3 t4 (.orL e ne (.andR (.ifThen bot e) t5 (.impR bot e (.orL e ne (.orL t3 t4 .bot .bot) (.impL e bot (.orL t3 t4 .bot .bot) .bot))) (.ax t5)) (.impL e bot (.andR (.ifThen bot e) t5 (.impR bot e (.impL e bot (.orL e ne (.orL t3 t4 .bot .bot) (.orL t3 t4 .bot (.impL t3 e .bot .bot))) .bot)) (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.andR (.ifThen bot e) t5 (.impR bot e (.impL t3 e (.orL t3 t4 (.orL e ne .bot (.impL e bot .bot .bot)) .bot) (.orL t3 t4 (.orL e ne .bot (.impL e bot .bot .bot)) .bot))) (.ax t5))) (.andR (.ifThen bot e) t5 (.impR bot e (.orL t3 t4 (.orL e ne .bot (.impL e bot .bot .bot)) .bot)) (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_0_2 : Interd (.and bot ne) bot :=
  interdTab (.impR (.and bot ne) bot (.andL bot ne .bot))
    (.impR bot (.and bot ne) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D5_or_0_2 : Interd (.or bot ne) ne :=
  interdTab (.impR (.or bot ne) ne (.orL bot ne .bot (.impL e bot (.ax ne) .bot)))
    (.impR ne (.or bot ne) (.impL e bot (.orR bot ne (.ax ne)) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_0_2 : Interd (.and (.ifThen bot ne) t5) t5 :=
  interdTab (.impR (.and (.ifThen bot ne) t5) t5 (.andL (.ifThen bot ne) t5 (.impL bot ne (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))) (.impL e bot (.orL t3 t4 (.orL e ne (.ax e) (.ax t5)) (.impL t3 e (.orR e ne (.ax ne)) (.ax e))) .bot))))
    (.impR t5 (.and (.ifThen bot ne) t5) (.orL t3 t4 (.orL e ne (.andR (.ifThen bot ne) t5 (.impR bot ne (.orL e ne (.orL t3 t4 .bot .bot) (.impL e bot (.orL t3 t4 .bot .bot) .bot))) (.ax t5)) (.impL e bot (.andR (.ifThen bot ne) t5 (.impR bot ne (.impL e bot (.orL e ne (.orL t3 t4 .bot .bot) (.orL t3 t4 .bot (.impL t3 e .bot .bot))) .bot)) (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.andR (.ifThen bot ne) t5 (.impR bot ne (.impL t3 e (.orL t3 t4 (.orL e ne .bot (.impL e bot .bot .bot)) .bot) (.orL t3 t4 (.orL e ne .bot (.impL e bot .bot .bot)) .bot))) (.ax t5))) (.andR (.ifThen bot ne) t5 (.impR bot ne (.orL t3 t4 (.orL e ne .bot (.impL e bot .bot .bot)) .bot)) (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_0_3 : Interd (.and bot t3) bot :=
  interdTab (.impR (.and bot t3) bot (.andL bot t3 .bot))
    (.impR bot (.and bot t3) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D5_or_0_3 : Interd (.or bot t3) t3 :=
  interdTab (.impR (.or bot t3) t3 (.orL bot t3 .bot (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot))))
    (.impR t3 (.or bot t3) (.orL e ne (.orR bot t3 (.ax t3)) (.impL e bot (.orR bot t3 (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_0_3 : Interd (.and (.ifThen bot t3) t5) t5 :=
  interdTab (.impR (.and (.ifThen bot t3) t5) t5 (.andL (.ifThen bot t3) t5 (.impL bot t3 (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))) (.orL e ne (.orL t3 t4 (.ax t5) (.ax t5)) (.impL e bot (.orL t3 t4 (.ax t5) (.impL t3 e (.ax t3) (.ax e))) .bot)))))
    (.impR t5 (.and (.ifThen bot t3) t5) (.orL t3 t4 (.orL e ne (.andR (.ifThen bot t3) t5 (.impR bot t3 (.orL e ne (.orL t3 t4 .bot .bot) (.impL e bot (.orL t3 t4 .bot .bot) .bot))) (.ax t5)) (.impL e bot (.andR (.ifThen bot t3) t5 (.impR bot t3 (.impL e bot (.orL e ne (.orL t3 t4 .bot .bot) (.orL t3 t4 .bot (.impL t3 e .bot .bot))) .bot)) (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.andR (.ifThen bot t3) t5 (.impR bot t3 (.impL t3 e (.orL t3 t4 (.orL e ne .bot (.impL e bot .bot .bot)) .bot) (.orL t3 t4 (.orL e ne .bot (.impL e bot .bot .bot)) .bot))) (.ax t5))) (.andR (.ifThen bot t3) t5 (.impR bot t3 (.orL t3 t4 (.orL e ne .bot (.impL e bot .bot .bot)) .bot)) (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_0_4 : Interd (.and bot t4) bot :=
  interdTab (.impR (.and bot t4) bot (.andL bot t4 .bot))
    (.impR bot (.and bot t4) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D5_or_0_4 : Interd (.or bot t4) t4 :=
  interdTab (.impR (.or bot t4) t4 (.orL bot t4 .bot (.impL t3 e (.orR e ne (.ax t4)) (.ax t4))))
    (.impR t4 (.or bot t4) (.impL t3 e (.orR e ne (.orR bot t4 (.ax t4))) (.orR bot t4 (.ax t4))))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_0_4 : Interd (.and (.ifThen bot t4) t5) t5 :=
  interdTab (.impR (.and (.ifThen bot t4) t5) t5 (.andL (.ifThen bot t4) t5 (.impL bot t4 (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))) (.impL t3 e (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orR e ne (.ax t5))) (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax e) .bot)) (.ax t5))))))
    (.impR t5 (.and (.ifThen bot t4) t5) (.orL t3 t4 (.orL e ne (.andR (.ifThen bot t4) t5 (.impR bot t4 (.orL e ne (.orL t3 t4 .bot .bot) (.impL e bot (.orL t3 t4 .bot .bot) .bot))) (.ax t5)) (.impL e bot (.andR (.ifThen bot t4) t5 (.impR bot t4 (.impL e bot (.orL e ne (.orL t3 t4 .bot .bot) (.orL t3 t4 .bot (.impL t3 e .bot .bot))) .bot)) (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.andR (.ifThen bot t4) t5 (.impR bot t4 (.impL t3 e (.orL t3 t4 (.orL e ne .bot (.impL e bot .bot .bot)) .bot) (.orL t3 t4 (.orL e ne .bot (.impL e bot .bot .bot)) .bot))) (.ax t5))) (.andR (.ifThen bot t4) t5 (.impR bot t4 (.orL t3 t4 (.orL e ne .bot (.impL e bot .bot .bot)) .bot)) (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_0_5 : Interd (.and bot t5) bot :=
  interdTab (.impR (.and bot t5) bot (.andL bot t5 .bot))
    (.impR bot (.and bot t5) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D5_or_0_5 : Interd (.or bot t5) t5 :=
  interdTab (.impR (.or bot t5) t5 (.orL bot t5 .bot (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5)))))
    (.impR t5 (.or bot t5) (.orL t3 t4 (.orL e ne (.orR bot t5 (.ax t5)) (.impL e bot (.orR bot t5 (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.orR bot t5 (.ax t5))) (.orR bot t5 (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_0_5 : Interd (.and (.ifThen bot t5) t5) t5 :=
  interdTab (.impR (.and (.ifThen bot t5) t5) t5 (.andL (.ifThen bot t5) t5 (.impL bot t5 (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))) (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))))))
    (.impR t5 (.and (.ifThen bot t5) t5) (.orL t3 t4 (.orL e ne (.andR (.ifThen bot t5) t5 (.impR bot t5 (.orL e ne (.orL t3 t4 .bot .bot) (.impL e bot (.orL t3 t4 .bot .bot) .bot))) (.ax t5)) (.impL e bot (.andR (.ifThen bot t5) t5 (.impR bot t5 (.impL e bot (.orL e ne (.orL t3 t4 .bot .bot) (.orL t3 t4 .bot (.impL t3 e .bot .bot))) .bot)) (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.andR (.ifThen bot t5) t5 (.impR bot t5 (.impL t3 e (.orL t3 t4 (.orL e ne .bot (.impL e bot .bot .bot)) .bot) (.orL t3 t4 (.orL e ne .bot (.impL e bot .bot .bot)) .bot))) (.ax t5))) (.andR (.ifThen bot t5) t5 (.impR bot t5 (.orL t3 t4 (.orL e ne .bot (.impL e bot .bot .bot)) .bot)) (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_box_1 : Interd (.and (.somehow e) t5) e :=
  interdTab (.impR (.and (.somehow e) t5) e (.andL (.somehow e) t5 (.orL t3 t4 (.orL e ne (.ax e) (.impL e bot (.boxR bot (.boxL e (.boxL bot .bot))) .bot)) (.impL t3 e (.orR e ne (.boxR bot (.boxL e (.boxL bot .bot)))) (.ax e)))))
    (.impR e (.and (.somehow e) t5) (.andR (.somehow e) t5 (.boxR e (.boxL bot .bot)) (.orR t3 t4 (.orR e ne (.ax e)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_1_0 : Interd (.and e bot) bot :=
  interdTab (.impR (.and e bot) bot (.andL e bot .bot))
    (.impR bot (.and e bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D5_or_1_0 : Interd (.or e bot) e :=
  interdTab (.impR (.or e bot) e (.orL e bot (.ax e) .bot))
    (.impR e (.or e bot) (.orR e bot (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_1_0 : Interd (.and ne t5) ne :=
  interdTab (.impR (.and ne t5) ne (.andL ne t5 (.impL e bot (.orL t3 t4 (.orL e ne (.ax e) (.ax ne)) (.impL t3 e (.orR e ne (.ax ne)) (.ax e))) .bot)))
    (.impR ne (.and ne t5) (.impL e bot (.andR ne t5 (.ax ne) (.orR t3 t4 (.orR e ne (.ax ne)))) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_1_1 : Interd (.and e e) e :=
  interdTab (.impR (.and e e) e (.andL e e (.ax e)))
    (.impR e (.and e e) (.andR e e (.ax e) (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D5_or_1_1 : Interd (.or e e) e :=
  interdTab (.impR (.or e e) e (.orL e e (.ax e) (.ax e)))
    (.impR e (.or e e) (.orR e e (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_1_1 : Interd (.and (.ifThen e e) t5) t5 :=
  interdTab (.impR (.and (.ifThen e e) t5) t5 (.andL (.ifThen e e) t5 (.impL e e (.orL t3 t4 (.orL e ne (.ax e) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax e))) (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax e) .bot)) (.ax t5)))))
    (.impR t5 (.and (.ifThen e e) t5) (.orL t3 t4 (.orL e ne (.andR (.ifThen e e) t5 (.impLoc e e (.ax e)) (.ax t5)) (.impL e bot (.andR (.ifThen e e) t5 (.impR e e (.impL e bot (.orL e ne (.orL t3 t4 (.ax e) (.ax e)) (.orL t3 t4 (.ax e) (.impL t3 e (.ax t3) (.ax e)))) .bot)) (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.andR (.ifThen e e) t5 (.impR e e (.impL t3 e (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax e) .bot)) (.orR e ne (.ax e))) (.orL t3 t4 (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)) (.ax e)))) (.ax t5))) (.andR (.ifThen e e) t5 (.impLoc e e (.ax e)) (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_1_2 : Interd (.and e ne) bot :=
  interdTab (.impR (.and e ne) bot (.andL e ne (.impL e bot (.ax e) .bot)))
    (.impR bot (.and e ne) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D5_or_1_2 : Interd (.or e ne) t3 :=
  interdTab (.impR t3 t3 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)))
    (.impR t3 t3 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_1_2 : Interd (.and (.ifThen e ne) t5) ne :=
  interdTab (.impR (.and (.ifThen e ne) t5) ne (.andL (.ifThen e ne) t5 (.impL e ne (.orL t3 t4 (.orL e ne (.ax e) (.impL e bot (.ax ne) .bot)) (.impL t3 e (.orR e ne (.boxR bot (.impL e ne (.impL t3 e (.orL t3 t4 (.orL e ne (.boxL bot .bot) (.impL e bot (.andL (.ifThen e ne) t5 (.boxLoc bot (.ax t3))) .bot)) (.andL (.ifThen e ne) t5 (.orR e ne (.boxLoc bot (.impR e bot (.impL e ne (.impL t3 e (.orL t3 t4 (.orL e ne (.andL (.ifThen e ne) t5 (.ax t3)) (.impL e bot (.andL (.ifThen e ne) t5 (.ax e)) .bot)) (.andL (.ifThen e ne) t5 (.orR e ne (.ax e)))) (.orL t3 t4 (.orL e ne (.andL (.ifThen e ne) t5 (.ax e)) (.impL e bot (.andL (.ifThen e ne) t5 (.ax e)) .bot)) (.andL (.ifThen e ne) t5 (.ax e)))) (.impL e bot (.impL t3 e (.orL t3 t4 (.orL e ne (.andL (.ifThen e ne) t5 (.ax t3)) (.andL (.ifThen e ne) t5 (.ax t3))) (.andL (.ifThen e ne) t5 (.orR e ne (.ax e)))) (.orL t3 t4 (.orL e ne (.andL (.ifThen e ne) t5 (.ax e)) (.andL (.ifThen e ne) t5 (.ax e))) (.andL (.ifThen e ne) t5 (.ax e)))) .bot))))))) (.boxL bot .bot)) (.impL e bot (.impL t3 e (.orL t3 t4 (.orL e ne (.boxL bot .bot) (.andL (.ifThen e ne) t5 (.ax t3))) (.andL (.ifThen e ne) t5 (.orR e ne (.boxLoc bot (.ax ne))))) (.boxL bot .bot)) .bot)))) (.ax e))) (.impL e bot (.orL t3 t4 (.orL e ne (.ax e) (.ax ne)) (.impL t3 e (.orR e ne (.ax ne)) (.ax e))) .bot))))
    (.impR ne (.and (.ifThen e ne) t5) (.impL e bot (.andR (.ifThen e ne) t5 (.impR e ne (.impL e bot (.ax e) .bot)) (.orR t3 t4 (.orR e ne (.ax ne)))) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_1_3 : Interd (.and e t3) e :=
  interdTab (.impR (.and e t3) e (.andL e t3 (.orL e ne (.ax e) (.impL e bot (.ax e) .bot))))
    (.impR e (.and e t3) (.andR e t3 (.ax e) (.orR e ne (.ax e))))
    (by decide +kernel) (by decide +kernel)

theorem D5_or_1_3 : Interd (.or e t3) t3 :=
  interdTab (.impR (.or e t3) t3 (.orL e t3 (.orR e ne (.ax e)) (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot))))
    (.impR t3 (.or e t3) (.orL e ne (.orR e t3 (.ax e)) (.impL e bot (.orR e t3 (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_1_3 : Interd (.and (.ifThen e t3) t5) t5 :=
  interdTab (.impR (.and (.ifThen e t3) t5) t5 (.andL (.ifThen e t3) t5 (.impL e t3 (.orL t3 t4 (.orL e ne (.ax e) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax e))) (.orL e ne (.orL t3 t4 (.ax t5) (.ax t5)) (.impL e bot (.orL t3 t4 (.ax t5) (.impL t3 e (.ax t3) (.ax e))) .bot)))))
    (.impR t5 (.and (.ifThen e t3) t5) (.orL t3 t4 (.orL e ne (.andR (.ifThen e t3) t5 (.impLoc e t3 (.ax t3)) (.ax t5)) (.impL e bot (.andR (.ifThen e t3) t5 (.impR e t3 (.impL e bot (.orL e ne (.orL t3 t4 (.ax e) (.ax e)) (.orL t3 t4 (.ax e) (.impL t3 e (.ax t3) (.ax e)))) .bot)) (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.andR (.ifThen e t3) t5 (.impR e t3 (.impL t3 e (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax e) .bot)) (.orR e ne (.ax e))) (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax e) .bot)) (.orR e ne (.ax e))))) (.ax t5))) (.andR (.ifThen e t3) t5 (.impLoc e t3 (.orR e ne (.ax e))) (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_1_4 : Interd (.and e t4) e :=
  interdTab (.impR (.and e t4) e (.andL e t4 (.ax e)))
    (.impR e (.and e t4) (.andR e t4 (.ax e) (.impR t3 e (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_or_1_4 : Interd (.or e t4) t4 :=
  interdTab (.impR (.or e t4) t4 (.orL e t4 (.impR t3 e (.orL e t4 (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)) (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)))) (.impL t3 e (.orR e ne (.ax t4)) (.ax t4))))
    (.impR t4 (.or e t4) (.impL t3 e (.orR e ne (.orR e t4 (.ax t4))) (.orR e t4 (.ax e))))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_1_4 : Interd (.and (.ifThen e t4) t5) t5 :=
  interdTab (.impR (.and (.ifThen e t4) t5) t5 (.andL (.ifThen e t4) t5 (.impL e t4 (.orL t3 t4 (.orL e ne (.ax e) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax e))) (.impL t3 e (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orR e ne (.ax t5))) (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax e) .bot)) (.ax t5))))))
    (.impR t5 (.and (.ifThen e t4) t5) (.orL t3 t4 (.orL e ne (.andR (.ifThen e t4) t5 (.impLoc e t4 (.impLoc t3 e (.ax e))) (.ax t5)) (.impL e bot (.andR (.ifThen e t4) t5 (.impR e t4 (.impL e bot (.orL e ne (.orL t3 t4 (.ax e) (.ax e)) (.orL t3 t4 (.ax e) (.impL t3 e (.ax t3) (.ax e)))) .bot)) (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.andR (.ifThen e t4) t5 (.impR e t4 (.impL t3 e (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax e) .bot)) (.orR e ne (.ax e))) (.orL t3 t4 (.orL e ne (.ax t4) (.impL e bot (.ax e) .bot)) (.ax t4)))) (.ax t5))) (.andR (.ifThen e t4) t5 (.impLoc e t4 (.ax t4)) (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_1_5 : Interd (.and e t5) e :=
  interdTab (.impR (.and e t5) e (.andL e t5 (.orL t3 t4 (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)) (.ax e))))
    (.impR e (.and e t5) (.andR e t5 (.ax e) (.orR t3 t4 (.orR e ne (.ax e)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_or_1_5 : Interd (.or e t5) t5 :=
  interdTab (.impR (.or e t5) t5 (.orL e t5 (.orR t3 t4 (.orR e ne (.ax e))) (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5)))))
    (.impR t5 (.or e t5) (.orL t3 t4 (.orL e ne (.orR e t5 (.ax e)) (.impL e bot (.orR e t5 (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.orR e t5 (.ax t5))) (.orR e t5 (.ax e)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_1_5 : Interd (.and (.ifThen e t5) t5) t5 :=
  interdTab (.impR (.and (.ifThen e t5) t5) t5 (.andL (.ifThen e t5) t5 (.impL e t5 (.orL t3 t4 (.orL e ne (.ax e) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax e))) (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))))))
    (.impR t5 (.and (.ifThen e t5) t5) (.orL t3 t4 (.orL e ne (.andR (.ifThen e t5) t5 (.impLoc e t5 (.ax t5)) (.ax t5)) (.impL e bot (.andR (.ifThen e t5) t5 (.impR e t5 (.impL e bot (.orL e ne (.orL t3 t4 (.ax e) (.ax e)) (.orL t3 t4 (.ax e) (.impL t3 e (.ax t3) (.ax e)))) .bot)) (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.andR (.ifThen e t5) t5 (.impR e t5 (.impL t3 e (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax e) .bot)) (.orR e ne (.ax e))) (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax e) .bot)) (.ax t5)))) (.ax t5))) (.andR (.ifThen e t5) t5 (.impLoc e t5 (.ax t5)) (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_box_2 : Interd (.and (.somehow ne) t5) t3 :=
  interdTab (.impR (.and (.somehow ne) t5) t3 (.andL (.somehow ne) t5 (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.impL t3 e (.orR e ne (.boxR bot (.boxL ne (.impL e bot (.impL t3 e (.orL t3 t4 (.orL e ne (.boxL bot .bot) (.andL (.somehow ne) t5 (.ax t3))) (.andL (.somehow ne) t5 (.orR e ne (.boxLoc bot (.ax ne))))) (.boxL bot .bot)) .bot)))) (.orR e ne (.ax e))))))
    (.impR t3 (.and (.somehow ne) t5) (.orL e ne (.andR (.somehow ne) t5 (.boxR ne (.boxL bot .bot)) (.orR t3 t4 (.ax t3))) (.impL e bot (.andR (.somehow ne) t5 (.boxR ne (.impL e bot (.orL e ne (.boxL bot .bot) (.boxLoc bot (.ax ne))) .bot)) (.orR t3 t4 (.ax t3))) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_2_0 : Interd (.and ne bot) bot :=
  interdTab (.impR (.and ne bot) bot (.andL ne bot (.impL e bot .bot .bot)))
    (.impR bot (.and ne bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D5_or_2_0 : Interd (.or ne bot) ne :=
  interdTab (.impR (.or ne bot) ne (.orL ne bot (.impL e bot (.ax ne) .bot) .bot))
    (.impR ne (.or ne bot) (.impL e bot (.orR ne bot (.ax ne)) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_2_0 : Interd (.and (.ifThen ne bot) t5) t4 :=
  interdTab (.impR (.and (.ifThen ne bot) t5) t4 (.andL (.ifThen ne bot) t5 (.impL ne bot (.orL t3 t4 (.orL e ne (.impLoc e bot (.impLoc t3 e (.ax e))) (.impL e bot (.ax ne) .bot)) (.impL t3 e (.orR e ne (.ax t4)) (.impLoc e bot (.ax t4)))) .bot)))
    (.impR t4 (.and (.ifThen ne bot) t5) (.impL t3 e (.orR e ne (.andR (.ifThen ne bot) t5 (.impR ne bot (.impL t3 e (.impL e bot (.orR e ne (.ax ne)) .bot) (.impL e bot (.ax e) .bot))) (.orR t3 t4 (.ax t4)))) (.andR (.ifThen ne bot) t5 (.impR ne bot (.impL e bot (.ax e) .bot)) (.orR t3 t4 (.orR e ne (.ax e))))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_2_1 : Interd (.and ne e) bot :=
  interdTab (.impR (.and ne e) bot (.andL ne e (.impL e bot (.ax e) .bot)))
    (.impR bot (.and ne e) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D5_or_2_1 : Interd (.or ne e) t3 :=
  interdTab (.impR (.or ne e) t3 (.orL ne e (.impL e bot (.orR e ne (.ax ne)) .bot) (.orR e ne (.ax e))))
    (.impR t3 (.or ne e) (.orL e ne (.orR ne e (.impLoc e bot (.ax e))) (.impL e bot (.orR ne e (.ax ne)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_2_1 : Interd (.and (.ifThen ne e) t5) t4 :=
  interdTab (.impR (.and (.ifThen ne e) t5) t4 (.andL (.ifThen ne e) t5 (.impL ne e (.orL t3 t4 (.orL e ne (.impLoc e bot (.impLoc t3 e (.ax e))) (.impL e bot (.ax ne) .bot)) (.impL t3 e (.orR e ne (.ax t4)) (.impLoc e bot (.ax t4)))) (.orL t3 t4 (.orL e ne (.impLoc t3 e (.ax e)) (.impL e bot (.ax e) .bot)) (.ax t4)))))
    (.impR t4 (.and (.ifThen ne e) t5) (.impL t3 e (.orR e ne (.andR (.ifThen ne e) t5 (.impR ne e (.impL t3 e (.impL e bot (.orR e ne (.ax ne)) .bot) (.impL e bot (.ax e) .bot))) (.orR t3 t4 (.ax t4)))) (.andR (.ifThen ne e) t5 (.impR ne e (.impL e bot (.ax e) .bot)) (.orR t3 t4 (.orR e ne (.ax e))))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_2_2 : Interd (.and ne ne) ne :=
  interdTab (.impR (.and ne ne) ne (.andL ne ne (.impL e bot (.ax ne) .bot)))
    (.impR ne (.and ne ne) (.impL e bot (.andR ne ne (.ax ne) (.ax ne)) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D5_or_2_2 : Interd (.or ne ne) ne :=
  interdTab (.impR (.or ne ne) ne (.orL ne ne (.impL e bot (.ax ne) .bot) (.impL e bot (.ax ne) .bot)))
    (.impR ne (.or ne ne) (.impL e bot (.orR ne ne (.ax ne)) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_2_2 : Interd (.and (.ifThen ne ne) t5) t5 :=
  interdTab (.impR (.and (.ifThen ne ne) t5) t5 (.andL (.ifThen ne ne) t5 (.impL ne ne (.orL t3 t4 (.orL e ne (.impLoc e bot (.ax t5)) (.impL e bot (.ax ne) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.impLoc e bot (.ax t5)))) (.impL e bot (.orL t3 t4 (.orL e ne (.ax e) (.ax t5)) (.impL t3 e (.orR e ne (.ax ne)) (.ax e))) .bot))))
    (.impR t5 (.and (.ifThen ne ne) t5) (.orL t3 t4 (.orL e ne (.andR (.ifThen ne ne) t5 (.impR ne ne (.orL e ne (.orL t3 t4 (.impL e bot (.ax e) .bot) (.impL e bot (.ax e) .bot)) (.impL e bot (.orL t3 t4 (.ax e) (.ax e)) .bot))) (.ax t5)) (.impL e bot (.andR (.ifThen ne ne) t5 (.impLoc ne ne (.ax ne)) (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.andR (.ifThen ne ne) t5 (.impR ne ne (.impL t3 e (.orL t3 t4 (.orL e ne (.impL e bot (.ax e) .bot) (.impL e bot (.ax t3) .bot)) (.impL e bot (.orR e ne (.ax ne)) .bot)) (.orL t3 t4 (.orL e ne (.impL e bot (.ax e) .bot) (.impL e bot (.ax e) .bot)) (.impL e bot (.ax e) .bot)))) (.ax t5))) (.andR (.ifThen ne ne) t5 (.impR ne ne (.orL t3 t4 (.orL e ne (.impL e bot (.ax e) .bot) (.impL e bot (.ax e) .bot)) (.impL e bot (.ax e) .bot))) (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_2_3 : Interd (.and ne t3) ne :=
  interdTab (.impR (.and ne t3) ne (.andL ne t3 (.impL e bot (.orL e ne (.ax e) (.ax ne)) .bot)))
    (.impR ne (.and ne t3) (.impL e bot (.andR ne t3 (.ax ne) (.orR e ne (.ax ne))) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D5_or_2_3 : Interd (.or ne t3) t3 :=
  interdTab (.impR (.or ne t3) t3 (.orL ne t3 (.impL e bot (.orR e ne (.ax ne)) .bot) (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot))))
    (.impR t3 (.or ne t3) (.orL e ne (.orR ne t3 (.impLoc e bot (.ax t3))) (.impL e bot (.orR ne t3 (.ax ne)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_2_3 : Interd (.and (.ifThen ne t3) t5) t5 :=
  interdTab (.impR (.and (.ifThen ne t3) t5) t5 (.andL (.ifThen ne t3) t5 (.impL ne t3 (.orL t3 t4 (.orL e ne (.impLoc e bot (.ax t5)) (.impL e bot (.ax ne) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.impLoc e bot (.ax t5)))) (.orL e ne (.orL t3 t4 (.ax t5) (.ax t5)) (.impL e bot (.orL t3 t4 (.ax t5) (.impL t3 e (.ax t3) (.ax e))) .bot)))))
    (.impR t5 (.and (.ifThen ne t3) t5) (.orL t3 t4 (.orL e ne (.andR (.ifThen ne t3) t5 (.impR ne t3 (.orL e ne (.orL t3 t4 (.impL e bot (.ax e) .bot) (.impL e bot (.ax e) .bot)) (.impL e bot (.orL t3 t4 (.ax e) (.ax e)) .bot))) (.ax t5)) (.impL e bot (.andR (.ifThen ne t3) t5 (.impLoc ne t3 (.ax t3)) (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.andR (.ifThen ne t3) t5 (.impR ne t3 (.impL t3 e (.orL t3 t4 (.orL e ne (.impL e bot (.ax e) .bot) (.impL e bot (.ax t3) .bot)) (.impL e bot (.orR e ne (.ax ne)) .bot)) (.orL t3 t4 (.orL e ne (.impL e bot (.ax e) .bot) (.impL e bot (.ax e) .bot)) (.impL e bot (.ax e) .bot)))) (.ax t5))) (.andR (.ifThen ne t3) t5 (.impR ne t3 (.orL t3 t4 (.orL e ne (.impL e bot (.ax e) .bot) (.impL e bot (.ax e) .bot)) (.impL e bot (.ax e) .bot))) (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_2_4 : Interd (.and ne t4) bot :=
  interdTab (.impR (.and ne t4) bot (.andL ne t4 (.impL e bot (.impL t3 e (.orR e ne (.ax ne)) (.ax e)) .bot)))
    (.impR bot (.and ne t4) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D5_or_2_4 : Interd (.or ne t4) t5 :=
  interdTab (.impR (.or ne t4) t5 (.orL ne t4 (.impL e bot (.orR t3 t4 (.orR e ne (.ax ne))) .bot) (.impL t3 e (.orR e ne (.orR t3 t4 (.ax t4))) (.orR t3 t4 (.orR e ne (.ax e))))))
    (.impR t5 (.or ne t4) (.orL t3 t4 (.orL e ne (.orR ne t4 (.impLoc e bot (.impLoc t3 e (.ax e)))) (.impL e bot (.orR ne t4 (.ax ne)) .bot)) (.impL t3 e (.orR e ne (.orR ne t4 (.ax t4))) (.orR ne t4 (.impLoc e bot (.ax t4))))))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_2_4 : Interd (.and (.ifThen ne t4) t5) t4 :=
  interdTab (.impR (.and (.ifThen ne t4) t5) t4 (.andL (.ifThen ne t4) t5 (.impL ne t4 (.orL t3 t4 (.orL e ne (.impLoc e bot (.impLoc t3 e (.ax e))) (.impL e bot (.ax ne) .bot)) (.impL t3 e (.orR e ne (.ax t4)) (.impLoc e bot (.ax t4)))) (.impL t3 e (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orR e ne (.ax t4))) (.orL t3 t4 (.orL e ne (.ax t4) (.impL e bot (.ax e) .bot)) (.ax t4))))))
    (.impR t4 (.and (.ifThen ne t4) t5) (.impL t3 e (.orR e ne (.andR (.ifThen ne t4) t5 (.impR ne t4 (.impL t3 e (.impL e bot (.orR e ne (.ax ne)) .bot) (.impL e bot (.ax e) .bot))) (.orR t3 t4 (.ax t4)))) (.andR (.ifThen ne t4) t5 (.impR ne t4 (.impL e bot (.ax e) .bot)) (.orR t3 t4 (.orR e ne (.ax e))))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_2_5 : Interd (.and ne t5) ne :=
  interdTab (.impR (.and ne t5) ne (.andL ne t5 (.impL e bot (.orL t3 t4 (.orL e ne (.ax e) (.ax ne)) (.impL t3 e (.orR e ne (.ax ne)) (.ax e))) .bot)))
    (.impR ne (.and ne t5) (.impL e bot (.andR ne t5 (.ax ne) (.orR t3 t4 (.orR e ne (.ax ne)))) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D5_or_2_5 : Interd (.or ne t5) t5 :=
  interdTab (.impR (.or ne t5) t5 (.orL ne t5 (.impL e bot (.orR t3 t4 (.orR e ne (.ax ne))) .bot) (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5)))))
    (.impR t5 (.or ne t5) (.orL t3 t4 (.orL e ne (.orR ne t5 (.impLoc e bot (.ax t5))) (.impL e bot (.orR ne t5 (.ax ne)) .bot)) (.impL t3 e (.orR e ne (.orR ne t5 (.ax t5))) (.orR ne t5 (.impLoc e bot (.ax t5))))))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_2_5 : Interd (.and (.ifThen ne t5) t5) t5 :=
  interdTab (.impR (.and (.ifThen ne t5) t5) t5 (.andL (.ifThen ne t5) t5 (.impL ne t5 (.orL t3 t4 (.orL e ne (.impLoc e bot (.ax t5)) (.impL e bot (.ax ne) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.impLoc e bot (.ax t5)))) (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))))))
    (.impR t5 (.and (.ifThen ne t5) t5) (.orL t3 t4 (.orL e ne (.andR (.ifThen ne t5) t5 (.impR ne t5 (.orL e ne (.orL t3 t4 (.impL e bot (.ax e) .bot) (.impL e bot (.ax e) .bot)) (.impL e bot (.orL t3 t4 (.ax e) (.ax e)) .bot))) (.ax t5)) (.impL e bot (.andR (.ifThen ne t5) t5 (.impLoc ne t5 (.ax t5)) (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.andR (.ifThen ne t5) t5 (.impR ne t5 (.impL t3 e (.orL t3 t4 (.orL e ne (.impL e bot (.ax e) .bot) (.impL e bot (.ax t3) .bot)) (.impL e bot (.orR e ne (.ax ne)) .bot)) (.orL t3 t4 (.orL e ne (.impL e bot (.ax e) .bot) (.impL e bot (.ax e) .bot)) (.impL e bot (.ax e) .bot)))) (.ax t5))) (.andR (.ifThen ne t5) t5 (.impR ne t5 (.orL t3 t4 (.orL e ne (.impL e bot (.ax e) .bot) (.impL e bot (.ax e) .bot)) (.impL e bot (.ax e) .bot))) (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_box_3 : Interd (.and (.somehow t3) t5) t3 :=
  interdTab (.impR (.and (.somehow t3) t5) t3 (.andL (.somehow t3) t5 (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.impL t3 e (.orR e ne (.boxR bot (.boxL t3 (.orL e ne (.boxL bot .bot) (.impL e bot (.impL t3 e (.orL t3 t4 (.andL (.somehow t3) t5 (.ax t3)) (.andL (.somehow t3) t5 (.ax t3))) (.boxL bot .bot)) .bot))))) (.orR e ne (.ax e))))))
    (.impR t3 (.and (.somehow t3) t5) (.orL e ne (.andR (.somehow t3) t5 (.boxR t3 (.boxL bot .bot)) (.orR t3 t4 (.ax t3))) (.impL e bot (.andR (.somehow t3) t5 (.boxR t3 (.impL e bot (.orL e ne (.boxL bot .bot) (.boxLoc bot (.ax t3))) .bot)) (.orR t3 t4 (.ax t3))) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_3_0 : Interd (.and t3 bot) bot :=
  interdTab (.impR (.and t3 bot) bot (.andL t3 bot (.orL e ne .bot (.impL e bot .bot .bot))))
    (.impR bot (.and t3 bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D5_or_3_0 : Interd (.or t3 bot) t3 :=
  interdTab (.impR (.or t3 bot) t3 (.orL t3 bot (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) .bot))
    (.impR t3 (.or t3 bot) (.orL e ne (.orR t3 bot (.ax t3)) (.impL e bot (.orR t3 bot (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_3_0 : Interd (.and (.ifThen t3 bot) t5) bot :=
  interdTab (.impR (.and (.ifThen t3 bot) t5) bot (.andL (.ifThen t3 bot) t5 (.impL t3 bot (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.impL t3 e (.orR e ne (.boxR bot (.impL t3 bot (.impL t3 e (.orL t3 t4 (.orL e ne (.boxL bot .bot) (.impL e bot (.andL (.ifThen t3 bot) t5 (.boxLoc bot (.ax t3))) .bot)) (.andL (.ifThen t3 bot) t5 (.orR e ne (.boxLoc bot (.impR e bot (.impL t3 bot (.impL t3 e (.orL t3 t4 (.orL e ne (.andL (.ifThen t3 bot) t5 (.ax t3)) (.impL e bot (.andL (.ifThen t3 bot) t5 (.ax e)) .bot)) (.andL (.ifThen t3 bot) t5 (.orR e ne (.ax e)))) (.orL t3 t4 (.orL e ne (.andL (.ifThen t3 bot) t5 (.ax t3)) (.impL e bot (.andL (.ifThen t3 bot) t5 (.ax e)) .bot)) (.andL (.ifThen t3 bot) t5 (.orR e ne (.ax e))))) .bot)))))) (.boxL bot .bot)) .bot))) (.orR e ne (.ax e)))) .bot)))
    (.impR bot (.and (.ifThen t3 bot) t5) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D5_and_3_1 : Interd (.and t3 e) e :=
  interdTab (.impR (.and t3 e) e (.andL t3 e (.orL e ne (.ax e) (.impL e bot (.ax e) .bot))))
    (.impR e (.and t3 e) (.andR t3 e (.orR e ne (.ax e)) (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D5_or_3_1 : Interd (.or t3 e) t3 :=
  interdTab (.impR (.or t3 e) t3 (.orL t3 e (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orR e ne (.ax e))))
    (.impR t3 (.or t3 e) (.orL e ne (.orR t3 e (.ax t3)) (.impL e bot (.orR t3 e (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_3_1 : Interd (.and t4 t5) t4 :=
  interdTab (.impR (.and t4 t5) t4 (.andL t4 t5 (.impL t3 e (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orR e ne (.ax t4))) (.orL t3 t4 (.orL e ne (.ax t4) (.impL e bot (.ax e) .bot)) (.ax t4)))))
    (.impR t4 (.and t4 t5) (.impL t3 e (.orR e ne (.andR t4 t5 (.ax t4) (.orR t3 t4 (.ax t4)))) (.andR t4 t5 (.ax t4) (.orR t3 t4 (.orR e ne (.ax e))))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_3_2 : Interd (.and t3 ne) ne :=
  interdTab (.impR (.and t3 ne) ne (.andL t3 ne (.orL e ne (.impL e bot (.ax e) .bot) (.impL e bot (.ax ne) .bot))))
    (.impR ne (.and t3 ne) (.impL e bot (.andR t3 ne (.orR e ne (.ax ne)) (.ax ne)) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D5_or_3_2 : Interd (.or t3 ne) t3 :=
  interdTab (.impR (.or t3 ne) t3 (.orL t3 ne (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.impL e bot (.orR e ne (.ax ne)) .bot)))
    (.impR t3 (.or t3 ne) (.orL e ne (.orR t3 ne (.ax t3)) (.impL e bot (.orR t3 ne (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_3_2 : Interd (.and (.ifThen t3 ne) t5) ne :=
  interdTab (.impR (.and (.ifThen t3 ne) t5) ne (.andL (.ifThen t3 ne) t5 (.impL t3 ne (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.impL t3 e (.orR e ne (.boxR bot (.impL t3 ne (.impL t3 e (.orL t3 t4 (.orL e ne (.boxL bot .bot) (.impL e bot (.andL (.ifThen t3 ne) t5 (.boxLoc bot (.ax t3))) .bot)) (.andL (.ifThen t3 ne) t5 (.orR e ne (.boxLoc bot (.impR e bot (.impL t3 ne (.impL t3 e (.orL t3 t4 (.orL e ne (.andL (.ifThen t3 ne) t5 (.ax t3)) (.impL e bot (.andL (.ifThen t3 ne) t5 (.ax e)) .bot)) (.andL (.ifThen t3 ne) t5 (.orR e ne (.ax e)))) (.orL t3 t4 (.orL e ne (.andL (.ifThen t3 ne) t5 (.ax t3)) (.impL e bot (.andL (.ifThen t3 ne) t5 (.ax e)) .bot)) (.andL (.ifThen t3 ne) t5 (.orR e ne (.ax e))))) (.impL e bot (.impL t3 e (.orL t3 t4 (.orL e ne (.andL (.ifThen t3 ne) t5 (.ax t3)) (.andL (.ifThen t3 ne) t5 (.ax t3))) (.andL (.ifThen t3 ne) t5 (.orR e ne (.ax e)))) (.orL t3 t4 (.orL e ne (.andL (.ifThen t3 ne) t5 (.ax e)) (.andL (.ifThen t3 ne) t5 (.ax e))) (.andL (.ifThen t3 ne) t5 (.ax e)))) .bot))))))) (.boxL bot .bot)) (.impL e bot (.impL t3 e (.orL t3 t4 (.orL e ne (.boxL bot .bot) (.andL (.ifThen t3 ne) t5 (.ax t3))) (.andL (.ifThen t3 ne) t5 (.orR e ne (.boxLoc bot (.ax ne))))) (.boxL bot .bot)) .bot)))) (.orR e ne (.ax e)))) (.impL e bot (.orL t3 t4 (.orL e ne (.ax e) (.ax ne)) (.impL t3 e (.orR e ne (.ax ne)) (.ax e))) .bot))))
    (.impR ne (.and (.ifThen t3 ne) t5) (.impL e bot (.andR (.ifThen t3 ne) t5 (.impR t3 ne (.impL e bot (.orL e ne (.ax e) (.ax ne)) .bot)) (.orR t3 t4 (.orR e ne (.ax ne)))) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_3_3 : Interd (.and t3 t3) t3 :=
  interdTab (.impR (.and t3 t3) t3 (.andL t3 t3 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot))))
    (.impR t3 (.and t3 t3) (.orL e ne (.andR t3 t3 (.ax t3) (.ax t3)) (.impL e bot (.andR t3 t3 (.ax t3) (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D5_or_3_3 : Interd (.or t3 t3) t3 :=
  interdTab (.impR (.or t3 t3) t3 (.orL t3 t3 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot))))
    (.impR t3 (.or t3 t3) (.orL e ne (.orR t3 t3 (.ax t3)) (.impL e bot (.orR t3 t3 (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_3_3 : Interd (.and (.ifThen t3 t3) t5) t5 :=
  interdTab (.impR (.and (.ifThen t3 t3) t5) t5 (.andL (.ifThen t3 t3) t5 (.impL t3 t3 (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.orR e ne (.ax e)))) (.orL e ne (.orL t3 t4 (.ax t5) (.ax t5)) (.impL e bot (.orL t3 t4 (.ax t5) (.impL t3 e (.ax t3) (.ax e))) .bot)))))
    (.impR t5 (.and (.ifThen t3 t3) t5) (.orL t3 t4 (.orL e ne (.andR (.ifThen t3 t3) t5 (.impLoc t3 t3 (.ax t3)) (.ax t5)) (.impL e bot (.andR (.ifThen t3 t3) t5 (.impLoc t3 t3 (.ax t3)) (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.andR (.ifThen t3 t3) t5 (.impR t3 t3 (.impL t3 e (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot))) (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax e) .bot)) (.orL e ne (.ax t3) (.impL e bot (.ax e) .bot))))) (.ax t5))) (.andR (.ifThen t3 t3) t5 (.impR t3 t3 (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax e) .bot)) (.orL e ne (.ax t3) (.impL e bot (.ax e) .bot)))) (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_3_4 : Interd (.and t3 t4) e :=
  interdTab (.impR (.and t3 t4) e (.andL t3 t4 (.orL e ne (.ax e) (.impL e bot (.impL t3 e (.ax t3) (.ax e)) .bot))))
    (.impR e (.and t3 t4) (.andR t3 t4 (.orR e ne (.ax e)) (.impR t3 e (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_or_3_4 : Interd (.or t3 t4) t5 :=
  interdTab (.impR t5 t5 (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))))
    (.impR t5 t5 (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_3_4 : Interd (.and (.ifThen t3 t4) t5) t4 :=
  interdTab (.impR (.and (.ifThen t3 t4) t5) t4 (.andL (.ifThen t3 t4) t5 (.impL t3 t4 (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.impL t3 e (.orR e ne (.ax t4)) (.orR e ne (.ax e)))) (.impL t3 e (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orR e ne (.ax t4))) (.orL t3 t4 (.orL e ne (.ax t4) (.impL e bot (.ax e) .bot)) (.ax t4))))))
    (.impR t4 (.and (.ifThen t3 t4) t5) (.impL t3 e (.orR e ne (.andR (.ifThen t3 t4) t5 (.impR t3 t4 (.impL t3 e (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orL e ne (.ax t4) (.impL e bot (.ax e) .bot)))) (.orR t3 t4 (.ax t4)))) (.andR (.ifThen t3 t4) t5 (.impR t3 t4 (.orL e ne (.ax t4) (.impL e bot (.ax e) .bot))) (.orR t3 t4 (.orR e ne (.ax e))))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_3_5 : Interd (.and t3 t5) t3 :=
  interdTab (.impR (.and t3 t5) t3 (.andL t3 t5 (.orL e ne (.orL t3 t4 (.ax t3) (.ax t3)) (.impL e bot (.orL t3 t4 (.ax t3) (.impL t3 e (.ax t3) (.ax e))) .bot))))
    (.impR t3 (.and t3 t5) (.orL e ne (.andR t3 t5 (.ax t3) (.orR t3 t4 (.ax t3))) (.impL e bot (.andR t3 t5 (.ax t3) (.orR t3 t4 (.ax t3))) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D5_or_3_5 : Interd (.or t3 t5) t5 :=
  interdTab (.impR (.or t3 t5) t5 (.orL t3 t5 (.orL e ne (.orR t3 t4 (.ax t3)) (.impL e bot (.orR t3 t4 (.ax t3)) .bot)) (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5)))))
    (.impR t5 (.or t3 t5) (.orL t3 t4 (.orL e ne (.orR t3 t5 (.ax t3)) (.impL e bot (.orR t3 t5 (.ax t3)) .bot)) (.impL t3 e (.orR e ne (.orR t3 t5 (.ax t5))) (.orR t3 t5 (.orR e ne (.ax e))))))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_3_5 : Interd (.and (.ifThen t3 t5) t5) t5 :=
  interdTab (.impR (.and (.ifThen t3 t5) t5) t5 (.andL (.ifThen t3 t5) t5 (.impL t3 t5 (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.orR e ne (.ax e)))) (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))))))
    (.impR t5 (.and (.ifThen t3 t5) t5) (.orL t3 t4 (.orL e ne (.andR (.ifThen t3 t5) t5 (.impLoc t3 t5 (.ax t5)) (.ax t5)) (.impL e bot (.andR (.ifThen t3 t5) t5 (.impLoc t3 t5 (.ax t5)) (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.andR (.ifThen t3 t5) t5 (.impR t3 t5 (.impL t3 e (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot))) (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax e) .bot)) (.orL e ne (.ax t5) (.impL e bot (.ax e) .bot))))) (.ax t5))) (.andR (.ifThen t3 t5) t5 (.impR t3 t5 (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax e) .bot)) (.orL e ne (.ax t5) (.impL e bot (.ax e) .bot)))) (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_box_4 : Interd (.and (.somehow t4) t5) t4 :=
  interdTab (.impR (.and (.somehow t4) t5) t4 (.andL (.somehow t4) t5 (.orL t3 t4 (.orL e ne (.impLoc t3 e (.ax e)) (.impL e bot (.impLoc t3 e (.boxR bot (.impL e bot (.orL e ne (.boxL bot .bot) (.boxL t4 (.impL t3 e (.orL t3 t4 (.andL (.somehow t4) t5 (.ax t3)) (.andL (.somehow t4) t5 (.ax t3))) (.boxL bot .bot)))) .bot))) .bot)) (.impL t3 e (.orR e ne (.ax t4)) (.ax t4)))))
    (.impR t4 (.and (.somehow t4) t5) (.impL t3 e (.orR e ne (.andR (.somehow t4) t5 (.boxR t4 (.impL t3 e (.orR e ne (.boxLoc bot (.ax t4))) (.boxL bot .bot))) (.orR t3 t4 (.ax t4)))) (.andR (.somehow t4) t5 (.boxR t4 (.boxL bot .bot)) (.orR t3 t4 (.orR e ne (.ax e))))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_4_0 : Interd (.and t4 bot) bot :=
  interdTab (.impR (.and t4 bot) bot (.andL t4 bot (.impL t3 e .bot .bot)))
    (.impR bot (.and t4 bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D5_or_4_0 : Interd (.or t4 bot) t4 :=
  interdTab (.impR (.or t4 bot) t4 (.orL t4 bot (.impL t3 e (.orR e ne (.ax t4)) (.ax t4)) .bot))
    (.impR t4 (.or t4 bot) (.impL t3 e (.orR e ne (.orR t4 bot (.ax t4))) (.orR t4 bot (.ax t4))))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_4_0 : Interd (.and (.ifThen t4 bot) t5) ne :=
  interdTab (.impR (.and (.ifThen t4 bot) t5) ne (.andL (.ifThen t4 bot) t5 (.impL t4 bot (.orL t3 t4 (.orL e ne (.impLoc t3 e (.ax e)) (.impL e bot (.impLoc t3 e (.ax ne)) .bot)) (.impL t3 e (.orR e ne (.ax t4)) (.ax t4))) .bot)))
    (.impR ne (.and (.ifThen t4 bot) t5) (.impL e bot (.andR (.ifThen t4 bot) t5 (.impR t4 bot (.impL e bot (.impL t3 e (.orR e ne (.ax ne)) (.ax e)) .bot)) (.orR t3 t4 (.orR e ne (.ax ne)))) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_4_1 : Interd (.and t4 e) e :=
  interdTab (.impR (.and t4 e) e (.andL t4 e (.impL t3 e (.orR e ne (.ax e)) (.ax e))))
    (.impR e (.and t4 e) (.andR t4 e (.impR t3 e (.orL e ne (.ax e) (.impL e bot (.ax e) .bot))) (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D5_or_4_1 : Interd (.or t4 e) t4 :=
  interdTab (.impR (.or t4 e) t4 (.orL t4 e (.impL t3 e (.orR e ne (.ax t4)) (.ax t4)) (.impR t3 e (.orL t4 e (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)) (.orL e ne (.ax e) (.impL e bot (.ax e) .bot))))))
    (.impR t4 (.or t4 e) (.impL t3 e (.orR e ne (.orR t4 e (.ax t4))) (.orR t4 e (.ax t4))))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_4_1 : Interd (.and (.ifThen t4 e) t5) t3 :=
  interdTab (.impR (.and (.ifThen t4 e) t5) t3 (.andL (.ifThen t4 e) t5 (.impL t4 e (.orL t3 t4 (.orL e ne (.impLoc t3 e (.ax e)) (.impL e bot (.impLoc t3 e (.ax t3)) .bot)) (.impL t3 e (.orR e ne (.ax t4)) (.ax t4))) (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax e) .bot)) (.orR e ne (.ax e))))))
    (.impR t3 (.and (.ifThen t4 e) t5) (.orL e ne (.andR (.ifThen t4 e) t5 (.impR t4 e (.orL e ne (.ax e) (.impL e bot (.ax e) .bot))) (.orR t3 t4 (.ax t3))) (.impL e bot (.andR (.ifThen t4 e) t5 (.impR t4 e (.impL e bot (.orL e ne (.ax e) (.impL t3 e (.ax t3) (.ax e))) .bot)) (.orR t3 t4 (.ax t3))) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_4_2 : Interd (.and t4 ne) bot :=
  interdTab (.impR (.and t4 ne) bot (.andL t4 ne (.impL t3 e (.impL e bot (.orR e ne (.ax ne)) .bot) (.impL e bot (.ax e) .bot))))
    (.impR bot (.and t4 ne) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D5_or_4_2 : Interd (.or t4 ne) t5 :=
  interdTab (.impR (.or t4 ne) t5 (.orL t4 ne (.impL t3 e (.orR e ne (.orR t3 t4 (.ax t4))) (.orR t3 t4 (.orR e ne (.ax e)))) (.impL e bot (.orR t3 t4 (.orR e ne (.ax ne))) .bot)))
    (.impR t5 (.or t4 ne) (.orL t3 t4 (.orL e ne (.orR t4 ne (.impLoc t3 e (.ax e))) (.impL e bot (.orR t4 ne (.impLoc t3 e (.ax ne))) .bot)) (.impL t3 e (.orR e ne (.orR t4 ne (.ax t4))) (.orR t4 ne (.ax t4)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_4_2 : Interd (.and (.ifThen t4 ne) t5) ne :=
  interdTab (.impR (.and (.ifThen t4 ne) t5) ne (.andL (.ifThen t4 ne) t5 (.impL t4 ne (.orL t3 t4 (.orL e ne (.impLoc t3 e (.ax e)) (.impL e bot (.impLoc t3 e (.ax ne)) .bot)) (.impL t3 e (.orR e ne (.ax t4)) (.ax t4))) (.impL e bot (.orL t3 t4 (.orL e ne (.ax e) (.ax ne)) (.impL t3 e (.orR e ne (.ax ne)) (.ax e))) .bot))))
    (.impR ne (.and (.ifThen t4 ne) t5) (.impL e bot (.andR (.ifThen t4 ne) t5 (.impR t4 ne (.impL e bot (.impL t3 e (.orR e ne (.ax ne)) (.ax e)) .bot)) (.orR t3 t4 (.orR e ne (.ax ne)))) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_4_3 : Interd (.and t4 t3) e :=
  interdTab (.impR (.and t4 t3) e (.andL t4 t3 (.impL t3 e (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)))))
    (.impR e (.and t4 t3) (.andR t4 t3 (.impR t3 e (.orL e ne (.ax e) (.impL e bot (.ax e) .bot))) (.orR e ne (.ax e))))
    (by decide +kernel) (by decide +kernel)

theorem D5_or_4_3 : Interd (.or t4 t3) t5 :=
  interdTab (.impR (.or t4 t3) t5 (.orL t4 t3 (.impL t3 e (.orR e ne (.orR t3 t4 (.ax t4))) (.orR t3 t4 (.orR e ne (.ax e)))) (.orL e ne (.orR t3 t4 (.ax t3)) (.impL e bot (.orR t3 t4 (.ax t3)) .bot))))
    (.impR t5 (.or t4 t3) (.orL t3 t4 (.orL e ne (.orR t4 t3 (.impLoc t3 e (.ax e))) (.impL e bot (.orR t4 t3 (.impLoc t3 e (.ax t3))) .bot)) (.impL t3 e (.orR e ne (.orR t4 t3 (.ax t4))) (.orR t4 t3 (.ax t4)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_4_3 : Interd (.and (.ifThen t4 t3) t5) t3 :=
  interdTab (.impR (.and (.ifThen t4 t3) t5) t3 (.andL (.ifThen t4 t3) t5 (.impL t4 t3 (.orL t3 t4 (.orL e ne (.impLoc t3 e (.ax e)) (.impL e bot (.impLoc t3 e (.ax t3)) .bot)) (.impL t3 e (.orR e ne (.ax t4)) (.ax t4))) (.orL e ne (.orL t3 t4 (.ax t3) (.ax t3)) (.impL e bot (.orL t3 t4 (.ax t3) (.impL t3 e (.ax t3) (.ax e))) .bot)))))
    (.impR t3 (.and (.ifThen t4 t3) t5) (.orL e ne (.andR (.ifThen t4 t3) t5 (.impR t4 t3 (.orL e ne (.ax t3) (.impL e bot (.ax e) .bot))) (.orR t3 t4 (.ax t3))) (.impL e bot (.andR (.ifThen t4 t3) t5 (.impR t4 t3 (.impL e bot (.orL e ne (.ax e) (.impL t3 e (.ax t3) (.ax e))) .bot)) (.orR t3 t4 (.ax t3))) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_4_4 : Interd (.and t4 t4) t4 :=
  interdTab (.impR (.and t4 t4) t4 (.andL t4 t4 (.impL t3 e (.orR e ne (.ax t4)) (.ax t4))))
    (.impR t4 (.and t4 t4) (.impL t3 e (.orR e ne (.andR t4 t4 (.ax t4) (.ax t4))) (.andR t4 t4 (.ax t4) (.ax t4))))
    (by decide +kernel) (by decide +kernel)

theorem D5_or_4_4 : Interd (.or t4 t4) t4 :=
  interdTab (.impR (.or t4 t4) t4 (.orL t4 t4 (.impL t3 e (.orR e ne (.ax t4)) (.ax t4)) (.impL t3 e (.orR e ne (.ax t4)) (.ax t4))))
    (.impR t4 (.or t4 t4) (.impL t3 e (.orR e ne (.orR t4 t4 (.ax t4))) (.orR t4 t4 (.ax t4))))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_4_4 : Interd (.and (.ifThen t4 t4) t5) t5 :=
  interdTab (.impR (.and (.ifThen t4 t4) t5) t5 (.andL (.ifThen t4 t4) t5 (.impL t4 t4 (.orL t3 t4 (.orL e ne (.impLoc t3 e (.ax e)) (.impL e bot (.impLoc t3 e (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.ax t4)) (.ax t4))) (.impL t3 e (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orR e ne (.ax t5))) (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax e) .bot)) (.ax t5))))))
    (.impR t5 (.and (.ifThen t4 t4) t5) (.orL t3 t4 (.orL e ne (.andR (.ifThen t4 t4) t5 (.impR t4 t4 (.orL e ne (.orL t3 t4 (.ax t4) (.ax t4)) (.impL e bot (.orL t3 t4 (.ax e) (.ax e)) .bot))) (.ax t5)) (.impL e bot (.andR (.ifThen t4 t4) t5 (.impR t4 t4 (.impL e bot (.orL e ne (.orL t3 t4 (.ax e) (.ax e)) (.orL t3 t4 (.impL t3 e (.ax t3) (.ax e)) (.impL t3 e (.ax t3) (.ax e)))) .bot)) (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.andR (.ifThen t4 t4) t5 (.impLoc t4 t4 (.ax t4)) (.ax t5))) (.andR (.ifThen t4 t4) t5 (.impLoc t4 t4 (.ax t4)) (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_4_5 : Interd (.and t4 t5) t4 :=
  interdTab (.impR (.and t4 t5) t4 (.andL t4 t5 (.impL t3 e (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orR e ne (.ax t4))) (.orL t3 t4 (.orL e ne (.ax t4) (.impL e bot (.ax e) .bot)) (.ax t4)))))
    (.impR t4 (.and t4 t5) (.impL t3 e (.orR e ne (.andR t4 t5 (.ax t4) (.orR t3 t4 (.ax t4)))) (.andR t4 t5 (.ax t4) (.orR t3 t4 (.orR e ne (.ax e))))))
    (by decide +kernel) (by decide +kernel)

theorem D5_or_4_5 : Interd (.or t4 t5) t5 :=
  interdTab (.impR (.or t4 t5) t5 (.orL t4 t5 (.impL t3 e (.orR e ne (.orR t3 t4 (.ax t4))) (.orR t3 t4 (.orR e ne (.ax e)))) (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5)))))
    (.impR t5 (.or t4 t5) (.orL t3 t4 (.orL e ne (.orR t4 t5 (.impLoc t3 e (.ax e))) (.impL e bot (.orR t4 t5 (.impLoc t3 e (.ax t5))) .bot)) (.impL t3 e (.orR e ne (.orR t4 t5 (.ax t4))) (.orR t4 t5 (.ax t4)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_4_5 : Interd (.and (.ifThen t4 t5) t5) t5 :=
  interdTab (.impR (.and (.ifThen t4 t5) t5) t5 (.andL (.ifThen t4 t5) t5 (.impL t4 t5 (.orL t3 t4 (.orL e ne (.impLoc t3 e (.ax e)) (.impL e bot (.impLoc t3 e (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.ax t4)) (.ax t4))) (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))))))
    (.impR t5 (.and (.ifThen t4 t5) t5) (.orL t3 t4 (.orL e ne (.andR (.ifThen t4 t5) t5 (.impR t4 t5 (.orL e ne (.orL t3 t4 (.ax t5) (.ax t5)) (.impL e bot (.orL t3 t4 (.ax e) (.ax e)) .bot))) (.ax t5)) (.impL e bot (.andR (.ifThen t4 t5) t5 (.impR t4 t5 (.impL e bot (.orL e ne (.orL t3 t4 (.ax e) (.ax e)) (.orL t3 t4 (.impL t3 e (.ax t3) (.ax e)) (.impL t3 e (.ax t3) (.ax e)))) .bot)) (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.andR (.ifThen t4 t5) t5 (.impLoc t4 t5 (.ax t5)) (.ax t5))) (.andR (.ifThen t4 t5) t5 (.impLoc t4 t5 (.ax t5)) (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_box_5 : Interd (.and (.somehow t5) t5) t5 :=
  interdTab (.impR (.and (.somehow t5) t5) t5 (.andL (.somehow t5) t5 (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5)))))
    (.impR t5 (.and (.somehow t5) t5) (.orL t3 t4 (.orL e ne (.andR (.somehow t5) t5 (.boxR t5 (.boxL bot .bot)) (.ax t5)) (.impL e bot (.andR (.somehow t5) t5 (.boxR t5 (.impL e bot (.orL e ne (.boxL bot .bot) (.orL t3 t4 (.boxLoc bot (.ax t5)) (.impL t3 e (.ax t3) (.boxL bot .bot)))) .bot)) (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.andR (.somehow t5) t5 (.boxR t5 (.impL t3 e (.orL t3 t4 (.orL e ne (.boxL bot .bot) (.impL e bot (.boxLoc bot (.ax t3)) .bot)) (.orR e ne (.boxLoc bot (.ax t5)))) (.boxL bot .bot))) (.ax t5))) (.andR (.somehow t5) t5 (.boxR t5 (.boxL bot .bot)) (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_5_0 : Interd (.and t5 bot) bot :=
  interdTab (.impR (.and t5 bot) bot (.andL t5 bot (.orL t3 t4 (.orL e ne .bot (.impL e bot .bot .bot)) (.impL t3 e .bot .bot))))
    (.impR bot (.and t5 bot) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D5_or_5_0 : Interd (.or t5 bot) t5 :=
  interdTab (.impR (.or t5 bot) t5 (.orL t5 bot (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))) .bot))
    (.impR t5 (.or t5 bot) (.orL t3 t4 (.orL e ne (.orR t5 bot (.ax t5)) (.impL e bot (.orR t5 bot (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.orR t5 bot (.ax t5))) (.orR t5 bot (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_5_0 : Interd (.and (.ifThen t5 bot) t5) bot :=
  interdTab (.impR (.and (.ifThen t5 bot) t5) bot (.andL (.ifThen t5 bot) t5 (.impL t5 bot (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))) .bot)))
    (.impR bot (.and (.ifThen t5 bot) t5) .bot)
    (by decide +kernel) (by decide +kernel)

theorem D5_and_5_1 : Interd (.and t5 e) e :=
  interdTab (.impR (.and t5 e) e (.andL t5 e (.orL t3 t4 (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)) (.impL t3 e (.orR e ne (.ax e)) (.ax e)))))
    (.impR e (.and t5 e) (.andR t5 e (.orR t3 t4 (.orR e ne (.ax e))) (.ax e)))
    (by decide +kernel) (by decide +kernel)

theorem D5_or_5_1 : Interd (.or t5 e) t5 :=
  interdTab (.impR (.or t5 e) t5 (.orL t5 e (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))) (.orR t3 t4 (.orR e ne (.ax e)))))
    (.impR t5 (.or t5 e) (.orL t3 t4 (.orL e ne (.orR t5 e (.ax t5)) (.impL e bot (.orR t5 e (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.orR t5 e (.ax t5))) (.orR t5 e (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_5_1 : Interd (.and (.ifThen t5 e) t5) e :=
  interdTab (.impR (.and (.ifThen t5 e) t5) e (.andL (.ifThen t5 e) t5 (.impL t5 e (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))) (.orL t3 t4 (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)) (.ax e)))))
    (.impR e (.and (.ifThen t5 e) t5) (.andR (.ifThen t5 e) t5 (.impR t5 e (.orL t3 t4 (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)) (.ax e))) (.orR t3 t4 (.orR e ne (.ax e)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_5_2 : Interd (.and t5 ne) ne :=
  interdTab (.impR (.and t5 ne) ne (.andL t5 ne (.orL t3 t4 (.orL e ne (.impL e bot (.ax e) .bot) (.impL e bot (.ax ne) .bot)) (.impL t3 e (.impL e bot (.orR e ne (.ax ne)) .bot) (.impL e bot (.ax e) .bot)))))
    (.impR ne (.and t5 ne) (.impL e bot (.andR t5 ne (.orR t3 t4 (.orR e ne (.ax ne))) (.ax ne)) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D5_or_5_2 : Interd (.or t5 ne) t5 :=
  interdTab (.impR (.or t5 ne) t5 (.orL t5 ne (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))) (.impL e bot (.orR t3 t4 (.orR e ne (.ax ne))) .bot)))
    (.impR t5 (.or t5 ne) (.orL t3 t4 (.orL e ne (.orR t5 ne (.ax t5)) (.impL e bot (.orR t5 ne (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.orR t5 ne (.ax t5))) (.orR t5 ne (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_5_2 : Interd (.and (.ifThen t5 ne) t5) ne :=
  interdTab (.impR (.and (.ifThen t5 ne) t5) ne (.andL (.ifThen t5 ne) t5 (.impL t5 ne (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))) (.impL e bot (.orL t3 t4 (.orL e ne (.ax e) (.ax ne)) (.impL t3 e (.orR e ne (.ax ne)) (.ax e))) .bot))))
    (.impR ne (.and (.ifThen t5 ne) t5) (.impL e bot (.andR (.ifThen t5 ne) t5 (.impR t5 ne (.impL e bot (.orL t3 t4 (.orL e ne (.ax e) (.ax ne)) (.impL t3 e (.orR e ne (.ax ne)) (.ax e))) .bot)) (.orR t3 t4 (.orR e ne (.ax ne)))) .bot))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_5_3 : Interd (.and t5 t3) t3 :=
  interdTab (.impR (.and t5 t3) t3 (.andL t5 t3 (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.impL t3 e (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orL e ne (.ax t3) (.impL e bot (.ax e) .bot))))))
    (.impR t3 (.and t5 t3) (.orL e ne (.andR t5 t3 (.orR t3 t4 (.ax t3)) (.ax t3)) (.impL e bot (.andR t5 t3 (.orR t3 t4 (.ax t3)) (.ax t3)) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D5_or_5_3 : Interd (.or t5 t3) t5 :=
  interdTab (.impR (.or t5 t3) t5 (.orL t5 t3 (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))) (.orL e ne (.orR t3 t4 (.ax t3)) (.impL e bot (.orR t3 t4 (.ax t3)) .bot))))
    (.impR t5 (.or t5 t3) (.orL t3 t4 (.orL e ne (.orR t5 t3 (.ax t5)) (.impL e bot (.orR t5 t3 (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.orR t5 t3 (.ax t5))) (.orR t5 t3 (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_5_3 : Interd (.and (.ifThen t5 t3) t5) t3 :=
  interdTab (.impR (.and (.ifThen t5 t3) t5) t3 (.andL (.ifThen t5 t3) t5 (.impL t5 t3 (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))) (.orL e ne (.orL t3 t4 (.ax t3) (.ax t3)) (.impL e bot (.orL t3 t4 (.ax t3) (.impL t3 e (.ax t3) (.ax e))) .bot)))))
    (.impR t3 (.and (.ifThen t5 t3) t5) (.orL e ne (.andR (.ifThen t5 t3) t5 (.impR t5 t3 (.orL e ne (.orL t3 t4 (.ax t3) (.ax t3)) (.impL e bot (.orL t3 t4 (.ax e) (.ax e)) .bot))) (.orR t3 t4 (.ax t3))) (.impL e bot (.andR (.ifThen t5 t3) t5 (.impR t5 t3 (.impL e bot (.orL e ne (.orL t3 t4 (.ax e) (.ax e)) (.orL t3 t4 (.ax t3) (.impL t3 e (.ax t3) (.ax e)))) .bot)) (.orR t3 t4 (.ax t3))) .bot)))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_5_4 : Interd (.and t5 t4) t4 :=
  interdTab (.impR (.and t5 t4) t4 (.andL t5 t4 (.orL t3 t4 (.orL e ne (.ax t4) (.impL e bot (.impL t3 e (.ax t3) (.ax e)) .bot)) (.impL t3 e (.orR e ne (.ax t4)) (.ax t4)))))
    (.impR t4 (.and t5 t4) (.impL t3 e (.orR e ne (.andR t5 t4 (.orR t3 t4 (.ax t4)) (.ax t4))) (.andR t5 t4 (.orR t3 t4 (.orR e ne (.ax e))) (.ax t4))))
    (by decide +kernel) (by decide +kernel)

theorem D5_or_5_4 : Interd (.or t5 t4) t5 :=
  interdTab (.impR (.or t5 t4) t5 (.orL t5 t4 (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))) (.impL t3 e (.orR e ne (.orR t3 t4 (.ax t4))) (.orR t3 t4 (.orR e ne (.ax e))))))
    (.impR t5 (.or t5 t4) (.orL t3 t4 (.orL e ne (.orR t5 t4 (.ax t5)) (.impL e bot (.orR t5 t4 (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.orR t5 t4 (.ax t5))) (.orR t5 t4 (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_5_4 : Interd (.and (.ifThen t5 t4) t5) t4 :=
  interdTab (.impR (.and (.ifThen t5 t4) t5) t4 (.andL (.ifThen t5 t4) t5 (.impL t5 t4 (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))) (.impL t3 e (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orR e ne (.ax t4))) (.orL t3 t4 (.orL e ne (.ax t4) (.impL e bot (.ax e) .bot)) (.ax t4))))))
    (.impR t4 (.and (.ifThen t5 t4) t5) (.impL t3 e (.orR e ne (.andR (.ifThen t5 t4) t5 (.impR t5 t4 (.impL t3 e (.orL t3 t4 (.orL e ne (.ax t3) (.impL e bot (.ax t3) .bot)) (.orR e ne (.ax t4))) (.orL t3 t4 (.orL e ne (.ax t4) (.impL e bot (.ax e) .bot)) (.ax t4)))) (.orR t3 t4 (.ax t4)))) (.andR (.ifThen t5 t4) t5 (.impR t5 t4 (.orL t3 t4 (.orL e ne (.ax t4) (.impL e bot (.ax e) .bot)) (.ax t4))) (.orR t3 t4 (.orR e ne (.ax e))))))
    (by decide +kernel) (by decide +kernel)

theorem D5_and_5_5 : Interd (.and t5 t5) t5 :=
  interdTab (.impR (.and t5 t5) t5 (.andL t5 t5 (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5)))))
    (.impR t5 (.and t5 t5) (.orL t3 t4 (.orL e ne (.andR t5 t5 (.ax t5) (.ax t5)) (.impL e bot (.andR t5 t5 (.ax t5) (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.andR t5 t5 (.ax t5) (.ax t5))) (.andR t5 t5 (.ax t5) (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_or_5_5 : Interd (.or t5 t5) t5 :=
  interdTab (.impR (.or t5 t5) t5 (.orL t5 t5 (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))) (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5)))))
    (.impR t5 (.or t5 t5) (.orL t3 t4 (.orL e ne (.orR t5 t5 (.ax t5)) (.impL e bot (.orR t5 t5 (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.orR t5 t5 (.ax t5))) (.orR t5 t5 (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

theorem D5_imp_5_5 : Interd (.and (.ifThen t5 t5) t5) t5 :=
  interdTab (.impR (.and (.ifThen t5 t5) t5) t5 (.andL (.ifThen t5 t5) t5 (.impL t5 t5 (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))) (.orL t3 t4 (.orL e ne (.ax t5) (.impL e bot (.ax t5) .bot)) (.impL t3 e (.orR e ne (.ax t5)) (.ax t5))))))
    (.impR t5 (.and (.ifThen t5 t5) t5) (.orL t3 t4 (.orL e ne (.andR (.ifThen t5 t5) t5 (.impLoc t5 t5 (.ax t5)) (.ax t5)) (.impL e bot (.andR (.ifThen t5 t5) t5 (.impLoc t5 t5 (.ax t5)) (.ax t5)) .bot)) (.impL t3 e (.orR e ne (.andR (.ifThen t5 t5) t5 (.impLoc t5 t5 (.ax t5)) (.ax t5))) (.andR (.ifThen t5 t5) t5 (.impLoc t5 t5 (.ax t5)) (.ax t5)))))
    (by decide +kernel) (by decide +kernel)

/-- The closure table of `D5`. -/
theorem D5_table : DownTable t5 D5_list where
  bot_mem := D5_mem_0
  top_mem := D5_mem_5
  below := allL_mem (.cons D5_below_0
      (.cons D5_below_1
      (.cons D5_below_2
      (.cons D5_below_3
      (.cons D5_below_4
      (.cons D5_below_5
      .nil))))))
  and_cl := allL_mem
    (.cons (allL_mem (.cons ⟨bot, D5_mem_0, D5_and_0_0⟩ (.cons ⟨bot, D5_mem_0, D5_and_0_1⟩ (.cons ⟨bot, D5_mem_0, D5_and_0_2⟩ (.cons ⟨bot, D5_mem_0, D5_and_0_3⟩ (.cons ⟨bot, D5_mem_0, D5_and_0_4⟩ (.cons ⟨bot, D5_mem_0, D5_and_0_5⟩ .nil)))))))
      (.cons (allL_mem (.cons ⟨bot, D5_mem_0, D5_and_1_0⟩ (.cons ⟨e, D5_mem_1, D5_and_1_1⟩ (.cons ⟨bot, D5_mem_0, D5_and_1_2⟩ (.cons ⟨e, D5_mem_1, D5_and_1_3⟩ (.cons ⟨e, D5_mem_1, D5_and_1_4⟩ (.cons ⟨e, D5_mem_1, D5_and_1_5⟩ .nil)))))))
      (.cons (allL_mem (.cons ⟨bot, D5_mem_0, D5_and_2_0⟩ (.cons ⟨bot, D5_mem_0, D5_and_2_1⟩ (.cons ⟨ne, D5_mem_2, D5_and_2_2⟩ (.cons ⟨ne, D5_mem_2, D5_and_2_3⟩ (.cons ⟨bot, D5_mem_0, D5_and_2_4⟩ (.cons ⟨ne, D5_mem_2, D5_and_2_5⟩ .nil)))))))
      (.cons (allL_mem (.cons ⟨bot, D5_mem_0, D5_and_3_0⟩ (.cons ⟨e, D5_mem_1, D5_and_3_1⟩ (.cons ⟨ne, D5_mem_2, D5_and_3_2⟩ (.cons ⟨t3, D5_mem_3, D5_and_3_3⟩ (.cons ⟨e, D5_mem_1, D5_and_3_4⟩ (.cons ⟨t3, D5_mem_3, D5_and_3_5⟩ .nil)))))))
      (.cons (allL_mem (.cons ⟨bot, D5_mem_0, D5_and_4_0⟩ (.cons ⟨e, D5_mem_1, D5_and_4_1⟩ (.cons ⟨bot, D5_mem_0, D5_and_4_2⟩ (.cons ⟨e, D5_mem_1, D5_and_4_3⟩ (.cons ⟨t4, D5_mem_4, D5_and_4_4⟩ (.cons ⟨t4, D5_mem_4, D5_and_4_5⟩ .nil)))))))
      (.cons (allL_mem (.cons ⟨bot, D5_mem_0, D5_and_5_0⟩ (.cons ⟨e, D5_mem_1, D5_and_5_1⟩ (.cons ⟨ne, D5_mem_2, D5_and_5_2⟩ (.cons ⟨t3, D5_mem_3, D5_and_5_3⟩ (.cons ⟨t4, D5_mem_4, D5_and_5_4⟩ (.cons ⟨t5, D5_mem_5, D5_and_5_5⟩ .nil)))))))
      .nil))))))
  or_cl := allL_mem
    (.cons (allL_mem (.cons ⟨bot, D5_mem_0, D5_or_0_0⟩ (.cons ⟨e, D5_mem_1, D5_or_0_1⟩ (.cons ⟨ne, D5_mem_2, D5_or_0_2⟩ (.cons ⟨t3, D5_mem_3, D5_or_0_3⟩ (.cons ⟨t4, D5_mem_4, D5_or_0_4⟩ (.cons ⟨t5, D5_mem_5, D5_or_0_5⟩ .nil)))))))
      (.cons (allL_mem (.cons ⟨e, D5_mem_1, D5_or_1_0⟩ (.cons ⟨e, D5_mem_1, D5_or_1_1⟩ (.cons ⟨t3, D5_mem_3, D5_or_1_2⟩ (.cons ⟨t3, D5_mem_3, D5_or_1_3⟩ (.cons ⟨t4, D5_mem_4, D5_or_1_4⟩ (.cons ⟨t5, D5_mem_5, D5_or_1_5⟩ .nil)))))))
      (.cons (allL_mem (.cons ⟨ne, D5_mem_2, D5_or_2_0⟩ (.cons ⟨t3, D5_mem_3, D5_or_2_1⟩ (.cons ⟨ne, D5_mem_2, D5_or_2_2⟩ (.cons ⟨t3, D5_mem_3, D5_or_2_3⟩ (.cons ⟨t5, D5_mem_5, D5_or_2_4⟩ (.cons ⟨t5, D5_mem_5, D5_or_2_5⟩ .nil)))))))
      (.cons (allL_mem (.cons ⟨t3, D5_mem_3, D5_or_3_0⟩ (.cons ⟨t3, D5_mem_3, D5_or_3_1⟩ (.cons ⟨t3, D5_mem_3, D5_or_3_2⟩ (.cons ⟨t3, D5_mem_3, D5_or_3_3⟩ (.cons ⟨t5, D5_mem_5, D5_or_3_4⟩ (.cons ⟨t5, D5_mem_5, D5_or_3_5⟩ .nil)))))))
      (.cons (allL_mem (.cons ⟨t4, D5_mem_4, D5_or_4_0⟩ (.cons ⟨t4, D5_mem_4, D5_or_4_1⟩ (.cons ⟨t5, D5_mem_5, D5_or_4_2⟩ (.cons ⟨t5, D5_mem_5, D5_or_4_3⟩ (.cons ⟨t4, D5_mem_4, D5_or_4_4⟩ (.cons ⟨t5, D5_mem_5, D5_or_4_5⟩ .nil)))))))
      (.cons (allL_mem (.cons ⟨t5, D5_mem_5, D5_or_5_0⟩ (.cons ⟨t5, D5_mem_5, D5_or_5_1⟩ (.cons ⟨t5, D5_mem_5, D5_or_5_2⟩ (.cons ⟨t5, D5_mem_5, D5_or_5_3⟩ (.cons ⟨t5, D5_mem_5, D5_or_5_4⟩ (.cons ⟨t5, D5_mem_5, D5_or_5_5⟩ .nil)))))))
      .nil))))))
  box_cl := allL_mem
    (.cons ⟨e, D5_mem_1, D5_box_0⟩
      (.cons ⟨e, D5_mem_1, D5_box_1⟩
      (.cons ⟨t3, D5_mem_3, D5_box_2⟩
      (.cons ⟨t3, D5_mem_3, D5_box_3⟩
      (.cons ⟨t4, D5_mem_4, D5_box_4⟩
      (.cons ⟨t5, D5_mem_5, D5_box_5⟩
      .nil))))))
  imp_cl := allL_mem
    (.cons (allL_mem (.cons ⟨t5, D5_mem_5, D5_imp_0_0⟩ (.cons ⟨t5, D5_mem_5, D5_imp_0_1⟩ (.cons ⟨t5, D5_mem_5, D5_imp_0_2⟩ (.cons ⟨t5, D5_mem_5, D5_imp_0_3⟩ (.cons ⟨t5, D5_mem_5, D5_imp_0_4⟩ (.cons ⟨t5, D5_mem_5, D5_imp_0_5⟩ .nil)))))))
      (.cons (allL_mem (.cons ⟨ne, D5_mem_2, D5_imp_1_0⟩ (.cons ⟨t5, D5_mem_5, D5_imp_1_1⟩ (.cons ⟨ne, D5_mem_2, D5_imp_1_2⟩ (.cons ⟨t5, D5_mem_5, D5_imp_1_3⟩ (.cons ⟨t5, D5_mem_5, D5_imp_1_4⟩ (.cons ⟨t5, D5_mem_5, D5_imp_1_5⟩ .nil)))))))
      (.cons (allL_mem (.cons ⟨t4, D5_mem_4, D5_imp_2_0⟩ (.cons ⟨t4, D5_mem_4, D5_imp_2_1⟩ (.cons ⟨t5, D5_mem_5, D5_imp_2_2⟩ (.cons ⟨t5, D5_mem_5, D5_imp_2_3⟩ (.cons ⟨t4, D5_mem_4, D5_imp_2_4⟩ (.cons ⟨t5, D5_mem_5, D5_imp_2_5⟩ .nil)))))))
      (.cons (allL_mem (.cons ⟨bot, D5_mem_0, D5_imp_3_0⟩ (.cons ⟨t4, D5_mem_4, D5_imp_3_1⟩ (.cons ⟨ne, D5_mem_2, D5_imp_3_2⟩ (.cons ⟨t5, D5_mem_5, D5_imp_3_3⟩ (.cons ⟨t4, D5_mem_4, D5_imp_3_4⟩ (.cons ⟨t5, D5_mem_5, D5_imp_3_5⟩ .nil)))))))
      (.cons (allL_mem (.cons ⟨ne, D5_mem_2, D5_imp_4_0⟩ (.cons ⟨t3, D5_mem_3, D5_imp_4_1⟩ (.cons ⟨ne, D5_mem_2, D5_imp_4_2⟩ (.cons ⟨t3, D5_mem_3, D5_imp_4_3⟩ (.cons ⟨t5, D5_mem_5, D5_imp_4_4⟩ (.cons ⟨t5, D5_mem_5, D5_imp_4_5⟩ .nil)))))))
      (.cons (allL_mem (.cons ⟨bot, D5_mem_0, D5_imp_5_0⟩ (.cons ⟨e, D5_mem_1, D5_imp_5_1⟩ (.cons ⟨ne, D5_mem_2, D5_imp_5_2⟩ (.cons ⟨t3, D5_mem_3, D5_imp_5_3⟩ (.cons ⟨t4, D5_mem_4, D5_imp_5_4⟩ (.cons ⟨t5, D5_mem_5, D5_imp_5_5⟩ .nil)))))))
      .nil))))))


/-! ### The pen facts behind the tables, checked

`◯¬◯⊥ ∧ t5 ⊣⊢ t3` is the cell `D5_box_2`, and `◯t4 ∧ t5 ⊣⊢ t4` is `D5_box_4`.
The other three, as cells of the same kind: -/

/-- `◯¬◯⊥ ∧ t4 ⊣⊢ t1`. -/
theorem pen_box_ne_t4 : Interd (.and (.somehow ne) t4) e :=
  interdTab (.impR (.and (.somehow ne) t4) e (.andL (.somehow ne) t4 (.impL t3 e (.orR e ne (.boxR bot (.boxL ne (.impL e bot (.impL t3 e (.andL (.somehow ne) t4 (.orR e ne (.boxLoc bot (.ax ne)))) (.boxL bot .bot)) .bot)))) (.ax e))))
    (.impR e (.and (.somehow ne) t4) (.andR (.somehow ne) t4 (.boxR ne (.boxL bot .bot)) (.impR t3 e (.orL e ne (.ax e) (.impL e bot (.ax e) .bot)))))
    (by decide +kernel) (by decide +kernel)

/-- `¬¬◯⊥ ⊣⊢ ¬◯⊥ ↠ ◯⊥`. -/
theorem pen_nn_eq : Interd (.ifThen ne .falsePLL) (.ifThen ne e) :=
  interdTab (.impR (.ifThen ne bot) (.ifThen ne e) (.impL ne bot (.impR ne e (.impL ne bot (.impL e bot (.ax ne) .bot) .bot)) .bot))
    (.impR (.ifThen ne e) (.ifThen ne bot) (.impL ne e (.impR ne bot (.impL ne e (.impL e bot (.ax ne) .bot) (.impL e bot (.ax e) .bot))) (.impR ne bot (.impL e bot (.ax e) .bot))))
    (by decide +kernel) (by decide +kernel)

/-- `¬¬◯⊥` is ◯-closed: `◯¬¬◯⊥ ⊢ ¬¬◯⊥`. -/
theorem pen_nn_closed : Deriv [.somehow (.ifThen ne .falsePLL)] (.ifThen ne .falsePLL) :=
  derivTab (.impR (.somehow (.ifThen ne bot)) (.ifThen ne bot) (.impR ne bot (.impL e bot (.boxR bot (.impL e bot (.boxL (.ifThen ne bot) (.impL ne bot (.ax ne) .bot)) .bot)) .bot)))
    (by decide +kernel)

/-! ## A2. Distinctness: one four-world countermodel

`M3`: worlds `0, 1, 2` of the Rieger–Nishimura ladder (`2` sees `0`; `0`
and `1` see only themselves) and a fallible top `3` above all three, with
`0 Rₘ 3`.  So `◯⊥` holds exactly at `0` (and `3`), and the truth sets on
`{0, 1, 2}` are

    ⊥ : ∅    t1 : {0}    t2 : {1}    t3 : {0,1}    t4 : {0,2}    t5 : {0,1,2}.
-/

/-- The countermodel. -/
def M3 : FinCM := ⟨4, [(2, 0), (0, 3), (1, 3), (2, 3)], [(0, 3)], [3], []⟩

/-- A checked refutation at world `w` of `M3`. -/
theorem nd (w : Nat) {x y : PLLFormula} (h : FinCM.checkB M3 w [x] y = true) : [x] ⊬ y :=
  FinCM.not_provable_of_check h

theorem nd_e_bot : [e] ⊬ bot := nd 0 (by decide)
theorem nd_ne_bot : [ne] ⊬ bot := nd 1 (by decide)
theorem nd_t3_bot : [t3] ⊬ bot := nd 0 (by decide)
theorem nd_t4_bot : [t4] ⊬ bot := nd 0 (by decide)
theorem nd_t5_bot : [t5] ⊬ bot := nd 0 (by decide)
theorem nd_e_ne : [e] ⊬ ne := nd 0 (by decide)
theorem nd_ne_e : [ne] ⊬ e := nd 1 (by decide)
theorem nd_ne_t4 : [ne] ⊬ t4 := nd 1 (by decide)
theorem nd_t3_e : [t3] ⊬ e := nd 1 (by decide)
theorem nd_t3_ne : [t3] ⊬ ne := nd 0 (by decide)
theorem nd_t3_t4 : [t3] ⊬ t4 := nd 1 (by decide)
theorem nd_t4_e : [t4] ⊬ e := nd 2 (by decide)
theorem nd_t4_ne : [t4] ⊬ ne := nd 0 (by decide)
theorem nd_t4_t3 : [t4] ⊬ t3 := nd 2 (by decide)
theorem nd_t5_e : [t5] ⊬ e := nd 1 (by decide)
theorem nd_t5_ne : [t5] ⊬ ne := nd 0 (by decide)
theorem nd_t5_t3 : [t5] ⊬ t3 := nd 2 (by decide)
theorem nd_t5_t4 : [t5] ⊬ t4 := nd 1 (by decide)

theorem ni_l {x y : PLLFormula} (h : [x] ⊬ y) : ¬ Interd x y := fun i => h i.1
theorem ni_r {x y : PLLFormula} (h : [y] ⊬ x) : ¬ Interd x y := fun i => h i.2

/-- The members of `↓t1` are pairwise distinct. -/
theorem D1_distinct : D1_list.Pairwise (fun x y => ¬ Interd x y) :=
  .cons (allL_mem (.cons (ni_r nd_e_bot) .nil)) (.cons (allL_mem .nil) .nil)

/-- The members of `↓t2` are pairwise distinct. -/
theorem D2_distinct : D2_list.Pairwise (fun x y => ¬ Interd x y) :=
  .cons (allL_mem (.cons (ni_r nd_ne_bot) .nil)) (.cons (allL_mem .nil) .nil)

/-- The members of `↓t3` are pairwise distinct. -/
theorem D3_distinct : D3_list.Pairwise (fun x y => ¬ Interd x y) :=
  .cons (allL_mem (.cons (ni_r nd_e_bot) (.cons (ni_r nd_ne_bot) (.cons (ni_r nd_t3_bot) .nil))))
  (.cons (allL_mem (.cons (ni_l nd_e_ne) (.cons (ni_r nd_t3_e) .nil)))
  (.cons (allL_mem (.cons (ni_r nd_t3_ne) .nil))
  (.cons (allL_mem .nil) .nil)))

/-- The members of `↓t4` are pairwise distinct. -/
theorem D4_distinct : D4_list.Pairwise (fun x y => ¬ Interd x y) :=
  .cons (allL_mem (.cons (ni_r nd_e_bot) (.cons (ni_r nd_t4_bot) .nil)))
  (.cons (allL_mem (.cons (ni_r nd_t4_e) .nil))
  (.cons (allL_mem .nil) .nil))

/-- The members of `↓t5` are pairwise distinct. -/
theorem D5_distinct : D5_list.Pairwise (fun x y => ¬ Interd x y) :=
  .cons (allL_mem (.cons (ni_r nd_e_bot) (.cons (ni_r nd_ne_bot) (.cons (ni_r nd_t3_bot)
    (.cons (ni_r nd_t4_bot) (.cons (ni_r nd_t5_bot) .nil))))))
  (.cons (allL_mem (.cons (ni_l nd_e_ne) (.cons (ni_r nd_t3_e) (.cons (ni_r nd_t4_e)
    (.cons (ni_r nd_t5_e) .nil)))))
  (.cons (allL_mem (.cons (ni_r nd_t3_ne) (.cons (ni_l nd_ne_t4) (.cons (ni_r nd_t5_ne) .nil))))
  (.cons (allL_mem (.cons (ni_l nd_t3_t4) (.cons (ni_r nd_t5_t3) .nil)))
  (.cons (allL_mem (.cons (ni_r nd_t5_t4) .nil))
  (.cons (allL_mem .nil) .nil)))))

/-! ## A3. The covers -/

/-- **Cover in F0**: `u ⊢ v`, `v ⊬ u`, and every variable-free `x` between
them is `⊣⊢ u` or `⊣⊢ v`. -/
def Covers (u v : PLLFormula) : Prop :=
  Deriv [u] v ∧ ([v] ⊬ u) ∧
    ∀ x : PLLFormula, atomFree x = true → Deriv [u] x → Deriv [x] v →
      Interd x u ∨ Interd x v

/-- A cover from a table for the downset of `v`: every member is `u`, `v`,
or not above `u`. -/
theorem covers_of_table {u v : PLLFormula} {L : List PLLFormula} (T : DownTable v L)
    (hu : u ∈ L) (hvu : [v] ⊬ u)
    (hcase : AllL (fun l => Interd l u ∨ Interd l v ∨ ([u] ⊬ l)) L) : Covers u v := by
  refine ⟨T.below u hu, hvu, fun x hx hux hxv => ?_⟩
  obtain ⟨l, hl, i⟩ := T.classify_below hx hxv
  rcases allL_mem hcase l hl with h | h | h
  · exact Or.inl (i.trans h)
  · exact Or.inr (i.trans h)
  · exact absurd (Deriv.cutHead hux i.1) h

/-- **`t0 ⋖ t1`**: `⊥ ⋖ ◯⊥`. -/
theorem cover_0_1 : Covers (rnSub 0) (rnSub 1) := by
  rw [rnSub_0, rnSub_1]
  exact covers_of_table D1_table D1_mem_0 nd_e_bot
    (.cons (.inl (Interd.refl _)) (.cons (.inr (.inl (Interd.refl _))) .nil))

/-- **`t0 ⋖ t2`**: `⊥ ⋖ ¬◯⊥`. -/
theorem cover_0_2 : Covers (rnSub 0) (rnSub 2) := by
  rw [rnSub_0, rnSub_2]
  exact covers_of_table D2_table D2_mem_0 nd_ne_bot
    (.cons (.inl (Interd.refl _)) (.cons (.inr (.inl (Interd.refl _))) .nil))

/-- **`t1 ⋖ t3`**. -/
theorem cover_1_3 : Covers (rnSub 1) (rnSub 3) := by
  rw [rnSub_1, rnSub_3]
  exact covers_of_table D3_table D3_mem_1 nd_t3_e
    (.cons (.inr (.inr nd_e_bot)) (.cons (.inl (Interd.refl _))
      (.cons (.inr (.inr nd_e_ne)) (.cons (.inr (.inl (Interd.refl _))) .nil))))

/-- **`t2 ⋖ t3`**. -/
theorem cover_2_3 : Covers (rnSub 2) (rnSub 3) := by
  rw [rnSub_2, rnSub_3]
  exact covers_of_table D3_table D3_mem_2 nd_t3_ne
    (.cons (.inr (.inr nd_ne_bot)) (.cons (.inr (.inr nd_ne_e))
      (.cons (.inl (Interd.refl _)) (.cons (.inr (.inl (Interd.refl _))) .nil))))

/-- **`t1 ⋖ t4`**. -/
theorem cover_1_4 : Covers (rnSub 1) (rnSub 4) := by
  rw [rnSub_1, rnSub_4]
  exact covers_of_table D4_table D4_mem_1 nd_t4_e
    (.cons (.inr (.inr nd_e_bot)) (.cons (.inl (Interd.refl _))
      (.cons (.inr (.inl (Interd.refl _))) .nil)))

/-- **`t3 ⋖ t5`**. -/
theorem cover_3_5 : Covers (rnSub 3) (rnSub 5) := by
  rw [rnSub_3, rnSub_5]
  exact covers_of_table D5_table D5_mem_3 nd_t5_t3
    (.cons (.inr (.inr nd_t3_bot)) (.cons (.inr (.inr nd_t3_e)) (.cons (.inr (.inr nd_t3_ne))
      (.cons (.inl (Interd.refl _)) (.cons (.inr (.inr nd_t3_t4))
        (.cons (.inr (.inl (Interd.refl _))) .nil))))))

/-- **`t4 ⋖ t5`**. -/
theorem cover_4_5 : Covers (rnSub 4) (rnSub 5) := by
  rw [rnSub_4, rnSub_5]
  exact covers_of_table D5_table D5_mem_4 nd_t5_t4
    (.cons (.inr (.inr nd_t4_bot)) (.cons (.inr (.inr nd_t4_e)) (.cons (.inr (.inr nd_t4_ne))
      (.cons (.inr (.inr nd_t4_t3)) (.cons (.inl (Interd.refl _))
        (.cons (.inr (.inl (Interd.refl _))) .nil))))))

/-- **Below `¬◯⊥` there is only `⊥`; everything else is above `◯⊥`.**  For
every variable-free `x`:  `◯⊥ ⊢ x`, or `x ⊣⊢ ⊥`, or `x ⊣⊢ ¬◯⊥`.
(`dichotomy`, then the table `↓t2`.) -/
theorem low_trichotomy (x : PLLFormula) (hx : atomFree x = true) :
    Deriv [oBot] x ∨ Interd x .falsePLL ∨ Interd x notOBot := by
  rcases dichotomy x hx with h | h
  · exact Or.inl h
  · obtain ⟨l, hl, i⟩ := D2_table.classify_below hx h
    rcases List.mem_cons.mp hl with rfl | hl
    · exact Or.inr (Or.inl i)
    · rcases List.mem_cons.mp hl with rfl | hl
      · exact Or.inr (Or.inr i)
      · simp at hl

end F0
end PLLND

/-! ## Pins

Every table pin bounds its cells too (the axiom closure of a table contains
those of the cells it uses). -/

#axioms_within PLLND.F0.red_bot [propext, Quot.sound]
#axioms_within PLLND.F0.red_and [propext, Quot.sound]
#axioms_within PLLND.F0.red_or [propext, Quot.sound]
#axioms_within PLLND.F0.red_imp [propext, Quot.sound]
#axioms_within PLLND.F0.red_box [propext, Quot.sound]
#axioms_within PLLND.F0.DownTable.classify [propext, Quot.sound]
#axioms_within PLLND.F0.DownTable.classify_below [propext, Quot.sound]
#axioms_within PLLND.F0.D1_table [propext, Quot.sound]
#axioms_within PLLND.F0.D2_table [propext, Quot.sound]
#axioms_within PLLND.F0.D3_table [propext, Quot.sound]
#axioms_within PLLND.F0.D4_table [propext, Quot.sound]
#axioms_within PLLND.F0.D5_table [propext, Quot.sound]
#axioms_within PLLND.F0.pen_box_ne_t4 [propext, Quot.sound]
#axioms_within PLLND.F0.pen_nn_eq [propext, Quot.sound]
#axioms_within PLLND.F0.pen_nn_closed [propext, Quot.sound]
#axioms_within PLLND.F0.D1_distinct [propext, Quot.sound]
#axioms_within PLLND.F0.D2_distinct [propext, Quot.sound]
#axioms_within PLLND.F0.D3_distinct [propext, Quot.sound]
#axioms_within PLLND.F0.D4_distinct [propext, Quot.sound]
#axioms_within PLLND.F0.D5_distinct [propext, Quot.sound]
#axioms_within PLLND.F0.cover_0_1 [propext, Quot.sound]
#axioms_within PLLND.F0.cover_0_2 [propext, Quot.sound]
#axioms_within PLLND.F0.cover_1_3 [propext, Quot.sound]
#axioms_within PLLND.F0.cover_2_3 [propext, Quot.sound]
#axioms_within PLLND.F0.cover_1_4 [propext, Quot.sound]
#axioms_within PLLND.F0.cover_3_5 [propext, Quot.sound]
#axioms_within PLLND.F0.cover_4_5 [propext, Quot.sound]
#axioms_within PLLND.F0.low_trichotomy [propext, Quot.sound]
