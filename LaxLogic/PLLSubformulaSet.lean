/-
# The `Set`-valued subformula island

`subformulasOf` and the `SomehowFree` subtype were the original
(2024) presentation; they are the ONLY things in `LaxLogic/PLLFormula.lean`
that needed `Set`, hence Mathlib, and nothing in the development uses
them — `PLLNDCore` mentions `eraseSomehow` in a comment only, and the
live subformula machinery is `FRJ.sfR` / `Search.subs` over lists.

Split out on 2026-09-03 so that `PLLFormula` — and therefore the whole
import closure of `lake exe pll` — is Mathlib-free.  Nothing here is
deleted: this is the def/proof split of `docs/decider-outputs-design.md`
applied at the one place the runtime closure needed it.
-/
import LaxLogic.PLLFormula
import Mathlib.Tactic

namespace PLLFormula

open PLLFormula

@[simp]
def subformulasOf (F: PLLFormula) : Set PLLFormula :=
    match F with
    | PLLFormula.prop str   => {PLLFormula.prop str }
    | falsePLL => {falsePLL}
    | somehow P =>   {somehow P} ∪ P.subformulasOf
    | ifThen P Q   =>  {ifThen P Q} ∪ P.subformulasOf ∪ Q.subformulasOf
    | and P Q =>  {and P Q} ∪ P.subformulasOf ∪ Q.subformulasOf
    | or P Q => {or P Q} ∪ P.subformulasOf ∪ Q.subformulasOf


@[simp] -- Predicate
def isSomehowFormula (F: PLLFormula) : Prop := ∃(P: PLLFormula), F = somehow P
-- Subtype
def SomehowFormula := {F: PLLFormula // isSomehowFormula F}

@[simp] -- If all subformulas of F are not somehow formuas then F is somehowFree
def isSomehowFree (F: PLLFormula): Prop := ∀ (P: F.subformulasOf), ¬ isSomehowFormula P

def SomehowFree := {F: PLLFormula // isSomehowFree F}

@[simp]
def eraseSomehowRaw (F: PLLFormula) : PLLFormula   :=
    match F with

    | PLLFormula.prop str   => PLLFormula.prop str
    | falsePLL => falsePLL
    | somehow P =>  P.eraseSomehowRaw
    | ifThen P Q   =>  ifThen P.eraseSomehowRaw Q.eraseSomehowRaw
    | and P Q =>  and P.eraseSomehowRaw Q.eraseSomehowRaw
    | or P Q => or P.eraseSomehowRaw Q.eraseSomehowRaw

theorem somehow_is_erased (F: PLLFormula) : ∀ (F_erased: PLLFormula ), F_erased = F.eraseSomehowRaw → ∀ (P: F_erased.subformulasOf), ¬ isSomehowFormula P := by
    simp
    intro P Q hP hEq
    subst hEq
    induction F with
    | prop str =>
        simp [eraseSomehowRaw, subformulasOf, isSomehowFree] at Q

    | falsePLL =>
        simp [eraseSomehowRaw, subformulasOf, isSomehowFree] at Q
    | and P' Q' ihP ihQ =>
        simp [eraseSomehowRaw, subformulasOf, isSomehowFree] at Q
        simp_all only [imp_false, or_self]
    | or P Q ihP ihQ =>
        simp [eraseSomehowRaw, subformulasOf, isSomehowFree] at Q
        simp_all only [imp_false, or_self]
    | ifThen P Q ihP ihQ =>
        simp [eraseSomehowRaw, subformulasOf, isSomehowFree] at Q
        simp_all only [imp_false, or_self]
    | somehow P ihP =>
        simp [eraseSomehowRaw, subformulasOf, isSomehowFree] at Q
        simp_all only [imp_false, not_true_eq_false]



-- This returns an erased PLLFormula packaged with a proof of the property that it is somehow free.
def eraseSomehow (F: PLLFormula) : SomehowFree :=
    let P := F.eraseSomehowRaw
    ⟨P, by
        simp
        have h := somehow_is_erased F P (by rfl)
        intro a b x
        simp_all only [isSomehowFormula, not_exists, Subtype.forall, not_false_eq_true, P]
    ⟩

end PLLFormula
