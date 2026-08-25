/-
# The order view: strict order and SCOPED covers

`Rel.le`/`Rel.nle` entries are the FACTS.  This module is the first
slice of the VIEW layer over them: the strict order as a `Prop`, and
cover-ness — which, the fragment being proved infinite, exists ONLY
relative to a named representative set (Matthew, 2026-08-24: "we don't
have a reliable way of determining covers anywhere"; the standing rule
is store `<`, expose covers as a scoped view).

Notation (Matthew, 2026-08-24): the strict order is plain `<`/`>`
(scoped instance); `≺/≻` is NOT used — many order-theory texts reserve
it for covering, so it invites exactly the confusion it caused.  The
covering relation is `⋖` ("is covered by") / `⋗` ("covers"), and it
appears ONLY in scoped form `a ⋖[S] b` — no element of `S` strictly
between — until emptiness of an open interval `(a, b)` is proved for
the WHOLE fragment, which the bare `Covers`/`⋖` below states and
nothing yet inhabits.

The worked example ρ6/ρ12 shows the machinery AND its coupling to the
frontier: deciding one candidate Hasse edge reduced, via the banked
entries, to two OPEN cells — which become frontier members below, not
assumptions.
-/
import RNDB.RhoEntries
import LaxLogic.PLLSearchConf
import LaxLogic.PLLNoFall

open PLLND PLLND.SemUI PLLFormula

namespace RNDB

/-- Strict order: derivable one way, refuted the other. -/
def Lt (a b : PLLFormula) : Prop := Deriv [a] b ∧ ¬ Deriv [b] a

/-- `a < b` on formulas is the derivability order, scoped to `RNDB`. -/
scoped instance : LT PLLFormula := ⟨Lt⟩

/-- Cover RELATIVE TO a named set: `a < b` and no element of `S` sits
strictly between. -/
def CoversIn (S : List PLLFormula) (a b : PLLFormula) : Prop :=
  Lt a b ∧ ∀ c ∈ S, ¬ (Lt a c ∧ Lt c b)

@[inherit_doc CoversIn] notation:50 a:51 " ⋖[" S "] " b:51 => CoversIn S a b
/-- `a ⋗[S] b` = `b ⋖[S] a` ("covers", within `S`). -/
notation:50 a:51 " ⋗[" S "] " b:51 => CoversIn S b a

/-- The ABSOLUTE cover — the open interval `(a, b)` empty over ALL
formulas.  Stated so the target of a generalisation is on record;
nothing inhabits it yet, and any scoped `⋖[S]` result is strictly
weaker.  (Quantifying over all of `PLLFormula` makes this the cover in
the full PLL derivability order; a variable-carrying interposer can
defeat it even where every closed one fails.) -/
def Covers (a b : PLLFormula) : Prop :=
  Lt a b ∧ ∀ c, ¬ (Lt a c ∧ Lt c b)

@[inherit_doc Covers] infix:50 " ⋖ " => Covers
/-- `a ⋗ b` = `b ⋖ a` ("covers", absolutely). -/
infix:50 " ⋗ " => fun a b => Covers b a

/-! ## The worked example: ρ6 < ρ12, and what its cover question needs

ρ6 = `¬◯⊥ ∨ ¬¬◯⊥`, ρ9 = `◯¬◯⊥ ∨ ¬¬◯⊥`, ρ12 = `(¬¬◯⊥ ⊃ ◯⊥) ⊃ ◯¬◯⊥`. -/

open RhoOrder RNReps

/-- `[ρ6] ⊢ ρ12`, hand-authored (`rncCertPos` style): case split on the
disjunction; the `¬◯⊥` branch closes by ◯-intro, the `¬¬◯⊥` branch
fires the hypothesis to get `◯⊥` and escapes through `laxElim`. -/
def nd_6_12 : LaxND [q7] q14 :=
  .impIntro <|
    .orElim (.iden (show q7 ∈ [q10, q7] by decide))
      (.laxIntro (.iden (show q3 ∈ q3 :: [q10, q7] by decide)))
      (.laxElim
        (.impElim (.iden (show q10 ∈ q6 :: [q10, q7] by decide))
          (.iden (show q6 ∈ q6 :: [q10, q7] by decide)))
        (.falsoElim (.somehow q3)
          (.iden (show falsePLL ∈ q0 :: q6 :: [q10, q7] by decide))))

/-- `[ρ6] ⊢ ρ9`: inject each disjunct (`¬◯⊥ ⊢ ◯¬◯⊥` is ◯-intro). -/
def nd_6_9 : LaxND [q7] q9 :=
  .orElim (.iden (show q7 ∈ [q7] by decide))
    (.orIntro1 (.laxIntro (.iden (show q3 ∈ q3 :: [q7] by decide))))
    (.orIntro2 (.iden (show q6 ∈ q6 :: [q7] by decide)))

/-- **ρ6 < ρ12** — Matthew's example, both halves kernel-checked: the
hand derivation above, and the banked 4-world countermodel entry
`nle_12_6` ("rho-0094") for strictness. -/
theorem rho6_lt_rho12 : rhoF 6 < rhoF 12 :=
  ⟨⟨nd_6_12⟩, nle_12_6.holds⟩

@[deprecated rho6_lt_rho12 (since := "2026-08-24")]
theorem rho12_gt_rho6 : rhoF 12 > rhoF 6 := rho6_lt_rho12

/-- ρ6 < ρ9, strict: the derivation above plus the banked `nle_9_6`
(one of the 48 cells the ground truth left unknown and FRJ(◯) settled). -/
theorem rho6_lt_rho9 : rhoF 6 < rhoF 9 :=
  ⟨⟨nd_6_9⟩, nle_9_6.holds⟩

/-- `[q9] ⊢ q14` (= ρ9 ⊢ ρ12): case split on `q9 = q5∨q6`; the `q6`
branch turns `q10 q6 = ◯⊥` into `◯q3` by ex falso under `◯`.
Restated from `wip/rncCertPos.lean`'s `PLLND.RNC.nd_9_14` so this
module closes wip-free; the wip original remains the discovery record. -/
def nd_9_14 : LaxND [q9] q14 :=
  .impIntro <|
    .orElim (.iden (show q9 ∈ [q10, q9] by decide))
      (.iden (show q5 ∈ q5 :: [q10, q9] by decide))
      (.laxElim
        (.impElim (.iden (show q10 ∈ q6 :: [q10, q9] by decide))
          (.iden (show q6 ∈ q6 :: [q10, q9] by decide)))
        (.laxIntro (.falsoElim q3
          (.iden (show falsePLL ∈ q0 :: q6 :: [q10, q9] by decide)))))

/-- ρ9 ≤ ρ12 (`wip/rncCertPos.lean`'s hand derivation `nd_9_14`;
ρ9 = q9, ρ12 = q14). -/
theorem rho9_le_rho12 : Deriv [rhoF 9] (rhoF 12) :=
  ⟨nd_9_14⟩

/-- **The cover question, reduced to one open cell.**  If `ρ12 ⊬ ρ9`
— currently OPEN (G4c unknown, FRJ(◯) found nothing) — then ρ9 sits
strictly between, and ρ12 does NOT cover ρ6 in the catalogue.  The
hypothesis is a `frontierOrder` member below, never an assumption
smuggled in. -/
theorem not_coversIn_of_open (h : ¬ Deriv [rhoF 12] (rhoF 9)) :
    ¬ rhoF 6 ⋖[rhoScope] rhoF 12 := fun hc =>
  hc.2 (rhoF 9) (by decide)
    ⟨rho6_lt_rho9, ⟨rho9_le_rho12, h⟩⟩

/-! ## The two cells, SETTLED — by lookup, not by search

Both cells were already refuted in the 2026-08-15 record: the DerivU
matrix (`wip/rho_order_out.txt`, rows ρ12/ρ13) separates them on the
confluent battery, kernel-escalatable; `rhoorder pin` re-emitted the
certificates 2026-08-24.  ONE 5-world mutually confluent frame
separates both cells at world 0, refuting `DerivU` — and `Deriv ⊆
DerivU` (`DerivU.of_nd`), so the PLL claims follow.  The former
`frontierOrder` members are RETIRED below. -/

/-- The separating frame: 5 worlds, `rm = {(2,3)}`, fallible world 3. -/
def sepM : FinCM :=
  ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩

/-- `ρ12 ⊬ᵤ ρ9` (PCLL): battery separation, kernel-checked. -/
theorem rho12_nleU_rho9 : ¬ ConfluentU.DerivU [rhoF 12] (rhoF 9) :=
  RNC.not_derivU_of_checkConf (M := sepM) (w := 0) (by decide) (by decide)

/-- `ρ13 ⊬ᵤ ρ6` (PCLL): the same frame, the same world. -/
theorem rho13_nleU_rho6 : ¬ ConfluentU.DerivU [rhoF 13] (rhoF 6) :=
  RNC.not_derivU_of_checkConf (M := sepM) (w := 0) (by decide) (by decide)

/-- `[ρ12] ⊬ ρ9` in PLL, since `Deriv ⊆ DerivU`. -/
theorem rho12_nle_rho9 : ¬ Deriv [rhoF 12] (rhoF 9) :=
  fun ⟨t⟩ => rho12_nleU_rho9 (ConfluentU.DerivU.of_nd t)

/-- `[ρ13] ⊬ ρ6` in PLL, since `Deriv ⊆ DerivU`. -/
theorem rho13_nle_rho6 : ¬ Deriv [rhoF 13] (rhoF 6) :=
  fun ⟨t⟩ => rho13_nleU_rho6 (ConfluentU.DerivU.of_nd t)

/-- **ρ9 interposes: ρ12 does NOT cover ρ6 in the catalogue.**  The
worked example's cover question, now unconditional. -/
theorem not_covers_rho6_rho12 : ¬ (rhoF 6 ⋖[rhoScope] rhoF 12) :=
  not_coversIn_of_open rho12_nle_rho9

/-- `[ρ6] ⊢ ρ13`, hand term: assume `¬¬◯⊥ ⊃ ◯⊥`; the `¬◯⊥` disjunct is
the right injection into `◯⊥ ∨ ¬◯⊥`, the `¬¬◯⊥` disjunct fires the
hypothesis for the left. -/
def nd_6_13 : LaxND [q7] (q10.ifThen q4) :=
  .impIntro <|
    .orElim (.iden (show q7 ∈ [q10, q7] by decide))
      (.orIntro2 (.iden (show q3 ∈ q3 :: [q10, q7] by decide)))
      (.orIntro1 (.impElim (.iden (show q10 ∈ q6 :: [q10, q7] by decide))
        (.iden (show q6 ∈ q6 :: [q10, q7] by decide))))

/-- ρ6 < ρ13, both halves kernel-checked. -/
theorem rho6_lt_rho13 : rhoF 6 < rhoF 13 :=
  ⟨⟨nd_6_13⟩, rho13_nle_rho6⟩

/-! ## Banked: the two settlements as database entries

`Engine.finCM`, not `frj`: the countermodel came from the confluent
battery, and the engine label is provenance, never a truth condition. -/

def nle_12_9 : Entry where
  id := "ord-0001"
  claim := ⟨rhoF 12, rhoF 9, Rel.nle, some rhoScope⟩
  ev := Evidence.countermodel Engine.finCM 5
  ok := ⟨Claim.wellScoped_some, rfl, by decide, rho12_nle_rho9⟩

def nle_13_6 : Entry where
  id := "ord-0002"
  claim := ⟨rhoF 13, rhoF 6, Rel.nle, some rhoScope⟩
  ev := Evidence.countermodel Engine.finCM 5
  ok := ⟨Claim.wellScoped_some, rfl, by decide, rho13_nle_rho6⟩

/-- The order module's entries, appended to `DB.allEntries`. -/
def orderEntries : List Entry := [nle_12_9, nle_13_6]

theorem orderEntries_length : orderEntries.length = 2 := rfl

/-- `[ρ20] ⊬ ρ10` was NEVER open: the FRJ(◯) 8-world countermodel is
banked as entry `rho-0167` (`RhoCerts.rho_20_nle_10`, one of the 48
cells FRJ settled beyond the 2026-08-15 ground truth).  The two-sided
record lists `ρ20 ⊢? ρ10` as a "genuine flag" — that flag is hereby
RESOLVED NEGATIVE by lookup; restated so the resolution is visible
where the order lives. -/
theorem rho20_nle_rho10 : ¬ Deriv [rhoF 20] (rhoF 10) :=
  nle_20_10.ok.holds

/-- The order view's LIVE frontier — now a SINGLE claim.  History: the
two original members (`ρ12 ⊬ ρ9?`, `ρ13 ⊬ ρ6?`) were retired
2026-08-24, settled from the 2026-08-15 battery record; the
`ρ20 ⊢? ρ10` flag briefly recorded here was then found ALREADY REFUTED
by the banked FRJ certificate above (the sweep machinery cannot see
FRJ countermodels — `rhocover` now overlays the database precisely so
this cannot recur).  What remains open in the whole 462-cell PLL
matrix is exactly `ρ12 ⊢? ρ15`; its converse (`ρ15 ⊬ ρ12`) is
battery-settled, so a positive resolution would add the strict pair
`ρ12 < ρ15` (and possibly one cover edge), and a negative one makes
`{ρ12, ρ15}` incomparable — either way no existing edge moves. -/
def frontierOrder : Frontier :=
  [ ⟨rhoF 12, rhoF 15, Rel.le, none⟩ ]

/-! ## Absolute covers in the CLOSED fragment — proofs testing cannot reach

Matthew, 2026-08-25: "I think it is perfectly possible to prove
`⊥ ⋖ ◯⊥` and `⊥ ⋖ ¬◯⊥`".  Two precisions, both settled below.

FIRST: for the all-formulas `Covers` above, `⊥ ⋖ ◯⊥` is REFUTED —
`◯⊥ ∧ p` interposes (consistent, entails `◯⊥`, and `◯⊥ ⊬ p`).  The
variable-carrying hazard is real, and kernel-checked
(`not_covers_bot_obot`).

SECOND: the right notion for RN(◯,{}) is the cover with interposers
ranging over the CLOSED (variable-free) fragment, `CoversVF`.  There
both covers are PROVED, via a lemma no finite test reaches: the
theories of `◯⊥` and of `¬◯⊥` are COMPLETE over closed formulas
(structural induction; under `◯⊥` every `◯ψ` is decided positively,
under `¬◯⊥` a decided `ψ` decides `◯ψ` since `◯ψ, ¬ψ ⊢ ◯⊥`).  A
closed interposer `c` would satisfy `[◯⊥] ⊬ c`, hence `[◯⊥] ⊢ ¬c` by
completeness, hence `c` inconsistent (it entails `◯⊥`), contradicting
`⊥ < c`. -/

/-- Cover with interposers restricted to the CLOSED fragment: the
covering relation OF RN(◯,{}) itself. -/
def CoversVF (a b : PLLFormula) : Prop :=
  Lt a b ∧ ∀ c, NoFall.VarFree c → ¬ (Lt a c ∧ Lt c b)

/-- The two smallest nontrivial classes. -/
abbrev oBot : PLLFormula := PLLFormula.somehow PLLFormula.falsePLL
abbrev nBot : PLLFormula := PLLFormula.ifThen oBot PLLFormula.falsePLL

private theorem wk1 {h c χ : PLLFormula} (d : Deriv [h] χ) : Deriv [c, h] χ :=
  d.rename (by intro x hm; simp at hm; simp [hm])

/-- Weaken a one-hypothesis derivation into any context containing it. -/
private theorem wkH {h χ : PLLFormula} (d : Deriv [h] χ)
    {Γ : List PLLFormula} (hh : h ∈ Γ) : Deriv Γ χ :=
  d.rename (by intro x hm; simp at hm; simpa [hm] using hh)

/-- `[◯⊥] ⊢ ◯ψ`, for every `ψ`. -/
theorem obot_somehow (ψ : PLLFormula) : Deriv [oBot] (PLLFormula.somehow ψ) :=
  ⟨.laxElim (.iden (show oBot ∈ [oBot] by simp))
    (.laxIntro (.falsoElim ψ
      (.iden (show PLLFormula.falsePLL ∈ [PLLFormula.falsePLL, oBot] by simp))))⟩

/-- The propositional induction shared by both deciders: any hypothesis
whose `◯`-case is supplied decides every closed formula. -/
theorem decides_of_somehow (h : PLLFormula)
    (hsom : ∀ ψ, NoFall.VarFree ψ →
      (Deriv [h] ψ ∨ Deriv [h] (ψ.ifThen .falsePLL)) →
      Deriv [h] (PLLFormula.somehow ψ) ∨
      Deriv [h] ((PLLFormula.somehow ψ).ifThen .falsePLL)) :
    ∀ φ, NoFall.VarFree φ →
      Deriv [h] φ ∨ Deriv [h] (φ.ifThen .falsePLL) := by
  intro φ
  induction φ with
  | prop a => exact fun hv => absurd hv (by simp [NoFall.VarFree])
  | falsePLL =>
      exact fun _ => .inr (Deriv.impIntro
        (Deriv.iden (show PLLFormula.falsePLL ∈ [PLLFormula.falsePLL, h] by simp)))
  | and φ ψ ihφ ihψ =>
      rintro ⟨hφ, hψ⟩
      match ihφ hφ, ihψ hψ with
      | .inl p, .inl q => exact .inl (Deriv.andIntro p q)
      | .inr np, _ =>
          exact .inr (Deriv.impIntro (Deriv.impElim (wk1 np)
            (Deriv.andElim1 (Deriv.iden (show φ.and ψ ∈ [φ.and ψ, h] by simp)))))
      | .inl _, .inr nq =>
          exact .inr (Deriv.impIntro (Deriv.impElim (wk1 nq)
            (Deriv.andElim2 (Deriv.iden (show φ.and ψ ∈ [φ.and ψ, h] by simp)))))
  | or φ ψ ihφ ihψ =>
      rintro ⟨hφ, hψ⟩
      match ihφ hφ, ihψ hψ with
      | .inl p, _ => exact .inl (Deriv.orIntro1 p)
      | .inr _, .inl q => exact .inl (Deriv.orIntro2 q)
      | .inr np, .inr nq =>
          refine .inr (Deriv.impIntro (Deriv.orElim
            (Deriv.iden (show φ.or ψ ∈ [φ.or ψ, h] by simp)) ?_ ?_))
          · exact Deriv.impElim (wkH np (by simp))
              (Deriv.iden (show φ ∈ [φ, φ.or ψ, h] by simp))
          · exact Deriv.impElim (wkH nq (by simp))
              (Deriv.iden (show ψ ∈ [ψ, φ.or ψ, h] by simp))
  | ifThen φ ψ ihφ ihψ =>
      rintro ⟨hφ, hψ⟩
      match ihφ hφ, ihψ hψ with
      | _, .inl q => exact .inl (Deriv.impIntro (wk1 q))
      | .inr np, .inr _ =>
          exact .inl (Deriv.impIntro (Deriv.falsoElim ψ
            (Deriv.impElim (wk1 np) (Deriv.iden (show φ ∈ [φ, h] by simp)))))
      | .inl p, .inr nq =>
          exact .inr (Deriv.impIntro (Deriv.impElim (wk1 nq)
            (Deriv.impElim
              (Deriv.iden (show φ.ifThen ψ ∈ [φ.ifThen ψ, h] by simp))
              (wk1 p))))
  | somehow ψ ih =>
      exact fun hv => hsom ψ hv (ih hv)

/-- The theory of `◯⊥` is complete over the closed fragment. -/
theorem obot_decides : ∀ φ, NoFall.VarFree φ →
    Deriv [oBot] φ ∨ Deriv [oBot] (φ.ifThen .falsePLL) :=
  decides_of_somehow oBot (fun ψ _ _ => .inl (obot_somehow ψ))

/-- The theory of `¬◯⊥` is complete over the closed fragment. -/
theorem nbot_decides : ∀ φ, NoFall.VarFree φ →
    Deriv [nBot] φ ∨ Deriv [nBot] (φ.ifThen .falsePLL) := by
  refine decides_of_somehow nBot (fun ψ _ dec => ?_)
  match dec with
  | .inl p =>
      exact .inl (p.cutHead ⟨.laxIntro (.iden (show ψ ∈ [ψ] by simp))⟩)
  | .inr np =>
      refine .inr (Deriv.impIntro ?_)
      have hstep : Deriv (ψ :: [PLLFormula.somehow ψ, nBot]) oBot :=
        Deriv.falsoElim _ (Deriv.impElim (wkH np (by simp))
          (Deriv.iden (show ψ ∈ [ψ, PLLFormula.somehow ψ, nBot] by simp)))
      have hOB : Deriv [PLLFormula.somehow ψ, nBot] oBot :=
        match (Deriv.iden
                (show PLLFormula.somehow ψ ∈ [PLLFormula.somehow ψ, nBot] by simp) :
               Deriv [PLLFormula.somehow ψ, nBot] (PLLFormula.somehow ψ)), hstep with
        | ⟨p₁⟩, ⟨p₂⟩ => ⟨.laxElim p₁ p₂⟩
      exact Deriv.impElim
        (Deriv.iden (show nBot ∈ [PLLFormula.somehow ψ, nBot] by simp)) hOB

/-- `⊥ < ◯⊥` (strictness = the banked consistency cell rho-0014). -/
theorem bot_lt_obot : Lt PLLFormula.falsePLL oBot :=
  ⟨Deriv.falsoElim _
    (Deriv.iden (show PLLFormula.falsePLL ∈ [PLLFormula.falsePLL] by simp)),
   nle_2_0.ok.holds⟩

/-- `⊥ < ¬◯⊥` (strictness = the banked consistency cell rho-0016). -/
theorem bot_lt_nbot : Lt PLLFormula.falsePLL nBot :=
  ⟨Deriv.falsoElim _
    (Deriv.iden (show PLLFormula.falsePLL ∈ [PLLFormula.falsePLL] by simp)),
   nle_3_0.ok.holds⟩

/-- **`⊥ ⋖ ◯⊥` in the closed fragment** — the first inhabitant of the
cover notion, and a theorem finite testing cannot decide. -/
theorem bot_coversVF_obot : CoversVF PLLFormula.falsePLL oBot := by
  refine ⟨bot_lt_obot, fun c hvf ⟨⟨_, hcons⟩, hup, hno⟩ => ?_⟩
  match obot_decides c hvf with
  | .inl hc => exact hno hc
  | .inr hnc =>
      exact hcons (Deriv.impElim (hup.cutHead hnc)
        (Deriv.iden (show c ∈ [c] by simp)))

/-- **`⊥ ⋖ ¬◯⊥` in the closed fragment.** -/
theorem bot_coversVF_nbot : CoversVF PLLFormula.falsePLL nBot := by
  refine ⟨bot_lt_nbot, fun c hvf ⟨⟨_, hcons⟩, hup, hno⟩ => ?_⟩
  match nbot_decides c hvf with
  | .inl hc => exact hno hc
  | .inr hnc =>
      exact hcons (Deriv.impElim (hup.cutHead hnc)
        (Deriv.iden (show c ∈ [c] by simp)))

/-- The ALL-FORMULAS cover `⊥ ⋖ ◯⊥` is REFUTED: `◯⊥ ∧ p` interposes.
Both countermodels kernel-checked (`FinCM.not_provable_of_check`). -/
theorem not_covers_bot_obot : ¬ Covers PLLFormula.falsePLL oBot := by
  intro h
  refine h.2 (oBot.and (.prop "p"))
    ⟨⟨Deriv.falsoElim _
        (Deriv.iden (show PLLFormula.falsePLL ∈ [PLLFormula.falsePLL] by simp)), ?_⟩,
      ⟨Deriv.andElim1
        (Deriv.iden (show oBot.and (.prop "p") ∈ [oBot.and (.prop "p")] by simp)), ?_⟩⟩
  · exact FinCM.not_provable_of_check
      (M := ⟨2, [(1, 0)], [(1, 0)], [0], [(1, "p")]⟩) (w := 1) (by decide)
  · exact FinCM.not_provable_of_check
      (M := ⟨2, [(1, 0)], [(1, 0)], [0], []⟩) (w := 1) (by decide)

/-! ## Pins — UNGUARDED as emitted; guard via tools/pin-backfill.py -/

/-- info: 'RNDB.rho6_lt_rho12' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rho6_lt_rho12

/-- info: 'RNDB.rho6_lt_rho9' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rho6_lt_rho9

/-- info: 'RNDB.not_coversIn_of_open' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_coversIn_of_open

/-- info: 'RNDB.rho12_nle_rho9' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rho12_nle_rho9
/-- info: 'RNDB.rho13_nle_rho6' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rho13_nle_rho6
/-- info: 'RNDB.not_covers_rho6_rho12' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_covers_rho6_rho12
/-- info: 'RNDB.rho6_lt_rho13' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rho6_lt_rho13
/-- info: 'RNDB.orderEntries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms orderEntries

/-- info: 'RNDB.obot_decides' depends on axioms: [propext] -/
#guard_msgs in
#print axioms obot_decides
/-- info: 'RNDB.nbot_decides' depends on axioms: [propext] -/
#guard_msgs in
#print axioms nbot_decides
/-- info: 'RNDB.bot_coversVF_obot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bot_coversVF_obot
/-- info: 'RNDB.bot_coversVF_nbot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bot_coversVF_nbot
/-- info: 'RNDB.not_covers_bot_obot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_covers_bot_obot

end RNDB
