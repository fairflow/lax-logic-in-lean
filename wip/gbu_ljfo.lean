/-
# The translation `T : LJF◯ → Gbu◯(G)` — stage F3, and F4's composition

`docs/frjw-plan.md`, "Route change" section.  Every LJF◯ derivation
translates into `Gbu◯(G)`, so with `bridge_iff` (focalization for PLL,
`LJF/OBridge.lean`), **Gbu◯ is complete in itself**:

    gbuC_complete : Nonempty (LaxND [] φ) → ProvableGbuC (ofPLL φ)

## Architecture (settled by the F2 screens)

`GbuIC` is not monotone (`gbuIC_not_monotone`) and has no modus ponens
(`gbuIC_no_mp`), so:

* every function is in CONTINUATION-PASSING style: it hoists the left
  activity of its subtree into a prefix of left steps and delivers the
  irregular derivation at the EXACT context of consumption — irregular
  terms are never weakened, only `≐`-transported;
* the traversal is MODE-GENERIC (`Kit`): above any `◯`-opening the
  prefix consists of REGULAR rules (`limpL`, `lorL`, `landL`, `lbot`,
  the `regKit`); a `.lax` left-focus spine builds ENTIRELY inside the
  irregular `◯`-goal judgment (`combSpineLaxI`), where the prefix
  consists of the IRREGULAR goal-conditioned rules (`limpLI`, `lorLI`,
  `landLI`, `lbotI`, the `irrKit`) and `lcircI` is the context bridge
  for `circL` — the regular judgment has no such bridge at a non-`◯`
  goal, which is what forces the mode switch;
* the two same-context irregular demands of `R∧ᵢ` are produced by
  `combPair`, which retries the pair until the context is `≐`-stable —
  fuel-founded on the count of universe formulas not yet in the context
  (`satMeasure_lt`), with `U ⊇ sfL G` covering every hoist addition;
* the `.lax` flag translates to `◯`-WRAPPED deliveries (`rcircI` at
  `laxOf`/`rfoc` leaves, `lcircI` for `circL`); nested `circR` at `.lax`
  is skipped — its premise's delivery IS the wrapped formula;
* the one syntactic corner with no sound image — right focus, lax flag,
  on `↓(↑P)` — is excluded by the `noDUP`/`noDUN` invariant, which
  `posOfO`/`negOfO` images satisfy (`noDUN_negOfO`).

The licenced `|◯C|` adaptation of `GbuIC.limpLI` (see the rule in
`wip/gbu_circ.lean`) is consumed at exactly one place: `irrKit.impOpen`
supplies the side condition from `A ∈ Sf^R G` — the OLD size condition
is not available for hoisted implications below a `◯`-opening.
-/
import wip.gbu_ljfo_transport
import LJF.OBridge

set_option maxHeartbeats 3200000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace FRJ.Gbu.LJFT

open FRJ Form LJFO

/-- Cast an irregular derivation along a formula equation. -/
def castIC {G : Form} {Ψ : List Form} {X Y : Form} (d : GbuIC G Ψ X)
    (h : X = Y) : GbuIC G Ψ Y := h ▸ d

/-! ## Invariant extractors -/

theorem ndN_up {P : Pos} (h : noDUN (.up P) = true) : noDUP P = true := by
  simpa [noDUN] using h
theorem ndN_imp {Q : Pos} {N : Neg} (h : noDUN (.imp Q N) = true) :
    noDUP Q = true ∧ noDUN N = true := by
  simpa [noDUN, Bool.and_eq_true] using h
theorem ndN_and {M N : Neg} (h : noDUN (.and M N) = true) :
    noDUN M = true ∧ noDUN N = true := by
  simpa [noDUN, Bool.and_eq_true] using h
theorem ndN_circ {P : Pos} (h : noDUN (.circ P) = true) : noDUP P = true := by
  simpa [noDUN] using h
theorem ndP_or {P Q : Pos} (h : noDUP (.or P Q) = true) :
    noDUP P = true ∧ noDUP Q = true := by
  simpa [noDUP, Bool.and_eq_true] using h
theorem ndP_down {M : Neg} (h : noDUP (.down M) = true) : noDUN M = true := by
  cases M <;> simp_all [noDUP, noDUN]

theorem sfRnf_imp {G : Form} {Q : Pos} {N : Neg} (h : nf (.imp Q N) ∈ sfR G) :
    pf Q ∈ sfL G ∧ nf N ∈ sfR G := by rw [nf_imp] at h; exact sfR_imp h
theorem sfRnf_and {G : Form} {M N : Neg} (h : nf (.and M N) ∈ sfR G) :
    nf M ∈ sfR G ∧ nf N ∈ sfR G := by rw [nf_and] at h; exact sfR_and h
theorem sfRnf_circ {G : Form} {P : Pos} (h : nf (.circ P) ∈ sfR G) :
    pf P ∈ sfR G := by rw [nf_circ] at h; exact sfR_circ h
theorem sfRpf_or {G : Form} {P Q : Pos} (h : pf (.or P Q) ∈ sfR G) :
    pf P ∈ sfR G ∧ pf Q ∈ sfR G := by rw [pf_or] at h; exact sfR_or h
theorem sfLnf_imp {G : Form} {Q : Pos} {N : Neg} (h : nf (.imp Q N) ∈ sfL G) :
    pf Q ∈ sfR G ∧ nf N ∈ sfL G := by rw [nf_imp] at h; exact sfL_imp h
theorem sfLnf_and {G : Form} {M N : Neg} (h : nf (.and M N) ∈ sfL G) :
    nf M ∈ sfL G ∧ nf N ∈ sfL G := by rw [nf_and] at h; exact sfL_and h
theorem sfLnf_circ {G : Form} {P : Pos} (h : nf (.circ P) ∈ sfL G) :
    pf P ∈ sfL G := by rw [nf_circ] at h; exact sfL_circ h
theorem sfLpf_or {G : Form} {P Q : Pos} (h : pf (.or P Q) ∈ sfL G) :
    pf P ∈ sfL G ∧ pf Q ∈ sfL G := by rw [pf_or] at h; exact sfL_or h

/-! ## The environment invariant -/

/-- What the translation knows at a node: every LJF◯ hypothesis and
queue member is `Clo`-available at the Gbu context, `Sf^L`-bounded and
`↓↑`-free, and the Gbu context stays inside the universe `U`. -/
structure Env (G : Form) (U : List Form) (Γ : List Neg) (Ω : List Pos)
    (Ψ : List Form) : Prop where
  hc : ∀ N ∈ Γ, Clo Ψ (nf N)
  hs : ∀ N ∈ Γ, nf N ∈ sfL G
  nd : ∀ N ∈ Γ, noDUN N = true
  qc : ∀ P ∈ Ω, Clo Ψ (pf P)
  qs : ∀ P ∈ Ω, pf P ∈ sfL G
  qd : ∀ P ∈ Ω, noDUP P = true
  hu : ∀ x ∈ Ψ, x ∈ U

namespace Env

variable {G : Form} {U : List Form} {Γ : List Neg} {Ω : List Pos}
  {Ψ Ψ' : List Form}

theorem mono (e : Env G U Γ Ω Ψ) (hsub : Ψ ⊆ Ψ')
    (hu' : ∀ x ∈ Ψ', x ∈ U) : Env G U Γ Ω Ψ' :=
  ⟨fun N h => clo_mono hsub (e.hc N h), e.hs, e.nd,
   fun P h => clo_mono hsub (e.qc P h), e.qs, e.qd, hu'⟩

theorem grow (e : Env G U Γ Ω Ψ) {x : Form} (hx : x ∈ U) :
    Env G U Γ Ω (x :: Ψ) :=
  e.mono (List.subset_cons_self _ _)
    (fun y hy => (List.mem_cons.mp hy).elim (fun h => h ▸ hx) (e.hu y))

theorem tail {Q : Pos} (e : Env G U Γ (Q :: Ω) Ψ) : Env G U Γ Ω Ψ :=
  ⟨e.hc, e.hs, e.nd,
   fun P h => e.qc P (List.mem_cons_of_mem _ h),
   fun P h => e.qs P (List.mem_cons_of_mem _ h),
   fun P h => e.qd P (List.mem_cons_of_mem _ h), e.hu⟩

theorem pushQ {Q : Pos} (e : Env G U Γ Ω Ψ) (hcq : Clo Ψ (pf Q))
    (hsq : pf Q ∈ sfL G) (hdq : noDUP Q = true) : Env G U Γ (Q :: Ω) Ψ :=
  ⟨e.hc, e.hs, e.nd,
   fun P h => (List.mem_cons.mp h).elim (fun hp => hp ▸ hcq) (e.qc P),
   fun P h => (List.mem_cons.mp h).elim (fun hp => hp ▸ hsq) (e.qs P),
   fun P h => (List.mem_cons.mp h).elim (fun hp => hp ▸ hdq) (e.qd P), e.hu⟩

theorem popAtom {a : String} (e : Env G U Γ (Pos.atom a :: Ω) Ψ) :
    Env G U (Neg.up (Pos.atom a) :: Γ) Ω Ψ :=
  ⟨fun N h => (List.mem_cons.mp h).elim
      (fun hn => hn ▸ (nf_up (P := .atom a) ▸ e.qc _ List.mem_cons_self))
      (e.hc N),
   fun N h => (List.mem_cons.mp h).elim
      (fun hn => hn ▸ (nf_up (P := .atom a) ▸ e.qs _ List.mem_cons_self))
      (e.hs N),
   fun N h => (List.mem_cons.mp h).elim
      (fun hn => hn ▸ (e.qd _ List.mem_cons_self)) (e.nd N),
   (e.tail).qc, (e.tail).qs, (e.tail).qd, e.hu⟩

theorem popDown {M : Neg} (e : Env G U Γ (Pos.down M :: Ω) Ψ) :
    Env G U (M :: Γ) Ω Ψ :=
  ⟨fun N h => (List.mem_cons.mp h).elim
      (fun hn => hn ▸ (pf_down (N := M) ▸ e.qc _ List.mem_cons_self))
      (e.hc N),
   fun N h => (List.mem_cons.mp h).elim
      (fun hn => hn ▸ (pf_down (N := M) ▸ e.qs _ List.mem_cons_self))
      (e.hs N),
   fun N h => (List.mem_cons.mp h).elim
      (fun hn => hn ▸ ndP_down (e.qd _ List.mem_cons_self)) (e.nd N),
   (e.tail).qc, (e.tail).qs, (e.tail).qd, e.hu⟩

end Env

/-- Extract a member of `l` missing from `l'` when the inclusion fails —
constructively, by walking `l`. -/
def findNotMem : (l l' : List Form) → (¬ ∀ x ∈ l, x ∈ l') →
    Σ' x : Form, x ∈ l ∧ x ∉ l'
  | [], _, h => absurd (fun _ hx => absurd hx List.not_mem_nil) h
  | a :: l, l', h =>
      if ha : a ∈ l' then
        let ⟨x, hx, hx'⟩ := findNotMem l l'
          (fun hall => h (fun x hx =>
            (List.mem_cons.mp hx).elim (fun e => e ▸ ha) (hall x)))
        ⟨x, List.mem_cons_of_mem _ hx, hx'⟩
      else ⟨a, List.mem_cons_self .., ha⟩

/-! ## Derivation weight

A shallow weight on the four LJF◯ judgment families — auto-`sizeOf`
drags in index sizes and reduces badly inside termination goals, so the
measures below use this instead. -/

mutual

@[simp] def wS : ∀ {Γ : List Neg} {j : JD} {P : Pos}, Stab Γ j P → Nat
  | _, _, _, .rfoc d => wRF d + 1
  | _, _, _, .lfoc _ d => wLF d + 1
  | _, _, _, .laxOf d => wS d + 1

@[simp] def wRF : ∀ {Γ : List Neg} {j : JD} {P : Pos}, RFocus Γ j P → Nat
  | _, _, _, .init _ => 1
  | _, _, _, .or1 d => wRF d + 1
  | _, _, _, .or2 d => wRF d + 1
  | _, _, _, .rel d => wI d + 1

@[simp] def wLF : ∀ {Γ : List Neg} {N : Neg} {j : JD} {P : Pos},
    LFoc Γ N j P → Nat
  | _, _, _, _, .rel d => wI d + 1
  | _, _, _, _, .impL dQ d => wS dQ + wLF d + 1
  | _, _, _, _, .and1 d => wLF d + 1
  | _, _, _, _, .and2 d => wLF d + 1
  | _, _, _, _, .circL d => wI d + 1

@[simp] def wI : ∀ {Γ : List Neg} {Ω : List Pos} {j : JD} {N : Neg},
    Inv Γ Ω j N → Nat
  | _, _, _, _, .impR d => wI d + 1
  | _, _, _, _, .andR d₁ d₂ => wI d₁ + wI d₂ + 1
  | _, _, _, _, .circR d => wI d + 1
  | _, _, _, _, .stable d => wS d + 1
  | _, _, _, _, .orL d₁ d₂ => wI d₁ + wI d₂ + 1
  | _, _, _, _, .flsL => 1
  | _, _, _, _, .downL d => wI d + 1
  | _, _, _, _, .atomL d => wI d + 1

end

/-! ## The step kit: one traversal, two target modes

The same hoisting traversal serves two targets: the REGULAR judgment
(`T Ψ = GbuRC G Ψ C`, arbitrary `C`) and — below a `circL` opening,
where availability lives inside the irregular term — the IRREGULAR
`◯`-goal judgment (`T Ψ = GbuIC G Ψ ◯C₀`).  A `Kit` packages the four
left steps a mode provides; only the irregular mode has a `◯`-opening,
handled concretely in the lax spine (`lcircI` is its context bridge —
the regular mode has none at a non-`◯` goal, which is what forces the
mode switch). -/

structure Kit (G : Form) (T : List Form → Type) : Type where
  orSplit : ∀ {Ψ : List Form} {A B : Form}, Form.or A B ∈ Ψ →
    T (A :: Ψ) → T (B :: Ψ) → T Ψ
  botClose : ∀ {Ψ : List Form}, Form.bot ∈ Ψ → T Ψ
  andOpen : ∀ {Ψ : List Form} {A B : Form}, Form.and A B ∈ Ψ →
    T (A :: B :: Ψ) → T Ψ
  impOpen : ∀ {Ψ : List Form} {A B : Form}, Form.imp A B ∈ Ψ → A ∈ sfR G →
    GbuIC G (.imp A B :: Ψ) A → T (B :: Ψ) → T Ψ

/-- The regular mode. -/
def regKit (G : Form) (C : Form) : Kit G (fun Ψ => GbuRC G Ψ C) where
  orSplit mem d₁ d₂ := .lorL d₁ d₂ (ctxEq_consSelf mem)
  botClose mem := .lbot _ (ctxEq_consSelf mem)
  andOpen mem d := .landL d (ctxEq_consSelf mem)
  impOpen mem _ d₁ d₂ := .limpL d₁ d₂ (ctxEq_consSelf mem)

/-- The irregular `◯`-goal mode.  `impOpen` supplies `L⊃ᵢ`'s ADAPTED
side condition from the antecedent's right-signed subformula weight —
this is where the licenced `|◯C|` adaptation is consumed. -/
def irrKit (G : Form) (C₀ : Form) (hgc : Form.circ C₀ ∈ sfR G) :
    Kit G (fun Ψ => GbuIC G Ψ (.circ C₀)) where
  orSplit mem d₁ d₂ := .lorLI d₁ d₂ hgc (ctxEq_consSelf mem)
  botClose mem := .lbotI hgc (ctxEq_consSelf mem)
  andOpen mem d := .landLI d hgc (ctxEq_consSelf mem)
  impOpen mem hAsf d₁ d₂ := .limpLI d₁ d₂ (Or.inr hAsf) hgc (ctxEq_consSelf mem)

/-! ## The translation -/

section Translation

variable {G : Form} {U : List Form}

mutual

/-- Inversion at `tru`: deliver `Ψ' →g ⌊N⌋`. -/
def combInv (hUL : ∀ x ∈ sfL G, x ∈ U) (T : List Form → Type)
    (kit : Kit G T) :
    ∀ {Γ : List Neg} {Ω : List Pos} {N : Neg},
    Inv Γ Ω .tru N → ∀ (Ψ : List Form), Env G U Γ Ω Ψ →
    nf N ∈ sfR G → noDUN N = true →
    (∀ Ψ' : List Form, Ψ ⊆ Ψ' → (∀ x ∈ Ψ', x ∈ U) →
      GbuIC G Ψ' (nf N) → T Ψ') → T Ψ
  | _, _, _, .impR (Q := Q) (N := N') d', Ψ, env, hg, ndg, k =>
      if hq : Clo Ψ (pf Q) then
        combInv hUL T kit d' Ψ (env.pushQ hq (sfRnf_imp hg).1 (ndN_imp ndg).1)
          (sfRnf_imp hg).2 (ndN_imp ndg).2
          (fun Ψ' hsub hu' irr =>
            k Ψ' hsub hu'
              (castIC (.rimpII irr (clo_mono hsub hq)) nf_imp.symm))
      else
        k Ψ (fun _ h => h) env.hu
          (castIC
            (.rimpNII
              (tInv hUL d' (pf Q :: Ψ)
                ((env.grow (hUL _ (sfRnf_imp hg).1)).pushQ
                  (.base List.mem_cons_self) (sfRnf_imp hg).1
                  (ndN_imp ndg).1)
                (sfRnf_imp hg).2 (ndN_imp ndg).2) hq)
            nf_imp.symm)
  | _, _, _, .andR d₁ d₂, Ψ, env, hg, ndg, k =>
      combPair hUL T kit ((U.filter (fun y => decide (y ∉ Ψ))).length + 1)
        d₁ d₂ Ψ env (sfRnf_and hg).1 (sfRnf_and hg).2
        (ndN_and ndg).1 (ndN_and ndg).2 (Nat.lt_succ_self _)
        (fun Ψ' hsub hu' irr₁ irr₂ =>
          k Ψ' hsub hu' (castIC (.randI irr₁ irr₂) nf_and.symm))
  | _, _, _, .circR d', Ψ, env, hg, ndg, k =>
      combLaxCUp hUL T kit d' Ψ env (nf_circ ▸ hg) (ndN_circ ndg)
        (fun Ψ' hsub hu' irr => k Ψ' hsub hu' (castIC irr nf_circ.symm))
  | _, _, _, .stable dS, Ψ, env, hg, ndg, k =>
      comb hUL T kit dS Ψ env (nf_up ▸ hg) (ndN_up ndg)
        (fun Ψ' hsub hu' irr => k Ψ' hsub hu' (castIC irr nf_up.symm))
  | _, _, _, .orL (P := P) (Q := Q) d₁ d₂, Ψ, env, hg, ndg, k =>
      have h' : Clo Ψ (.or (pf P) (pf Q)) :=
        pf_or ▸ env.qc _ List.mem_cons_self
      have hsl := sfLpf_or (env.qs _ List.mem_cons_self)
      have hnd := ndP_or (env.qd _ List.mem_cons_self)
      if hm : Form.or (pf P) (pf Q) ∈ Ψ then
        kit.orSplit hm
          (combInv hUL T kit d₁ (pf P :: Ψ)
            ((env.tail.grow (hUL _ hsl.1)).pushQ (.base List.mem_cons_self)
              hsl.1 hnd.1) hg ndg
            (fun Ψ' hsub hu' irr =>
              k Ψ' (fun _ hx => hsub (List.mem_cons_of_mem _ hx)) hu' irr))
          (combInv hUL T kit d₂ (pf Q :: Ψ)
            ((env.tail.grow (hUL _ hsl.2)).pushQ (.base List.mem_cons_self)
              hsl.2 hnd.2) hg ndg
            (fun Ψ' hsub hu' irr =>
              k Ψ' (fun _ hx => hsub (List.mem_cons_of_mem _ hx)) hu' irr))
      else if hP : Clo Ψ (pf P) then
        combInv hUL T kit d₁ Ψ (env.tail.pushQ hP hsl.1 hnd.1) hg ndg k
      else
        combInv hUL T kit d₂ Ψ
          (env.tail.pushQ (((clo_or_inv h').resolve_left hm).resolve_left hP)
            hsl.2 hnd.2) hg ndg k
  | _, _, _, .flsL, Ψ, env, _, _, _ =>
      kit.botClose (clo_bot_mem (pf_fls ▸ env.qc _ List.mem_cons_self))
  | _, _, _, .downL d', Ψ, env, hg, ndg, k =>
      combInv hUL T kit d' Ψ env.popDown hg ndg k
  | _, _, _, .atomL d', Ψ, env, hg, ndg, k =>
      combInv hUL T kit d' Ψ env.popAtom hg ndg k

termination_by _ _ _ d => (2 * wI d, 0)
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | (apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left;
         first
           | omega
           | (simp only [wS, wRF, wLF, wI]; omega))

/-- Stable at `tru`. -/
def comb (hUL : ∀ x ∈ sfL G, x ∈ U) (T : List Form → Type) (kit : Kit G T) :
    ∀ {Γ : List Neg} {P : Pos},
    Stab Γ .tru P → ∀ (Ψ : List Form), Env G U Γ [] Ψ →
    pf P ∈ sfR G → noDUP P = true →
    (∀ Ψ' : List Form, Ψ ⊆ Ψ' → (∀ x ∈ Ψ', x ∈ U) →
      GbuIC G Ψ' (pf P) → T Ψ') → T Ψ
  | _, _, .rfoc dRF, Ψ, env, hg, ndg, k =>
      combRFT hUL T kit dRF Ψ env hg ndg k
  | _, _, .lfoc hM dM, Ψ, env, hg, ndg, k =>
      combSpine hUL T kit dM Ψ env (env.hc _ hM) (env.hs _ hM) (env.nd _ hM)
        hg ndg k

termination_by _ _ d => (2 * wS d, 0)
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | (apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left;
         first
           | omega
           | (simp only [wS, wRF, wLF, wI]; omega))

/-- Right focus at `tru`. -/
def combRFT (hUL : ∀ x ∈ sfL G, x ∈ U) (T : List Form → Type)
    (kit : Kit G T) :
    ∀ {Γ : List Neg} {P : Pos},
    RFocus Γ .tru P → ∀ (Ψ : List Form), Env G U Γ [] Ψ →
    pf P ∈ sfR G → noDUP P = true →
    (∀ Ψ' : List Form, Ψ ⊆ Ψ' → (∀ x ∈ Ψ', x ∈ U) →
      GbuIC G Ψ' (pf P) → T Ψ') → T Ψ
  | _, _, .init h, Ψ, env, _, _, k =>
      k Ψ (fun _ h => h) env.hu
        (castIC (.ax _ (ctxEq_consSelf
          (clo_atom_mem (pf_atom ▸ nf_up ▸ env.hc _ h)))) pf_atom.symm)
  | _, _, .or1 d', Ψ, env, hg, ndg, k =>
      combRFT hUL T kit d' Ψ env (sfRpf_or hg).1 (ndP_or ndg).1
        (fun Ψ' hsub hu' irr =>
          k Ψ' hsub hu' (castIC (.rorI1 irr) pf_or.symm))
  | _, _, .or2 d', Ψ, env, hg, ndg, k =>
      combRFT hUL T kit d' Ψ env (sfRpf_or hg).2 (ndP_or ndg).2
        (fun Ψ' hsub hu' irr =>
          k Ψ' hsub hu' (castIC (.rorI2 irr) pf_or.symm))
  | _, _, .rel d', Ψ, env, hg, ndg, k =>
      combInv hUL T kit d' Ψ env (pf_down ▸ hg) (ndP_down ndg)
        (fun Ψ' hsub hu' irr => k Ψ' hsub hu' (castIC irr pf_down.symm))

termination_by _ _ d => (2 * wRF d, 0)
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | (apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left;
         first
           | omega
           | (simp only [wS, wRF, wLF, wI]; omega))

/-- Right focus at `lax`: the UNWRAPPED delivery (`↓↑` excluded by
`noDUP`). -/
def combRFLaxU (hUL : ∀ x ∈ sfL G, x ∈ U) (T : List Form → Type)
    (kit : Kit G T) :
    ∀ {Γ : List Neg} {P : Pos},
    RFocus Γ .lax P → ∀ (Ψ : List Form), Env G U Γ [] Ψ →
    pf P ∈ sfR G → noDUP P = true →
    (∀ Ψ' : List Form, Ψ ⊆ Ψ' → (∀ x ∈ Ψ', x ∈ U) →
      GbuIC G Ψ' (pf P) → T Ψ') → T Ψ
  | _, _, .init h, Ψ, env, _, _, k =>
      k Ψ (fun _ h => h) env.hu
        (castIC (.ax _ (ctxEq_consSelf
          (clo_atom_mem (pf_atom ▸ nf_up ▸ env.hc _ h)))) pf_atom.symm)
  | _, _, .or1 d', Ψ, env, hg, ndg, k =>
      combRFLaxU hUL T kit d' Ψ env (sfRpf_or hg).1 (ndP_or ndg).1
        (fun Ψ' hsub hu' irr =>
          k Ψ' hsub hu' (castIC (.rorI1 irr) pf_or.symm))
  | _, _, .or2 d', Ψ, env, hg, ndg, k =>
      combRFLaxU hUL T kit d' Ψ env (sfRpf_or hg).2 (ndP_or ndg).2
        (fun Ψ' hsub hu' irr =>
          k Ψ' hsub hu' (castIC (.rorI2 irr) pf_or.symm))
  | _, _, .rel (N := .circ P'') d', Ψ, env, hg, ndg, k =>
      combLaxC hUL T kit d' Ψ env (nf_circ ▸ pf_down ▸ hg)
        (ndN_circ (ndP_down ndg))
        (fun Ψ' hsub hu' irr =>
          k Ψ' hsub hu' (castIC irr (pf_down.trans nf_circ).symm))
  | _, _, .rel (N := .up _) _, _, _, _, ndg, _ =>
      absurd ndg (by simp [noDUP])
  | _, _, .rel (N := .imp _ _) d', _, _, _, _, _ => nomatch d'
  | _, _, .rel (N := .and _ _) d', _, _, _, _, _ => nomatch d'

termination_by _ _ d => (2 * wRF d, 0)
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | (apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left;
         first
           | omega
           | (simp only [wS, wRF, wLF, wI]; omega))

/-- A `tru` left-focus spine. -/
def combSpine (hUL : ∀ x ∈ sfL G, x ∈ U) (T : List Form → Type)
    (kit : Kit G T) :
    ∀ {Γ : List Neg} {M : Neg} {P : Pos},
    LFoc Γ M .tru P → ∀ (Ψ : List Form), Env G U Γ [] Ψ →
    Clo Ψ (nf M) → nf M ∈ sfL G → noDUN M = true →
    pf P ∈ sfR G → noDUP P = true →
    (∀ Ψ' : List Form, Ψ ⊆ Ψ' → (∀ x ∈ Ψ', x ∈ U) →
      GbuIC G Ψ' (pf P) → T Ψ') → T Ψ
  | _, _, _, .rel dI, Ψ, env, hm, hms, ndm, hg, ndg, k =>
      combInv hUL T kit dI Ψ
        (env.pushQ (nf_up ▸ hm) (nf_up ▸ hms) (ndN_up ndm))
        (nf_up.symm ▸ hg) (by simpa [noDUN] using ndg)
        (fun Ψ' hsub hu' irr => k Ψ' hsub hu' (castIC irr nf_up))
  | _, _, _, .impL (Q := Q) (N := N') dQ dRest, Ψ, env, hm, hms, ndm, hg, ndg, k =>
      have h' : Clo Ψ (.imp (pf Q) (nf N')) := nf_imp ▸ hm
      if hmem : Form.imp (pf Q) (nf N') ∈ Ψ then
        comb hUL T kit dQ Ψ env (sfLnf_imp hms).1 (ndN_imp ndm).1
          (fun Ψ' hsub hu' irrQ =>
            kit.impOpen (hsub hmem) (sfLnf_imp hms).1
              (transportIC irrQ (ctxEq_consSelf (hsub hmem)))
              (combSpine hUL T kit dRest (nf N' :: Ψ')
                ((env.mono hsub hu').grow (hUL _ (sfLnf_imp hms).2))
                (.base List.mem_cons_self) (sfLnf_imp hms).2
                (ndN_imp ndm).2 hg ndg
                (fun Ψ'' hs2 hu2 irr =>
                  k Ψ'' (fun _ hx =>
                    hs2 (List.mem_cons_of_mem _ (hsub hx))) hu2 irr)))
      else
        combSpine hUL T kit dRest Ψ env ((clo_imp_inv h').resolve_left hmem)
          (sfLnf_imp hms).2 (ndN_imp ndm).2 hg ndg k
  | _, _, _, .and1 (M := M₁) (N := M₂) dRest, Ψ, env, hm, hms, ndm, hg, ndg, k =>
      have h' : Clo Ψ (.and (nf M₁) (nf M₂)) := nf_and ▸ hm
      if hmem : Form.and (nf M₁) (nf M₂) ∈ Ψ then
        kit.andOpen hmem
          (combSpine hUL T kit dRest (nf M₁ :: nf M₂ :: Ψ)
            ((env.grow (hUL _ (sfLnf_and hms).2)).grow
              (hUL _ (sfLnf_and hms).1))
            (.base List.mem_cons_self) (sfLnf_and hms).1 (ndN_and ndm).1
            hg ndg
            (fun Ψ' hsub hu' irr =>
              k Ψ' (fun _ hx =>
                hsub (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
                hu' irr))
      else
        combSpine hUL T kit dRest Ψ env ((clo_and_inv h').resolve_left hmem).1
          (sfLnf_and hms).1 (ndN_and ndm).1 hg ndg k
  | _, _, _, .and2 (M := M₁) (N := M₂) dRest, Ψ, env, hm, hms, ndm, hg, ndg, k =>
      have h' : Clo Ψ (.and (nf M₁) (nf M₂)) := nf_and ▸ hm
      if hmem : Form.and (nf M₁) (nf M₂) ∈ Ψ then
        kit.andOpen hmem
          (combSpine hUL T kit dRest (nf M₁ :: nf M₂ :: Ψ)
            ((env.grow (hUL _ (sfLnf_and hms).2)).grow
              (hUL _ (sfLnf_and hms).1))
            (.base (List.mem_cons_of_mem _ List.mem_cons_self))
            (sfLnf_and hms).2 (ndN_and ndm).2 hg ndg
            (fun Ψ' hsub hu' irr =>
              k Ψ' (fun _ hx =>
                hsub (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
                hu' irr))
      else
        combSpine hUL T kit dRest Ψ env ((clo_and_inv h').resolve_left hmem).2
          (sfLnf_and hms).2 (ndN_and ndm).2 hg ndg k

termination_by _ _ _ d => (2 * wLF d, 0)
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | (apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left;
         first
           | omega
           | (simp only [wS, wRF, wLF, wI]; omega))

/-- Inversion at `lax`, `up` goal: the WRAPPED delivery. -/
def combLaxCUp (hUL : ∀ x ∈ sfL G, x ∈ U) (T : List Form → Type)
    (kit : Kit G T) :
    ∀ {Γ : List Neg} {Ω : List Pos} {P : Pos},
    Inv Γ Ω .lax (.up P) → ∀ (Ψ : List Form), Env G U Γ Ω Ψ →
    Form.circ (pf P) ∈ sfR G → noDUP P = true →
    (∀ Ψ' : List Form, Ψ ⊆ Ψ' → (∀ x ∈ Ψ', x ∈ U) →
      GbuIC G Ψ' (.circ (pf P)) → T Ψ') → T Ψ
  | _, _, _, .stable dS, Ψ, env, hg, ndg, k =>
      combLaxSC hUL T kit dS Ψ env hg ndg k
  | _, _, _, .orL (P := P) (Q := Q) d₁ d₂, Ψ, env, hg, ndg, k =>
      have h' : Clo Ψ (.or (pf P) (pf Q)) :=
        pf_or ▸ env.qc _ List.mem_cons_self
      have hsl := sfLpf_or (env.qs _ List.mem_cons_self)
      have hnd := ndP_or (env.qd _ List.mem_cons_self)
      if hm : Form.or (pf P) (pf Q) ∈ Ψ then
        kit.orSplit hm
          (combLaxCUp hUL T kit d₁ (pf P :: Ψ)
            ((env.tail.grow (hUL _ hsl.1)).pushQ (.base List.mem_cons_self)
              hsl.1 hnd.1) hg ndg
            (fun Ψ' hsub hu' irr =>
              k Ψ' (fun _ hx => hsub (List.mem_cons_of_mem _ hx)) hu' irr))
          (combLaxCUp hUL T kit d₂ (pf Q :: Ψ)
            ((env.tail.grow (hUL _ hsl.2)).pushQ (.base List.mem_cons_self)
              hsl.2 hnd.2) hg ndg
            (fun Ψ' hsub hu' irr =>
              k Ψ' (fun _ hx => hsub (List.mem_cons_of_mem _ hx)) hu' irr))
      else if hP : Clo Ψ (pf P) then
        combLaxCUp hUL T kit d₁ Ψ (env.tail.pushQ hP hsl.1 hnd.1) hg ndg k
      else
        combLaxCUp hUL T kit d₂ Ψ
          (env.tail.pushQ (((clo_or_inv h').resolve_left hm).resolve_left hP)
            hsl.2 hnd.2) hg ndg k
  | _, _, _, .flsL, Ψ, env, _, _, _ =>
      kit.botClose (clo_bot_mem (pf_fls ▸ env.qc _ List.mem_cons_self))
  | _, _, _, .downL d', Ψ, env, hg, ndg, k =>
      combLaxCUp hUL T kit d' Ψ env.popDown hg ndg k
  | _, _, _, .atomL d', Ψ, env, hg, ndg, k =>
      combLaxCUp hUL T kit d' Ψ env.popAtom hg ndg k

termination_by _ _ _ d => (2 * wI d, 0)
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | (apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left;
         first
           | omega
           | (simp only [wS, wRF, wLF, wI]; omega))

/-- Inversion at `lax`, `circ` goal: the `circR` node is skipped. -/
def combLaxC (hUL : ∀ x ∈ sfL G, x ∈ U) (T : List Form → Type)
    (kit : Kit G T) :
    ∀ {Γ : List Neg} {Ω : List Pos} {P : Pos},
    Inv Γ Ω .lax (.circ P) → ∀ (Ψ : List Form), Env G U Γ Ω Ψ →
    Form.circ (pf P) ∈ sfR G → noDUP P = true →
    (∀ Ψ' : List Form, Ψ ⊆ Ψ' → (∀ x ∈ Ψ', x ∈ U) →
      GbuIC G Ψ' (.circ (pf P)) → T Ψ') → T Ψ
  | _, _, _, .circR d', Ψ, env, hg, ndg, k =>
      combLaxCUp hUL T kit d' Ψ env hg ndg k
  | _, _, _, .orL (P := P) (Q := Q) d₁ d₂, Ψ, env, hg, ndg, k =>
      have h' : Clo Ψ (.or (pf P) (pf Q)) :=
        pf_or ▸ env.qc _ List.mem_cons_self
      have hsl := sfLpf_or (env.qs _ List.mem_cons_self)
      have hnd := ndP_or (env.qd _ List.mem_cons_self)
      if hm : Form.or (pf P) (pf Q) ∈ Ψ then
        kit.orSplit hm
          (combLaxC hUL T kit d₁ (pf P :: Ψ)
            ((env.tail.grow (hUL _ hsl.1)).pushQ (.base List.mem_cons_self)
              hsl.1 hnd.1) hg ndg
            (fun Ψ' hsub hu' irr =>
              k Ψ' (fun _ hx => hsub (List.mem_cons_of_mem _ hx)) hu' irr))
          (combLaxC hUL T kit d₂ (pf Q :: Ψ)
            ((env.tail.grow (hUL _ hsl.2)).pushQ (.base List.mem_cons_self)
              hsl.2 hnd.2) hg ndg
            (fun Ψ' hsub hu' irr =>
              k Ψ' (fun _ hx => hsub (List.mem_cons_of_mem _ hx)) hu' irr))
      else if hP : Clo Ψ (pf P) then
        combLaxC hUL T kit d₁ Ψ (env.tail.pushQ hP hsl.1 hnd.1) hg ndg k
      else
        combLaxC hUL T kit d₂ Ψ
          (env.tail.pushQ (((clo_or_inv h').resolve_left hm).resolve_left hP)
            hsl.2 hnd.2) hg ndg k
  | _, _, _, .flsL, Ψ, env, _, _, _ =>
      kit.botClose (clo_bot_mem (pf_fls ▸ env.qc _ List.mem_cons_self))
  | _, _, _, .downL d', Ψ, env, hg, ndg, k =>
      combLaxC hUL T kit d' Ψ env.popDown hg ndg k
  | _, _, _, .atomL d', Ψ, env, hg, ndg, k =>
      combLaxC hUL T kit d' Ψ env.popAtom hg ndg k

termination_by _ _ _ d => (2 * wI d, 0)
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | (apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left;
         first
           | omega
           | (simp only [wS, wRF, wLF, wI]; omega))

/-- Stable at `lax`: wrapped delivery; the left-focus case switches to
the IRREGULAR mode. -/
def combLaxSC (hUL : ∀ x ∈ sfL G, x ∈ U) (T : List Form → Type)
    (kit : Kit G T) :
    ∀ {Γ : List Neg} {P : Pos},
    Stab Γ .lax P → ∀ (Ψ : List Form), Env G U Γ [] Ψ →
    Form.circ (pf P) ∈ sfR G → noDUP P = true →
    (∀ Ψ' : List Form, Ψ ⊆ Ψ' → (∀ x ∈ Ψ', x ∈ U) →
      GbuIC G Ψ' (.circ (pf P)) → T Ψ') → T Ψ
  | _, _, .laxOf dT, Ψ, env, hg, ndg, k =>
      comb hUL T kit dT Ψ env (sfR_circ hg) ndg
        (fun Ψ' hsub hu' irr => k Ψ' hsub hu' (.rcircI irr hg))
  | _, _, .rfoc dRF, Ψ, env, hg, ndg, k =>
      combRFLaxU hUL T kit dRF Ψ env (sfR_circ hg) ndg
        (fun Ψ' hsub hu' irr => k Ψ' hsub hu' (.rcircI irr hg))
  | _, _, .lfoc hM dM, Ψ, env, hg, ndg, k =>
      k Ψ (fun _ h => h) env.hu
        (combSpineLaxI hUL dM Ψ env (env.hc _ hM) (env.hs _ hM)
          (env.nd _ hM) hg ndg)

termination_by _ _ d => (2 * wS d, 0)
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | (apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left;
         first
           | omega
           | (simp only [wS, wRF, wLF, wI]; omega))

/-- A `lax` left-focus spine, built ENTIRELY inside the irregular
`◯`-goal judgment (`lcircI` is its context bridge; `L⊃ᵢ` its
implication step, via the adapted side condition; everything the spine
needs below runs at the irregular mode through `irrKit`). -/
def combSpineLaxI (hUL : ∀ x ∈ sfL G, x ∈ U) :
    ∀ {Γ : List Neg} {M : Neg} {P : Pos},
    LFoc Γ M .lax P → ∀ (Ψ : List Form), Env G U Γ [] Ψ →
    Clo Ψ (nf M) → nf M ∈ sfL G → noDUN M = true →
    Form.circ (pf P) ∈ sfR G → noDUP P = true →
    GbuIC G Ψ (.circ (pf P))
  | _, _, P, .rel dI, Ψ, env, hm, hms, ndm, hg, ndg =>
      combLaxCUp hUL (fun Ψ₀ => GbuIC G Ψ₀ (Form.circ (pf P))) (irrKit G (pf P) hg)
        dI Ψ (env.pushQ (nf_up ▸ hm) (nf_up ▸ hms) (ndN_up ndm)) hg ndg
        (fun _ _ _ irr => irr)
  | _, _, P, .circL (Q := Qb) dI, Ψ, env, hm, hms, ndm, hg, ndg =>
      have h' : Clo Ψ (.circ (pf Qb)) := nf_circ ▸ hm
      if hmem : Form.circ (pf Qb) ∈ Ψ then
        .lcircI
          (combLaxCUp hUL (fun Ψ₀ => GbuIC G Ψ₀ (Form.circ (pf P)))
            (irrKit G (pf P) hg) dI (pf Qb :: Ψ)
            ((env.grow (hUL _ (sfLnf_circ hms))).pushQ
              (.base List.mem_cons_self) (sfLnf_circ hms) (ndN_circ ndm))
            hg ndg (fun _ _ _ irr => irr))
          (nf_circ ▸ hms) (ctxEq_consSelf hmem)
      else
        combLaxCUp hUL (fun Ψ₀ => GbuIC G Ψ₀ (Form.circ (pf P)))
          (irrKit G (pf P) hg) dI Ψ
          (env.pushQ ((clo_circ_inv h').resolve_left hmem)
            (sfLnf_circ hms) (ndN_circ ndm)) hg ndg
          (fun _ _ _ irr => irr)
  | _, _, P, .impL (Q := Q) (N := N') dQ dRest, Ψ, env, hm, hms, ndm, hg, ndg =>
      have h' : Clo Ψ (.imp (pf Q) (nf N')) := nf_imp ▸ hm
      if hmem : Form.imp (pf Q) (nf N') ∈ Ψ then
        comb hUL (fun Ψ₀ => GbuIC G Ψ₀ (Form.circ (pf P))) (irrKit G (pf P) hg)
          dQ Ψ env (sfLnf_imp hms).1 (ndN_imp ndm).1
          (fun Ψ' hsub hu' irrQ =>
            .limpLI (transportIC irrQ (ctxEq_consSelf (hsub hmem)))
              (combSpineLaxI hUL dRest (nf N' :: Ψ')
                ((env.mono hsub hu').grow (hUL _ (sfLnf_imp hms).2))
                (.base List.mem_cons_self) (sfLnf_imp hms).2
                (ndN_imp ndm).2 hg ndg)
              (Or.inr (sfLnf_imp hms).1) hg (ctxEq_consSelf (hsub hmem)))
      else
        combSpineLaxI hUL dRest Ψ env ((clo_imp_inv h').resolve_left hmem)
          (sfLnf_imp hms).2 (ndN_imp ndm).2 hg ndg
  | _, _, _, .and1 (M := M₁) (N := M₂) dRest, Ψ, env, hm, hms, ndm, hg, ndg =>
      have h' : Clo Ψ (.and (nf M₁) (nf M₂)) := nf_and ▸ hm
      if hmem : Form.and (nf M₁) (nf M₂) ∈ Ψ then
        .landLI
          (combSpineLaxI hUL dRest (nf M₁ :: nf M₂ :: Ψ)
            ((env.grow (hUL _ (sfLnf_and hms).2)).grow
              (hUL _ (sfLnf_and hms).1))
            (.base List.mem_cons_self) (sfLnf_and hms).1 (ndN_and ndm).1
            hg ndg)
          hg (ctxEq_consSelf hmem)
      else
        combSpineLaxI hUL dRest Ψ env ((clo_and_inv h').resolve_left hmem).1
          (sfLnf_and hms).1 (ndN_and ndm).1 hg ndg
  | _, _, _, .and2 (M := M₁) (N := M₂) dRest, Ψ, env, hm, hms, ndm, hg, ndg =>
      have h' : Clo Ψ (.and (nf M₁) (nf M₂)) := nf_and ▸ hm
      if hmem : Form.and (nf M₁) (nf M₂) ∈ Ψ then
        .landLI
          (combSpineLaxI hUL dRest (nf M₁ :: nf M₂ :: Ψ)
            ((env.grow (hUL _ (sfLnf_and hms).2)).grow
              (hUL _ (sfLnf_and hms).1))
            (.base (List.mem_cons_of_mem _ List.mem_cons_self))
            (sfLnf_and hms).2 (ndN_and ndm).2 hg ndg)
          hg (ctxEq_consSelf hmem)
      else
        combSpineLaxI hUL dRest Ψ env ((clo_and_inv h').resolve_left hmem).2
          (sfLnf_and hms).2 (ndN_and ndm).2 hg ndg

termination_by _ _ _ d => (2 * wLF d, 0)
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | (apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left;
         first
           | omega
           | (simp only [wS, wRF, wLF, wI]; omega))

/-- The `R∧ᵢ` pair, fuel-founded on the missing-universe count. -/
def combPair (hUL : ∀ x ∈ sfL G, x ∈ U) (T : List Form → Type)
    (kit : Kit G T) :
    ∀ (fuel : Nat) {Γ : List Neg} {Ω : List Pos} {M N : Neg},
    Inv Γ Ω .tru M → Inv Γ Ω .tru N → ∀ (Ψ : List Form), Env G U Γ Ω Ψ →
    nf M ∈ sfR G → nf N ∈ sfR G → noDUN M = true → noDUN N = true →
    (U.filter (fun y => decide (y ∉ Ψ))).length < fuel →
    (∀ Ψ', Ψ ⊆ Ψ' → (∀ x ∈ Ψ', x ∈ U) →
      GbuIC G Ψ' (nf M) → GbuIC G Ψ' (nf N) → T Ψ') →
    T Ψ
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, hfuel, _ =>
      absurd hfuel (Nat.not_lt_zero _)
  | fuel + 1, _, _, _, _, d₁, d₂, Ψ, env, hg₁, hg₂, nd₁, nd₂, hfuel, k =>
      combInv hUL T kit d₁ Ψ env hg₁ nd₁ (fun Ψ₁ h₁ hu₁ irr₁ =>
        combInv hUL T kit d₂ Ψ₁ (env.mono h₁ hu₁) hg₂ nd₂
          (fun Ψ₂ h₂ hu₂ irr₂ =>
            if hstab : ∀ x ∈ Ψ₂, x ∈ Ψ₁ then
              k Ψ₂ (fun _ hx => h₂ (h₁ hx)) hu₂
                (transportIC irr₁ (fun y => ⟨fun hy => h₂ hy, hstab y⟩))
                irr₂
            else
              let ⟨x, hxΨ₂, hxΨ₁⟩ := findNotMem Ψ₂ Ψ₁ hstab
              combPair hUL T kit fuel d₁ d₂ Ψ₂
                (env.mono (fun _ hy => h₂ (h₁ hy)) hu₂) hg₁ hg₂ nd₁ nd₂
                (Nat.lt_of_lt_of_le
                  (satMeasure_lt (fun _ hy => h₂ (h₁ hy)) (hu₂ x hxΨ₂)
                    hxΨ₂ (fun hxΨ => hxΨ₁ (h₁ hxΨ)))
                  (Nat.lt_succ_iff.mp hfuel))
                (fun Ψ' h' hu' i1 i2 =>
                  k Ψ' (fun _ hy => h' (h₂ (h₁ hy))) hu' i1 i2)))

termination_by fuel _ _ _ _ d₁ d₂ => (2 * (wI d₁ + wI d₂) + 1, fuel)
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | (apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left;
         first
           | omega
           | (simp only [wS, wRF, wLF, wI]; omega))

/-- The regular translation: hoist, deliver, regularise. -/
def tInv (hUL : ∀ x ∈ sfL G, x ∈ U) :
    ∀ {Γ : List Neg} {Ω : List Pos} {N : Neg},
    Inv Γ Ω .tru N → ∀ (Ψ : List Form), Env G U Γ Ω Ψ →
    nf N ∈ sfR G → noDUN N = true → GbuRC G Ψ (nf N)
  | _, _, N, d, Ψ, env, hg, ndg =>
      combInv hUL (fun Ψ₀ => GbuRC G Ψ₀ (nf N)) (regKit G (nf N))
        d Ψ env hg ndg (fun _ _ _ irr => regOfIrr irr)

termination_by _ _ _ d => (2 * wI d + 1, 0)
decreasing_by
  all_goals simp_wf
  all_goals
    first
      | (apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left;
         first
           | omega
           | (simp only [wS, wRF, wLF, wI]; omega))

end

end Translation

/-! ## F4: completeness of `Gbu◯` -/

/-- Cast a regular derivation along a goal equation. -/
def castRC {G : Form} {Ψ : List Form} {X Y : Form} (d : GbuRC G Ψ X)
    (h : X = Y) : GbuRC G Ψ Y := h ▸ d

/-- The empty environment over the universe `Sf^L G`. -/
theorem Env.empty (G : Form) : Env G (sfL G) [] [] [] :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
   fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
   fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
   fun _ h => absurd h List.not_mem_nil⟩

/-- **F4 — `Gbu◯` is complete in itself**: every PLL theorem has a
regular `Gbu◯` derivation of its own translation.

    Nonempty (LaxND [] φ) → Nonempty ([] ⇒g ⌈φ⌉)   (G := ⌈φ⌉)

Composition: `bridge_iff` (focalization, `LJF/OBridge.lean`) gives the
LJF◯ derivation; `tInv` translates it; `nf_negOfO` rewrites the goal. -/
theorem gbuC_complete {φ : PLLFormula} (h : Nonempty (PLLND.LaxND [] φ)) :
    ProvableGbuC (ofPLL φ) := by
  obtain ⟨d⟩ := (LJFO.bridge_iff [] φ).mp h
  exact ⟨castRC
    (tInv (G := ofPLL φ) (U := sfL (ofPLL φ)) (fun _ hx => hx) d []
      (Env.empty _) (by rw [nf_negOfO]; exact sfR_self _) (noDUN_negOfO φ))
    (nf_negOfO φ)⟩

/--
info: 'FRJ.Gbu.LJFT.gbuC_complete' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms gbuC_complete

end FRJ.Gbu.LJFT
