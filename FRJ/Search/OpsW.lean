/-
# The FRJW calculus as an engine instance

`Ops G` (FRJ/Search/Core.lean) instantiated with the W-family
`FRJWr`/`FRJWi` (FRJ/CalculusW.lean).  A mechanical transcription of
the V-instance (`FRJ/Search/OpsV.lean`) — derivation-carrying rows, so
rule side conditions are discharged by `Decidable` instances at
insertion and a faithfulness bug is a type error — with exactly the
two rule-set changes of the W-family:

* `⊃∉` is DELETED: `stepNotInW` has no `.imp` branch;
* `Lift` is ADDED: from every regular row `Γ ⇒ C`, the irregular row
  `∅; Θ → C` with the MAXIMAL retained zone
  `Θ := (Ĝ G).filter (Clo Γ ·)` — mirroring `◯∉`'s canonical Θ; the
  engine's `th`-monotone subsumption makes the maximal row the general
  currency, exactly as for `◯∉`.  `Lift` rides in the `stepNotIn` slot
  of `Ops` (it is a not-in-style step, `RS → List IS`), so the shared
  loop in `Core.lean` is UNTOUCHED and the registered paper/V engines
  cannot be affected.

A hit is an `FRJWr` derivation: every hit is a `DisprovableW` witness
by construction (`soundnessW` then refutes PLL-validity).
-/
import FRJ.Search.Core
import FRJ.CalculusW

namespace FRJ.Search.W

open FRJ Form FRJ.Search

/-! ## Rows -/

structure WRS (G : Form) where
  t : Tag
  ctx : List Form
  rhs : Form
  der : FRJWr G t ctx rhs

structure WIS (G : Form) where
  stab : List Form
  th : List Form
  rhs : Form
  der : FRJWi G stab th rhs

/-! ## Seeds -/

def seedsRW (G : Form) : List (WRS G) :=
  (sfR G).filterMap (fun F =>
    if hF : F.isPrime then
      if hg : F ∈ sfR G then
        some ⟨.barren, rm (gAt G) F, F, .axR F hF hg (CtxEq.refl _)⟩
      else none
    else none)

def seedsIW (G : Form) : List (WIS G) :=
  (sfR G).filterMap (fun F =>
    if hF : F.isPrime then
      if hg : F ∈ sfR G then
        some ⟨[], (rm (gAt G) F) ++ gImp G ++ gCirc G, F,
          .axI F hF hg (CtxEq.refl _)⟩
      else none
    else none)

def seedsICW (G : Form) : List (WIS G) :=
  (sfR G).flatMap (fun C =>
    match C with
    | .circ F =>
      if hg : Form.circ F ∈ sfR G then
        let vals := if (gAt G).length ≤ 4 then (gAt G).sublists
          else [[], gAt G, rm (gAt G) F]
        vals.filterMap (fun ats =>
          if hats : ats ⊆ gAt G then
            if hFf : classForce ats F = false then
              some ⟨[], vacZoneA G ats, .circ F,
                .axIC F ats hats hFf hg (CtxEq.refl _)⟩
            else none
          else none)
      else []
    | _ => [])

/-! ## Single-premise rules -/

def stepR1W (G : Form) (r : WRS G) : List (WRS G) :=
  (sfR G).filterMap (fun T =>
    if hg : T ∈ sfR G then
      match T, hg with
      | .and A B, hg =>
          if h1 : r.rhs = A then
            some ⟨r.t, r.ctx, .and A B, .andR1 (h1 ▸ r.der) hg⟩
          else if h2 : r.rhs = B then
            some ⟨r.t, r.ctx, .and A B, .andR2 (h2 ▸ r.der) hg⟩
          else none
      | .imp A B, hg =>
          if h : r.rhs = B then
            if hA : Clo r.ctx A then
              some ⟨r.t, r.ctx, .imp A B, .impIn (h ▸ r.der) hA hg⟩
            else none
          else none
      | .circ Z, hg =>
          if h : r.rhs = Z then
            if ht : r.t = .barren ∨ ∃ W, r.t = .chain W ∧ Covers r.ctx W Z then
              some ⟨r.t, r.ctx, .circ Z, .circIn (h ▸ r.der) ht hg⟩
            else none
          else none
      | _, _ => none
    else none)

def stepI1W (G : Form) (i : WIS G) : List (WIS G) :=
  (sfR G).filterMap (fun T =>
    if hg : T ∈ sfR G then
      match T, hg with
      | .and A B, hg =>
          if h1 : i.rhs = A then
            some ⟨i.stab, i.th, .and A B, .andI1 (h1 ▸ i.der) hg⟩
          else if h2 : i.rhs = B then
            some ⟨i.stab, i.th, .and A B, .andI2 (h2 ▸ i.der) hg⟩
          else none
      | _, _ => none
    else none)

def stepOrIW (G : Form) (i1 i2 : WIS G) : List (WIS G) :=
  (sfR G).filterMap (fun T =>
    if hg : T ∈ sfR G then
      match T, hg with
      | .or C₁ C₂, hg =>
          if h1 : i1.rhs = C₁ then
            if h2 : i2.rhs = C₂ then
              if hs1 : i1.stab ⊆ i2.stab ++ i2.th then
                if hs2 : i2.stab ⊆ i1.stab ++ i1.th then
                  some ⟨i1.stab ++ i2.stab, cap i1.th i2.th, .or C₁ C₂,
                    .orI (h1 ▸ i1.der) (h2 ▸ i2.der) hs1 hs2 hg
                      (CtxEq.refl _) (CtxEq.refl _)⟩
                else none
              else none
            else none
          else none
      | _, _ => none
    else none)

def stepImpInIW (G : Form) (lamCap : Nat) (i : WIS G) : List (WIS G) × Bool :=
  let (lams, capped) := lamCandidates i.th lamCap
  (((sfR G).flatMap (fun T =>
    if hg : T ∈ sfR G then
      match T, hg with
      | .imp A B, hg =>
          if h : i.rhs = B then
            lams.filterMap (fun Λ =>
              if hΛ : ∀ x ∈ Λ, x ∈ i.th then
                if hA : Clo (i.stab ++ Λ) A then
                  some ⟨i.stab ++ Λ, FRJ.sdiff i.th Λ, .imp A B,
                    .impInI (h ▸ i.der) (zone_split hΛ) cap_sdiff_eq_nil hA hg
                      (CtxEq.refl _) (CtxEq.refl _)⟩
                else none
              else none)
          else []
      | _, _ => []
    else [])), capped)

/-- `◯∉` and `Lift` from one regular row (`⊃∉` is deleted in the
W-family).  Both use the maximal retained zone
`Θ := (Ĝ G).filter (Clo Γ ·)`. -/
def stepNotInW (G : Form) (r : WRS G) : List (WIS G) :=
  let Θ := (gHat G).filter (fun X => cloB r.ctx X)
  let liftRows : List (WIS G) :=
    if hTh : ∀ X ∈ Θ, Clo r.ctx X ∧ X ∈ gHat G then
      [⟨[], Θ, r.rhs, .lift r.der hTh⟩]
    else []
  let circRows : List (WIS G) :=
    (sfR G).flatMap (fun T =>
      if hg : T ∈ sfR G then
        match T, hg with
        | .circ Z, hg =>
            if h : r.rhs = Z then
              if ht : r.t = .barren ∨ ∃ W, r.t = .chain W ∧ Covers r.ctx W Z then
                if hTh : ∀ X ∈ Θ, Clo r.ctx X ∧ X ∈ gHat G then
                  [⟨[], Θ, .circ Z, .circNotIn (h ▸ r.der) ht hTh hg⟩]
                else []
              else []
            else []
        | _, _ => []
      else [])
  liftRows ++ circRows

/-! ## Joins -/

section Joins

variable {G : Form}

def stabFW (a : WIS G) (rest : List (WIS G)) : Fin (rest.length + 1) → List Form :=
  fun j => ((a :: rest).get j).stab

def thFW (a : WIS G) (rest : List (WIS G)) : Fin (rest.length + 1) → List Form :=
  fun j => ((a :: rest).get j).th

def rhsFW (a : WIS G) (rest : List (WIS G)) : Fin (rest.length + 1) → Form :=
  fun j => ((a :: rest).get j).rhs

def premFW (a : WIS G) (rest : List (WIS G)) :
    ∀ j, FRJWi G (stabFW a rest j) (thFW a rest j) (rhsFW a rest j) :=
  fun j => ((a :: rest).get j).der

def dctxFW (p : WRS G) (prest : List (WRS G)) : Fin (prest.length + 1) → List Form :=
  fun i => ((p :: prest).get i).ctx

def drhsFW (p : WRS G) (prest : List (WRS G)) : Fin (prest.length + 1) → Form :=
  fun i => ((p :: prest).get i).rhs

def dtagFW (p : WRS G) (prest : List (WRS G)) : Fin (prest.length + 1) → Tag :=
  fun i => ((p :: prest).get i).t

def dpsFW (p : WRS G) (prest : List (WRS G)) :
    ∀ i, FRJWr G (dtagFW p prest i) (dctxFW p prest i) (drhsFW p prest i) :=
  fun i => ((p :: prest).get i).der

def j1j2CheckW (a : WIS G) (rest : List (WIS G)) :
    Option (PLift ((∀ i j, i ≠ j → stabFW a rest i ⊆ stabFW a rest j ++ thFW a rest j) ∧
      (∀ X ∈ unionAll (fun j => impPart (stabFW a rest j)),
        ImpAnteOk (upsilon (rhsFW a rest)) X))) :=
  if h1 : ∀ i j, i ≠ j → stabFW a rest i ⊆ stabFW a rest j ++ thFW a rest j then
    if h2 : ∀ X ∈ unionAll (fun j => impPart (stabFW a rest j)),
        ImpAnteOk (upsilon (rhsFW a rest)) X then
      some ⟨h1, h2⟩
    else none
  else none

theorem hJ2_of_checkW {a : WIS G} {rest : List (WIS G)}
    (h : ∀ X ∈ unionAll (fun j => impPart (stabFW a rest j)),
      ImpAnteOk (upsilon (rhsFW a rest)) X) :
    ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stabFW a rest j)) →
      A ∈ upsilon (rhsFW a rest) :=
  fun _ _ hm => h _ hm

/-- The barren joins, RefAt-relaxed: the kept zone is the greedy chain
`keptOf`, certified by `keptOf_ok`; the `⋈^∨`/`⋈^◯` targets pass the
decidable `RefAt` test over the full conclusion context. -/
def mkJoinBarrenW (G : Form) (a : WIS G) (rest : List (WIS G)) : List (WRS G) :=
  match j1j2CheckW a rest with
  | none => []
  | some ⟨h1, h2⟩ =>
    if hcirc : unionAll (fun j => circPart (stabFW a rest j)) = [] then
      -- ⋈^At over prime targets
      ((sfR G).filterMap (fun F =>
        if hF : F.isPrime then
          if hFnot : F ∉ unionAll (fun j => atPart (stabFW a rest j)) then
            if hg : F ∈ sfR G then
              some ⟨.barren,
                joinCtxAtVBase (stabFW a rest) (thFW a rest) F ++
                  keptOf (upsilon (rhsFW a rest))
                    (joinCtxAtVBase (stabFW a rest) (thFW a rest) F)
                    (thPool (thFW a rest)), F,
                .joinAt (premFW a rest) h1 (hJ2_of_checkW h2) hcirc
                  (keptOf_ok _ _ _) hF hFnot hg (CtxEq.refl _)⟩
            else none
          else none
        else none)) ++
      -- ⋈^∨ and ⋈^◯ over disjunction / modal targets
      ((sfR G).filterMap (fun T =>
        if hg : T ∈ sfR G then
          match T, hg with
          | .or C₁ C₂, hg =>
              if hC : RefAt true (upsilon (rhsFW a rest))
                    (joinCtxOrVBase (stabFW a rest) (thFW a rest) ++
                      keptOf (upsilon (rhsFW a rest))
                        (joinCtxOrVBase (stabFW a rest) (thFW a rest))
                        (thPool (thFW a rest))) C₁ ∧
                  RefAt true (upsilon (rhsFW a rest))
                    (joinCtxOrVBase (stabFW a rest) (thFW a rest) ++
                      keptOf (upsilon (rhsFW a rest))
                        (joinCtxOrVBase (stabFW a rest) (thFW a rest))
                        (thPool (thFW a rest))) C₂ then
                some ⟨.barren,
                  joinCtxOrVBase (stabFW a rest) (thFW a rest) ++
                    keptOf (upsilon (rhsFW a rest))
                      (joinCtxOrVBase (stabFW a rest) (thFW a rest))
                      (thPool (thFW a rest)), .or C₁ C₂,
                  .joinOr (premFW a rest) h1 (hJ2_of_checkW h2) hcirc
                    (keptOf_ok _ _ _) hC hg (CtxEq.refl _)⟩
              else none
          | .circ Z, hg =>
              if hZ : RefAt true (upsilon (rhsFW a rest))
                    (joinCtxOrVBase (stabFW a rest) (thFW a rest) ++
                      keptOf (upsilon (rhsFW a rest))
                        (joinCtxOrVBase (stabFW a rest) (thFW a rest))
                        (thPool (thFW a rest))) Z then
                some ⟨.barren,
                  joinCtxOrVBase (stabFW a rest) (thFW a rest) ++
                    keptOf (upsilon (rhsFW a rest))
                      (joinCtxOrVBase (stabFW a rest) (thFW a rest))
                      (thPool (thFW a rest)), .circ Z,
                  .joinCirc (premFW a rest) h1
                    (fun A B h => .ups (hJ2_of_checkW h2 A B h)) hcirc
                    (keptOf_ok _ _ _) hZ hg (CtxEq.refl _)⟩
              else none
          | _, _ => none
        else none))
    else []

/-- The fallible joins — the paper rules, V-typed. -/
def mkJoinFW (G : Form) (a : WIS G) (rest : List (WIS G)) : List (WRS G) :=
  match j1j2CheckW a rest with
  | none => []
  | some ⟨h1, h2⟩ =>
    ((sfR G).filterMap (fun F =>
      if hF : F.isPrime then
        if hFnot : F ∉ unionAll (fun j => atPart (stabFW a rest j)) then
          if hg : F ∈ sfR G then
            some ⟨.blocked, joinCtxAtF (stabFW a rest) (thFW a rest) (rhsFW a rest) F, F,
              .joinAtF (premFW a rest) h1 (hJ2_of_checkW h2) hF hFnot hg (CtxEq.refl _)⟩
          else none
        else none
      else none)) ++
    ((sfR G).filterMap (fun T =>
      if hg : T ∈ sfR G then
        match T, hg with
        | .or C₁ C₂, hg =>
            if hC : C₁ ∈ upsilon (rhsFW a rest) ∧ C₂ ∈ upsilon (rhsFW a rest) then
              some ⟨.blocked, joinCtxOrF (stabFW a rest) (thFW a rest) (rhsFW a rest),
                .or C₁ C₂,
                .joinOrF (premFW a rest) h1 (hJ2_of_checkW h2) hC hg (CtxEq.refl _)⟩
            else none
        | _, _ => none
      else none))

/-- The promise joins — the paper rules, V-typed. -/
def mkJoinPW (G : Form) (a : WIS G) (rest : List (WIS G)) (p : WRS G)
    (prest : List (WRS G)) : List (WRS G) :=
  match j1j2CheckW a rest with
  | none => []
  | some ⟨h1, h2⟩ =>
    if h5 : ∀ X ∈ unionAll (fun j => circPart (stabFW a rest j)),
        CircBodyOk (dctxFW p prest) X then
      let hJ5 : ∀ Y : Form,
          Form.circ Y ∈ unionAll (fun j => circPart (stabFW a rest j)) →
          ∃ i, Clo (dctxFW p prest i) Y := fun _ hm => h5 _ hm
      if h7 : ∀ i j, ∀ X ∈ stabFW a rest j, Clo (dctxFW p prest i) X then
      let tags : List ((t' : Tag) ×'
          (t' = .blocked ∨ (t' = .chain (drhsFW p prest 0) ∧ ∀ i,
            drhsFW p prest i = drhsFW p prest 0 ∧
            (dtagFW p prest i = .barren ∨ ∃ W, dtagFW p prest i = .chain W ∧
              Covers (dctxFW p prest i) W (drhsFW p prest 0))))) :=
        ⟨.blocked, Or.inl rfl⟩ ::
        (if hch : ∀ i, drhsFW p prest i = drhsFW p prest 0 ∧
            (dtagFW p prest i = .barren ∨ ∃ W, dtagFW p prest i = .chain W ∧
              Covers (dctxFW p prest i) W (drhsFW p prest 0)) then
          [⟨.chain (drhsFW p prest 0), Or.inr ⟨rfl, hch⟩⟩]
        else [])
      (tags.flatMap (fun tg =>
        ((sfR G).filterMap (fun F =>
          if hF : F.isPrime then
            if hFnot : F ∉ unionAll (fun j => atPart (stabFW a rest j)) then
              if hg : F ∈ sfR G then
                some ⟨tg.1,
                  joinCtxAtP (stabFW a rest) (thFW a rest) (rhsFW a rest) F (dctxFW p prest), F,
                  .joinAtP (premFW a rest) (dpsFW p prest) h1 (hJ2_of_checkW h2)
                    hJ5 h7 tg.2 hF hFnot hg (CtxEq.refl _)⟩
              else none
            else none
          else none)) ++
        ((sfR G).filterMap (fun T =>
          if hg : T ∈ sfR G then
            match T, hg with
            | .or C₁ C₂, hg =>
                if hC : C₁ ∈ upsilon (rhsFW a rest) ∧ C₂ ∈ upsilon (rhsFW a rest) then
                  some ⟨tg.1,
                    joinCtxOrP (stabFW a rest) (thFW a rest) (rhsFW a rest) (dctxFW p prest),
                    .or C₁ C₂,
                    .joinOrP (premFW a rest) (dpsFW p prest) h1 (hJ2_of_checkW h2)
                      hJ5 h7 tg.2 hC hg (CtxEq.refl _)⟩
                else none
            | _, _ => none
          else none)))) ++
      ((sfR G).filterMap (fun T =>
        if hg : T ∈ sfR G then
          match T, hg with
          | .circ Z, hg =>
              if hZ : Z ∈ upsilon (rhsFW a rest) then
                if hDs : ∀ i, drhsFW p prest i = Z ∧
                    (dtagFW p prest i = .barren ∨ ∃ W, dtagFW p prest i = .chain W ∧
                      Covers (dctxFW p prest i) W Z) then
                  some ⟨.chain Z,
                    joinCtxOrP (stabFW a rest) (thFW a rest) (rhsFW a rest) (dctxFW p prest),
                    .circ Z,
                    .joinCircP (premFW a rest) (dpsFW p prest) h1 (hJ2_of_checkW h2)
                      hJ5 h7 hDs hZ hg (CtxEq.refl _)⟩
                else none
              else none
          | _, _ => none
        else none))
      else []
    else []

end Joins

/-! ## The instance -/

def wOps (G : Form) : Ops G where
  RS := WRS G
  IS := WIS G
  rsTag := (·.t)
  rsCtx := (·.ctx)
  rsRhs := (·.rhs)
  isStab := (·.stab)
  isTh := (·.th)
  isRhs := (·.rhs)
  seedsR := seedsRW G
  seedsI := seedsIW G ++ seedsICW G
  stepR1 := stepR1W G
  stepI1 := stepI1W G
  stepOrI := stepOrIW G
  stepImpInI := fun cap i => stepImpInIW G cap i
  stepNotIn := stepNotInW G
  mkJoinBarren := fun a rest => mkJoinBarrenW G a rest
  mkJoinF := fun a rest => mkJoinFW G a rest
  mkJoinP := fun a rest p prest => mkJoinPW G a rest p prest

/-- A hit in the W-engine is a `DisprovableW` witness. -/
theorem disprovableW_of_hit {G : Form} {r : WRS G} (h : r.rhs = G) :
    DisprovableW G :=
  ⟨r.t, r.ctx, ⟨cast (congrArg (fun X => FRJWr G r.t r.ctx X) h) r.der⟩⟩

end FRJ.Search.W
