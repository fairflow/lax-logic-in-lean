/-
# The repaired calculus as an engine instance

`Ops G` (FRJ/Search/Core.lean) instantiated with the RefAt calculus
`FRJVr`/`FRJVi` (FRJ/CalculusV.lean).  Everything is the paper
instance's code with the V constructors — derivation-carrying, so rule
side conditions are discharged by `Decidable` instances at insertion
and a faithfulness bug is a type error — except the barren joins:

* the conclusion context is `base ++ kept` where `kept` is the GREEDY
  chain `keptOf` of `FRJ/RefAt.lean`, whose certificate is the proved
  `keptOf_ok` — no decision procedure runs for the chain;
* the `⋈^∨`/`⋈^◯` targets are admitted by the decidable `RefAt` test
  over the full conclusion context.

A hit in this engine is an `FRJVr` derivation, so once `soundnessV`
lands every hit is sound by construction; no ground-truth sweep is
needed for the typed engine.
-/
import FRJ.Search.Core
import FRJ.CalculusV

namespace FRJ.Search.V

open FRJ Form FRJ.Search

/-! ## Rows -/

structure VRS (G : Form) where
  t : Tag
  ctx : List Form
  rhs : Form
  der : FRJVr G t ctx rhs

structure VIS (G : Form) where
  stab : List Form
  th : List Form
  rhs : Form
  der : FRJVi G stab th rhs

/-! ## Seeds -/

def seedsRV (G : Form) : List (VRS G) :=
  (sfR G).filterMap (fun F =>
    if hF : F.isPrime then
      if hg : F ∈ sfR G then
        some ⟨.barren, rm (gAt G) F, F, .axR F hF hg (CtxEq.refl _)⟩
      else none
    else none)

def seedsIV (G : Form) : List (VIS G) :=
  (sfR G).filterMap (fun F =>
    if hF : F.isPrime then
      if hg : F ∈ sfR G then
        some ⟨[], (rm (gAt G) F) ++ gImp G ++ gCirc G, F,
          .axI F hF hg (CtxEq.refl _)⟩
      else none
    else none)

def seedsICV (G : Form) : List (VIS G) :=
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

def stepR1V (G : Form) (r : VRS G) : List (VRS G) :=
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

def stepI1V (G : Form) (i : VIS G) : List (VIS G) :=
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

def stepOrIV (G : Form) (i1 i2 : VIS G) : List (VIS G) :=
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

def stepImpInIV (G : Form) (lamCap : Nat) (i : VIS G) : List (VIS G) × Bool :=
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

def stepNotInV (G : Form) (r : VRS G) : List (VIS G) :=
  (sfR G).flatMap (fun T =>
    if hg : T ∈ sfR G then
      match T, hg with
      | .imp A B, hg =>
          if h : r.rhs = B then
            if hA : Clo r.ctx A then
              (thetaCandidates G r.ctx A).filterMap (fun l =>
                let Θ := l.filter (fun x => decide (x ∈ gHat G))
                if hTh : ∀ X ∈ Θ, Clo r.ctx X ∧ X ∈ gHat G then
                  if hAnot : ¬ Clo Θ A then
                    some ⟨[], Θ, .imp A B,
                      .impNotIn (h ▸ r.der) hTh hA hAnot hg⟩
                  else none
                else none)
            else []
          else []
      | .circ Z, hg =>
          if h : r.rhs = Z then
            if ht : r.t = .barren ∨ ∃ W, r.t = .chain W ∧ Covers r.ctx W Z then
              let Θ := (gHat G).filter (fun X => cloB r.ctx X)
              if hTh : ∀ X ∈ Θ, Clo r.ctx X ∧ X ∈ gHat G then
                [⟨[], Θ, .circ Z, .circNotIn (h ▸ r.der) ht hTh hg⟩]
              else []
            else []
          else []
      | _, _ => []
    else [])

/-! ## Joins -/

section Joins

variable {G : Form}

def stabFV (a : VIS G) (rest : List (VIS G)) : Fin (rest.length + 1) → List Form :=
  fun j => ((a :: rest).get j).stab

def thFV (a : VIS G) (rest : List (VIS G)) : Fin (rest.length + 1) → List Form :=
  fun j => ((a :: rest).get j).th

def rhsFV (a : VIS G) (rest : List (VIS G)) : Fin (rest.length + 1) → Form :=
  fun j => ((a :: rest).get j).rhs

def premFV (a : VIS G) (rest : List (VIS G)) :
    ∀ j, FRJVi G (stabFV a rest j) (thFV a rest j) (rhsFV a rest j) :=
  fun j => ((a :: rest).get j).der

def dctxFV (p : VRS G) (prest : List (VRS G)) : Fin (prest.length + 1) → List Form :=
  fun i => ((p :: prest).get i).ctx

def drhsFV (p : VRS G) (prest : List (VRS G)) : Fin (prest.length + 1) → Form :=
  fun i => ((p :: prest).get i).rhs

def dtagFV (p : VRS G) (prest : List (VRS G)) : Fin (prest.length + 1) → Tag :=
  fun i => ((p :: prest).get i).t

def dpsFV (p : VRS G) (prest : List (VRS G)) :
    ∀ i, FRJVr G (dtagFV p prest i) (dctxFV p prest i) (drhsFV p prest i) :=
  fun i => ((p :: prest).get i).der

def j1j2CheckV (a : VIS G) (rest : List (VIS G)) :
    Option (PLift ((∀ i j, i ≠ j → stabFV a rest i ⊆ stabFV a rest j ++ thFV a rest j) ∧
      (∀ X ∈ unionAll (fun j => impPart (stabFV a rest j)),
        ImpAnteOk (upsilon (rhsFV a rest)) X))) :=
  if h1 : ∀ i j, i ≠ j → stabFV a rest i ⊆ stabFV a rest j ++ thFV a rest j then
    if h2 : ∀ X ∈ unionAll (fun j => impPart (stabFV a rest j)),
        ImpAnteOk (upsilon (rhsFV a rest)) X then
      some ⟨h1, h2⟩
    else none
  else none

theorem hJ2_of_checkV {a : VIS G} {rest : List (VIS G)}
    (h : ∀ X ∈ unionAll (fun j => impPart (stabFV a rest j)),
      ImpAnteOk (upsilon (rhsFV a rest)) X) :
    ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stabFV a rest j)) →
      A ∈ upsilon (rhsFV a rest) :=
  fun _ _ hm => h _ hm

/-- The barren joins, RefAt-relaxed: the kept zone is the greedy chain
`keptOf`, certified by `keptOf_ok`; the `⋈^∨`/`⋈^◯` targets pass the
decidable `RefAt` test over the full conclusion context. -/
def mkJoinBarrenV (G : Form) (a : VIS G) (rest : List (VIS G)) : List (VRS G) :=
  match j1j2CheckV a rest with
  | none => []
  | some ⟨h1, h2⟩ =>
    if hcirc : unionAll (fun j => circPart (stabFV a rest j)) = [] then
      -- ⋈^At over prime targets
      ((sfR G).filterMap (fun F =>
        if hF : F.isPrime then
          if hFnot : F ∉ unionAll (fun j => atPart (stabFV a rest j)) then
            if hg : F ∈ sfR G then
              some ⟨.barren,
                joinCtxAtVBase (stabFV a rest) (thFV a rest) F ++
                  keptOf (upsilon (rhsFV a rest))
                    (joinCtxAtVBase (stabFV a rest) (thFV a rest) F)
                    (thPool (thFV a rest)), F,
                .joinAt (premFV a rest) h1 (hJ2_of_checkV h2) hcirc
                  (keptOf_ok _ _ _) hF hFnot hg (CtxEq.refl _)⟩
            else none
          else none
        else none)) ++
      -- ⋈^∨ and ⋈^◯ over disjunction / modal targets
      ((sfR G).filterMap (fun T =>
        if hg : T ∈ sfR G then
          match T, hg with
          | .or C₁ C₂, hg =>
              if hC : RefAt true (upsilon (rhsFV a rest))
                    (joinCtxOrVBase (stabFV a rest) (thFV a rest) ++
                      keptOf (upsilon (rhsFV a rest))
                        (joinCtxOrVBase (stabFV a rest) (thFV a rest))
                        (thPool (thFV a rest))) C₁ ∧
                  RefAt true (upsilon (rhsFV a rest))
                    (joinCtxOrVBase (stabFV a rest) (thFV a rest) ++
                      keptOf (upsilon (rhsFV a rest))
                        (joinCtxOrVBase (stabFV a rest) (thFV a rest))
                        (thPool (thFV a rest))) C₂ then
                some ⟨.barren,
                  joinCtxOrVBase (stabFV a rest) (thFV a rest) ++
                    keptOf (upsilon (rhsFV a rest))
                      (joinCtxOrVBase (stabFV a rest) (thFV a rest))
                      (thPool (thFV a rest)), .or C₁ C₂,
                  .joinOr (premFV a rest) h1 (hJ2_of_checkV h2) hcirc
                    (keptOf_ok _ _ _) hC hg (CtxEq.refl _)⟩
              else none
          | .circ Z, hg =>
              if hZ : RefAt true (upsilon (rhsFV a rest))
                    (joinCtxOrVBase (stabFV a rest) (thFV a rest) ++
                      keptOf (upsilon (rhsFV a rest))
                        (joinCtxOrVBase (stabFV a rest) (thFV a rest))
                        (thPool (thFV a rest))) Z then
                some ⟨.barren,
                  joinCtxOrVBase (stabFV a rest) (thFV a rest) ++
                    keptOf (upsilon (rhsFV a rest))
                      (joinCtxOrVBase (stabFV a rest) (thFV a rest))
                      (thPool (thFV a rest)), .circ Z,
                  .joinCirc (premFV a rest) h1 (hJ2_of_checkV h2) hcirc
                    (keptOf_ok _ _ _) hZ hg (CtxEq.refl _)⟩
              else none
          | _, _ => none
        else none))
    else []

/-- The fallible joins — the paper rules, V-typed. -/
def mkJoinFV (G : Form) (a : VIS G) (rest : List (VIS G)) : List (VRS G) :=
  match j1j2CheckV a rest with
  | none => []
  | some ⟨h1, h2⟩ =>
    ((sfR G).filterMap (fun F =>
      if hF : F.isPrime then
        if hFnot : F ∉ unionAll (fun j => atPart (stabFV a rest j)) then
          if hg : F ∈ sfR G then
            some ⟨.blocked, joinCtxAtF (stabFV a rest) (thFV a rest) (rhsFV a rest) F, F,
              .joinAtF (premFV a rest) h1 (hJ2_of_checkV h2) hF hFnot hg (CtxEq.refl _)⟩
          else none
        else none
      else none)) ++
    ((sfR G).filterMap (fun T =>
      if hg : T ∈ sfR G then
        match T, hg with
        | .or C₁ C₂, hg =>
            if hC : C₁ ∈ upsilon (rhsFV a rest) ∧ C₂ ∈ upsilon (rhsFV a rest) then
              some ⟨.blocked, joinCtxOrF (stabFV a rest) (thFV a rest) (rhsFV a rest),
                .or C₁ C₂,
                .joinOrF (premFV a rest) h1 (hJ2_of_checkV h2) hC hg (CtxEq.refl _)⟩
            else none
        | _, _ => none
      else none))

/-- The promise joins — the paper rules, V-typed. -/
def mkJoinPV (G : Form) (a : VIS G) (rest : List (VIS G)) (p : VRS G)
    (prest : List (VRS G)) : List (VRS G) :=
  match j1j2CheckV a rest with
  | none => []
  | some ⟨h1, h2⟩ =>
    if h5 : ∀ X ∈ unionAll (fun j => circPart (stabFV a rest j)),
        CircBodyOk (dctxFV p prest) X then
      let hJ5 : ∀ Y : Form,
          Form.circ Y ∈ unionAll (fun j => circPart (stabFV a rest j)) →
          ∃ i, Clo (dctxFV p prest i) Y := fun _ hm => h5 _ hm
      if h7 : ∀ i j, ∀ X ∈ stabFV a rest j, Clo (dctxFV p prest i) X then
      let tags : List ((t' : Tag) ×'
          (t' = .blocked ∨ (t' = .chain (drhsFV p prest 0) ∧ ∀ i,
            drhsFV p prest i = drhsFV p prest 0 ∧
            (dtagFV p prest i = .barren ∨ ∃ W, dtagFV p prest i = .chain W ∧
              Covers (dctxFV p prest i) W (drhsFV p prest 0))))) :=
        ⟨.blocked, Or.inl rfl⟩ ::
        (if hch : ∀ i, drhsFV p prest i = drhsFV p prest 0 ∧
            (dtagFV p prest i = .barren ∨ ∃ W, dtagFV p prest i = .chain W ∧
              Covers (dctxFV p prest i) W (drhsFV p prest 0)) then
          [⟨.chain (drhsFV p prest 0), Or.inr ⟨rfl, hch⟩⟩]
        else [])
      (tags.flatMap (fun tg =>
        ((sfR G).filterMap (fun F =>
          if hF : F.isPrime then
            if hFnot : F ∉ unionAll (fun j => atPart (stabFV a rest j)) then
              if hg : F ∈ sfR G then
                some ⟨tg.1,
                  joinCtxAtP (stabFV a rest) (thFV a rest) (rhsFV a rest) F (dctxFV p prest), F,
                  .joinAtP (premFV a rest) (dpsFV p prest) h1 (hJ2_of_checkV h2)
                    hJ5 h7 tg.2 hF hFnot hg (CtxEq.refl _)⟩
              else none
            else none
          else none)) ++
        ((sfR G).filterMap (fun T =>
          if hg : T ∈ sfR G then
            match T, hg with
            | .or C₁ C₂, hg =>
                if hC : C₁ ∈ upsilon (rhsFV a rest) ∧ C₂ ∈ upsilon (rhsFV a rest) then
                  some ⟨tg.1,
                    joinCtxOrP (stabFV a rest) (thFV a rest) (rhsFV a rest) (dctxFV p prest),
                    .or C₁ C₂,
                    .joinOrP (premFV a rest) (dpsFV p prest) h1 (hJ2_of_checkV h2)
                      hJ5 h7 tg.2 hC hg (CtxEq.refl _)⟩
                else none
            | _, _ => none
          else none)))) ++
      ((sfR G).filterMap (fun T =>
        if hg : T ∈ sfR G then
          match T, hg with
          | .circ Z, hg =>
              if hZ : Z ∈ upsilon (rhsFV a rest) then
                if hDs : ∀ i, drhsFV p prest i = Z ∧
                    (dtagFV p prest i = .barren ∨ ∃ W, dtagFV p prest i = .chain W ∧
                      Covers (dctxFV p prest i) W Z) then
                  some ⟨.chain Z,
                    joinCtxOrP (stabFV a rest) (thFV a rest) (rhsFV a rest) (dctxFV p prest),
                    .circ Z,
                    .joinCircP (premFV a rest) (dpsFV p prest) h1 (hJ2_of_checkV h2)
                      hJ5 h7 hDs hZ hg (CtxEq.refl _)⟩
                else none
              else none
          | _, _ => none
        else none))
      else []
    else []

end Joins

/-! ## The instance -/

def vOps (G : Form) : Ops G where
  RS := VRS G
  IS := VIS G
  rsTag := (·.t)
  rsCtx := (·.ctx)
  rsRhs := (·.rhs)
  isStab := (·.stab)
  isTh := (·.th)
  isRhs := (·.rhs)
  seedsR := seedsRV G
  seedsI := seedsIV G ++ seedsICV G
  stepR1 := stepR1V G
  stepI1 := stepI1V G
  stepOrI := stepOrIV G
  stepImpInI := fun cap i => stepImpInIV G cap i
  stepNotIn := stepNotInV G
  mkJoinBarren := fun a rest => mkJoinBarrenV G a rest
  mkJoinF := fun a rest => mkJoinFV G a rest
  mkJoinP := fun a rest p prest => mkJoinPV G a rest p prest

/-- A hit in the V-engine is a `ProvableV` witness. -/
theorem provableV_of_hit {G : Form} {r : VRS G} (h : r.rhs = G) : ProvableV G :=
  ⟨r.t, r.ctx, ⟨cast (congrArg (fun X => FRJVr G r.t r.ctx X) h) r.der⟩⟩

end FRJ.Search.V
