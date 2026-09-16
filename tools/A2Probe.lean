/-
# `a2probe` — the arity question (A2), as a compiled probe

The practical decision-procedure campaign (2026-09-02, Matthew: "Go
ahead with the A2 probe").  The question, refute-first:

    A2.  Is the store saturated under join families of arity ≤ k
         (and promise families of arity ≤ k) already closed under the
         join clauses of `DBClosed` at EVERY arity — i.e. is every
         higher-arity join's conclusion subsumed by a stored row?

If A2 holds at a small `k` on the corpus, a checker for `DBClosed` can
enumerate bounded families only and the bounded-check-suffices theorem
is the one to scope.  If it fails, the witness is a family of stored
irregular rows whose join conclusion no stored row subsumes.

What this file computes, per cell `G` and per bound `k = 1..K`:

  * `db_k` — the saturation of the CORE non-join emitters
    (`FRJ/Gbu/W/Saturate.lean`, unchanged) together with copies of the
    eight join emitters restricted to families of size ≤ k.  The copies
    are verbatim except for the family list, so every emitted row still
    carries its `FRJW` derivation: `db_k : List (WRow G)`.
  * the ladder — the CORE-shaped join emitters at families of EXACT
    size m, m = k+1 .. M, over `db_k`; a row none of `db_k` subsumes is
    an A2 witness at arity m.
  * the full check — `stepAll G db_k` (the core emitters, all arities)
    when its family count is inside `--budget`; every row must be
    subsumed.  Reported as SKIPPED (with the count) when not.
  * the engine comparison — `saturateO (wOps G)` at `jmax = pmax = k`
    with the other caps lifted, its rows against `db_k` both ways under
    subsumption.  This is the strict-vs-relaxed gap (A3) in miniature:
    engine rows no probe row subsumes, and probe rows no engine row
    subsumes.

Verdicts per cell (three-valued):
  * `PASS k`  — the full check passed at bound k (minimal such k).
  * `FAIL k m` — an unsubsumed join row of arity m over `db_k` at the
    largest bound tried; the witness is printed.
  * `FLAG`    — no witness up to the ladder's reach but the full check
    was skipped at every k: re-run with a larger budget, never drop.

Untrusted engineering evidence: nothing here is pinned; the stores are
derivation-carrying by construction, the subsumption test is a Boolean
mirror of `WSubsumes`.  One cell per invocation so the shell can impose
a real timeout:

    lake exe a2probe <cell-index> [--K=4] [--M=6] [--budget=22]

`--budget=b` allows a full check when the family count is ≤ 2^b.
-/
import FRJ.Gbu.W.Saturate
import FRJ.Search.OpsW
import FRJ.Bridge

open FRJ FRJ.Gbu.W Form

namespace A2Probe

/-! ## Family enumerators -/

/-- All sublists of exact length `n`, order preserved. -/
def sublistsLen {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | n + 1, a :: as => (sublistsLen n as).map (a :: ·) ++ sublistsLen (n + 1) as

/-- All sublists of length `1 .. k`. -/
def sublistsUpTo {α : Type} (k : Nat) (l : List α) : List (List α) :=
  (List.range k).flatMap (fun m => sublistsLen (m + 1) l)

/-- `C(n, m)`. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, m + 1 => choose n m + choose n (m + 1)

/-! ## The join emitters, parametrised by the family list

Verbatim copies of `emitJoin*` in `FRJ/Gbu/W/Saturate.lean` (S4), with
`(irrTs db).sublists` replaced by `fams` and `(regTs db).sublists` by
`pfams`.  Nothing else differs, so the derivations are built by the
same constructors with the same guards. -/

section JoinOn

variable (G : Form) (fams : List (List (IrrT G)))

def joinCircOn : List (WRow G) :=
  fams.flatMap (fun l =>
    match l with
    | [] => []
    | a :: t =>
        let stabF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Ξ
        let thF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Θ
        let rhsF : Fin (t.length + 1) → Form :=
          fun j => ((a :: t).get j).C
        let base := joinCtxOrVBase stabF thF
        let kept := keptOf (upsilon rhsF) base (thPool thF)
        (goalPool G).filterMap (fun X =>
          match X with
          | .circ Z =>
              if h : (∀ i j, i ≠ j → stabF i ⊆ stabF j ++ thF j) ∧
                  (∀ x ∈ unionAll (fun j => impPart (stabF j)), ∀ A B : Form,
                    x = Form.imp A B →
                    RefAt true (upsilon rhsF) (base ++ kept) A) ∧
                  unionAll (fun j => circPart (stabF j)) = [] ∧
                  RefAt true (upsilon rhsF) (base ++ kept) Z ∧
                  Form.circ Z ∈ sfR G then
                some ⟨.reg .barren (base ++ kept) (.circ Z),
                  .joinCirc (fun j => ((a :: t).get j).d) h.1
                    (impGuard_elim h.2.1) h.2.2.1 (keptOf_ok _ _ _)
                    h.2.2.2.1 h.2.2.2.2 (CtxEq.refl _)⟩
              else none
          | _ => none))

def joinOrOn : List (WRow G) :=
  fams.flatMap (fun l =>
    match l with
    | [] => []
    | a :: t =>
        let stabF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Ξ
        let thF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Θ
        let rhsF : Fin (t.length + 1) → Form :=
          fun j => ((a :: t).get j).C
        let base := joinCtxOrVBase stabF thF
        let kept := keptOf (upsilon rhsF) base (thPool thF)
        (goalPool G).filterMap (fun X =>
          match X with
          | .or C₁ C₂ =>
              if h : (∀ i j, i ≠ j → stabF i ⊆ stabF j ++ thF j) ∧
                  (∀ x ∈ unionAll (fun j => impPart (stabF j)), ∀ A B : Form,
                    x = Form.imp A B → A ∈ upsilon rhsF) ∧
                  unionAll (fun j => circPart (stabF j)) = [] ∧
                  (RefAt true (upsilon rhsF) (base ++ kept) C₁ ∧
                    RefAt true (upsilon rhsF) (base ++ kept) C₂) ∧
                  Form.or C₁ C₂ ∈ sfR G then
                some ⟨.reg .barren (base ++ kept) (.or C₁ C₂),
                  .joinOr (fun j => ((a :: t).get j).d) h.1
                    (impGuard_elim h.2.1) h.2.2.1 (keptOf_ok _ _ _)
                    h.2.2.2.1 h.2.2.2.2 (CtxEq.refl _)⟩
              else none
          | _ => none))

def joinAtOn : List (WRow G) :=
  fams.flatMap (fun l =>
    match l with
    | [] => []
    | a :: t =>
        let stabF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Ξ
        let thF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Θ
        let rhsF : Fin (t.length + 1) → Form :=
          fun j => ((a :: t).get j).C
        (goalPool G).filterMap (fun F =>
          let base := joinCtxAtVBase stabF thF F
          let kept := keptOf (upsilon rhsF) base (thPool thF)
          if h : (∀ i j, i ≠ j → stabF i ⊆ stabF j ++ thF j) ∧
              (∀ x ∈ unionAll (fun j => impPart (stabF j)), ∀ A B : Form,
                x = Form.imp A B → A ∈ upsilon rhsF) ∧
              unionAll (fun j => circPart (stabF j)) = [] ∧
              F.isPrime = true ∧
              F ∉ unionAll (fun j => atPart (stabF j)) ∧
              F ∈ sfR G then
            some ⟨.reg .barren (base ++ kept) F,
              .joinAt (fun j => ((a :: t).get j).d) h.1
                (impGuard_elim h.2.1) h.2.2.1 (keptOf_ok _ _ _)
                h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 (CtxEq.refl _)⟩
          else none))

def joinAtFOn : List (WRow G) :=
  fams.flatMap (fun l =>
    match l with
    | [] => []
    | a :: t =>
        let stabF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Ξ
        let thF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Θ
        let rhsF : Fin (t.length + 1) → Form :=
          fun j => ((a :: t).get j).C
        (goalPool G).filterMap (fun F =>
          if h : (∀ i j, i ≠ j → stabF i ⊆ stabF j ++ thF j) ∧
              (∀ x ∈ unionAll (fun j => impPart (stabF j)), ∀ A B : Form,
                x = Form.imp A B → A ∈ upsilon rhsF) ∧
              F.isPrime = true ∧
              F ∉ unionAll (fun j => atPart (stabF j)) ∧
              F ∈ sfR G then
            some ⟨.reg .blocked (joinCtxAtF stabF thF rhsF F) F,
              .joinAtF (fun j => ((a :: t).get j).d) h.1
                (impGuard_elim h.2.1) h.2.2.1 h.2.2.2.1 h.2.2.2.2
                (CtxEq.refl _)⟩
          else none))

def joinOrFOn : List (WRow G) :=
  fams.flatMap (fun l =>
    match l with
    | [] => []
    | a :: t =>
        let stabF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Ξ
        let thF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Θ
        let rhsF : Fin (t.length + 1) → Form :=
          fun j => ((a :: t).get j).C
        (goalPool G).filterMap (fun X =>
          match X with
          | .or C₁ C₂ =>
              if h : (∀ i j, i ≠ j → stabF i ⊆ stabF j ++ thF j) ∧
                  (∀ x ∈ unionAll (fun j => impPart (stabF j)), ∀ A B : Form,
                    x = Form.imp A B → A ∈ upsilon rhsF) ∧
                  (C₁ ∈ upsilon rhsF ∧ C₂ ∈ upsilon rhsF) ∧
                  Form.or C₁ C₂ ∈ sfR G then
                some ⟨.reg .blocked (joinCtxOrF stabF thF rhsF) (.or C₁ C₂),
                  .joinOrF (fun j => ((a :: t).get j).d) h.1
                    (impGuard_elim h.2.1) h.2.2.1 h.2.2.2 (CtxEq.refl _)⟩
              else none
          | _ => none))

variable (pfams : List (List (RegT G)))

def joinAtPOn : List (WRow G) :=
  fams.flatMap (fun l =>
    match l with
    | [] => []
    | a :: t =>
        let stabF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Ξ
        let thF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Θ
        let rhsF : Fin (t.length + 1) → Form :=
          fun j => ((a :: t).get j).C
        pfams.flatMap (fun lr =>
          match lr with
          | [] => []
          | b :: u =>
              let tpsF : Fin (u.length + 1) → Tag :=
                fun i => ((b :: u).get i).t
              let ΔsF : Fin (u.length + 1) → List Form :=
                fun i => ((b :: u).get i).Γ
              let DsF : Fin (u.length + 1) → Form :=
                fun i => ((b :: u).get i).C
              (goalPool G).filterMap (fun F =>
                if h : (∀ i j, i ≠ j → stabF i ⊆ stabF j ++ thF j) ∧
                    (∀ x ∈ unionAll (fun j => impPart (stabF j)),
                      ∀ A B : Form, x = Form.imp A B → A ∈ upsilon rhsF) ∧
                    (∀ x ∈ unionAll (fun j => circPart (stabF j)),
                      ∀ Y : Form, x = Form.circ Y → ∃ i, Clo (ΔsF i) Y) ∧
                    (∀ i j, ∀ X ∈ stabF j, Clo (ΔsF i) X) ∧
                    (∀ i, DsF i = DsF 0 ∧
                      (tpsF i = .barren ∨ ∃ W, tpsF i = .chain W ∧
                        Covers (ΔsF i) W (DsF 0))) ∧
                    F.isPrime = true ∧
                    F ∉ unionAll (fun j => atPart (stabF j)) ∧
                    F ∈ sfR G then
                  some ⟨.reg (.chain (DsF 0))
                      (joinCtxAtP stabF thF rhsF F ΔsF) F,
                    .joinAtP (fun j => ((a :: t).get j).d)
                      (fun i => ((b :: u).get i).d) h.1
                      (impGuard_elim h.2.1) (circGuard_elim h.2.2.1)
                      h.2.2.2.1 (Or.inr ⟨rfl, h.2.2.2.2.1⟩)
                      h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2
                      (CtxEq.refl _)⟩
                else none)))

def joinOrPOn : List (WRow G) :=
  fams.flatMap (fun l =>
    match l with
    | [] => []
    | a :: t =>
        let stabF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Ξ
        let thF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Θ
        let rhsF : Fin (t.length + 1) → Form :=
          fun j => ((a :: t).get j).C
        pfams.flatMap (fun lr =>
          match lr with
          | [] => []
          | b :: u =>
              let tpsF : Fin (u.length + 1) → Tag :=
                fun i => ((b :: u).get i).t
              let ΔsF : Fin (u.length + 1) → List Form :=
                fun i => ((b :: u).get i).Γ
              let DsF : Fin (u.length + 1) → Form :=
                fun i => ((b :: u).get i).C
              (goalPool G).filterMap (fun X =>
                match X with
                | .or C₁ C₂ =>
                    if h : (∀ i j, i ≠ j → stabF i ⊆ stabF j ++ thF j) ∧
                        (∀ x ∈ unionAll (fun j => impPart (stabF j)),
                          ∀ A B : Form, x = Form.imp A B →
                            A ∈ upsilon rhsF) ∧
                        (∀ x ∈ unionAll (fun j => circPart (stabF j)),
                          ∀ Y : Form, x = Form.circ Y →
                            ∃ i, Clo (ΔsF i) Y) ∧
                        (∀ i j, ∀ X ∈ stabF j, Clo (ΔsF i) X) ∧
                        (∀ i, DsF i = DsF 0 ∧
                          (tpsF i = .barren ∨ ∃ W, tpsF i = .chain W ∧
                            Covers (ΔsF i) W (DsF 0))) ∧
                        (C₁ ∈ upsilon rhsF ∧ C₂ ∈ upsilon rhsF) ∧
                        Form.or C₁ C₂ ∈ sfR G then
                      some ⟨.reg (.chain (DsF 0))
                          (joinCtxOrP stabF thF rhsF ΔsF) (.or C₁ C₂),
                        .joinOrP (fun j => ((a :: t).get j).d)
                          (fun i => ((b :: u).get i).d) h.1
                          (impGuard_elim h.2.1) (circGuard_elim h.2.2.1)
                          h.2.2.2.1 (Or.inr ⟨rfl, h.2.2.2.2.1⟩)
                          h.2.2.2.2.2.1 h.2.2.2.2.2.2 (CtxEq.refl _)⟩
                    else none
                | _ => none)))

def joinCircPOn : List (WRow G) :=
  fams.flatMap (fun l =>
    match l with
    | [] => []
    | a :: t =>
        let stabF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Ξ
        let thF : Fin (t.length + 1) → List Form :=
          fun j => ((a :: t).get j).Θ
        let rhsF : Fin (t.length + 1) → Form :=
          fun j => ((a :: t).get j).C
        pfams.flatMap (fun lr =>
          match lr with
          | [] => []
          | b :: u =>
              let tpsF : Fin (u.length + 1) → Tag :=
                fun i => ((b :: u).get i).t
              let ΔsF : Fin (u.length + 1) → List Form :=
                fun i => ((b :: u).get i).Γ
              let DsF : Fin (u.length + 1) → Form :=
                fun i => ((b :: u).get i).C
              (goalPool G).filterMap (fun X =>
                match X with
                | .circ Z =>
                    if h : (∀ i j, i ≠ j → stabF i ⊆ stabF j ++ thF j) ∧
                        (∀ x ∈ unionAll (fun j => impPart (stabF j)),
                          ∀ A B : Form, x = Form.imp A B →
                            A ∈ upsilon rhsF) ∧
                        (∀ x ∈ unionAll (fun j => circPart (stabF j)),
                          ∀ Y : Form, x = Form.circ Y →
                            ∃ i, Clo (ΔsF i) Y) ∧
                        (∀ i j, ∀ X ∈ stabF j, Clo (ΔsF i) X) ∧
                        (∀ i, DsF i = Z ∧
                          (tpsF i = .barren ∨ ∃ W, tpsF i = .chain W ∧
                            Covers (ΔsF i) W Z)) ∧
                        Z ∈ upsilon rhsF ∧
                        Form.circ Z ∈ sfR G then
                      some ⟨.reg (.chain Z)
                          (joinCtxOrP stabF thF rhsF ΔsF) (.circ Z),
                        .joinCircP (fun j => ((a :: t).get j).d)
                          (fun i => ((b :: u).get i).d) h.1
                          (impGuard_elim h.2.1) (circGuard_elim h.2.2.1)
                          h.2.2.2.1 h.2.2.2.2.1
                          h.2.2.2.2.2.1 h.2.2.2.2.2.2 (CtxEq.refl _)⟩
                    else none
                | _ => none)))

/-- The barren and fallible joins over a family list. -/
def joinsBF : List (WRow G) :=
  joinAtOn G fams ++ joinOrOn G fams ++ joinCircOn G fams ++
    joinAtFOn G fams ++ joinOrFOn G fams

/-- The promise joins over a family list and a promise-family list. -/
def joinsP : List (WRow G) :=
  joinAtPOn G fams pfams ++ joinOrPOn G fams pfams ++ joinCircPOn G fams pfams

end JoinOn

/-! ## The bounded saturation -/

/-- The core non-join emitters, exactly as `emitters` lists them. -/
def nonJoin (G : Form) (db : List (WRow G)) : List (WRow G) :=
  [emitAxR G, emitAxI G, emitAxIC G,
    emitAndR G db, emitImpIn G db, emitCircIn G db,
    emitAndI G db, emitOrI G db, emitImpInI G db,
    emitLift G db, emitCircNotIn G db].flatten

/-- One round with join families of size ≤ k and promise families of
size ≤ kp.  `nop = true` drops the promise joins.  Exact for `◯`-free `G`: the
promise joins produce `chain`-tagged rows, which subsume no `barren`
row (`tagLeB`) and are consumed only by `◯∈` and the promise joins
themselves, so with no `◯` in `Sf^R G` they never reach a barren
conclusion. -/
def stepK (G : Form) (nop : Bool) (k kp : Nat) (db : List (WRow G)) : List (WRow G) :=
  let fams := sublistsUpTo k (irrTs db)
  let pfams := if nop then [] else sublistsUpTo kp (regTs db)
  nonJoin G db ++ joinsBF G fams ++ joinsP G fams pfams

def stepNewK (G : Form) (nop : Bool) (k kp : Nat) (db : List (WRow G)) : List (WRow G) :=
  (stepK G nop k kp db).filter (fun r => decide (keyOf G r ∉ keysOf G db))

/-- Saturate to the fixpoint (the pigeonhole of S6 bounds the rounds;
`fuel` only guards the loop).  Returns the store and the rounds used. -/
def satK (G : Form) (nop : Bool) (k kp : Nat) : Nat → List (WRow G) → Nat → List (WRow G) × Nat
  | 0, db, n => (db, n)
  | fuel + 1, db, n =>
      let new := stepNewK G nop k kp db
      if new.isEmpty then (db, n) else satK G nop k kp fuel (insertNew G new db) (n + 1)

/-- The full step without promise joins: every family of the irregular
store. -/
def stepAllNoP (G : Form) (db : List (WRow G)) : List (WRow G) :=
  nonJoin G db ++ joinsBF G ((irrTs db).sublists)

/-! ## Subsumption, as a Boolean -/

def subB (l m : List Form) : Bool := l.all (fun x => decide (x ∈ m))
def ctxEqB (l m : List Form) : Bool := subB l m && subB m l

/-- Boolean mirror of `WSubsumes` (`FRJ/Gbu/W/Dichotomy.lean`). -/
def wsubB : WSeq → WSeq → Bool
  | .reg t₁ Γ₁ C₁, .reg t₂ Γ₂ C₂ =>
      decide (C₁ = C₂) && FRJ.Search.tagLeB t₁ t₂ && subB Γ₁ Γ₂
  | .irr Ξ₁ Θ₁ C₁, .irr Ξ₂ Θ₂ C₂ =>
      decide (C₁ = C₂) && ctxEqB Ξ₁ Ξ₂ && subB Θ₁ Θ₂
  | _, _ => false

/-- Rows of `rows` that no row of `db` subsumes, deduplicated by key. -/
def unsubsumed (G : Form) (db rows : List (WRow G)) : List (WRow G) :=
  let bad := rows.filter (fun r => !(db.any (fun s => wsubB r.s s.s)))
  bad.foldl (fun acc r =>
    if keyOf G r ∈ keysOf G acc then acc else acc ++ [r]) []

/-! ## Printing -/

def ppFAux : Nat → Form → String
  | _, .atom s => s
  | _, .bot => "⊥"
  | p, .and a b =>
      let s := ppFAux 3 a ++ " ∧ " ++ ppFAux 4 b
      if p > 3 then "(" ++ s ++ ")" else s
  | p, .or a b =>
      let s := ppFAux 2 a ++ " ∨ " ++ ppFAux 3 b
      if p > 2 then "(" ++ s ++ ")" else s
  | p, .imp a b =>
      let s := ppFAux 2 a ++ " ⊃ " ++ ppFAux 1 b
      if p > 1 then "(" ++ s ++ ")" else s
  | _, .circ a => "◯" ++ ppFAux 4 a

def ppF (A : Form) : String := ppFAux 0 A
def ppL (l : List Form) : String :=
  "[" ++ String.intercalate ", " (l.map ppF) ++ "]"
def ppTag : Tag → String
  | .barren => "barren"
  | .chain D => s!"chain {ppF D}"
  | .blocked => "blocked"
def ppSeq : WSeq → String
  | .reg t Γ C => s!"{ppTag t} : {ppL Γ} ⇒ {ppF C}"
  | .irr Ξ Θ C => s!"{ppL Ξ} ; {ppL Θ} → {ppF C}"

/-- Which join constructor built a regular row (for the witness line). -/
def ruleOfR {G : Form} {t : Tag} {Γ : List Form} {C : Form} :
    FRJWr G t Γ C → String
  | .joinAt .. => "⋈At" | .joinOr .. => "⋈∨" | .joinCirc .. => "⋈◯"
  | .joinAtF .. => "⋈AtF" | .joinOrF .. => "⋈∨F"
  | .joinAtP .. => "⋈AtP" | .joinOrP .. => "⋈∨P" | .joinCircP .. => "⋈◯P"
  | _ => "non-join"

def ruleOf {G : Form} (r : WRow G) : String :=
  match r with
  | ⟨.reg _ _ _, d⟩ => ruleOfR d
  | ⟨.irr _ _ _, _⟩ => "irregular"

/-! ## Cells (the `wscreen` set, plus the explainer's `G2`) -/

abbrev P := PLLFormula
def p : P := .prop "p"
def q : P := .prop "q"
def r : P := .prop "r"
def z : P := .prop "z"

/-- `(⋀_{j=1..n} (pⱼ ⊃ q)) ⊃ q`, right-nested conjunction. -/
def witnessA2 (n : Nat) : P :=
  let imps := (List.range n).map (fun j => PLLFormula.ifThen (.prop s!"p{j + 1}") q)
  let conj := match imps with
    | [] => q
    | a :: rest => rest.foldl (fun acc x => PLLFormula.and acc x) a
  .ifThen conj q

def cells : List (String × P) := [
  ("p ⊃ p [valid]", .ifThen p p),
  ("⊥ ⊃ ⊥ [valid]", .ifThen .falsePLL .falsePLL),
  ("p ⊃ ◯p [valid]", .ifThen p (.somehow p)),
  ("◯◯p ⊃ ◯p [valid]", .ifThen (.somehow (.somehow p)) (.somehow p)),
  ("◯p ⊃ ◯◯p [valid]", .ifThen (.somehow p) (.somehow (.somehow p))),
  ("(◯p∧◯q) ⊃ ◯(p∧q) [valid]", .ifThen ((PLLFormula.somehow p).and (.somehow q))
      (.somehow (p.and q))),
  ("licence-w [valid]", .ifThen (.somehow ((PLLFormula.ifThen (.somehow p) r).and
      (.somehow p))) ((PLLFormula.somehow r).or z)),
  ("p [inv]", p),
  ("⊥ [inv]", .falsePLL),
  ("◯⊥ [inv]", .somehow .falsePLL),
  ("¬◯⊥ [inv]", .ifThen (.somehow .falsePLL) .falsePLL),
  ("◯p ⊃ p (Gcr) [inv]", .ifThen (.somehow p) p),
  ("◯(◯p ⊃ p) (Gcc) [inv]", .somehow (.ifThen (.somehow p) p)),
  ("◯(p∨q) ⊃ ◯p∨◯q [inv]", .ifThen (.somehow (p.or q))
      ((PLLFormula.somehow p).or (.somehow q))),
  ("big-ante [inv]", .ifThen (.somehow ((PLLFormula.ifThen (.somehow p) q).and
      (.somehow p))) (.somehow r)),
  ("p ∨ ¬p [inv]", p.or (.ifThen p .falsePLL)),
  ("Peirce [inv]", .ifThen (.ifThen (.ifThen p q) p) p),
  ("◯p ∨ ¬◯p [inv]", (PLLFormula.somehow p).or (.ifThen (.somehow p) .falsePLL)),
  ("G2: ◯p ⊃ ◯p∧◯p [valid]", .ifThen (.somehow p) ((PLLFormula.somehow p).and (.somehow p))),
  -- the DESIGNED witness family for A2 (2026-09-02): the restriction
  -- `Θ^⊃/Υ` keeps `pⱼ ⊃ q` only when `pⱼ` is a premise goal, one goal
  -- per premise, so the root context `{p₁⊃q, …, pₙ⊃q} ⇒ q` needs an
  -- n-ary `⋈At`.  Indices 19, 20, 21 = n = 2, 3, 4.
  ("A2 witness n=2: (p₁⊃q ∧ p₂⊃q) ⊃ q [inv]", witnessA2 2),
  ("A2 witness n=3: (⋀ⱼ pⱼ⊃q) ⊃ q [inv]", witnessA2 3),
  ("A2 witness n=4: (⋀ⱼ pⱼ⊃q) ⊃ q [inv]", witnessA2 4)
]

/-! ## The engine comparison (A3 in miniature) -/

def engineKeys (G : Form) (k : Nat) : List WSeq × FRJ.Search.Stats :=
  let O := FRJ.Search.W.wOps G
  let cfg : FRJ.Search.Config :=
    { rounds := 64, jmax := k, pmax := k, lamCap := 4096, maxRS := 200000, maxIS := 200000 }
  let (db, st) := FRJ.Search.saturateO O cfg
  let rs := db.rs.map (fun x => WSeq.reg (O.rsTag x) (O.rsCtx x) (O.rsRhs x))
  let is := db.is.map (fun x => WSeq.irr (O.isStab x) (O.isTh x) (O.isRhs x))
  (rs ++ is, st)

def flags (st : FRJ.Search.Stats) : String :=
  let l := [(st.lamCapped, "lamCap"), (st.dbCapped, "dbCap"),
            (st.jmaxBinding, "jmax"), (st.pmaxBinding, "pmax")]
  match (l.filter (·.1)).map (·.2) with
  | [] => "-"
  | fs => String.intercalate "," fs

/-! ## Driver -/

def getNat (args : List String) (key : String) (d : Nat) : Nat :=
  match args.find? (fun a => a.startsWith ("--" ++ key ++ "=")) with
  | some a => ((a.drop (key.length + 3)).toNat?).getD d
  | none => d

def pow2 (b : Nat) : Nat := 2 ^ b

/-- Family count of the full check: all nonempty sublists of the
irregular store, times (for the promise joins) all nonempty sublists of
the regular store. -/
def fullCostBF (irr : Nat) : Nat := pow2 irr
def fullCostP (irr reg : Nat) : Nat := pow2 irr * pow2 reg

/-- Gate watch (`--dropjoins=1`): remove every join-built row from the
saturated store before the checks.  Where joins fired, the checks MUST
then report unsubsumed rows; a clean report under this switch would mean
the checks see nothing. -/
def dropJoins {G : Form} (db : List (WRow G)) : List (WRow G) :=
  db.filter (fun r => ruleOf r == "non-join" || ruleOf r == "irregular")

def runCell (idx : Nat) (K M budget : Nat) (drop nop : Bool) : IO Unit := do
  match cells[idx]? with
  | none => IO.println s!"unknown cell index {idx} (0..{cells.length - 1})"
  | some (nm, φ) =>
    let G := ofPLL φ
    let gp := gPool G
    let goals := goalPool G
    IO.println s!"cell {idx}: {nm}{if drop then "  [GATE WATCH: join rows dropped from the store]" else ""}{if nop then "  [promise joins OFF]" else ""}"
    IO.println s!"  G = {ppF G}"
    IO.println s!"  |Ĝ| = {gp.length}  |Sf^R| = {goals.length}  |univ| ≈ {(3 + goals.length) * pow2 gp.length * goals.length + pow2 gp.length * pow2 gp.length * goals.length}"
    let mut passK : Option Nat := none
    let mut failed : Option (Nat × Nat) := none
    let mut anySkipped := false
    for k in List.range K do
      let k := k + 1
      let t0 ← IO.monoMsNow
      let (db0, rounds) := satK G nop k k 100000 [] 0
      let db := if drop then dropJoins db0 else db0
      let t1 ← IO.monoMsNow
      let irr := (irrTs db).length
      let reg := (regTs db).length
      let rootHit := (regTs db).any (fun tr => decide (tr.C = G))
      IO.println s!"  k={k}: rounds={rounds} |reg|={reg} |irr|={irr} keys={db.length} sat={t1 - t0}ms  root-disproof-present={rootHit}"
      (← IO.getStdout).flush
      -- the ladder: exact arity m = k+1 .. M over db_k
      let mut witness : Option (Nat × WRow G) := none
      let pfK := if nop then [] else sublistsUpTo k (regTs db)
      for m in List.range (M - k) do
        let m := k + 1 + m
        if m ≤ irr then
          let nfam := choose irr m
          if nfam * (1 + pfK.length) ≤ pow2 budget then
            let fams := sublistsLen m (irrTs db)
            let t2 ← IO.monoMsNow
            let rows := joinsBF G fams ++ joinsP G fams pfK
            let bad := unsubsumed G db rows
            let t3 ← IO.monoMsNow
            IO.println s!"    ladder irr-arity={m} (C({irr},{m})={nfam} families × {1 + pfK.length}): emitted={rows.length} unsubsumed={bad.length} {t3 - t2}ms"
            if witness.isNone then
              if let some w := bad.head? then witness := some (m, w)
          else
            anySkipped := true
            IO.println s!"    ladder irr-arity={m} SKIPPED: C({irr},{m})×{1 + pfK.length} = {nfam * (1 + pfK.length)} > 2^{budget}"
          (← IO.getStdout).flush
      -- the promise ladder: irregular ≤ k, promise families of exact size m
      let famsK := sublistsUpTo k (irrTs db)
      for m in List.range (M - k) do
        let m := k + 1 + m
        if m ≤ reg && !nop then
          let nfam := choose reg m
          if nfam * famsK.length ≤ pow2 budget then
            let pf := sublistsLen m (regTs db)
            let t2 ← IO.monoMsNow
            let rows := joinsP G famsK pf
            let bad := unsubsumed G db rows
            let t3 ← IO.monoMsNow
            IO.println s!"    ladder promise-arity={m} (C({reg},{m})={nfam} families × {famsK.length}): emitted={rows.length} unsubsumed={bad.length} {t3 - t2}ms"
            if witness.isNone then
              if let some w := bad.head? then witness := some (m, w)
          else
            anySkipped := true
            IO.println s!"    ladder promise-arity={m} SKIPPED: C({reg},{m})×{famsK.length} = {nfam * famsK.length} > 2^{budget}"
          (← IO.getStdout).flush
      -- the full check (core emitters, all arities)
      let cBF := fullCostBF irr
      let cP := if nop then 0 else fullCostP irr reg
      let mut fullOk : Option Bool := none
      if cBF ≤ pow2 budget && cP ≤ pow2 budget then
        let t4 ← IO.monoMsNow
        let rows := if nop then stepAllNoP G db else stepAll G db
        let bad := unsubsumed G db rows
        let t5 ← IO.monoMsNow
        IO.println s!"    full check{if nop then " (no promise joins)" else ""}: families 2^{irr}{if nop then "" else s!"·(1+2^{reg})"} emitted={rows.length} unsubsumed={bad.length} {t5 - t4}ms"
        fullOk := some bad.isEmpty
        if witness.isNone then
          if let some w := bad.head? then witness := some (0, w)
      else
        anySkipped := true
        IO.println s!"    full check SKIPPED: family count 2^{irr} / 2^{irr}·2^{reg} exceeds budget 2^{budget}"
      -- the engine comparison
      let (ek, st) := engineKeys G k
      let engRows := ek
      let probeSeqs : List WSeq := db.map (fun (r : WRow G) => r.s)
      let engNotProbe := engRows.filter (fun e => !(probeSeqs.any (fun s => wsubB e s)))
      let probeNotEng := probeSeqs.filter (fun s => !(engRows.any (fun e => wsubB s e)))
      IO.println s!"    engine@jmax=pmax={k}: rows={engRows.length} rounds={st.roundsUsed} caps={flags st}  engine-rows-unsubsumed-by-probe={engNotProbe.length}  probe-rows-unsubsumed-by-engine={probeNotEng.length}"
      if let some e := engNotProbe.head? then IO.println s!"      e.g. engine-only: {ppSeq e}"
      if let some s := probeNotEng.head? then IO.println s!"      e.g. probe-only:  {ppSeq s}"
      -- verdict bookkeeping
      match witness with
      | some (m, w) =>
          failed := some (k, m)
          IO.println s!"    WITNESS at k={k}, arity={if m = 0 then "full" else toString m}: {ruleOf w} gives {ppSeq w.s}"
      | none =>
          if fullOk == some true && passK.isNone then passK := some k
    match passK, failed with
    | some k, _ => IO.println s!"VERDICT {nm}: PASS k={k} (bounded closure at k is closed under all arities)"
    | none, some (k, m) => IO.println s!"VERDICT {nm}: FAIL k={k} arity={m} (see WITNESS)"
    | none, none =>
        if anySkipped then IO.println s!"VERDICT {nm}: FLAG (no witness to the ladder's reach; full check skipped — raise --budget)"
        else IO.println s!"VERDICT {nm}: FLAG (no witness, no full check passed)"

end A2Probe

def main (args : List String) : IO Unit := do
  match args with
  | [] => IO.println s!"usage: a2probe <cell-index 0..{A2Probe.cells.length - 1}> [--K=4] [--M=6] [--budget=22]"
  | s :: rest =>
      match s.toNat? with
      | none =>
          if s == "list" then
            for (i, (nm, _)) in (List.range A2Probe.cells.length).zip A2Probe.cells do
              IO.println s!"{i}: {nm}"
          else IO.println "first argument must be a cell index or `list`"
      | some i =>
          A2Probe.runCell i (A2Probe.getNat rest "K" 4) (A2Probe.getNat rest "M" 6)
            (A2Probe.getNat rest "budget" 22) (A2Probe.getNat rest "dropjoins" 0 == 1)
            (A2Probe.getNat rest "nopromise" 0 == 1)
