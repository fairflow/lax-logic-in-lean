/-
# `LaxLogic.QLL.CLPCertify` — abstract proofs as λ̄c terms, checked by `certify`

An abstract proof tree (`AProof`) is read as a proof term of Fig. 5 with the
derived terms of the CLP draft's Fig. 3:

    val(⋆),   ∧◯(p, r) = let y ⇐ p in let z ⇐ r in val(y, z),
    ∨◯(p, i) = let z ⇐ p in val(ιᵢ z),   ∃◯(p, t) = let z ⇐ p in val(⟨t⟩ z),
    ⊃◯(p, w, t̃) = let z ⇐ p in w t̃ z,

and handed to `certify`, the verified checker of `Certify.lean`, with the abstract
program as the context (one proof variable per clause).  A success is a
derivation `Derives p Γ (◯S)` in the calculus of TPHOLs 2001, obtained without
any appeal to `ATyped`.

**Scaling.**  Only small terms: `certify` names each binder `freshFor` of the
names in scope, which concatenates them (`freshFor_byteSize`), so fresh names
double in length with each nested `let`.  The term of a 3-bit adder (about 25
nested lets) exhausted memory (38 GB, killed).  Do not run `certify` on deep
terms until `freshFor` is made linear.
-/
import LaxLogic.QLL.CLPExamples
import LaxLogic.QLL.Certify

namespace LaxLogic.QLL.CLPCertify

open LaxLogic.QLL LaxLogic.QLL.Engine LaxLogic.QLL.LinQ LaxLogic.QLL.CLPExamples

/-- The λ̄c term of an abstract proof; clause `w` is the proof variable `names[w]`. -/
def AProof.toPf (q : Q) (names : List String) : AProof → Pf
  | .val => .val q .star
  | .andC p r =>
      .letQ q (AProof.toPf q names p)
        (.letQ q (AProof.toPf q names r) (.val q (.pair (.bvar 1) (.bvar 0))))
  | .orL p => .letQ q (AProof.toPf q names p) (.val q (.inl (.bvar 0)))
  | .orR p => .letQ q (AProof.toPf q names p) (.val q (.inr (.bvar 0)))
  | .exC t p => .letQ q (AProof.toPf q names p) (.val q (.pack t (.bvar 0)))
  | .impC w ts p =>
      .letQ q (AProof.toPf q names p) (.app (Pf.insts ts (.fvar (names.getD w "?"))) (.bvar 0))

/-- Close the named proof variable `a` into the bound index `k`. -/
def closeP (k : Nat) (a : String) : Pf → Pf
  | .bvar i => .bvar i
  | .fvar x => if x = a then .bvar k else .fvar x
  | .star => .star
  | .pair p r => .pair (closeP k a p) (closeP k a r)
  | .fst p => .fst (closeP k a p)
  | .snd p => .snd (closeP k a p)
  | .inl p => .inl (closeP k a p)
  | .inr p => .inr (closeP k a p)
  | .caseOr r p₁ p₂ => .caseOr (closeP k a r) (closeP (k + 1) a p₁) (closeP (k + 1) a p₂)
  | .lam p => .lam (closeP (k + 1) a p)
  | .app p r => .app (closeP k a p) (closeP k a r)
  | .val q p => .val q (closeP k a p)
  | .letQ q p r => .letQ q (closeP k a p) (closeP (k + 1) a r)
  | .gen p => .gen (closeP k a p)
  | .inst t p => .inst t (closeP k a p)
  | .pack t p => .pack t (closeP k a p)
  | .caseEx r p => .caseEx (closeP k a r) (closeP (k + 1) a p)
  | .exf A p => .exf A (closeP k a p)

/-- The let-flattened term: values are combined purely (pairs, injections,
packs, `⋆`), and only clause applications `w t̃ v` are `let`-bound.  Equal to
`toPf` by the commuting conversions of the monad; every `let` scrutinee is now
inferable, as a bidirectional checker requires. -/
def anf (q : Q) (names : List String) : AProof → Nat → (Pf → Nat → Pf) → Pf
  | .val, n, K => K .star n
  | .andC p r, n, K => anf q names p n fun v₁ n₁ => anf q names r n₁ fun v₂ n₂ => K (.pair v₁ v₂) n₂
  | .orL p, n, K => anf q names p n fun v n' => K (.inl v) n'
  | .orR p, n, K => anf q names p n fun v n' => K (.inr v) n'
  | .exC t p, n, K => anf q names p n fun v n' => K (.pack t v) n'
  | .impC w ts p, n, K => anf q names p n fun v n' =>
      let z := s!"_z{n'}"
      .letQ q (.app (Pf.insts ts (.fvar (names.getD w "?"))) v) (closeP 0 z (K (.fvar z) (n' + 1)))

/-- The let-flattened λ̄c term of an abstract proof, which `certify` accepts. -/
def AProof.toPfN (q : Q) (names : List String) (a : AProof) : Pf :=
  anf q names a 0 fun v _ => .val q v

/-- Proof-variable names for the clauses of a program. -/
def clauseNames (n : Nat) : List String := (List.range n).map fun i => s!"θ{i}"

/-- Run `certify` on the abstract image of a concrete proof tree, in the direct
reading of Fig. 3 (`flat := false`) or let-flattened (`flat := true`). -/
def certifyAbs (flat : Bool) (isC : String → Bool) (q : Q) (Θ : Program) (S : Form)
    (p : CProof) : String :=
  let names := clauseNames Θ.length
  let t := if flat then AProof.toPfN q names p.toA else AProof.toPf q names p.toA
  match certify (Program.ctx names (Θ.abs isC q)) t (.circ q (S.strip isC)) with
  | .ok _ => "certified"
  | .error e => s!"rejected: {repr e}"

/-- info: "rejected: LaxLogic.QLL.Err.notInferable \"ι_t(p)\"" -/
#guard_msgs in #eval certifyAbs false isLinC .ex ex61 goal61 proof61
/-- info: "certified" -/
#guard_msgs in #eval certifyAbs true isLinC .ex ex61 goal61 proof61
/-- info: "certified" -/
#guard_msgs in #eval certifyAbs true isC95 .ex ex95 goal95 proof95

#eval Surface.renderPf (AProof.toPfN .ex (clauseNames 3) proof61.toA)

end LaxLogic.QLL.CLPCertify
