/-
COPY, not a move.  The `wip/` original is left in place unchanged so that
other branches still compile; this file is the maintained version.  Do not
edit the `wip/` twin — it is stale by construction (2026-08-21).
-/
/-
# Route B: the DERIVATION-preserving extractor

`wip/rnpin.lean` is route A: it finds the hit row, keeps `modR r.der`, and
throws the derivation away.  The certificate it emits is a finite Kripke
table re-checked by `decide` and consumed by
`FRJ.not_entails_of_countermodel` — a semantic route that never mentions
`FRJ.soundness`.

This file keeps the row.  A row of `db.rs` whose `rhs` is the goal IS a
witness for

    Provable G := ∃ t Γ, Nonempty (FRJr G t Γ G)

so `FRJ.soundness : Provable G → ¬ PLL G` applies to it directly, and the
bridge lemmas `not_derivable_of_provable` / `not_entails_of_provable` /
`not_interd_of_provable` (all already in `FRJ/Bridge.lean`) turn it into a
statement about `LaxND`.  Both routes were designed into the bridge; only
route A was ever wired to an emitter.

`lake exe frjderive <cell> <→|←> [--rounds=N] [--tree]` reports the hit,
the size of the derivation it built, and — with `--tree` — the derivation
itself, one line per rule with its sequent.
-/
import FRJ.Search.Fast
import FRJ.Search.Pin
import Tools.Bank

open FRJ

namespace FrjDerive

/-! ## Rendering the syntax -/

def ppF : Form → String
  | .atom p => p
  | .bot => "⊥"
  | .and a b => s!"({ppF a} ∧ {ppF b})"
  | .or a b => s!"({ppF a} ∨ {ppF b})"
  | .imp a .bot => s!"¬{ppF a}"
  | .imp a b => s!"({ppF a} ⊃ {ppF b})"
  | .circ a => s!"◯{ppF a}"

def ppL (l : List Form) : String :=
  if l.isEmpty then "·" else String.intercalate ", " (l.map ppF)

def ppTag : Tag → String
  | .barren => "barren"
  | .chain D => s!"chain {ppF D}"
  | .blocked => "blocked"

/-! ## Size and tree

`FRJr`/`FRJi` are reflexive inductives: the join constructors carry their
irregular premises as a family `∀ j : Fin (n+1), FRJi …`.  Recursion runs
through the family, so both functions are structural, not fuelled — no cap
is applied and none is reported. -/

mutual

def sizeR {G : Form} {t : Tag} {Γ : List Form} {C : Form} : FRJr G t Γ C → Nat
  | .axR .. => 1
  | .andR1 d _ => 1 + sizeR d
  | .andR2 d _ => 1 + sizeR d
  | .impIn d _ _ => 1 + sizeR d
  | .circIn d _ _ => 1 + sizeR d
  | .joinAt (n := n) prem .. =>
      1 + ((List.finRange (n+1)).map (fun j => sizeI (prem j))).sum
  | .joinAtF (n := n) prem .. =>
      1 + ((List.finRange (n+1)).map (fun j => sizeI (prem j))).sum
  | .joinOr (n := n) prem .. =>
      1 + ((List.finRange (n+1)).map (fun j => sizeI (prem j))).sum
  | .joinOrF (n := n) prem .. =>
      1 + ((List.finRange (n+1)).map (fun j => sizeI (prem j))).sum
  | .joinCirc (n := n) prem .. =>
      1 + ((List.finRange (n+1)).map (fun j => sizeI (prem j))).sum
  | .joinAtP (n := n) (k := k) prem dps .. =>
      1 + ((List.finRange (n+1)).map (fun j => sizeI (prem j))).sum
        + ((List.finRange (k+1)).map (fun i => sizeR (dps i))).sum
  | .joinOrP (n := n) (k := k) prem dps .. =>
      1 + ((List.finRange (n+1)).map (fun j => sizeI (prem j))).sum
        + ((List.finRange (k+1)).map (fun i => sizeR (dps i))).sum
  | .joinCircP (n := n) (k := k) prem dps .. =>
      1 + ((List.finRange (n+1)).map (fun j => sizeI (prem j))).sum
        + ((List.finRange (k+1)).map (fun i => sizeR (dps i))).sum

def sizeI {G : Form} {St Th : List Form} {C : Form} : FRJi G St Th C → Nat
  | .axI .. => 1
  | .andI1 d _ => 1 + sizeI d
  | .andI2 d _ => 1 + sizeI d
  | .orI d₁ d₂ .. => 1 + sizeI d₁ + sizeI d₂
  | .impInI d .. => 1 + sizeI d
  | .impNotIn d .. => 1 + sizeR d
  | .circNotIn d .. => 1 + sizeR d
  | .axIC .. => 1

end

/-! ## The tree -/

def ind (n : Nat) : String := String.ofList (List.replicate n ' ')

def lineR (pad : Nat) (nm : String) (t : Tag) (Γ : List Form) (C : Form) : String :=
  s!"{ind pad}{nm}  [{ppTag t}]  {ppL Γ} ⇒ {ppF C}"

def lineI (pad : Nat) (nm : String) (St Th : List Form) (C : Form) : String :=
  s!"{ind pad}{nm}  {ppL St} ; {ppL Th} → {ppF C}"

mutual

def renderR {G : Form} {t : Tag} {Γ : List Form} {C : Form} (pad : Nat) :
    FRJr G t Γ C → List String
  | .axR .. => [lineR pad "Ax^R" t Γ C]
  | .andR1 d _ => lineR pad "∧R₁" t Γ C :: renderR (pad+2) d
  | .andR2 d _ => lineR pad "∧R₂" t Γ C :: renderR (pad+2) d
  | .impIn d _ _ => lineR pad "⊃∈" t Γ C :: renderR (pad+2) d
  | .circIn d _ _ => lineR pad "◯∈" t Γ C :: renderR (pad+2) d
  | .joinAt (n := n) prem .. =>
      lineR pad s!"⋈^At({n+1})" t Γ C ::
        ((List.finRange (n+1)).map (fun j => renderI (pad+2) (prem j))).flatten
  | .joinAtF (n := n) prem .. =>
      lineR pad s!"⋈^At,⊥({n+1})" t Γ C ::
        ((List.finRange (n+1)).map (fun j => renderI (pad+2) (prem j))).flatten
  | .joinOr (n := n) prem .. =>
      lineR pad s!"⋈^∨({n+1})" t Γ C ::
        ((List.finRange (n+1)).map (fun j => renderI (pad+2) (prem j))).flatten
  | .joinOrF (n := n) prem .. =>
      lineR pad s!"⋈^∨,⊥({n+1})" t Γ C ::
        ((List.finRange (n+1)).map (fun j => renderI (pad+2) (prem j))).flatten
  | .joinCirc (n := n) prem .. =>
      lineR pad s!"⋈^◯({n+1})" t Γ C ::
        ((List.finRange (n+1)).map (fun j => renderI (pad+2) (prem j))).flatten
  | .joinAtP (n := n) (k := k) prem dps .. =>
      lineR pad s!"⋈^At,p({n+1};{k+1})" t Γ C ::
        (((List.finRange (n+1)).map (fun j => renderI (pad+2) (prem j))).flatten
          ++ ((List.finRange (k+1)).map (fun i =>
               (ind (pad+2) ++ "· promise:") :: renderR (pad+4) (dps i))).flatten)
  | .joinOrP (n := n) (k := k) prem dps .. =>
      lineR pad s!"⋈^∨,p({n+1};{k+1})" t Γ C ::
        (((List.finRange (n+1)).map (fun j => renderI (pad+2) (prem j))).flatten
          ++ ((List.finRange (k+1)).map (fun i =>
               (ind (pad+2) ++ "· promise:") :: renderR (pad+4) (dps i))).flatten)
  | .joinCircP (n := n) (k := k) prem dps .. =>
      lineR pad s!"⋈^◯,p({n+1};{k+1})" t Γ C ::
        (((List.finRange (n+1)).map (fun j => renderI (pad+2) (prem j))).flatten
          ++ ((List.finRange (k+1)).map (fun i =>
               (ind (pad+2) ++ "· promise:") :: renderR (pad+4) (dps i))).flatten)

def renderI {G : Form} {St Th : List Form} {C : Form} (pad : Nat) :
    FRJi G St Th C → List String
  | .axI .. => [lineI pad "Ax^I" St Th C]
  | .axIC .. => [lineI pad "Ax^I◯" St Th C]
  | .andI1 d _ => lineI pad "∧I₁" St Th C :: renderI (pad+2) d
  | .andI2 d _ => lineI pad "∧I₂" St Th C :: renderI (pad+2) d
  | .orI d₁ d₂ .. =>
      lineI pad "∨I" St Th C :: (renderI (pad+2) d₁ ++ renderI (pad+2) d₂)
  | .impInI d .. => lineI pad "⊃∈I" St Th C :: renderI (pad+2) d
  | .impNotIn d .. => lineI pad "⊃∉" St Th C :: renderR (pad+2) d
  | .circNotIn d .. => lineI pad "◯∉" St Th C :: renderR (pad+2) d

end

/-! ## Keeping the row: the `Provable` witness

Route A's `hitModel` maps the found row through `modR`, discarding the
derivation.  This keeps it. -/

def hitRow (G : Form) (cfg : Search.Config) : Option (Search.RS G) :=
  (Search.saturateFast G cfg).1.rs.find? (fun x => decide (x.rhs = G))

/-- A search hit IS a `Provable` witness — this is the step route A drops.
Discharging `h` in the kernel would mean running the search there; the
usable certificate is the emitted derivation TERM, and this lemma is what
that term is consumed by. -/
theorem provable_of_hitRow {G : Form} {cfg : Search.Config} {r : Search.RS G}
    (h : hitRow G cfg = some r) : Provable G := by
  unfold hitRow at h
  have hb := List.find?_some (p := fun (x : Search.RS G) => decide (x.rhs = G))
    (a := r) (l := (Search.saturateFast G cfg).1.rs) h
  have hp : r.rhs = G := of_decide_eq_true hb
  exact ⟨r.t, r.ctx, ⟨cast (congrArg (fun X => FRJr G r.t r.ctx X) hp) r.der⟩⟩

/-! ## Driver -/

def run (cellName dir : String) (tree : Bool) (cfg : Search.Config) : IO Unit := do
  match RNBank.cells.find? (fun c => c.name == cellName) with
  | none => IO.println s!"no such cell: {cellName}"
  | some c =>
      let forms := c.forms
      match forms.find? (fun p => p.1.endsWith dir) with
      | none => IO.println s!"no such direction: {dir}"
      | some (nm, G) =>
          IO.println s!"cell {nm}   goal G = {ppF G}"
          let t0 ← IO.monoMsNow
          match hitRow G cfg with
          | none =>
              let t1 ← IO.monoMsNow
              IO.println s!"no derivation at this budget [{t1 - t0} ms] \
                (rounds={cfg.rounds}, jmax={cfg.jmax}, pmax={cfg.pmax}, \
                 lamCap={cfg.lamCap}, maxRS={cfg.maxRS}, maxIS={cfg.maxIS})"
          | some r =>
              let sz := sizeR r.der
              let t1 ← IO.monoMsNow
              IO.println s!"HIT [{t1 - t0} ms]: tag {ppTag r.t}, \
                context {ppL r.ctx}, derivation size {sz}"
              IO.println s!"  the row is a Provable witness: \
                ⟨{ppTag r.t}, {ppL r.ctx}, ⟨r.der⟩⟩ : Provable G"
              if tree then
                IO.println "-- BEGIN DERIVATION --"
                for l in renderR 0 r.der do IO.println l
                IO.println "-- END DERIVATION --"
          (← IO.getStdout).flush

end FrjDerive

def main (args : List String) : IO Unit := do
  let cell := args.getD 0 "cAnd_10_13"
  let dir := args.getD 1 "←"
  let rounds := ((args.getD 2 "10").toNat?).getD 10
  let tree := args.contains "--tree"
  FrjDerive.run cell dir tree { rounds := rounds }
