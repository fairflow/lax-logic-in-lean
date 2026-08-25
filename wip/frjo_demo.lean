/-
# FRJ◯ end to end on one sequent

The sequent:

    ⊢  ¬¬◯⊥ ∨ (¬¬◯⊥ ⊃ ◯⊥) ∨ ((¬¬◯⊥ ⊃ ◯⊥) ⊃ ◯¬◯⊥)

which in the dictionary's numbering is `q6 ∨ q10 ∨ q14`.  Both
associations are run; ∨ is associative only up to interderivability,
so the two are separate sequents and both are reported.

What this file prints, in order:

1. the polarised sequent FRJ◯ actually works on, `negOfO`-translated;
2. the verdict of `FRJO.diagnose`, naming the stage if it fails;
3. the refutation derivation `t : RT` in tree form, each node
   annotated with the rule instance chosen and the premise refuted;
4. the extracted `FinCM`, and the VERIFIED gate `FinCM.checkB M w Γ φ`
   re-evaluated here, which is what makes the result kernel-usable via
   `FinCM.not_provable_of_check`;
5. the same model written out as SVG by `PLLND.Diagram.writeSvg`.

FRJ◯'s own soundness (`FRJO.SoundnessFRJO`) and completeness
(`FRJO.CompletenessFRJO`) are OPEN — they are stated as `Prop`s in
`FRJO/Core.lean` and not proved.  Nothing here depends on them: the
certificate is the model plus `checkB`, and its soundness theorem is
`FinCM.not_provable_of_check`, proved.  FRJ◯ is a searcher, and the
kernel checks its output.

NEW FILE; nothing existing is edited.
-/
import FRJO.Core
import wip.rnDict
import LaxLogic.PLLDiagram

open PLLND PLLFormula LJFO
open PLLND.SemUI.RND (repsL)

namespace FrjoDemo

abbrev F := PLLFormula

def q (i : Nat) : F := repsL.getD i .falsePLL

/-- `(q6 ∨ q10) ∨ q14` and `q6 ∨ (q10 ∨ q14)`. -/
def phiL : F := ((q 6).or (q 10)).or (q 14)
def phiR : F := (q 6).or ((q 10).or (q 14))

/-! ## Display -/

def ppF : F → String
  | .falsePLL => "⊥"
  | .prop a => a
  | .and a b => s!"({ppF a} ∧ {ppF b})"
  | .or a b => s!"({ppF a} ∨ {ppF b})"
  | .ifThen a .falsePLL => s!"¬{ppF a}"
  | .ifThen a b => s!"({ppF a} ⊃ {ppF b})"
  | .somehow a => s!"◯{ppF a}"

mutual
partial def ppP : Pos → String
  | .atom a => a
  | .fls => "0"
  | .or p q => s!"({ppP p} ⊕ {ppP q})"
  | .down n => s!"↓{ppN n}"
partial def ppN : Neg → String
  | .up p => s!"↑{ppP p}"
  | .imp p n => s!"({ppP p} → {ppN n})"
  | .and m n => s!"({ppN m} & {ppN n})"
  | .circ p => s!"◯{ppP p}"
end

def ppJ : JD → String | .tru => "tru" | .lax => "lax"

def ppCtx (Γ : List Neg) : String :=
  if Γ.isEmpty then "·" else String.intercalate ", " (Γ.map ppN)

def ppSeq : LSeq → String
  | .stab Γ j P => s!"{ppCtx Γ} ⊢[{ppJ j}] {ppP P}     ⟨stable⟩"
  | .rfocus Γ j P => s!"{ppCtx Γ} ⊢[{ppJ j}] ⟦{ppP P}⟧     ⟨right focus⟩"
  | .lfoc Γ N j P => s!"{ppCtx Γ} ; ⟦{ppN N}⟧ ⊢[{ppJ j}] {ppP P}     ⟨left focus⟩"
  | .inv Γ Ω j C =>
      let om := String.intercalate ", " (Ω.map ppP)
      s!"{ppCtx Γ} ; [{om}] ⊢[{ppJ j}] {ppN C}     ⟨inversion⟩"

/-- The name of rule instance `i` of `s`, mirroring `LSeq.succs`. -/
def ruleName (s : LSeq) (i : Nat) : String :=
  match s with
  | .stab Γ j _ =>
      if i == 0 then "Rfocus"
      else if i ≤ Γ.length then s!"Lfocus on {ppN (Γ.getD (i-1) (.up .fls))}"
      else "lax-coercion (tru→lax)"
  | .rfocus _ _ P =>
      match P with
      | .or _ _ => if i == 0 then "⊕R₁" else "⊕R₂"
      | .down _ => "↓R (release)"
      | .atom _ => "init"
      | .fls => "(no instance)"
  | .lfoc _ N _ _ =>
      match N with
      | .up _ => "↑L (release)"
      | .imp _ _ => "→L"
      | .and _ _ => if i == 0 then "&L₁" else "&L₂"
      | .circ _ => "◯L  ← the lax box-opening (records an Rₘ edge)"
  | .inv Γ Ω j C =>
      let nGoal := (LSeq.goalInsts Γ Ω C j).length
      let nStab := (LSeq.stableInsts Γ Ω C j).length
      if i < nGoal then
        match C with
        | .imp _ _ => "→R"
        | .and _ _ => "&R"
        | .circ _ => "◯R  ← enters the lax phase"
        | _ => "goal"
      else if i < nGoal + nStab then "stabilise"
      else
        match Ω with
        | .or _ _ :: _ => "⊕L"
        | .fls :: _ => "0L (closes)"
        | .down _ :: _ => "↓L (to context)"
        | .atom _ :: _ => "atomL (to context)"
        | [] => "ω"

/-- Walk the derivation beside the sequent, exactly as `FRJO.wf` does. -/
partial def render (ind : Nat) (s : LSeq) : FRJO.RT → List String
  | .cyc => [s!"{String.replicate ind ' '}└─ CYCLE — back-edge to this stable sequent in the history"]
  | .mk ks =>
      let pad := String.replicate ind ' '
      let pss := s.succs
      let head := s!"{pad}{ppSeq s}"
      let body := (List.zipIdx (List.zip ks pss)).flatMap fun ((k, ps), i) =>
        let prem := ps.getD k.1 (LSeq.stab [] .tru .fls)
        let tag := s!"{pad}  ├ rule {i}: {ruleName s i} — refuting premise {k.1} of {ps.length}"
        tag :: render (ind + 4) prem k.2
      head :: body

def ppM (M : FinCM) : String :=
  s!"⟨n := {M.n}, ri := {M.ri}, rm := {M.rm}, fall := {M.fall}, val := {M.val}⟩"

def one (label : String) (φ : F) (svgPath : String) : IO Unit := do
  let out ← IO.getStdout
  IO.println s!"════════ {label} ════════"
  IO.println s!"φ  = {ppF φ}"
  let s : LSeq := .inv [] [] .tru (negOfO φ)
  IO.println s!"polarised sequent handed to FRJ◯:"
  IO.println s!"   {ppSeq s}"
  IO.println ""
  match FRJO.diagnose [] φ with
  | .inr f =>
      IO.println s!"FRJ◯ verdict: NO CERTIFICATE — stage `{f.str}`"
      IO.println "  noDeriv  = the refutation search found no derivation"
      IO.println "  wfReject = search returned a tree its own checker rejects (a defect)"
      IO.println "  gateMiss = derivation found, but no assembled model passed checkB"
  | .inl (t, M, w) =>
      IO.println s!"FRJ◯ verdict: REFUTED.  derivation size {t.size} nodes, model {M.n} worlds, root world {w}"
      IO.println ""
      IO.println "──── the refutation derivation ────"
      for l in render 0 s t do IO.println l
      IO.println ""
      IO.println "──── the extracted countermodel ────"
      IO.println s!"M = {ppM M}"
      IO.println s!"wellB M                 = {FinCM.wellB M}"
      IO.println s!"FRJO.wf [] s t          = {FRJO.wf [] s t}   (searcher self-check, control)"
      IO.println s!"FinCM.checkB M {w} [] φ    = {FinCM.checkB M w [] φ}   ← the VERIFIED gate"
      IO.println s!"forceB {w} φ              = {M.forceB w φ}   (must be false at the root)"
      IO.println ""
      IO.println "consumable as:  FinCM.not_provable_of_check (M := M) (w := w) (C := φ) (by decide)"
      -- label each world by which of q6, q10, q14 it forces; the SECOND
      -- label component is rendered by toSvg with a ⊘ prefix meaning
      -- "promises-false", so it is left empty and fallibility is carried
      -- by the node fill, as the renderer intends.
      let labels : Nat → String × String := fun v =>
        let parts := [(6, "q6"), (10, "q10"), (14, "q14")].filterMap fun (i, nm) =>
          if M.forceB v (q i) then some nm else none
        let body := if parts.isEmpty then "⊮ all" else String.intercalate ", " parts
        (s!"w{v}: {body}", "")
      let (wd, ht) := Diagram.autoSize M
      let svg := Diagram.toSvg M (Diagram.autoPos M) labels (some w) wd ht
      IO.FS.writeFile svgPath svg
      IO.println s!"SVG by PLLND.Diagram.toSvg (autoPos/autoSize/hasseRi) → {svgPath}"
      IO.println s!"  world labels: {String.intercalate "  |  " ((List.range M.n).map (fun v => (labels v).1))}"
  out.flush
  IO.println ""

def main : IO Unit := do
  IO.println "=== FRJ◯ worked example ==="
  IO.println "engine: FRJO.diagnose → FRJO.find (unfueled; terminates by history loop-check)"
  IO.println "        → FRJO.wf → FRJO.worldsEdgesOf → Unravel.assemble → FinCM.checkB"
  IO.println ""
  one "LEFT association:  (q6 ∨ q10) ∨ q14" phiL "docs/frjo-q6q10q14-left.svg"
  one "RIGHT association: q6 ∨ (q10 ∨ q14)" phiR "docs/frjo-q6q10q14-right.svg"
  IO.println "FRJO-DEMO-DONE"

end FrjoDemo

def main : IO Unit := FrjoDemo.main
