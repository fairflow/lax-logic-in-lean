/-
# `lake exe pll` — the user-facing PLL decider with its output layer

The pipeline of `docs/decider-outputs-design.md`, at the seam of §4.4:

  formula ─ ofPLL ─→ untrusted W-engine ─ rowsOfDBO ─→ checkClosed (VERIFIED)
     ─ decideOfStore ─→ GbuRC ⊕ FRJW disproof ─ answerOf ─→ Answer φ

  * PROVED:  Gbu◯ derivation → `laxOfR` → `ndToTm` → a `PLLND.Tm [] φ`
    proof term; its Lax type is its INDEX, so "the type equals the checked
    formula" is the elaborator's business, not a runtime test.  A
    re-elaboration snippet is written; `--check-term` runs Lean on it and
    re-emits with the `#print axioms` line guarded (the `frjcert`
    two-pass discipline).
  * REFUTED: FRJW disproof → `modR` → `tabOf` → `Tab.minimise`
    (untrusted-but-checked) → SVG (`tools/Svg.lean`) + a kernel
    certificate: `okB`/`root`/`¬ force` by `decide` and
    `not_derivable_of_countermodel`.  The VERDICT itself is already
    certified in-process (`checkClosed` ran; `checkClosed_sound` and
    `decideGbuW_of_check` are compiled theorems), so `--check` is OPT-IN
    (default OFF since 2026-09-03, revising D6): it re-checks the emitted
    FILE as a standalone kernel artefact, which is what you want before
    committing a cell to the record, not on every interactive run.

FRJW objects are DISPROOFS.  A `none` from the engine route is
`not-closed-within-bound`, never a verdict (raise `--rounds`/`--jmax`/
`--pmax`; or `--proof-object` for the verified saturation, which is
infeasible beyond tiny formulas).

    lake exe pll "◯p ⊃ p" [--out=NAME] [--view=min|calc|both]
        [--check] [--check-term] [--proof-object]
        [--rounds=N] [--jmax=N] [--pmax=N] [--lamCap=N] [--maxRS=N] [--maxIS=N]

Exit codes (the `frjcert` convention):
    0  done (and, where checking ran, Lean ACCEPTED the artefacts)
    1  Lean REJECTED a generated artefact — a TOOL/ENGINE DEFECT
    2  parse error in the formula
    3  the engine's store was not certified at this budget — a FRONTIER
       MARKER, not a verdict
-/
import wip.check_closed
import FRJ.Gbu.LaxND
import LaxLogic.PLLTerms
import tools.Svg

open FRJ FRJ.Gbu FRJ.Search FRJ.Gbu.W PLLND

namespace PLLTools

/-! ## 1. Parsing (the `frjcert` grammar, atoms only — no `q<k>` names) -/

inductive Tok where
  | lp | rp | bot | top | neg | box | conj | disj | imp
  | id (s : String)
  deriving BEq, Repr

def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

partial def tokenize (cs : List Char) : Except String (List Tok) :=
  match cs with
  | [] => .ok []
  | c :: rest =>
    if c == ' ' || c == '\t' then tokenize rest
    else if c == '(' then (tokenize rest).map (.lp :: ·)
    else if c == ')' then (tokenize rest).map (.rp :: ·)
    else if c == '⊥' then (tokenize rest).map (.bot :: ·)
    else if c == '⊤' then (tokenize rest).map (.top :: ·)
    else if c == '¬' || c == '~' then (tokenize rest).map (.neg :: ·)
    else if c == '◯' || c == '#' then (tokenize rest).map (.box :: ·)
    else if c == '∧' || c == '&' then (tokenize rest).map (.conj :: ·)
    else if c == '⊃' || c == '→' then (tokenize rest).map (.imp :: ·)
    else if c == '∨' then (tokenize rest).map (.disj :: ·)
    else if c == '|' then (tokenize rest).map (.disj :: ·)
    else if c == '-' then
      match rest with
      | '>' :: r => (tokenize r).map (.imp :: ·)
      | _ => .error "stray '-'"
    else if isIdChar c then
      let name := String.ofList (c :: rest.takeWhile isIdChar)
      (tokenize (rest.dropWhile isIdChar)).map (.id name :: ·)
    else .error s!"unexpected character '{c}'"

mutual

partial def pImp (ts : List Tok) : Except String (Form × List Tok) := do
  let (a, ts) ← pDisj ts
  match ts with
  | .imp :: r => let (b, r) ← pImp r; pure (.imp a b, r)
  | _ => pure (a, ts)

partial def pDisj (ts : List Tok) : Except String (Form × List Tok) := do
  let (a, ts) ← pConj ts
  match ts with
  | .disj :: r => let (b, r) ← pDisj r; pure (.or a b, r)
  | _ => pure (a, ts)

partial def pConj (ts : List Tok) : Except String (Form × List Tok) := do
  let (a, ts) ← pUn ts
  match ts with
  | .conj :: r => let (b, r) ← pConj r; pure (.and a b, r)
  | _ => pure (a, ts)

partial def pUn (ts : List Tok) : Except String (Form × List Tok) := do
  match ts with
  | .neg :: r => let (a, r) ← pUn r; pure (.imp a .bot, r)
  | .box :: r => let (a, r) ← pUn r; pure (.circ a, r)
  | .bot :: r => pure (.bot, r)
  | .top :: r => pure (.imp .bot .bot, r)
  | .id s :: r => pure (.atom s, r)
  | .lp :: r => do
      let (a, r) ← pImp r
      match r with
      | .rp :: r' => pure (a, r')
      | _ => .error "expected ')'"
  | _ => .error "expected a formula"

end

def parseFormula (s : String) : Except String PLLFormula := do
  let ts ← tokenize s.toList
  let (g, r) ← pImp ts
  if r.isEmpty then pure (toPLL g) else .error "trailing tokens after the formula"

/-! ## 2. Source printers (paste-ready Lean) -/

/-- A `PLLFormula` as fully qualified Lean source (as
`PLLND.Search.srcOf`, copied here to keep the search engine out of the
decider's import graph). -/
def srcOfP : PLLFormula → String
  | .prop a      => s!"(PLLFormula.prop \"{a}\")"
  | .falsePLL    => "PLLFormula.falsePLL"
  | .and A B     => s!"({srcOfP A}.and {srcOfP B})"
  | .or A B      => s!"({srcOfP A}.or {srcOfP B})"
  | .ifThen A B  => s!"({srcOfP A}.ifThen {srcOfP B})"
  | .somehow A   => s!"({srcOfP A}.somehow)"

/-- de Bruijn index of a variable (as `PLLND.Var.idx`, kept local so the
tool does not import `LaxLogic.PLLRun` — that module drags
`PLLTopTop`/Mathlib ordinals into the closure for a printer). -/
def varIdx : ∀ {Γ : List PLLFormula} {φ : PLLFormula}, Var Γ φ → Nat
  | _, _, .here => 0
  | _, _, .there v => varIdx v + 1

/-- Compact λ-syntax.  A de Bruijn index prints as the bare numeral —
the `#` of `PLLRun`'s printer is redundant here and reads as
contradiction in a mathematical context (Matthew, 2026-09-03); the term
language has no numeric literals, so a bare index is unambiguous.  `λ`
is the `⊃`-intro binder and `λ'` the MONADIC one: `bind t u` prints as
`((λ'. u) t)`, replacing `let val• := t in u` (the `•` is U+2022,
dropped as unnecessary). -/
def tmPretty : ∀ {Γ : List PLLFormula} {φ : PLLFormula}, Tm Γ φ → String
  | _, _, .var v => s!"{varIdx v}"
  | _, _, .abort _ t => s!"abort {tmPretty t}"
  | _, _, .lam b => s!"(λ. {tmPretty b})"
  | _, _, .app f a => s!"({tmPretty f} {tmPretty a})"
  | _, _, .pair a b => s!"⟨{tmPretty a}, {tmPretty b}⟩"
  | _, _, .fst t => s!"{tmPretty t}.1"
  | _, _, .snd t => s!"{tmPretty t}.2"
  | _, _, .inl t => s!"(inl {tmPretty t})"
  | _, _, .inr t => s!"(inr {tmPretty t})"
  | _, _, .case t u v => s!"(case {tmPretty t} of {tmPretty u} | {tmPretty v})"
  | _, _, .val t => s!"val {tmPretty t}"
  | _, _, .bind t u => s!"((λ'. {tmPretty u}) {tmPretty t})"

/-- A variable as elaborable source. -/
def varSrc : ∀ {Γ : List PLLFormula} {φ : PLLFormula}, Var Γ φ → String
  | _, _, .here => "PLLND.Var.here"
  | _, _, .there v => s!"(PLLND.Var.there {varSrc v})"

/-- A proof term as Lean source that re-elaborates to it (modelled on
`G4cTm.src`).  The implicit formulas the goal type does NOT determine —
`app`'s argument type, the discarded component of `fst`/`snd`, `case`'s
disjuncts, `bind`'s bound type — are supplied by name. -/
def tmSrc : ∀ {Γ : List PLLFormula} {φ : PLLFormula}, Tm Γ φ → String
  | _, _, .var v => s!"(PLLND.Tm.var {varSrc v})"
  | _, _, .abort φ t => s!"(PLLND.Tm.abort {srcOfP φ} {tmSrc t})"
  | _, _, .lam t => s!"(PLLND.Tm.lam {tmSrc t})"
  | _, _, @Tm.app _ A _ f a => s!"(PLLND.Tm.app (φ := {srcOfP A}) {tmSrc f} {tmSrc a})"
  | _, _, .pair a b => s!"(PLLND.Tm.pair {tmSrc a} {tmSrc b})"
  | _, _, @Tm.fst _ _ B t => s!"(PLLND.Tm.fst (ψ := {srcOfP B}) {tmSrc t})"
  | _, _, @Tm.snd _ A _ t => s!"(PLLND.Tm.snd (φ := {srcOfP A}) {tmSrc t})"
  | _, _, .inl t => s!"(PLLND.Tm.inl {tmSrc t})"
  | _, _, .inr t => s!"(PLLND.Tm.inr {tmSrc t})"
  | _, _, @Tm.case _ A B _ t u v =>
      s!"(PLLND.Tm.case (φ := {srcOfP A}) (ψ := {srcOfP B}) {tmSrc t} {tmSrc u} {tmSrc v})"
  | _, _, .val t => s!"(PLLND.Tm.val {tmSrc t})"
  | _, _, @Tm.bind _ A _ t u => s!"(PLLND.Tm.bind (φ := {srcOfP A}) {tmSrc t} {tmSrc u})"

/-- The proof-side snippet: the term, its theorem, the audit line
(guarded on the second pass). -/
def tmSnippet (nm : String) {φ : PLLFormula} (t : Tm [] φ)
    (pin : Option String) : String :=
  "/- GENERATED by `lake exe pll`.  Do not edit. -/\n" ++
  "import LaxLogic.PLLTerms\n\n" ++
  s!"/-- The proof term the Gbu◯ decider found for `{PLLSvg.ppF (ofPLL φ)}`;\n" ++
  s!"    its Lax type is its index — the elaborator checks the agreement. -/\n" ++
  s!"def {nm}_term : PLLND.Tm [] {srcOfP φ} :=\n  {tmSrc t}\n\n" ++
  s!"theorem {nm} : Nonempty (PLLND.LaxND [] {srcOfP φ}) :=\n" ++
  s!"  ⟨({nm}_term).toND⟩\n\n" ++
  (match pin with
   | none => s!"#print axioms {nm}\n"
   | some p => s!"/-- info: {p} -/\n#guard_msgs in\n#print axioms {nm}\n")

/-- The countermodel certificate: the minimised table, its frame checks,
`¬ force` at the root by `decide`, and the pinning bridge lemma. -/
def cmFile (T : Tab) (nm : String) (φ : PLLFormula) (pin : Option String) : String :=
  "/- GENERATED by `lake exe pll`.  Do not edit. -/\n" ++
  "import FRJ.Search.Pin\n\nopen FRJ\n\n" ++
  render T s!"cm_{nm}" ++ "\n" ++
  s!"theorem cm_{nm}_ok : (cm_{nm}).okB = true := by decide\n" ++
  s!"theorem cm_{nm}_root : (cm_{nm}).root < (cm_{nm}).n := by decide\n\n" ++
  s!"def K_{nm} : Kripke := (cm_{nm}).toKripke cm_{nm}_ok cm_{nm}_root\n\n" ++
  "set_option maxRecDepth 1000000 in\n" ++
  s!"theorem {nm}_force :\n" ++
  s!"    ¬ (K_{nm}).force (K_{nm}).root (ofPLL {srcOfP φ}) := by decide\n\n" ++
  s!"/-- **⊬ {PLLSvg.ppF (ofPLL φ)}** — refuted by the finite rooted poset model above. -/\n" ++
  s!"theorem {nm} : ¬ Nonempty (PLLND.LaxND [] {srcOfP φ}) :=\n" ++
  s!"  not_derivable_of_countermodel K_{nm} {nm}_force\n\n" ++
  "/-- Control: the model is not degenerate — it still forces `⊤`. -/\n" ++
  s!"theorem cm_{nm}_control :\n" ++
  s!"    (K_{nm}).force (K_{nm}).root (ofPLL (PLLFormula.falsePLL.ifThen PLLFormula.falsePLL)) := by decide\n\n" ++
  (match pin with
   | none => s!"#print axioms {nm}\n"
   | some p => s!"/-- info: {p} -/\n#guard_msgs in\n#print axioms {nm}\n")

/-! ## 3. The seam (`docs/decider-outputs-design.md` §4.4) -/

/-- What the decider hands the output layer. -/
inductive Answer (φ : PLLFormula) where
  | proved (t : Tm [] φ)
  | refuted (fromCalc minimised : Tab)

/-- The one wiring function: everything downstream consumes `Answer φ`.
Swapping the decision source changes the argument and no other line. -/
def answerOf (φ : PLLFormula)
    (dec : GbuRC (ofPLL φ) [] (ofPLL φ) ⊕ (Σ' t Γ, FRJWr (ofPLL φ) t Γ (ofPLL φ))) :
    Answer φ :=
  match dec with
  | .inl d => .proved (toPLL_ofPLL φ ▸ ndToTm (FRJ.Gbu.laxOfR d))
  | .inr ⟨_, _, d⟩ =>
      let raw := tabOf (FRJ.W.modR d) (atomsOf (ofPLL φ)).eraseDups
      .refuted raw (raw.minimise (ofPLL φ))

/-! ## 4. The driver -/

/-- Pull the payload out of one of Lean's own axiom lines (as `frjcert`). -/
def axiomPayload (l : String) : Option String :=
  if (l.splitOn "depends on axioms:").length > 1
     || (l.splitOn "does not depend on any axioms").length > 1 then
    match l.splitOn "'" with
    | _ :: nm :: rest => some ("'" ++ nm ++ "'" ++ String.intercalate "'" rest)
    | _ => none
  else none

/-- Run Lean on one file.  **Direct `lean`, not `lake env lean`**: this
process already runs inside the environment Lake set up, so `LEAN_PATH`
is inherited and re-entering Lake costs ~8 s of config elaboration and
filesystem scan per pass, warm, for ~1.8 s of actual Lean work
(measured 2026-09-03).  `LEAN_PATH` absent means the tool was launched
outside `lake env`; say so rather than hanging in a rebuild. -/
def runLean (path : String) : IO (Option (UInt32 × String)) := do
  match ← IO.getEnv "LEAN_PATH" with
  | none =>
      IO.println "SKIPPED   no LEAN_PATH in the environment — run under `lake exe pll` \
(or `lake env`) for checking, or check the emitted file yourself."
      return none
  | some _ =>
      let r ← IO.Process.output { cmd := "lean", args := #[path] }
      return some (r.exitCode, r.stdout ++ r.stderr)

/-- Two-pass check: run Lean on the emitted file; on success re-emit with
the axiom line Lean itself printed, guarded, and run again.  Returns
`some exitCode`; `none` means the check could not run or no axiom line
was found. -/
def twoPass (path : String) (reEmit : String → String) : IO (Option UInt32) := do
  IO.println s!"checking   {path} (pass 1: unguarded pin) …"
  let t0 ← IO.monoMsNow
  match ← runLean path with
  | none => return some 0
  | some (code, txt) =>
    let t1 ← IO.monoMsNow
    for l in txt.splitOn "\n" do
      if !l.isEmpty then IO.println s!"  | {l}"
    if code != 0 then
      IO.println s!"VERDICT   LEAN REJECTED {path} (exit {code}) — a TOOL/ENGINE DEFECT."
      return some 1
    match (txt.splitOn "\n").filterMap axiomPayload with
    | p :: _ =>
        IO.FS.writeFile path (reEmit p)
        IO.println s!"checking   (pass 2: #guard_msgs-guarded pin) … [pass 1 took {t1 - t0} ms]"
        match ← runLean path with
        | none => return some 0
        | some (code2, txt2) =>
          if code2 == 0 then
            let t2 ← IO.monoMsNow
            IO.println s!"CHECKED   {path} — accepted [{t2 - t1} ms], pin GUARDED: {p}"
            return some 0
          else
            for l in txt2.splitOn "\n" do
              if !l.isEmpty then IO.println s!"  | {l}"
            IO.println "VERDICT   the guarded pin did not match — a TOOL defect."
            return some 1
    | [] => return none

structure Args where
  out : String := "pll_out"
  view : String := "min"
  check : Bool := false
  checkTerm : Bool := false
  proofObject : Bool := false
  cfg : Config :=
    { rounds := 16, jmax := 3, pmax := 2, lamCap := 24, maxRS := 3000, maxIS := 3000 }

def parseArgs (l : List String) : Except String (String × Args) := do
  let mut φ? : Option String := none
  let mut a : Args := {}
  for s in l do
    if s.startsWith "--out=" then a := { a with out := (s.drop 6).toString }
    else if s.startsWith "--view=" then
      let v := (s.drop 7).toString
      if v == "min" || v == "calc" || v == "both" then a := { a with view := v }
      else throw s!"--view must be min|calc|both, got {v}"
    else if s == "--check" then a := { a with check := true }
    else if s == "--no-check" then a := { a with check := false }
    else if s == "--check-term" then a := { a with checkTerm := true }
    else if s == "--proof-object" then a := { a with proofObject := true }
    else if s.startsWith "--rounds=" then
      a := { a with cfg := { a.cfg with rounds := (s.drop 9).toString.toNat! } }
    else if s.startsWith "--jmax=" then
      a := { a with cfg := { a.cfg with jmax := (s.drop 7).toString.toNat! } }
    else if s.startsWith "--pmax=" then
      a := { a with cfg := { a.cfg with pmax := (s.drop 7).toString.toNat! } }
    else if s.startsWith "--lamCap=" then
      a := { a with cfg := { a.cfg with lamCap := (s.drop 9).toString.toNat! } }
    else if s.startsWith "--maxRS=" then
      a := { a with cfg := { a.cfg with maxRS := (s.drop 8).toString.toNat! } }
    else if s.startsWith "--maxIS=" then
      a := { a with cfg := { a.cfg with maxIS := (s.drop 8).toString.toNat! } }
    else if s.startsWith "--" then throw s!"unknown flag {s}"
    else if φ?.isNone then φ? := some s
    else throw s!"two formulas given: {φ?.get!} and {s}"
  match φ? with
  | some f => pure (f, a)
  | none => throw "no formula given"

/-- The SVG caption for one view. -/
def captionFor (φ : PLLFormula) (T : Tab) (view : String) (rawN : Nat) :
    List String :=
  [ s!"{PLLSvg.ppF (ofPLL φ)}  —  REFUTED at w{T.root} (root), over a finite rooted poset model.",
    if view == "min" then
      s!"View: minimised, {T.n} worlds ({rawN} before minimisation)."
    else
      s!"View: from the calculus, {T.n} worlds." ]

def emitRefuted (φ : PLLFormula) (raw min : Tab) (a : Args) : IO UInt32 := do
  IO.println s!"model     {raw.n} worlds (from the calculus) → minimised {min.n}; \
frame-ok={min.okB}, refutes={min.refutes (ofPLL φ)}"
  let wr := fun (p : String) (T : Tab) (v : String) => do
    IO.FS.writeFile p (PLLSvg.svgOfTab T (ofPLL φ) { caption := captionFor φ T v raw.n })
    IO.println s!"wrote     {p}"
  match a.view with
  | "calc" => wr s!"{a.out}.svg" raw "calc"
  | "both" => wr s!"{a.out}.min.svg" min "min"; wr s!"{a.out}.calc.svg" raw "calc"
  | _ => wr s!"{a.out}.svg" min "min"
  let nm := ((a.out.splitOn "/").getLastD a.out).replace "-" "_"
  let leanPath := s!"{a.out}.lean"
  IO.FS.writeFile leanPath (cmFile min nm φ none)
  IO.println s!"wrote     {leanPath}  (kernel certificate)"
  if a.check then
    match ← twoPass leanPath (fun p => cmFile min nm φ (some p)) with
    | some c => return c
    | none => IO.println "VERDICT   no axiom line found — a TOOL defect."; return 1
  else
    IO.println s!"re-check   lean {a.out}.lean      (or pass --check; the VERDICT above is \
already certified in-process by checkClosed — this re-checks the FILE as a standalone \
kernel artefact)"
    return 0

def emitProved (φ : PLLFormula) (t : Tm [] φ) (a : Args) : IO UInt32 := do
  IO.println s!"term      {tmPretty t}"
  IO.println s!"type      {PLLSvg.ppF (ofPLL φ)}   (the term's index, by construction)"
  let nm := ((a.out.splitOn "/").getLastD a.out).replace "-" "_"
  let leanPath := s!"{a.out}.lean"
  IO.FS.writeFile leanPath (tmSnippet nm t none)
  IO.println s!"wrote     {leanPath}  (re-elaboration snippet)"
  if a.checkTerm then
    match ← twoPass leanPath (fun p => tmSnippet nm t (some p)) with
    | some c => return c
    | none => IO.println "VERDICT   no axiom line found — a TOOL defect."; return 1
  else
    return 0

def run (fs : String) (a : Args) : IO UInt32 := do
  match parseFormula fs with
  | .error e => IO.println s!"parse error: {e}"; return 2
  | .ok φ =>
    IO.println s!"formula   {PLLSvg.ppF (ofPLL φ)}"
    let t0 ← IO.monoMsNow
    let dec ← do
      if a.proofObject then
        IO.println "NOTE      --proof-object saturates the whole universe of the formula; \
infeasible beyond tiny cells."
        pure (some (decideGbuWData (ofPLL φ)))
      else
        pure (FRJ.Arity.decideDataByEngine (ofPLL φ) a.cfg)
    let t1 ← IO.monoMsNow
    match dec with
    | none =>
        IO.println s!"NOT CLOSED at this budget [{t1 - t0} ms] (rounds={a.cfg.rounds}, \
jmax={a.cfg.jmax}, pmax={a.cfg.pmax}, lamCap={a.cfg.lamCap}) — the engine's store \
did not pass checkClosed.  A frontier marker, NOT a verdict; raise the budget."
        return 3
    | some d =>
        match answerOf φ d with
        | .proved t =>
            IO.println s!"verdict   PROVED  [{t1 - t0} ms]  (Gbu◯ derivation → LaxND → Tm)"
            emitProved φ t a
        | .refuted raw min =>
            IO.println s!"verdict   REFUTED [{t1 - t0} ms]  (FRJW disproof → Kripke countermodel)"
            emitRefuted φ raw min a

/-- The `#decide` command's worker: decide, draw to `path` per `view`,
return the report (no shelling out — the command is for looking, the CLI
for certified artefacts). -/
def decideReport (φ : PLLFormula) (path : String) (view : String := "min") :
    IO String := do
  match FRJ.Arity.decideDataByEngine (ofPLL φ) ({} : Args).cfg with
  | none =>
      return s!"formula  {PLLSvg.ppF (ofPLL φ)}\nverdict  NOT CLOSED at the default budget — \
a frontier marker, not a verdict.  Use `lake exe pll` with a raised budget."
  | some d =>
      match answerOf φ d with
      | .proved t =>
          return s!"formula  {PLLSvg.ppF (ofPLL φ)}\nverdict  PROVED\nterm     {tmPretty t}\n\
type     {PLLSvg.ppF (ofPLL φ)}\n(nothing drawn: proved formulas have no countermodel)"
      | .refuted raw min =>
          let base := if path.endsWith ".svg" then String.ofList (path.toList.take (path.toList.length - 4)) else path
          let wr := fun (p : String) (T : Tab) (v : String) => do
            IO.FS.writeFile p (PLLSvg.svgOfTab T (ofPLL φ) { caption := captionFor φ T v raw.n })
          let drawn ← do
            match view with
            | "calc" => wr path raw "calc"; pure path
            | "both" =>
                wr s!"{base}.min.svg" min "min"; wr s!"{base}.calc.svg" raw "calc"
                pure s!"{base}.min.svg, {base}.calc.svg"
            | _ => wr path min "min"; pure path
          return s!"formula  {PLLSvg.ppF (ofPLL φ)}\nverdict  REFUTED at the root\n\
model    {raw.n} worlds (calculus) → {min.n} (minimised); refutes={min.refutes (ofPLL φ)}\n\
drawing  {drawn}"

end PLLTools
