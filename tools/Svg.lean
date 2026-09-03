/-
# The shared countermodel SVG renderer

Hoisted from `tools/Cert.lean`'s `FrjCert.toSvg` (which stays as the
ρ-certificate renderer) and extended per `docs/decider-outputs-design.md`
§3.5 with Matthew's convention (2026-09-02):

  * `≤`  — Hasse diagram (transitive reduction), DASHED, grey, WITH
    arrowheads, drawn low → high;
  * `Rm` — EVERY non-reflexive pair, SOLID, blue, WITH arrowheads,
    offset sideways so it never hides behind a `≤` cover edge (`Rm ⊆ ≤`
    is a filling-in of the order, so it is the solid part);
  * nodes — ordinary worlds open (white fill, dark stroke), fallible
    worlds FILLED with a `⊥` in the label, the root stroked red and
    named `root`; labels are the atoms the world is labelled with
    (`SvgOpts.subformulaLabels := true` lists every forced subformula of
    the goal instead); a `<title>` hover always carries the full forced
    set;
  * layering — by the LONGEST `≤`-chain below the world (the Hasse
    metric; `Cert`'s predecessor count over-flattens);
  * an explicit white background and a caption block below the picture.

The renderer proves nothing: soundness of a displayed countermodel is the
kernel's `decide` on the emitted certificate, never the picture.
-/
import FRJ.Search.Pin

namespace PLLSvg

open FRJ FRJ.Search

/-- Display options.  `caption` lines are drawn under the picture, after
the fixed legend line. -/
structure SvgOpts where
  /-- Label worlds with every forced subformula of the goal instead of
  the atom label (longer; the certificate style). -/
  subformulaLabels : Bool := false
  caption : List String := []

def esc (s : String) : String :=
  ((s.replace "&" "&amp;").replace "<" "&lt;").replace ">" "&gt;"

def ppF : Form → String
  | .atom p => p
  | .bot => "⊥"
  | .and a b => s!"({ppF a} ∧ {ppF b})"
  | .or a b => s!"({ppF a} ∨ {ppF b})"
  | .imp .bot .bot => "⊤"
  | .imp a .bot => s!"¬{ppF a}"
  | .imp a b => s!"({ppF a} ⊃ {ppF b})"
  | .circ a => s!"◯{ppF a}"

def subs : Form → List Form
  | .atom p => [.atom p]
  | .bot => [.bot]
  | .and a b => .and a b :: (subs a ++ subs b)
  | .or a b => .or a b :: (subs a ++ subs b)
  | .imp a b => .imp a b :: (subs a ++ subs b)
  | .circ a => .circ a :: subs a

def forcesAt (T : Tab) (w : Nat) (A : Form) : Bool :=
  match T.toKripke? with
  | none => false
  | some K => match K.elems[w]? with
              | none => false
              | some a => decide (K.force a A)

/-- Every subformula of the goal the world forces. -/
def forcedList (T : Tab) (G : Form) (w : Nat) : List Form :=
  ((subs G).eraseDups).filter (fun A => forcesAt T w A)

/-- The node label: atoms (default) or forced subformulas, with the
fallible marker. -/
def labelOf (T : Tab) (G : Form) (o : SvgOpts) (w : Nat) : String :=
  let fal := T.falT.getD w false
  let core :=
    if o.subformulaLabels then
      String.intercalate ", " ((forcedList T G w).map ppF)
    else
      String.intercalate ", " (T.atomsT.getD w [])
  if fal then (if core.isEmpty then "⊥" else s!"⊥, {core}")
  else if core.isEmpty then "∅" else core

/-- Transitive reduction of `≤`: the Hasse edges, low → high. -/
def hasse (T : Tab) : List (Nat × Nat) :=
  let le := fun a b => (T.leT.getD a []).getD b false
  (List.range T.n).flatMap fun a =>
    (List.range T.n).filterMap fun b =>
      if a != b && le a b &&
         !((List.range T.n).any (fun c => c != a && c != b && le a c && le c b))
      then some (a, b) else none

/-- Every non-reflexive `Rm` pair. -/
def rmPairs (T : Tab) : List (Nat × Nat) :=
  (List.range T.n).flatMap fun a =>
    (List.range T.n).filterMap fun b =>
      if a != b && (T.rmT.getD a []).getD b false then some (a, b) else none

/-- Layer of each world = the longest strict `≤`-chain below it (the
Hasse layering; a predecessor count over-flattens diamonds). -/
def layers (T : Tab) : Array Nat := Id.run do
  let lt := fun a b => a != b && (T.leT.getD a []).getD b false
  let mut ls : Array Nat := Array.replicate T.n 0
  for _ in [0:T.n] do
    for w in [0:T.n] do
      for v in [0:T.n] do
        if lt v w && ls[v]! + 1 > ls[w]! then
          ls := ls.set! w (ls[v]! + 1)
  return ls

/-- One edge with an arrowhead, pulled back from both node circles;
`off` is a perpendicular offset (used by `Rm` so it never hides behind a
`≤` cover edge). -/
def edgeSvg (x1 y1 x2 y2 : Float) (colour : String) (dashed : Bool)
    (marker : String) (off : Float) : String :=
  let dx := x2 - x1
  let dy := y2 - y1
  let len := Float.sqrt (dx * dx + dy * dy)
  let len := if len < 1 then 1 else len
  let (ux, uy) := (dx / len, dy / len)
  let (px, py) := (-uy * off, ux * off)
  let pull := 14.0
  let (a1, b1) := (x1 + ux * pull + px, y1 + uy * pull + py)
  let (a2, b2) := (x2 - ux * pull + px, y2 - uy * pull + py)
  s!"<line x1=\"{a1}\" y1=\"{b1}\" x2=\"{a2}\" y2=\"{b2}\" stroke=\"{colour}\" " ++
  s!"stroke-width=\"{if dashed then "1.4" else "2"}\"" ++
  (if dashed then " stroke-dasharray=\"6,4\"" else "") ++
  s!" marker-end=\"url(#{marker})\" />"

/-- **The renderer.**  `T` should already be the view wanted (raw or
minimised); this function only draws. -/
def svgOfTab (T : Tab) (G : Form) (o : SvgOpts := {}) : String :=
  let rowH : Nat := 110
  let colW : Nat := 230
  let ls := layers T
  let maxL := ls.foldl Nat.max 0
  let posOf : Nat → Nat × Nat := fun w =>
    let l := ls[w]!
    let peers := (List.range T.n).filter (fun v => ls[v]! == l)
    let k := peers.idxOf w
    (70 + k * colW, 70 + (maxL - l) * rowH)
  let labels := (List.range T.n).map (fun w => labelOf T G o w)
  let width := (List.range T.n).foldl (fun acc w =>
      Nat.max acc ((posOf w).1 + 40 + 8 * (labels.getD w "").length)) 560
  let capLines :=
    s!"dashed grey = ≤ (Hasse), solid blue = Rm (⊆ ≤, the filled-in part); ⊥ marks a fallible world" ::
    o.caption
  let height := 150 + rowH * maxL + 18 * capLines.length
  let defs :=
    "<defs>" ++
    "<marker id=\"aLe\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\"><path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"#999\"/></marker>" ++
    "<marker id=\"aRm\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\"><path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"#2266cc\"/></marker>" ++
    "</defs>"
  let fl := fun (n : Nat) => Float.ofNat n
  let les := (hasse T).map (fun (a, b) =>
    let (x1, y1) := posOf a
    let (x2, y2) := posOf b
    edgeSvg (fl x1) (fl y1) (fl x2) (fl y2) "#999" true "aLe" 0)
  let rms := (rmPairs T).map (fun (a, b) =>
    let (x1, y1) := posOf a
    let (x2, y2) := posOf b
    edgeSvg (fl x1) (fl y1) (fl x2) (fl y2) "#2266cc" false "aRm" 7)
  let nodes := (List.range T.n).map fun w =>
    let (x, y) := posOf w
    let isRoot := w == T.root
    let isFal := T.falT.getD w false
    let fill := if isFal then "#333" else "white"
    let stroke := if isRoot then "#cc2222" else "#333"
    let title := s!"<title>w{w} forces: {esc (String.intercalate ", " ((forcedList T G w).map ppF))}</title>"
    s!"<g>{title}<circle cx=\"{x}\" cy=\"{y}\" r=\"9\" fill=\"{fill}\" stroke=\"{stroke}\" stroke-width=\"2.5\" />" ++
    s!"<text x=\"{x + 15}\" y=\"{y - 5}\" font-family=\"sans-serif\" font-size=\"13\" font-weight=\"bold\"{if isRoot then " fill=\"#cc2222\"" else ""}>w{w}{if isRoot then " (root)" else ""}</text>" ++
    s!"<text x=\"{x + 15}\" y=\"{y + 13}\" font-family=\"sans-serif\" font-size=\"12\" fill=\"#444\">{esc (labels.getD w "")}</text></g>"
  let caps := capLines.zipIdx.map fun (l, i) =>
    s!"<text x=\"20\" y=\"{height - 14 - 18 * (capLines.length - 1 - i)}\" font-family=\"sans-serif\" font-size=\"12\" fill=\"#666\">{esc l}</text>"
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{width}\" height=\"{height}\" viewBox=\"0 0 {width} {height}\">\n" ++
  "<rect width=\"100%\" height=\"100%\" fill=\"white\"/>\n" ++ defs ++ "\n" ++
  String.intercalate "\n" (les ++ rms ++ nodes ++ caps) ++
  "\n</svg>\n"

end PLLSvg
