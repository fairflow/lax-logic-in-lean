import FRJ.CalculusV
open FRJ Form
def aF : Form := .circ .bot
def naF : Form := .imp aF .bot
def bF : Form := .circ naF
def r4 : Form := .or aF naF
def r11 : Form := .imp bF r4
def G114 : Form := .imp r11 r4
def pp : Form → String
  | .atom s => s | .bot => "F"
  | .and x y => s!"({pp x}&{pp y})" | .or x y => s!"({pp x}|{pp y})"
  | .imp x .bot => s!"~{pp x}" | .imp x y => s!"({pp x}>{pp y})"
  | .circ x => s!"O{pp x}"
#eval ((gHat G114).map pp, (sfR G114).map pp)
#eval (decide (Form.bot ∈ sfR G114), decide (naF ∈ sfR G114),
       decide (aF ∈ sfR G114), decide (r4 ∈ sfR G114))
