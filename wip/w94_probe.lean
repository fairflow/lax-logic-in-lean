import FRJ.CalculusV
open FRJ Form
def aF : Form := .circ .bot
def naF : Form := .imp aF .bot
def bF : Form := .circ naF
def nnaF : Form := .imp naF .bot
def r4 : Form := .or aF naF
def r9 : Form := .or bF nnaF
def G94 : Form := .imp r9 r4
def pp : Form → String
  | .atom s => s | .bot => "F"
  | .and x y => s!"({pp x}&{pp y})" | .or x y => s!"({pp x}|{pp y})"
  | .imp x .bot => s!"~{pp x}" | .imp x y => s!"({pp x}>{pp y})"
  | .circ x => s!"O{pp x}"
#eval ((gHat G94).map pp, (vacZoneA G94 []).map pp)
#eval (decide (Form.bot ∈ sfR G94), decide (naF ∈ sfR G94),
       decide (aF ∈ sfR G94), decide (r4 ∈ sfR G94),
       decide (classForce [] Form.bot))
