import FRJ.CalculusV
open FRJ Form
def aF : Form := .circ .bot
def naF : Form := .imp aF .bot
def bF : Form := .circ naF
def nnaF : Form := .imp naF .bot
def r4 : Form := .or aF naF
def r6 : Form := .or naF nnaF
def r8 : Form := .imp nnaF aF
def r11 : Form := .imp bF r4
def r12 : Form := .imp r8 bF
def r13 : Form := .imp r8 r4
def r20 : Form := .imp r11 r6
def G2012 : Form := .imp r20 r12
def G2013 : Form := .imp r20 r13
def pp : Form → String
  | .atom s => s | .bot => "F"
  | .and x y => s!"({pp x}&{pp y})" | .or x y => s!"({pp x}|{pp y})"
  | .imp x .bot => s!"~{pp x}" | .imp x y => s!"({pp x}>{pp y})"
  | .circ x => s!"O{pp x}"
#eval ((gHat G2012).map pp, (gHat G2013).map pp)
-- sfR memberships needed by the two designs
#eval ("G2013", decide (Form.bot ∈ sfR G2013), decide (naF ∈ sfR G2013),
  decide (aF ∈ sfR G2013), decide (nnaF ∈ sfR G2013), decide (r4 ∈ sfR G2013),
  decide (r11 ∈ sfR G2013), decide (r13 ∈ sfR G2013), decide (bF ∈ sfR G2013))
#eval ("G2012", decide (Form.bot ∈ sfR G2012), decide (naF ∈ sfR G2012),
  decide (aF ∈ sfR G2012), decide (nnaF ∈ sfR G2012), decide (r4 ∈ sfR G2012),
  decide (r11 ∈ sfR G2012), decide (r12 ∈ sfR G2012), decide (bF ∈ sfR G2012))
-- Ĝ membership of the context riders
#eval ("hat", decide (r8 ∈ gHat G2012), decide (r20 ∈ gHat G2012),
  decide (bF ∈ gHat G2012), decide (r8 ∈ gHat G2013), decide (r20 ∈ gHat G2013),
  decide (bF ∈ gHat G2013), decide (naF ∈ gHat G2013))
