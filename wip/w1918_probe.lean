import FRJ.CalculusV

open FRJ Form

-- the alphabet (W1215 names: β=a, ν=¬a, σ=b, δ=¬¬a, ι=ρ8)
def aF : Form := .circ .bot
def naF : Form := .imp aF .bot
def bF : Form := .circ naF
def nnaF : Form := .imp naF .bot
def r4 : Form := .or aF naF
def r9 : Form := .or bF nnaF
def r11 : Form := .imp bF r4
def r14 : Form := .imp r9 r4
def r18 : Form := .or r14 r9
def r19 : Form := .imp r11 bF
def G1918 : Form := .imp r19 r18

def pp : Form → String
  | .atom s => s
  | .bot => "F"
  | .and x y => s!"({pp x}&{pp y})"
  | .or x y => s!"({pp x}|{pp y})"
  | .imp x .bot => s!"~{pp x}"
  | .imp x y => s!"({pp x}>{pp y})"
  | .circ x => s!"O{pp x}"

#eval (sfR G1918).map pp
#eval (gHat G1918).map pp
#eval (gAt G1918).map pp
#eval ((gImp G1918).map pp, (gCirc G1918).map pp)
-- membership probes for planned conclusions
#eval (decide (Form.bot ∈ sfR G1918), decide (naF ∈ sfR G1918),
       decide (aF ∈ sfR G1918), decide (bF ∈ sfR G1918),
       decide (r4 ∈ sfR G1918), decide (nnaF ∈ sfR G1918),
       decide (r14 ∈ sfR G1918), decide (r9 ∈ sfR G1918),
       decide (r18 ∈ sfR G1918))
