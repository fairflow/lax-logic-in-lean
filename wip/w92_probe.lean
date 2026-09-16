import FRJ.CalculusV
open FRJ Form
def aF : Form := .circ .bot
def naF : Form := .imp aF .bot
def bF : Form := .circ naF
def nnaF : Form := .imp naF .bot
def r9 : Form := .or bF nnaF
def G92 : Form := .imp r9 aF
def G90 : Form := .imp r9 .bot
#eval (decide (aF ∈ sfR G92), decide (Form.bot ∈ sfR G92), decide (G92 ∈ sfR G92),
       decide (Form.bot ∈ sfR G90), decide (G90 ∈ sfR G90),
       decide (bF ∈ gHat G92), decide (bF ∈ gHat G90))
