/- Weight probe for the attack banks: place the screening horizon
before spending engine time.  sum3 done = Σ 3^wNeg drives interp's
recursion; value sizes explode with it. -/
import LaxLogic.LJFOCore

open LJFO

namespace W

def pv : String := "p"
def aP : Pos := .atom pv
def aQ : Pos := .atom "q"
def uQ : Neg := .up aQ
def uR : Neg := .up (.atom "r")
def boxP : Neg := .circ aP
def boxQ : Neg := .circ aQ
def hyp : Neg := .imp (.down (.circ aP)) uR
def chi : Neg := .imp (.down hyp) (.circ aP)
def bchi : Neg := .circ (.down chi)
def joinP : Neg := .imp (.down (.circ aP)) (.circ aP)
def dq : Neg := .imp (.down (.imp aQ uR)) (.circ aQ)
def cimpNest : Neg := .imp (.down (.circ (.down (.circ aP)))) uR
def cimpNest2 : Neg := .imp (.down (.circ (.down (.circ (.down (.circ aP)))))) uR
def cimpOr : Neg := .imp (.down (.circ (.or aP aQ))) uR
def cimpImp : Neg := .imp (.down (.circ (.down (.imp aQ uR)))) uR

#eval [("hyp", wNeg hyp), ("chi", wNeg chi), ("bchi", wNeg bchi),
       ("joinP", wNeg joinP), ("dq", wNeg dq),
       ("cimpNest", wNeg cimpNest), ("cimpNest2", wNeg cimpNest2),
       ("cimpOr", wNeg cimpOr), ("cimpImp", wNeg cimpImp),
       ("boxP", wNeg boxP), ("boxQ", wNeg boxQ), ("uQ", wNeg uQ)]

#eval [("[hyp]", sum3 [hyp]), ("[joinP]", sum3 [joinP]),
       ("[hyp,boxQ]", sum3 [hyp, boxQ]),
       ("[hyp,chi]", sum3 [hyp, chi]),
       ("[hyp,bchi]", sum3 [hyp, bchi]),
       ("[cimpNest,boxP]", sum3 [cimpNest, boxP]),
       ("[cimpNest2,boxP]", sum3 [cimpNest2, boxP])]

/- Node count of an interpolant value. -/
mutual
def szP : Pos → Nat
  | .atom _ => 1
  | .fls => 1
  | .or P Q => szP P + szP Q + 1
  | .down M => szN M + 1
def szN : Neg → Nat
  | .up P => szP P + 1
  | .imp Q N => szP Q + szN N + 1
  | .and M N => szN M + szN N + 1
  | .circ P => szP P + 1
end

#eval ("E[hyp]", szN (interp pv [] [hyp] none))
#eval ("A[hyp=>op]", szN (interp pv [] [hyp] (some (.up (.down (.circ aP))))))
#eval ("E[joinP]", szN (interp pv [] [joinP] none))
#eval ("E[hyp,boxQ]", szN (interp pv [] [hyp, boxQ] none))
#eval ("A[boxQ=>op]", szN (interp pv [] [boxQ] (some (.up (.down (.circ aP))))))

end W
