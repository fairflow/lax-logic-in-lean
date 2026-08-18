/-
# RN(◯,{}) dictionary cells refuted by the FRJ(◯) search — GENERATED FILE

Produced by `sh tools/rn-cert-gen.sh` + `python3 tools/rn-cert-asm.py`.

Each block below is a countermodel found by the FRJ(◯) forward-saturation
search (`FRJ/Search/Fast.lean`), extracted from the derivation the search
built (`FRJ.modR`), minimised, and re-checked here BY THE KERNEL: the frame
conditions and the refutation are both `decide`, and the conclusion goes
through `FRJ.not_entails_of_countermodel`, which is a theorem about the
original `LaxND` judgment.  The search is nowhere in the certificate.

Every goal below was NOT refuted by the exhaustive ≤4-world battery: every
model here needs five worlds or more, which is why these were open.

READ THE NAMES CAREFULLY.  An open cell of `wip/rnDict.lean` carries a
CANDIDATE LIST and is sorried at the FIRST open candidate, so refuting the
stated collapse eliminates ONE candidate and closes the cell only when that
candidate was the last.

* `<cell>_FALSE` refutes the collapse as the dictionary states it.
* `<cell>_qK_FALSE` refutes the collapse against representative `qK`
  instead — that is how a SURVIVING candidate is eliminated.
* `<cell>_no_candidate` is emitted only where every candidate is gone, and
  IS the statement that the fifteen-representative closure fails at that
  cell.  Its scope is exactly the candidates named in it: the remaining
  representatives were eliminated earlier by the ≤4-world battery, which is
  what produced the candidate list, and that elimination is recorded in
  `wip/rnDict.lean`, not re-proved here.

Goals refuted here: 24 — cAnd_10_13, cAnd_11_13, cBox_11, cBox_11_q11, cBox_11_q13, cImp_10_7, cImp_11_7, cImp_12_11, cImp_12_11_q11, cImp_12_11_q13, cImp_8_4, cImp_8_5, cOr_10_12, cOr_10_12_q11, cOr_10_12_q13, cOr_10_14, cOr_11_12, cOr_11_12_q11, cOr_11_12_q13, cOr_11_14, cOr_8_10, cOr_8_11, cOr_8_12, cOr_8_14.
-/
import FRJ.Search.Pin
import LaxLogic.PLLSemUIFrag
import wip.rnBank

namespace RNFRJCerts

open FRJ


/-! ### `cAnd_10_13` — the stated collapse is FALSE (← direction) -/

def cm_cAnd_10_13_bwd : Search.Tab where
  n := 5
  root := 0
  leT := [[true, true, true, true, true], [false, true, true, true, true], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  rmT := [[true, false, false, false, false], [false, true, false, false, true], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  falT := [false, false, false, true, false]
  atomsT := [[], [], [], [], []]

theorem cm_cAnd_10_13_bwd_ok : cm_cAnd_10_13_bwd.okB = true := by decide
theorem cm_cAnd_10_13_bwd_root : cm_cAnd_10_13_bwd.root < cm_cAnd_10_13_bwd.n := by decide

def K_cAnd_10_13_bwd : Kripke := cm_cAnd_10_13_bwd.toKripke cm_cAnd_10_13_bwd_ok cm_cAnd_10_13_bwd_root

set_option maxRecDepth 1000000 in
theorem cm_cAnd_10_13_bwd_force :
    ¬ (K_cAnd_10_13_bwd).force (K_cAnd_10_13_bwd).root
        (ofPLL (.ifThen (RNBank.q10) (RNBank.q10.and RNBank.q13))) := by decide

theorem cAnd_10_13_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q10.and RNBank.q13) (RNBank.q10) :=
  fun h => not_entails_of_countermodel (K_cAnd_10_13_bwd) cm_cAnd_10_13_bwd_force h.2

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cAnd_10_13_bwd_control :
    (K_cAnd_10_13_bwd).force (K_cAnd_10_13_bwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cAnd_11_13` — the stated collapse is FALSE (← direction) -/

def cm_cAnd_11_13_bwd : Search.Tab where
  n := 5
  root := 0
  leT := [[true, true, true, true, true], [false, true, true, true, true], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  rmT := [[true, false, false, false, false], [false, true, false, false, true], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  falT := [false, false, false, true, false]
  atomsT := [[], [], [], [], []]

theorem cm_cAnd_11_13_bwd_ok : cm_cAnd_11_13_bwd.okB = true := by decide
theorem cm_cAnd_11_13_bwd_root : cm_cAnd_11_13_bwd.root < cm_cAnd_11_13_bwd.n := by decide

def K_cAnd_11_13_bwd : Kripke := cm_cAnd_11_13_bwd.toKripke cm_cAnd_11_13_bwd_ok cm_cAnd_11_13_bwd_root

set_option maxRecDepth 1000000 in
theorem cm_cAnd_11_13_bwd_force :
    ¬ (K_cAnd_11_13_bwd).force (K_cAnd_11_13_bwd).root
        (ofPLL (.ifThen (RNBank.q1) (RNBank.q11.and RNBank.q13))) := by decide

theorem cAnd_11_13_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q11.and RNBank.q13) (RNBank.q1) :=
  fun h => not_entails_of_countermodel (K_cAnd_11_13_bwd) cm_cAnd_11_13_bwd_force h.2

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cAnd_11_13_bwd_control :
    (K_cAnd_11_13_bwd).force (K_cAnd_11_13_bwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cBox_11` — the stated collapse is FALSE (← direction) -/

def cm_cBox_11_bwd : Search.Tab where
  n := 5
  root := 0
  leT := [[true, true, true, true, true], [false, true, true, true, false], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  rmT := [[true, false, false, false, false], [false, true, false, false, false], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  falT := [false, false, false, true, false]
  atomsT := [[], [], [], [], []]

theorem cm_cBox_11_bwd_ok : cm_cBox_11_bwd.okB = true := by decide
theorem cm_cBox_11_bwd_root : cm_cBox_11_bwd.root < cm_cBox_11_bwd.n := by decide

def K_cBox_11_bwd : Kripke := cm_cBox_11_bwd.toKripke cm_cBox_11_bwd_ok cm_cBox_11_bwd_root

set_option maxRecDepth 1000000 in
theorem cm_cBox_11_bwd_force :
    ¬ (K_cBox_11_bwd).force (K_cBox_11_bwd).root
        (ofPLL (.ifThen (RNBank.q1) (RNBank.q11.somehow))) := by decide

theorem cBox_11_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q11.somehow) (RNBank.q1) :=
  fun h => not_entails_of_countermodel (K_cBox_11_bwd) cm_cBox_11_bwd_force h.2

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cBox_11_bwd_control :
    (K_cBox_11_bwd).force (K_cBox_11_bwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cBox_11_q11` — the stated collapse is FALSE (→ direction) -/

def cm_cBox_11_q11_fwd : Search.Tab where
  n := 5
  root := 0
  leT := [[true, true, true, true, true], [false, true, false, false, false], [false, false, true, true, true], [false, false, false, true, true], [false, false, false, false, true]]
  rmT := [[true, false, true, false, false], [false, true, false, false, false], [false, false, true, false, false], [false, false, false, true, true], [false, false, false, false, true]]
  falT := [false, false, false, false, true]
  atomsT := [[], [], [], [], []]

theorem cm_cBox_11_q11_fwd_ok : cm_cBox_11_q11_fwd.okB = true := by decide
theorem cm_cBox_11_q11_fwd_root : cm_cBox_11_q11_fwd.root < cm_cBox_11_q11_fwd.n := by decide

def K_cBox_11_q11_fwd : Kripke := cm_cBox_11_q11_fwd.toKripke cm_cBox_11_q11_fwd_ok cm_cBox_11_q11_fwd_root

set_option maxRecDepth 1000000 in
theorem cm_cBox_11_q11_fwd_force :
    ¬ (K_cBox_11_q11_fwd).force (K_cBox_11_q11_fwd).root
        (ofPLL (.ifThen (RNBank.q11.somehow) (RNBank.q11))) := by decide

theorem cBox_11_q11_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q11.somehow) (RNBank.q11) :=
  fun h => not_entails_of_countermodel (K_cBox_11_q11_fwd) cm_cBox_11_q11_fwd_force h.1

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cBox_11_q11_fwd_control :
    (K_cBox_11_q11_fwd).force (K_cBox_11_q11_fwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cBox_11_q13` — the stated collapse is FALSE (→ direction) -/

def cm_cBox_11_q13_fwd : Search.Tab where
  n := 5
  root := 0
  leT := [[true, true, true, true, true], [false, true, true, true, true], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  rmT := [[true, false, false, false, false], [false, true, false, false, true], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  falT := [false, false, false, true, false]
  atomsT := [[], [], [], [], []]

theorem cm_cBox_11_q13_fwd_ok : cm_cBox_11_q13_fwd.okB = true := by decide
theorem cm_cBox_11_q13_fwd_root : cm_cBox_11_q13_fwd.root < cm_cBox_11_q13_fwd.n := by decide

def K_cBox_11_q13_fwd : Kripke := cm_cBox_11_q13_fwd.toKripke cm_cBox_11_q13_fwd_ok cm_cBox_11_q13_fwd_root

set_option maxRecDepth 1000000 in
theorem cm_cBox_11_q13_fwd_force :
    ¬ (K_cBox_11_q13_fwd).force (K_cBox_11_q13_fwd).root
        (ofPLL (.ifThen (RNBank.q11.somehow) (RNBank.q13))) := by decide

theorem cBox_11_q13_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q11.somehow) (RNBank.q13) :=
  fun h => not_entails_of_countermodel (K_cBox_11_q13_fwd) cm_cBox_11_q13_fwd_force h.1

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cBox_11_q13_fwd_control :
    (K_cBox_11_q13_fwd).force (K_cBox_11_q13_fwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cImp_10_7` — the stated collapse is FALSE (→ direction) -/

def cm_cImp_10_7_fwd : Search.Tab where
  n := 5
  root := 0
  leT := [[true, true, true, true, true], [false, true, true, true, false], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  rmT := [[true, false, false, false, false], [false, true, false, false, false], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  falT := [false, false, false, true, false]
  atomsT := [[], [], [], [], []]

theorem cm_cImp_10_7_fwd_ok : cm_cImp_10_7_fwd.okB = true := by decide
theorem cm_cImp_10_7_fwd_root : cm_cImp_10_7_fwd.root < cm_cImp_10_7_fwd.n := by decide

def K_cImp_10_7_fwd : Kripke := cm_cImp_10_7_fwd.toKripke cm_cImp_10_7_fwd_ok cm_cImp_10_7_fwd_root

set_option maxRecDepth 1000000 in
theorem cm_cImp_10_7_fwd_force :
    ¬ (K_cImp_10_7_fwd).force (K_cImp_10_7_fwd).root
        (ofPLL (.ifThen (RNBank.q10.ifThen RNBank.q7) (RNBank.q7))) := by decide

theorem cImp_10_7_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q10.ifThen RNBank.q7) (RNBank.q7) :=
  fun h => not_entails_of_countermodel (K_cImp_10_7_fwd) cm_cImp_10_7_fwd_force h.1

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cImp_10_7_fwd_control :
    (K_cImp_10_7_fwd).force (K_cImp_10_7_fwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cImp_11_7` — the stated collapse is FALSE (→ direction) -/

def cm_cImp_11_7_fwd : Search.Tab where
  n := 5
  root := 0
  leT := [[true, true, true, true, true], [false, true, true, true, false], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  rmT := [[true, false, false, false, false], [false, true, false, false, false], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  falT := [false, false, false, true, false]
  atomsT := [[], [], [], [], []]

theorem cm_cImp_11_7_fwd_ok : cm_cImp_11_7_fwd.okB = true := by decide
theorem cm_cImp_11_7_fwd_root : cm_cImp_11_7_fwd.root < cm_cImp_11_7_fwd.n := by decide

def K_cImp_11_7_fwd : Kripke := cm_cImp_11_7_fwd.toKripke cm_cImp_11_7_fwd_ok cm_cImp_11_7_fwd_root

set_option maxRecDepth 1000000 in
theorem cm_cImp_11_7_fwd_force :
    ¬ (K_cImp_11_7_fwd).force (K_cImp_11_7_fwd).root
        (ofPLL (.ifThen (RNBank.q11.ifThen RNBank.q7) (RNBank.q7))) := by decide

theorem cImp_11_7_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q11.ifThen RNBank.q7) (RNBank.q7) :=
  fun h => not_entails_of_countermodel (K_cImp_11_7_fwd) cm_cImp_11_7_fwd_force h.1

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cImp_11_7_fwd_control :
    (K_cImp_11_7_fwd).force (K_cImp_11_7_fwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cImp_12_11` — the stated collapse is FALSE (← direction) -/

def cm_cImp_12_11_bwd : Search.Tab where
  n := 5
  root := 0
  leT := [[true, true, true, true, true], [false, true, true, true, false], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  rmT := [[true, false, false, false, true], [false, true, false, false, false], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  falT := [false, false, false, true, false]
  atomsT := [[], [], [], [], []]

theorem cm_cImp_12_11_bwd_ok : cm_cImp_12_11_bwd.okB = true := by decide
theorem cm_cImp_12_11_bwd_root : cm_cImp_12_11_bwd.root < cm_cImp_12_11_bwd.n := by decide

def K_cImp_12_11_bwd : Kripke := cm_cImp_12_11_bwd.toKripke cm_cImp_12_11_bwd_ok cm_cImp_12_11_bwd_root

set_option maxRecDepth 1000000 in
theorem cm_cImp_12_11_bwd_force :
    ¬ (K_cImp_12_11_bwd).force (K_cImp_12_11_bwd).root
        (ofPLL (.ifThen (RNBank.q1) (RNBank.q12.ifThen RNBank.q11))) := by decide

theorem cImp_12_11_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q12.ifThen RNBank.q11) (RNBank.q1) :=
  fun h => not_entails_of_countermodel (K_cImp_12_11_bwd) cm_cImp_12_11_bwd_force h.2

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cImp_12_11_bwd_control :
    (K_cImp_12_11_bwd).force (K_cImp_12_11_bwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cImp_12_11_q11` — the stated collapse is FALSE (→ direction) -/

def cm_cImp_12_11_q11_fwd : Search.Tab where
  n := 5
  root := 0
  leT := [[true, true, true, true, true], [false, true, true, true, false], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  rmT := [[true, false, false, false, false], [false, true, false, false, false], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  falT := [false, false, false, true, false]
  atomsT := [[], [], [], [], []]

theorem cm_cImp_12_11_q11_fwd_ok : cm_cImp_12_11_q11_fwd.okB = true := by decide
theorem cm_cImp_12_11_q11_fwd_root : cm_cImp_12_11_q11_fwd.root < cm_cImp_12_11_q11_fwd.n := by decide

def K_cImp_12_11_q11_fwd : Kripke := cm_cImp_12_11_q11_fwd.toKripke cm_cImp_12_11_q11_fwd_ok cm_cImp_12_11_q11_fwd_root

set_option maxRecDepth 1000000 in
theorem cm_cImp_12_11_q11_fwd_force :
    ¬ (K_cImp_12_11_q11_fwd).force (K_cImp_12_11_q11_fwd).root
        (ofPLL (.ifThen (RNBank.q12.ifThen RNBank.q11) (RNBank.q11))) := by decide

theorem cImp_12_11_q11_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q12.ifThen RNBank.q11) (RNBank.q11) :=
  fun h => not_entails_of_countermodel (K_cImp_12_11_q11_fwd) cm_cImp_12_11_q11_fwd_force h.1

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cImp_12_11_q11_fwd_control :
    (K_cImp_12_11_q11_fwd).force (K_cImp_12_11_q11_fwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cImp_12_11_q13` — the stated collapse is FALSE (→ direction) -/

def cm_cImp_12_11_q13_fwd : Search.Tab where
  n := 5
  root := 0
  leT := [[true, true, true, true, true], [false, true, true, true, true], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  rmT := [[true, false, false, false, false], [false, true, false, false, true], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  falT := [false, false, false, true, false]
  atomsT := [[], [], [], [], []]

theorem cm_cImp_12_11_q13_fwd_ok : cm_cImp_12_11_q13_fwd.okB = true := by decide
theorem cm_cImp_12_11_q13_fwd_root : cm_cImp_12_11_q13_fwd.root < cm_cImp_12_11_q13_fwd.n := by decide

def K_cImp_12_11_q13_fwd : Kripke := cm_cImp_12_11_q13_fwd.toKripke cm_cImp_12_11_q13_fwd_ok cm_cImp_12_11_q13_fwd_root

set_option maxRecDepth 1000000 in
theorem cm_cImp_12_11_q13_fwd_force :
    ¬ (K_cImp_12_11_q13_fwd).force (K_cImp_12_11_q13_fwd).root
        (ofPLL (.ifThen (RNBank.q12.ifThen RNBank.q11) (RNBank.q13))) := by decide

theorem cImp_12_11_q13_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q12.ifThen RNBank.q11) (RNBank.q13) :=
  fun h => not_entails_of_countermodel (K_cImp_12_11_q13_fwd) cm_cImp_12_11_q13_fwd_force h.1

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cImp_12_11_q13_fwd_control :
    (K_cImp_12_11_q13_fwd).force (K_cImp_12_11_q13_fwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cImp_8_4` — the stated collapse is FALSE (→ direction) -/

def cm_cImp_8_4_fwd : Search.Tab where
  n := 5
  root := 0
  leT := [[true, true, true, true, true], [false, true, true, true, true], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  rmT := [[true, false, false, false, false], [false, true, false, false, true], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  falT := [false, false, false, true, false]
  atomsT := [[], [], [], [], []]

theorem cm_cImp_8_4_fwd_ok : cm_cImp_8_4_fwd.okB = true := by decide
theorem cm_cImp_8_4_fwd_root : cm_cImp_8_4_fwd.root < cm_cImp_8_4_fwd.n := by decide

def K_cImp_8_4_fwd : Kripke := cm_cImp_8_4_fwd.toKripke cm_cImp_8_4_fwd_ok cm_cImp_8_4_fwd_root

set_option maxRecDepth 1000000 in
theorem cm_cImp_8_4_fwd_force :
    ¬ (K_cImp_8_4_fwd).force (K_cImp_8_4_fwd).root
        (ofPLL (.ifThen (RNBank.q8.ifThen RNBank.q4) (RNBank.q5))) := by decide

theorem cImp_8_4_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q8.ifThen RNBank.q4) (RNBank.q5) :=
  fun h => not_entails_of_countermodel (K_cImp_8_4_fwd) cm_cImp_8_4_fwd_force h.1

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cImp_8_4_fwd_control :
    (K_cImp_8_4_fwd).force (K_cImp_8_4_fwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cImp_8_5` — the stated collapse is FALSE (→ direction) -/

def cm_cImp_8_5_fwd : Search.Tab where
  n := 5
  root := 0
  leT := [[true, true, true, true, true], [false, true, true, true, true], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  rmT := [[true, false, false, false, false], [false, true, false, false, true], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  falT := [false, false, false, true, false]
  atomsT := [[], [], [], [], []]

theorem cm_cImp_8_5_fwd_ok : cm_cImp_8_5_fwd.okB = true := by decide
theorem cm_cImp_8_5_fwd_root : cm_cImp_8_5_fwd.root < cm_cImp_8_5_fwd.n := by decide

def K_cImp_8_5_fwd : Kripke := cm_cImp_8_5_fwd.toKripke cm_cImp_8_5_fwd_ok cm_cImp_8_5_fwd_root

set_option maxRecDepth 1000000 in
theorem cm_cImp_8_5_fwd_force :
    ¬ (K_cImp_8_5_fwd).force (K_cImp_8_5_fwd).root
        (ofPLL (.ifThen (RNBank.q8.ifThen RNBank.q5) (RNBank.q5))) := by decide

theorem cImp_8_5_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q8.ifThen RNBank.q5) (RNBank.q5) :=
  fun h => not_entails_of_countermodel (K_cImp_8_5_fwd) cm_cImp_8_5_fwd_force h.1

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cImp_8_5_fwd_control :
    (K_cImp_8_5_fwd).force (K_cImp_8_5_fwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cOr_10_12` — the stated collapse is FALSE (← direction) -/

def cm_cOr_10_12_bwd : Search.Tab where
  n := 5
  root := 0
  leT := [[true, true, true, true, true], [false, true, true, true, false], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  rmT := [[true, false, false, false, false], [false, true, false, false, false], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  falT := [false, false, false, true, false]
  atomsT := [[], [], [], [], []]

theorem cm_cOr_10_12_bwd_ok : cm_cOr_10_12_bwd.okB = true := by decide
theorem cm_cOr_10_12_bwd_root : cm_cOr_10_12_bwd.root < cm_cOr_10_12_bwd.n := by decide

def K_cOr_10_12_bwd : Kripke := cm_cOr_10_12_bwd.toKripke cm_cOr_10_12_bwd_ok cm_cOr_10_12_bwd_root

set_option maxRecDepth 1000000 in
theorem cm_cOr_10_12_bwd_force :
    ¬ (K_cOr_10_12_bwd).force (K_cOr_10_12_bwd).root
        (ofPLL (.ifThen (RNBank.q1) (RNBank.q10.or RNBank.q12))) := by decide

theorem cOr_10_12_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q10.or RNBank.q12) (RNBank.q1) :=
  fun h => not_entails_of_countermodel (K_cOr_10_12_bwd) cm_cOr_10_12_bwd_force h.2

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cOr_10_12_bwd_control :
    (K_cOr_10_12_bwd).force (K_cOr_10_12_bwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cOr_10_12_q11` — the stated collapse is FALSE (→ direction) -/

def cm_cOr_10_12_q11_fwd : Search.Tab where
  n := 5
  root := 0
  leT := [[true, true, true, true, true], [false, true, false, false, false], [false, false, true, true, true], [false, false, false, true, true], [false, false, false, false, true]]
  rmT := [[true, false, true, false, false], [false, true, false, false, false], [false, false, true, false, false], [false, false, false, true, true], [false, false, false, false, true]]
  falT := [false, false, false, false, true]
  atomsT := [[], [], [], [], []]

theorem cm_cOr_10_12_q11_fwd_ok : cm_cOr_10_12_q11_fwd.okB = true := by decide
theorem cm_cOr_10_12_q11_fwd_root : cm_cOr_10_12_q11_fwd.root < cm_cOr_10_12_q11_fwd.n := by decide

def K_cOr_10_12_q11_fwd : Kripke := cm_cOr_10_12_q11_fwd.toKripke cm_cOr_10_12_q11_fwd_ok cm_cOr_10_12_q11_fwd_root

set_option maxRecDepth 1000000 in
theorem cm_cOr_10_12_q11_fwd_force :
    ¬ (K_cOr_10_12_q11_fwd).force (K_cOr_10_12_q11_fwd).root
        (ofPLL (.ifThen (RNBank.q10.or RNBank.q12) (RNBank.q11))) := by decide

theorem cOr_10_12_q11_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q10.or RNBank.q12) (RNBank.q11) :=
  fun h => not_entails_of_countermodel (K_cOr_10_12_q11_fwd) cm_cOr_10_12_q11_fwd_force h.1

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cOr_10_12_q11_fwd_control :
    (K_cOr_10_12_q11_fwd).force (K_cOr_10_12_q11_fwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cOr_10_12_q13` — the stated collapse is FALSE (→ direction) -/

def cm_cOr_10_12_q13_fwd : Search.Tab where
  n := 5
  root := 0
  leT := [[true, true, true, true, true], [false, true, true, true, true], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  rmT := [[true, false, false, false, false], [false, true, false, false, true], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  falT := [false, false, false, true, false]
  atomsT := [[], [], [], [], []]

theorem cm_cOr_10_12_q13_fwd_ok : cm_cOr_10_12_q13_fwd.okB = true := by decide
theorem cm_cOr_10_12_q13_fwd_root : cm_cOr_10_12_q13_fwd.root < cm_cOr_10_12_q13_fwd.n := by decide

def K_cOr_10_12_q13_fwd : Kripke := cm_cOr_10_12_q13_fwd.toKripke cm_cOr_10_12_q13_fwd_ok cm_cOr_10_12_q13_fwd_root

set_option maxRecDepth 1000000 in
theorem cm_cOr_10_12_q13_fwd_force :
    ¬ (K_cOr_10_12_q13_fwd).force (K_cOr_10_12_q13_fwd).root
        (ofPLL (.ifThen (RNBank.q10.or RNBank.q12) (RNBank.q13))) := by decide

theorem cOr_10_12_q13_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q10.or RNBank.q12) (RNBank.q13) :=
  fun h => not_entails_of_countermodel (K_cOr_10_12_q13_fwd) cm_cOr_10_12_q13_fwd_force h.1

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cOr_10_12_q13_fwd_control :
    (K_cOr_10_12_q13_fwd).force (K_cOr_10_12_q13_fwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cOr_10_14` — the stated collapse is FALSE (← direction) -/

def cm_cOr_10_14_bwd : Search.Tab where
  n := 8
  root := 0
  leT := [[true, true, true, true, true, true, true, true], [false, true, true, true, true, false, false, false], [false, false, true, false, false, false, false, false], [false, false, false, true, true, false, false, false], [false, false, false, false, true, false, false, false], [false, false, false, false, false, true, true, true], [false, false, false, false, false, false, true, true], [false, false, false, false, false, false, false, true]]
  rmT := [[true, false, false, false, false, false, false, false], [false, true, false, false, false, false, false, false], [false, false, true, false, false, false, false, false], [false, false, false, true, true, false, false, false], [false, false, false, false, true, false, false, false], [false, false, false, false, false, true, false, false], [false, false, false, false, false, false, true, true], [false, false, false, false, false, false, false, true]]
  falT := [false, false, false, false, true, false, false, true]
  atomsT := [[], [], [], [], [], [], [], []]

theorem cm_cOr_10_14_bwd_ok : cm_cOr_10_14_bwd.okB = true := by decide
theorem cm_cOr_10_14_bwd_root : cm_cOr_10_14_bwd.root < cm_cOr_10_14_bwd.n := by decide

def K_cOr_10_14_bwd : Kripke := cm_cOr_10_14_bwd.toKripke cm_cOr_10_14_bwd_ok cm_cOr_10_14_bwd_root

set_option maxRecDepth 1000000 in
theorem cm_cOr_10_14_bwd_force :
    ¬ (K_cOr_10_14_bwd).force (K_cOr_10_14_bwd).root
        (ofPLL (.ifThen (RNBank.q1) (RNBank.q10.or RNBank.q14))) := by decide

theorem cOr_10_14_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q10.or RNBank.q14) (RNBank.q1) :=
  fun h => not_entails_of_countermodel (K_cOr_10_14_bwd) cm_cOr_10_14_bwd_force h.2

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cOr_10_14_bwd_control :
    (K_cOr_10_14_bwd).force (K_cOr_10_14_bwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cOr_11_12` — the stated collapse is FALSE (← direction) -/

def cm_cOr_11_12_bwd : Search.Tab where
  n := 5
  root := 0
  leT := [[true, true, true, true, true], [false, true, true, true, false], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  rmT := [[true, false, false, false, false], [false, true, false, false, false], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  falT := [false, false, false, true, false]
  atomsT := [[], [], [], [], []]

theorem cm_cOr_11_12_bwd_ok : cm_cOr_11_12_bwd.okB = true := by decide
theorem cm_cOr_11_12_bwd_root : cm_cOr_11_12_bwd.root < cm_cOr_11_12_bwd.n := by decide

def K_cOr_11_12_bwd : Kripke := cm_cOr_11_12_bwd.toKripke cm_cOr_11_12_bwd_ok cm_cOr_11_12_bwd_root

set_option maxRecDepth 1000000 in
theorem cm_cOr_11_12_bwd_force :
    ¬ (K_cOr_11_12_bwd).force (K_cOr_11_12_bwd).root
        (ofPLL (.ifThen (RNBank.q1) (RNBank.q11.or RNBank.q12))) := by decide

theorem cOr_11_12_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q11.or RNBank.q12) (RNBank.q1) :=
  fun h => not_entails_of_countermodel (K_cOr_11_12_bwd) cm_cOr_11_12_bwd_force h.2

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cOr_11_12_bwd_control :
    (K_cOr_11_12_bwd).force (K_cOr_11_12_bwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cOr_11_12_q11` — the stated collapse is FALSE (→ direction) -/

def cm_cOr_11_12_q11_fwd : Search.Tab where
  n := 5
  root := 0
  leT := [[true, true, true, true, true], [false, true, false, false, false], [false, false, true, true, true], [false, false, false, true, true], [false, false, false, false, true]]
  rmT := [[true, false, true, false, false], [false, true, false, false, false], [false, false, true, false, false], [false, false, false, true, true], [false, false, false, false, true]]
  falT := [false, false, false, false, true]
  atomsT := [[], [], [], [], []]

theorem cm_cOr_11_12_q11_fwd_ok : cm_cOr_11_12_q11_fwd.okB = true := by decide
theorem cm_cOr_11_12_q11_fwd_root : cm_cOr_11_12_q11_fwd.root < cm_cOr_11_12_q11_fwd.n := by decide

def K_cOr_11_12_q11_fwd : Kripke := cm_cOr_11_12_q11_fwd.toKripke cm_cOr_11_12_q11_fwd_ok cm_cOr_11_12_q11_fwd_root

set_option maxRecDepth 1000000 in
theorem cm_cOr_11_12_q11_fwd_force :
    ¬ (K_cOr_11_12_q11_fwd).force (K_cOr_11_12_q11_fwd).root
        (ofPLL (.ifThen (RNBank.q11.or RNBank.q12) (RNBank.q11))) := by decide

theorem cOr_11_12_q11_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q11.or RNBank.q12) (RNBank.q11) :=
  fun h => not_entails_of_countermodel (K_cOr_11_12_q11_fwd) cm_cOr_11_12_q11_fwd_force h.1

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cOr_11_12_q11_fwd_control :
    (K_cOr_11_12_q11_fwd).force (K_cOr_11_12_q11_fwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cOr_11_12_q13` — the stated collapse is FALSE (→ direction) -/

def cm_cOr_11_12_q13_fwd : Search.Tab where
  n := 5
  root := 0
  leT := [[true, true, true, true, true], [false, true, true, true, true], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  rmT := [[true, false, false, false, false], [false, true, false, false, true], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  falT := [false, false, false, true, false]
  atomsT := [[], [], [], [], []]

theorem cm_cOr_11_12_q13_fwd_ok : cm_cOr_11_12_q13_fwd.okB = true := by decide
theorem cm_cOr_11_12_q13_fwd_root : cm_cOr_11_12_q13_fwd.root < cm_cOr_11_12_q13_fwd.n := by decide

def K_cOr_11_12_q13_fwd : Kripke := cm_cOr_11_12_q13_fwd.toKripke cm_cOr_11_12_q13_fwd_ok cm_cOr_11_12_q13_fwd_root

set_option maxRecDepth 1000000 in
theorem cm_cOr_11_12_q13_fwd_force :
    ¬ (K_cOr_11_12_q13_fwd).force (K_cOr_11_12_q13_fwd).root
        (ofPLL (.ifThen (RNBank.q11.or RNBank.q12) (RNBank.q13))) := by decide

theorem cOr_11_12_q13_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q11.or RNBank.q12) (RNBank.q13) :=
  fun h => not_entails_of_countermodel (K_cOr_11_12_q13_fwd) cm_cOr_11_12_q13_fwd_force h.1

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cOr_11_12_q13_fwd_control :
    (K_cOr_11_12_q13_fwd).force (K_cOr_11_12_q13_fwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cOr_11_14` — the stated collapse is FALSE (← direction) -/

def cm_cOr_11_14_bwd : Search.Tab where
  n := 8
  root := 0
  leT := [[true, true, true, true, true, true, true, true], [false, true, true, true, false, false, false, false], [false, false, true, true, false, false, false, false], [false, false, false, true, false, false, false, false], [false, false, false, false, true, true, true, true], [false, false, false, false, false, true, false, false], [false, false, false, false, false, false, true, true], [false, false, false, false, false, false, false, true]]
  rmT := [[true, false, false, false, false, false, false, false], [false, true, false, false, false, false, false, false], [false, false, true, true, false, false, false, false], [false, false, false, true, false, false, false, false], [false, false, false, false, true, false, false, false], [false, false, false, false, false, true, false, false], [false, false, false, false, false, false, true, true], [false, false, false, false, false, false, false, true]]
  falT := [false, false, false, true, false, false, false, true]
  atomsT := [[], [], [], [], [], [], [], []]

theorem cm_cOr_11_14_bwd_ok : cm_cOr_11_14_bwd.okB = true := by decide
theorem cm_cOr_11_14_bwd_root : cm_cOr_11_14_bwd.root < cm_cOr_11_14_bwd.n := by decide

def K_cOr_11_14_bwd : Kripke := cm_cOr_11_14_bwd.toKripke cm_cOr_11_14_bwd_ok cm_cOr_11_14_bwd_root

set_option maxRecDepth 1000000 in
theorem cm_cOr_11_14_bwd_force :
    ¬ (K_cOr_11_14_bwd).force (K_cOr_11_14_bwd).root
        (ofPLL (.ifThen (RNBank.q1) (RNBank.q11.or RNBank.q14))) := by decide

theorem cOr_11_14_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q11.or RNBank.q14) (RNBank.q1) :=
  fun h => not_entails_of_countermodel (K_cOr_11_14_bwd) cm_cOr_11_14_bwd_force h.2

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cOr_11_14_bwd_control :
    (K_cOr_11_14_bwd).force (K_cOr_11_14_bwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cOr_8_10` — the stated collapse is FALSE (← direction) -/

def cm_cOr_8_10_bwd : Search.Tab where
  n := 8
  root := 0
  leT := [[true, true, true, true, true, true, true, true], [false, true, true, true, false, false, false, false], [false, false, true, true, false, false, false, false], [false, false, false, true, false, false, false, false], [false, false, false, false, true, true, true, true], [false, false, false, false, false, true, true, false], [false, false, false, false, false, false, true, false], [false, false, false, false, false, false, false, true]]
  rmT := [[true, false, false, false, false, false, false, false], [false, true, false, false, false, false, false, false], [false, false, true, true, false, false, false, false], [false, false, false, true, false, false, false, false], [false, false, false, false, true, false, false, true], [false, false, false, false, false, true, true, false], [false, false, false, false, false, false, true, false], [false, false, false, false, false, false, false, true]]
  falT := [false, false, false, true, false, false, true, false]
  atomsT := [[], [], [], [], [], [], [], []]

theorem cm_cOr_8_10_bwd_ok : cm_cOr_8_10_bwd.okB = true := by decide
theorem cm_cOr_8_10_bwd_root : cm_cOr_8_10_bwd.root < cm_cOr_8_10_bwd.n := by decide

def K_cOr_8_10_bwd : Kripke := cm_cOr_8_10_bwd.toKripke cm_cOr_8_10_bwd_ok cm_cOr_8_10_bwd_root

set_option maxRecDepth 1000000 in
theorem cm_cOr_8_10_bwd_force :
    ¬ (K_cOr_8_10_bwd).force (K_cOr_8_10_bwd).root
        (ofPLL (.ifThen (RNBank.q1) (RNBank.q8.or RNBank.q10))) := by decide

theorem cOr_8_10_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q8.or RNBank.q10) (RNBank.q1) :=
  fun h => not_entails_of_countermodel (K_cOr_8_10_bwd) cm_cOr_8_10_bwd_force h.2

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cOr_8_10_bwd_control :
    (K_cOr_8_10_bwd).force (K_cOr_8_10_bwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cOr_8_11` — the stated collapse is FALSE (← direction) -/

def cm_cOr_8_11_bwd : Search.Tab where
  n := 8
  root := 0
  leT := [[true, true, true, true, true, true, true, true], [false, true, true, true, false, false, false, false], [false, false, true, true, false, false, false, false], [false, false, false, true, false, false, false, false], [false, false, false, false, true, true, true, true], [false, false, false, false, false, true, true, false], [false, false, false, false, false, false, true, false], [false, false, false, false, false, false, false, true]]
  rmT := [[true, false, false, false, false, false, false, false], [false, true, false, false, false, false, false, false], [false, false, true, true, false, false, false, false], [false, false, false, true, false, false, false, false], [false, false, false, false, true, false, false, true], [false, false, false, false, false, true, true, false], [false, false, false, false, false, false, true, false], [false, false, false, false, false, false, false, true]]
  falT := [false, false, false, true, false, false, true, false]
  atomsT := [[], [], [], [], [], [], [], []]

theorem cm_cOr_8_11_bwd_ok : cm_cOr_8_11_bwd.okB = true := by decide
theorem cm_cOr_8_11_bwd_root : cm_cOr_8_11_bwd.root < cm_cOr_8_11_bwd.n := by decide

def K_cOr_8_11_bwd : Kripke := cm_cOr_8_11_bwd.toKripke cm_cOr_8_11_bwd_ok cm_cOr_8_11_bwd_root

set_option maxRecDepth 1000000 in
theorem cm_cOr_8_11_bwd_force :
    ¬ (K_cOr_8_11_bwd).force (K_cOr_8_11_bwd).root
        (ofPLL (.ifThen (RNBank.q1) (RNBank.q8.or RNBank.q11))) := by decide

theorem cOr_8_11_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q8.or RNBank.q11) (RNBank.q1) :=
  fun h => not_entails_of_countermodel (K_cOr_8_11_bwd) cm_cOr_8_11_bwd_force h.2

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cOr_8_11_bwd_control :
    (K_cOr_8_11_bwd).force (K_cOr_8_11_bwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cOr_8_12` — the stated collapse is FALSE (← direction) -/

def cm_cOr_8_12_bwd : Search.Tab where
  n := 5
  root := 0
  leT := [[true, true, true, true, true], [false, true, true, true, true], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  rmT := [[true, false, false, false, false], [false, true, false, false, true], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  falT := [false, false, false, true, false]
  atomsT := [[], [], [], [], []]

theorem cm_cOr_8_12_bwd_ok : cm_cOr_8_12_bwd.okB = true := by decide
theorem cm_cOr_8_12_bwd_root : cm_cOr_8_12_bwd.root < cm_cOr_8_12_bwd.n := by decide

def K_cOr_8_12_bwd : Kripke := cm_cOr_8_12_bwd.toKripke cm_cOr_8_12_bwd_ok cm_cOr_8_12_bwd_root

set_option maxRecDepth 1000000 in
theorem cm_cOr_8_12_bwd_force :
    ¬ (K_cOr_8_12_bwd).force (K_cOr_8_12_bwd).root
        (ofPLL (.ifThen (RNBank.q1) (RNBank.q8.or RNBank.q12))) := by decide

theorem cOr_8_12_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q8.or RNBank.q12) (RNBank.q1) :=
  fun h => not_entails_of_countermodel (K_cOr_8_12_bwd) cm_cOr_8_12_bwd_force h.2

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cOr_8_12_bwd_control :
    (K_cOr_8_12_bwd).force (K_cOr_8_12_bwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cOr_8_14` — the stated collapse is FALSE (← direction) -/

def cm_cOr_8_14_bwd : Search.Tab where
  n := 5
  root := 0
  leT := [[true, true, true, true, true], [false, true, true, true, true], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  rmT := [[true, false, false, false, false], [false, true, false, false, true], [false, false, true, true, false], [false, false, false, true, false], [false, false, false, false, true]]
  falT := [false, false, false, true, false]
  atomsT := [[], [], [], [], []]

theorem cm_cOr_8_14_bwd_ok : cm_cOr_8_14_bwd.okB = true := by decide
theorem cm_cOr_8_14_bwd_root : cm_cOr_8_14_bwd.root < cm_cOr_8_14_bwd.n := by decide

def K_cOr_8_14_bwd : Kripke := cm_cOr_8_14_bwd.toKripke cm_cOr_8_14_bwd_ok cm_cOr_8_14_bwd_root

set_option maxRecDepth 1000000 in
theorem cm_cOr_8_14_bwd_force :
    ¬ (K_cOr_8_14_bwd).force (K_cOr_8_14_bwd).root
        (ofPLL (.ifThen (RNBank.q1) (RNBank.q8.or RNBank.q14))) := by decide

theorem cOr_8_14_FALSE : ¬ PLLND.SemUI.Interd (RNBank.q8.or RNBank.q14) (RNBank.q1) :=
  fun h => not_entails_of_countermodel (K_cOr_8_14_bwd) cm_cOr_8_14_bwd_force h.2

/-- Control: the model is not degenerate — it still forces `q1 = ⊤`.  A
model machinery that made every formula false would refute everything, so
this is the cheap check that the refutation above says something. -/
theorem cm_cOr_8_14_bwd_control :
    (K_cOr_8_14_bwd).force (K_cOr_8_14_bwd).root (ofPLL RNBank.q1) := by decide

/-! ### `cBox_11` — NO candidate survives, so the closure FAILS here

The candidate list of this cell was `[1, 11, 13]`; all three are now
eliminated by kernel-checked countermodels.  The other twelve
representatives were eliminated by the ≤4-world battery recorded in
`wip/rnDict.lean`, so this theorem's scope is exactly the three named. -/

theorem cBox_11_no_candidate :
    ¬ PLLND.SemUI.Interd (RNBank.q11.somehow) (RNBank.q1) ∧ ¬ PLLND.SemUI.Interd (RNBank.q11.somehow) (RNBank.q11) ∧ ¬ PLLND.SemUI.Interd (RNBank.q11.somehow) (RNBank.q13) :=
  ⟨cBox_11_FALSE, cBox_11_q11_FALSE, cBox_11_q13_FALSE⟩

/-! ### `cImp_12_11` — NO candidate survives, so the closure FAILS here

The candidate list of this cell was `[1, 11, 13]`; all three are now
eliminated by kernel-checked countermodels.  The other twelve
representatives were eliminated by the ≤4-world battery recorded in
`wip/rnDict.lean`, so this theorem's scope is exactly the three named. -/

theorem cImp_12_11_no_candidate :
    ¬ PLLND.SemUI.Interd (RNBank.q12.ifThen RNBank.q11) (RNBank.q1) ∧ ¬ PLLND.SemUI.Interd (RNBank.q12.ifThen RNBank.q11) (RNBank.q11) ∧ ¬ PLLND.SemUI.Interd (RNBank.q12.ifThen RNBank.q11) (RNBank.q13) :=
  ⟨cImp_12_11_FALSE, cImp_12_11_q11_FALSE, cImp_12_11_q13_FALSE⟩

/-! ### `cOr_10_12` — NO candidate survives, so the closure FAILS here

The candidate list of this cell was `[1, 11, 13]`; all three are now
eliminated by kernel-checked countermodels.  The other twelve
representatives were eliminated by the ≤4-world battery recorded in
`wip/rnDict.lean`, so this theorem's scope is exactly the three named. -/

theorem cOr_10_12_no_candidate :
    ¬ PLLND.SemUI.Interd (RNBank.q10.or RNBank.q12) (RNBank.q1) ∧ ¬ PLLND.SemUI.Interd (RNBank.q10.or RNBank.q12) (RNBank.q11) ∧ ¬ PLLND.SemUI.Interd (RNBank.q10.or RNBank.q12) (RNBank.q13) :=
  ⟨cOr_10_12_FALSE, cOr_10_12_q11_FALSE, cOr_10_12_q13_FALSE⟩

/-! ### `cOr_11_12` — NO candidate survives, so the closure FAILS here

The candidate list of this cell was `[1, 11, 13]`; all three are now
eliminated by kernel-checked countermodels.  The other twelve
representatives were eliminated by the ≤4-world battery recorded in
`wip/rnDict.lean`, so this theorem's scope is exactly the three named. -/

theorem cOr_11_12_no_candidate :
    ¬ PLLND.SemUI.Interd (RNBank.q11.or RNBank.q12) (RNBank.q1) ∧ ¬ PLLND.SemUI.Interd (RNBank.q11.or RNBank.q12) (RNBank.q11) ∧ ¬ PLLND.SemUI.Interd (RNBank.q11.or RNBank.q12) (RNBank.q13) :=
  ⟨cOr_11_12_FALSE, cOr_11_12_q11_FALSE, cOr_11_12_q13_FALSE⟩

/-! ## Axiom pins -/

#print axioms cAnd_10_13_FALSE
#print axioms cAnd_11_13_FALSE
#print axioms cBox_11_FALSE
#print axioms cBox_11_q11_FALSE
#print axioms cBox_11_q13_FALSE
#print axioms cImp_10_7_FALSE
#print axioms cImp_11_7_FALSE
#print axioms cImp_12_11_FALSE
#print axioms cImp_12_11_q11_FALSE
#print axioms cImp_12_11_q13_FALSE
#print axioms cImp_8_4_FALSE
#print axioms cImp_8_5_FALSE
#print axioms cOr_10_12_FALSE
#print axioms cOr_10_12_q11_FALSE
#print axioms cOr_10_12_q13_FALSE
#print axioms cOr_10_14_FALSE
#print axioms cOr_11_12_FALSE
#print axioms cOr_11_12_q11_FALSE
#print axioms cOr_11_12_q13_FALSE
#print axioms cOr_11_14_FALSE
#print axioms cOr_8_10_FALSE
#print axioms cOr_8_11_FALSE
#print axioms cOr_8_12_FALSE
#print axioms cOr_8_14_FALSE
#print axioms cBox_11_no_candidate
#print axioms cImp_12_11_no_candidate
#print axioms cOr_10_12_no_candidate
#print axioms cOr_11_12_no_candidate

end RNFRJCerts
