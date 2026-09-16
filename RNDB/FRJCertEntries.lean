/-
# The `rnFRJCerts` countermodels as DATABASE ENTRIES

GENERATED 2026-08-24.  Each entry consumes a `cm_*_force` theorem of
`wip/rnFRJCerts.lean` — the SELF-CERTIFYING primitive of that corpus —
through `FRJ.not_entails_of_countermodel`, giving the DIRECTIONAL fact
`[A] ⊬ B` the countermodel actually establishes.  The corpus's own
`_FALSE` (`¬ Interd`) theorems are deliberately NOT cited: they weaken a
directional refutation into a negated conjunction, which is exactly the
information loss the database schema was built to prevent.

Scope: the shared representative set (`RNReps.reps`, 16 formulas) —
these certificates were produced against dictionary cells.
-/
import RNDB.Types
import Tools.Bank
import wip.rnFRJCerts
import FRJ.Bridge

open PLLND PLLND.SemUI FRJ

namespace RNDB

/-- Directional refutation entry from an rnFRJCerts countermodel. -/
def frjCertEntry (id : EntryId) (a b : PLLFormula) (w : Nat) (hw : 0 < w)
    (h : ¬ Deriv [a] b) : Entry where
  id := id
  claim := ⟨a, b, Rel.nle, some RNReps.reps⟩
  ev := Evidence.countermodel Engine.frj w
  ok := ⟨Claim.wellScoped_some, rfl, hw, h⟩

def f_cAnd_10_13_bwd : Entry := frjCertEntry "fc-0000" ((RNBank.q10)) ((RNBank.q10.and RNBank.q13)) 5 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cAnd_10_13_bwd) RNFRJCerts.cm_cAnd_10_13_bwd_force)
def f_cAnd_11_13_bwd : Entry := frjCertEntry "fc-0001" ((RNBank.q1)) ((RNBank.q11.and RNBank.q13)) 5 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cAnd_11_13_bwd) RNFRJCerts.cm_cAnd_11_13_bwd_force)
def f_cBox_11_bwd : Entry := frjCertEntry "fc-0002" ((RNBank.q1)) ((RNBank.q11.somehow)) 5 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cBox_11_bwd) RNFRJCerts.cm_cBox_11_bwd_force)
def f_cBox_11_q11_fwd : Entry := frjCertEntry "fc-0003" ((RNBank.q11.somehow)) ((RNBank.q11)) 5 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cBox_11_q11_fwd) RNFRJCerts.cm_cBox_11_q11_fwd_force)
def f_cBox_11_q13_fwd : Entry := frjCertEntry "fc-0004" ((RNBank.q11.somehow)) ((RNBank.q13)) 5 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cBox_11_q13_fwd) RNFRJCerts.cm_cBox_11_q13_fwd_force)
def f_cImp_10_7_fwd : Entry := frjCertEntry "fc-0005" ((RNBank.q10.ifThen RNBank.q7)) ((RNBank.q7)) 5 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cImp_10_7_fwd) RNFRJCerts.cm_cImp_10_7_fwd_force)
def f_cImp_11_7_fwd : Entry := frjCertEntry "fc-0006" ((RNBank.q11.ifThen RNBank.q7)) ((RNBank.q7)) 5 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cImp_11_7_fwd) RNFRJCerts.cm_cImp_11_7_fwd_force)
def f_cImp_12_11_bwd : Entry := frjCertEntry "fc-0007" ((RNBank.q1)) ((RNBank.q12.ifThen RNBank.q11)) 5 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cImp_12_11_bwd) RNFRJCerts.cm_cImp_12_11_bwd_force)
def f_cImp_12_11_q11_fwd : Entry := frjCertEntry "fc-0008" ((RNBank.q12.ifThen RNBank.q11)) ((RNBank.q11)) 5 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cImp_12_11_q11_fwd) RNFRJCerts.cm_cImp_12_11_q11_fwd_force)
def f_cImp_12_11_q13_fwd : Entry := frjCertEntry "fc-0009" ((RNBank.q12.ifThen RNBank.q11)) ((RNBank.q13)) 5 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cImp_12_11_q13_fwd) RNFRJCerts.cm_cImp_12_11_q13_fwd_force)
def f_cImp_8_4_fwd : Entry := frjCertEntry "fc-0010" ((RNBank.q8.ifThen RNBank.q4)) ((RNBank.q5)) 5 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cImp_8_4_fwd) RNFRJCerts.cm_cImp_8_4_fwd_force)
def f_cImp_8_5_fwd : Entry := frjCertEntry "fc-0011" ((RNBank.q8.ifThen RNBank.q5)) ((RNBank.q5)) 5 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cImp_8_5_fwd) RNFRJCerts.cm_cImp_8_5_fwd_force)
def f_cOr_10_12_bwd : Entry := frjCertEntry "fc-0012" ((RNBank.q1)) ((RNBank.q10.or RNBank.q12)) 5 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cOr_10_12_bwd) RNFRJCerts.cm_cOr_10_12_bwd_force)
def f_cOr_10_12_q11_fwd : Entry := frjCertEntry "fc-0013" ((RNBank.q10.or RNBank.q12)) ((RNBank.q11)) 5 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cOr_10_12_q11_fwd) RNFRJCerts.cm_cOr_10_12_q11_fwd_force)
def f_cOr_10_12_q13_fwd : Entry := frjCertEntry "fc-0014" ((RNBank.q10.or RNBank.q12)) ((RNBank.q13)) 5 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cOr_10_12_q13_fwd) RNFRJCerts.cm_cOr_10_12_q13_fwd_force)
def f_cOr_10_14_bwd : Entry := frjCertEntry "fc-0015" ((RNBank.q1)) ((RNBank.q10.or RNBank.q14)) 8 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cOr_10_14_bwd) RNFRJCerts.cm_cOr_10_14_bwd_force)
def f_cOr_11_12_bwd : Entry := frjCertEntry "fc-0016" ((RNBank.q1)) ((RNBank.q11.or RNBank.q12)) 5 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cOr_11_12_bwd) RNFRJCerts.cm_cOr_11_12_bwd_force)
def f_cOr_11_12_q11_fwd : Entry := frjCertEntry "fc-0017" ((RNBank.q11.or RNBank.q12)) ((RNBank.q11)) 5 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cOr_11_12_q11_fwd) RNFRJCerts.cm_cOr_11_12_q11_fwd_force)
def f_cOr_11_12_q13_fwd : Entry := frjCertEntry "fc-0018" ((RNBank.q11.or RNBank.q12)) ((RNBank.q13)) 5 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cOr_11_12_q13_fwd) RNFRJCerts.cm_cOr_11_12_q13_fwd_force)
def f_cOr_11_14_bwd : Entry := frjCertEntry "fc-0019" ((RNBank.q1)) ((RNBank.q11.or RNBank.q14)) 8 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cOr_11_14_bwd) RNFRJCerts.cm_cOr_11_14_bwd_force)
def f_cOr_8_10_bwd : Entry := frjCertEntry "fc-0020" ((RNBank.q1)) ((RNBank.q8.or RNBank.q10)) 8 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cOr_8_10_bwd) RNFRJCerts.cm_cOr_8_10_bwd_force)
def f_cOr_8_11_bwd : Entry := frjCertEntry "fc-0021" ((RNBank.q1)) ((RNBank.q8.or RNBank.q11)) 8 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cOr_8_11_bwd) RNFRJCerts.cm_cOr_8_11_bwd_force)
def f_cOr_8_12_bwd : Entry := frjCertEntry "fc-0022" ((RNBank.q1)) ((RNBank.q8.or RNBank.q12)) 5 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cOr_8_12_bwd) RNFRJCerts.cm_cOr_8_12_bwd_force)
def f_cOr_8_14_bwd : Entry := frjCertEntry "fc-0023" ((RNBank.q1)) ((RNBank.q8.or RNBank.q14)) 5 (by decide)
  (not_entails_of_countermodel (RNFRJCerts.K_cOr_8_14_bwd) RNFRJCerts.cm_cOr_8_14_bwd_force)

def frjCertEntries : List Entry :=
  [ f_cAnd_10_13_bwd,
    f_cAnd_11_13_bwd,
    f_cBox_11_bwd,
    f_cBox_11_q11_fwd,
    f_cBox_11_q13_fwd,
    f_cImp_10_7_fwd,
    f_cImp_11_7_fwd,
    f_cImp_12_11_bwd,
    f_cImp_12_11_q11_fwd,
    f_cImp_12_11_q13_fwd,
    f_cImp_8_4_fwd,
    f_cImp_8_5_fwd,
    f_cOr_10_12_bwd,
    f_cOr_10_12_q11_fwd,
    f_cOr_10_12_q13_fwd,
    f_cOr_10_14_bwd,
    f_cOr_11_12_bwd,
    f_cOr_11_12_q11_fwd,
    f_cOr_11_12_q13_fwd,
    f_cOr_11_14_bwd,
    f_cOr_8_10_bwd,
    f_cOr_8_11_bwd,
    f_cOr_8_12_bwd,
    f_cOr_8_14_bwd ]

set_option maxRecDepth 8192 in
theorem frjCertEntries_length : frjCertEntries.length = 24 := rfl

/-! ## Pins — UNGUARDED as emitted; guard via tools/pin-backfill.py -/

/-- info: 'RNDB.frjCertEntries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms frjCertEntries

/-- info: 'RNDB.frjCertEntries_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms frjCertEntries_length

end RNDB