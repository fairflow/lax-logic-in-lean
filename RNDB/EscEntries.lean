/-
# The round-2 UNIVERSAL ESCAPES, decomposed to directional entries

GENERATED 2026-08-24.  `wip/rnDictRefute2.lean` proves, for each of the
58 refuted round-2 cells, `∀ k : Fin 16, ¬ Interd (compound) (rep2 k)` —
the strong "collapses to NO representative" form.  Its proof bodies are
per-`k` DIRECTIONAL countermodels (`h.1` arms refute `compound ⊢ repₖ`,
`h.2` arms refute `repₖ ⊢ compound`), so the schema needs no `¬ Interd`
relation: this file re-states each arm at its true directional strength,
928 `nle` entries, each `ok` a self-contained `FinCM.not_provable_of_check`
re-checked by `decide` on the inline model — the `wip/` theorems are NOT
imported.  The universal closure fact is recoverable as: all 16 `k`-rows
of a cell present, in the recorded scope.

Provenance `Engine.finCM`: these models came from the battery/checker
machinery, not from FRJ(◯) construction.
-/
import RNDB.Types
import LaxLogic.RN.Reps
import LaxLogic.PLLCountermodel

open PLLND PLLND.SemUI

namespace RNDB

/-- Directional escape entry: the countermodel is inline and re-checked
here by `decide`; nothing is taken on trust from the source file. -/
def escEntry (id : EntryId) (a b : PLLFormula) (w : Nat) (hw : 0 < w)
    (h : ¬ Deriv [a] b) : Entry where
  id := id
  claim := ⟨a, b, Rel.nle, some RNReps.reps⟩
  ev := Evidence.countermodel Engine.finCM w
  ok := ⟨Claim.wellScoped_some, rfl, hw, h⟩

def r2e_cAnd_8_11_k0_fwd : Entry := escEntry "esc-0000" (RNReps.q8.and RNReps.q11) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_11_k1_bwd : Entry := escEntry "esc-0001" (RNReps.q1) (RNReps.q8.and RNReps.q11) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_11_k2_fwd : Entry := escEntry "esc-0002" (RNReps.q8.and RNReps.q11) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_11_k3_fwd : Entry := escEntry "esc-0003" (RNReps.q8.and RNReps.q11) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_11_k4_fwd : Entry := escEntry "esc-0004" (RNReps.q8.and RNReps.q11) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_11_k5_fwd : Entry := escEntry "esc-0005" (RNReps.q8.and RNReps.q11) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_11_k6_fwd : Entry := escEntry "esc-0006" (RNReps.q8.and RNReps.q11) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_11_k7_fwd : Entry := escEntry "esc-0007" (RNReps.q8.and RNReps.q11) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_11_k8_bwd : Entry := escEntry "esc-0008" (RNReps.q8) (RNReps.q8.and RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_11_k9_fwd : Entry := escEntry "esc-0009" (RNReps.q8.and RNReps.q11) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_11_k10_fwd : Entry := escEntry "esc-0010" (RNReps.q8.and RNReps.q11) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_11_k11_bwd : Entry := escEntry "esc-0011" (RNReps.q11) (RNReps.q8.and RNReps.q11) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_11_k12_fwd : Entry := escEntry "esc-0012" (RNReps.q8.and RNReps.q11) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_11_k13_bwd : Entry := escEntry "esc-0013" (RNReps.q13) (RNReps.q8.and RNReps.q11) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_11_k14_fwd : Entry := escEntry "esc-0014" (RNReps.q8.and RNReps.q11) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_11_k15_fwd : Entry := escEntry "esc-0015" (RNReps.q8.and RNReps.q11) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_15_k0_fwd : Entry := escEntry "esc-0016" (RNReps.q15.somehow) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_15_k1_bwd : Entry := escEntry "esc-0017" (RNReps.q1) (RNReps.q15.somehow) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_15_k2_fwd : Entry := escEntry "esc-0018" (RNReps.q15.somehow) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_15_k3_fwd : Entry := escEntry "esc-0019" (RNReps.q15.somehow) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_15_k4_fwd : Entry := escEntry "esc-0020" (RNReps.q15.somehow) (RNReps.q4) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_15_k5_fwd : Entry := escEntry "esc-0021" (RNReps.q15.somehow) (RNReps.q5) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_15_k6_fwd : Entry := escEntry "esc-0022" (RNReps.q15.somehow) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_15_k7_fwd : Entry := escEntry "esc-0023" (RNReps.q15.somehow) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_15_k8_fwd : Entry := escEntry "esc-0024" (RNReps.q15.somehow) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_15_k9_fwd : Entry := escEntry "esc-0025" (RNReps.q15.somehow) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_15_k10_bwd : Entry := escEntry "esc-0026" (RNReps.q10) (RNReps.q15.somehow) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_15_k11_bwd : Entry := escEntry "esc-0027" (RNReps.q11) (RNReps.q15.somehow) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_15_k12_fwd : Entry := escEntry "esc-0028" (RNReps.q15.somehow) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_15_k13_bwd : Entry := escEntry "esc-0029" (RNReps.q13) (RNReps.q15.somehow) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_15_k14_fwd : Entry := escEntry "esc-0030" (RNReps.q15.somehow) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_15_k15_fwd : Entry := escEntry "esc-0031" (RNReps.q15.somehow) (RNReps.q15) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_13_k0_fwd : Entry := escEntry "esc-0032" (RNReps.q11.ifThen RNReps.q13) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_13_k1_bwd : Entry := escEntry "esc-0033" (RNReps.q1) (RNReps.q11.ifThen RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_13_k2_fwd : Entry := escEntry "esc-0034" (RNReps.q11.ifThen RNReps.q13) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_13_k3_fwd : Entry := escEntry "esc-0035" (RNReps.q11.ifThen RNReps.q13) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_13_k4_fwd : Entry := escEntry "esc-0036" (RNReps.q11.ifThen RNReps.q13) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_13_k5_fwd : Entry := escEntry "esc-0037" (RNReps.q11.ifThen RNReps.q13) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_13_k6_fwd : Entry := escEntry "esc-0038" (RNReps.q11.ifThen RNReps.q13) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_13_k7_fwd : Entry := escEntry "esc-0039" (RNReps.q11.ifThen RNReps.q13) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_13_k8_fwd : Entry := escEntry "esc-0040" (RNReps.q11.ifThen RNReps.q13) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_13_k9_fwd : Entry := escEntry "esc-0041" (RNReps.q11.ifThen RNReps.q13) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_13_k10_fwd : Entry := escEntry "esc-0042" (RNReps.q11.ifThen RNReps.q13) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_13_k11_fwd : Entry := escEntry "esc-0043" (RNReps.q11.ifThen RNReps.q13) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_13_k12_fwd : Entry := escEntry "esc-0044" (RNReps.q11.ifThen RNReps.q13) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_13_k13_fwd : Entry := escEntry "esc-0045" (RNReps.q11.ifThen RNReps.q13) (RNReps.q13) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_13_k14_fwd : Entry := escEntry "esc-0046" (RNReps.q11.ifThen RNReps.q13) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_13_k15_fwd : Entry := escEntry "esc-0047" (RNReps.q11.ifThen RNReps.q13) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_9_k0_fwd : Entry := escEntry "esc-0048" (RNReps.q12.ifThen RNReps.q9) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_9_k1_bwd : Entry := escEntry "esc-0049" (RNReps.q1) (RNReps.q12.ifThen RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(0, 1), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_9_k2_fwd : Entry := escEntry "esc-0050" (RNReps.q12.ifThen RNReps.q9) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_9_k3_fwd : Entry := escEntry "esc-0051" (RNReps.q12.ifThen RNReps.q9) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_9_k4_fwd : Entry := escEntry "esc-0052" (RNReps.q12.ifThen RNReps.q9) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_9_k5_fwd : Entry := escEntry "esc-0053" (RNReps.q12.ifThen RNReps.q9) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_9_k6_fwd : Entry := escEntry "esc-0054" (RNReps.q12.ifThen RNReps.q9) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_9_k7_fwd : Entry := escEntry "esc-0055" (RNReps.q12.ifThen RNReps.q9) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_9_k8_fwd : Entry := escEntry "esc-0056" (RNReps.q12.ifThen RNReps.q9) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_9_k9_fwd : Entry := escEntry "esc-0057" (RNReps.q12.ifThen RNReps.q9) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_9_k10_fwd : Entry := escEntry "esc-0058" (RNReps.q12.ifThen RNReps.q9) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_9_k11_fwd : Entry := escEntry "esc-0059" (RNReps.q12.ifThen RNReps.q9) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_9_k12_fwd : Entry := escEntry "esc-0060" (RNReps.q12.ifThen RNReps.q9) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_9_k13_fwd : Entry := escEntry "esc-0061" (RNReps.q12.ifThen RNReps.q9) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_9_k14_fwd : Entry := escEntry "esc-0062" (RNReps.q12.ifThen RNReps.q9) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_9_k15_fwd : Entry := escEntry "esc-0063" (RNReps.q12.ifThen RNReps.q9) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_9_k0_fwd : Entry := escEntry "esc-0064" (RNReps.q13.ifThen RNReps.q9) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_9_k1_bwd : Entry := escEntry "esc-0065" (RNReps.q1) (RNReps.q13.ifThen RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_9_k2_fwd : Entry := escEntry "esc-0066" (RNReps.q13.ifThen RNReps.q9) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_9_k3_fwd : Entry := escEntry "esc-0067" (RNReps.q13.ifThen RNReps.q9) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_9_k4_fwd : Entry := escEntry "esc-0068" (RNReps.q13.ifThen RNReps.q9) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_9_k5_fwd : Entry := escEntry "esc-0069" (RNReps.q13.ifThen RNReps.q9) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_9_k6_fwd : Entry := escEntry "esc-0070" (RNReps.q13.ifThen RNReps.q9) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_9_k7_fwd : Entry := escEntry "esc-0071" (RNReps.q13.ifThen RNReps.q9) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_9_k8_fwd : Entry := escEntry "esc-0072" (RNReps.q13.ifThen RNReps.q9) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_9_k9_fwd : Entry := escEntry "esc-0073" (RNReps.q13.ifThen RNReps.q9) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_9_k10_fwd : Entry := escEntry "esc-0074" (RNReps.q13.ifThen RNReps.q9) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_9_k11_fwd : Entry := escEntry "esc-0075" (RNReps.q13.ifThen RNReps.q9) (RNReps.q11) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_9_k12_fwd : Entry := escEntry "esc-0076" (RNReps.q13.ifThen RNReps.q9) (RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_9_k13_fwd : Entry := escEntry "esc-0077" (RNReps.q13.ifThen RNReps.q9) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_9_k14_fwd : Entry := escEntry "esc-0078" (RNReps.q13.ifThen RNReps.q9) (RNReps.q14) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_9_k15_fwd : Entry := escEntry "esc-0079" (RNReps.q13.ifThen RNReps.q9) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_7_k0_fwd : Entry := escEntry "esc-0080" (RNReps.q14.ifThen RNReps.q7) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_7_k1_bwd : Entry := escEntry "esc-0081" (RNReps.q1) (RNReps.q14.ifThen RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_7_k2_fwd : Entry := escEntry "esc-0082" (RNReps.q14.ifThen RNReps.q7) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_7_k3_fwd : Entry := escEntry "esc-0083" (RNReps.q14.ifThen RNReps.q7) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_7_k4_fwd : Entry := escEntry "esc-0084" (RNReps.q14.ifThen RNReps.q7) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_7_k5_fwd : Entry := escEntry "esc-0085" (RNReps.q14.ifThen RNReps.q7) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_7_k6_fwd : Entry := escEntry "esc-0086" (RNReps.q14.ifThen RNReps.q7) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_7_k7_fwd : Entry := escEntry "esc-0087" (RNReps.q14.ifThen RNReps.q7) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_7_k8_bwd : Entry := escEntry "esc-0088" (RNReps.q8) (RNReps.q14.ifThen RNReps.q7) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_7_k9_fwd : Entry := escEntry "esc-0089" (RNReps.q14.ifThen RNReps.q7) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_7_k10_fwd : Entry := escEntry "esc-0090" (RNReps.q14.ifThen RNReps.q7) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_7_k11_fwd : Entry := escEntry "esc-0091" (RNReps.q14.ifThen RNReps.q7) (RNReps.q11) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_7_k12_fwd : Entry := escEntry "esc-0092" (RNReps.q14.ifThen RNReps.q7) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_7_k13_bwd : Entry := escEntry "esc-0093" (RNReps.q13) (RNReps.q14.ifThen RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_7_k14_fwd : Entry := escEntry "esc-0094" (RNReps.q14.ifThen RNReps.q7) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_7_k15_fwd : Entry := escEntry "esc-0095" (RNReps.q14.ifThen RNReps.q7) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_4_k0_fwd : Entry := escEntry "esc-0096" (RNReps.q15.ifThen RNReps.q4) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_4_k1_bwd : Entry := escEntry "esc-0097" (RNReps.q1) (RNReps.q15.ifThen RNReps.q4) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_4_k2_fwd : Entry := escEntry "esc-0098" (RNReps.q15.ifThen RNReps.q4) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_4_k3_fwd : Entry := escEntry "esc-0099" (RNReps.q15.ifThen RNReps.q4) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_4_k4_fwd : Entry := escEntry "esc-0100" (RNReps.q15.ifThen RNReps.q4) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_4_k5_fwd : Entry := escEntry "esc-0101" (RNReps.q15.ifThen RNReps.q4) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_4_k6_fwd : Entry := escEntry "esc-0102" (RNReps.q15.ifThen RNReps.q4) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_4_k7_fwd : Entry := escEntry "esc-0103" (RNReps.q15.ifThen RNReps.q4) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_4_k8_fwd : Entry := escEntry "esc-0104" (RNReps.q15.ifThen RNReps.q4) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_4_k9_fwd : Entry := escEntry "esc-0105" (RNReps.q15.ifThen RNReps.q4) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_4_k10_fwd : Entry := escEntry "esc-0106" (RNReps.q15.ifThen RNReps.q4) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_4_k11_fwd : Entry := escEntry "esc-0107" (RNReps.q15.ifThen RNReps.q4) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_4_k12_fwd : Entry := escEntry "esc-0108" (RNReps.q15.ifThen RNReps.q4) (RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_4_k13_fwd : Entry := escEntry "esc-0109" (RNReps.q15.ifThen RNReps.q4) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_4_k14_fwd : Entry := escEntry "esc-0110" (RNReps.q15.ifThen RNReps.q4) (RNReps.q14) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_4_k15_fwd : Entry := escEntry "esc-0111" (RNReps.q15.ifThen RNReps.q4) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_11_k0_fwd : Entry := escEntry "esc-0112" (RNReps.q8.ifThen RNReps.q11) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_11_k1_bwd : Entry := escEntry "esc-0113" (RNReps.q1) (RNReps.q8.ifThen RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_11_k2_fwd : Entry := escEntry "esc-0114" (RNReps.q8.ifThen RNReps.q11) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_11_k3_fwd : Entry := escEntry "esc-0115" (RNReps.q8.ifThen RNReps.q11) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_11_k4_fwd : Entry := escEntry "esc-0116" (RNReps.q8.ifThen RNReps.q11) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_11_k5_fwd : Entry := escEntry "esc-0117" (RNReps.q8.ifThen RNReps.q11) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_11_k6_fwd : Entry := escEntry "esc-0118" (RNReps.q8.ifThen RNReps.q11) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_11_k7_fwd : Entry := escEntry "esc-0119" (RNReps.q8.ifThen RNReps.q11) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_11_k8_fwd : Entry := escEntry "esc-0120" (RNReps.q8.ifThen RNReps.q11) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_11_k9_fwd : Entry := escEntry "esc-0121" (RNReps.q8.ifThen RNReps.q11) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_11_k10_fwd : Entry := escEntry "esc-0122" (RNReps.q8.ifThen RNReps.q11) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_11_k11_fwd : Entry := escEntry "esc-0123" (RNReps.q8.ifThen RNReps.q11) (RNReps.q11) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_11_k12_fwd : Entry := escEntry "esc-0124" (RNReps.q8.ifThen RNReps.q11) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_11_k13_fwd : Entry := escEntry "esc-0125" (RNReps.q8.ifThen RNReps.q11) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_11_k14_fwd : Entry := escEntry "esc-0126" (RNReps.q8.ifThen RNReps.q11) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_11_k15_fwd : Entry := escEntry "esc-0127" (RNReps.q8.ifThen RNReps.q11) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_5_k0_fwd : Entry := escEntry "esc-0128" (RNReps.q8.ifThen RNReps.q5) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_5_k1_bwd : Entry := escEntry "esc-0129" (RNReps.q1) (RNReps.q8.ifThen RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_5_k2_fwd : Entry := escEntry "esc-0130" (RNReps.q8.ifThen RNReps.q5) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_5_k3_fwd : Entry := escEntry "esc-0131" (RNReps.q8.ifThen RNReps.q5) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_5_k4_fwd : Entry := escEntry "esc-0132" (RNReps.q8.ifThen RNReps.q5) (RNReps.q4) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_5_k5_fwd : Entry := escEntry "esc-0133" (RNReps.q8.ifThen RNReps.q5) (RNReps.q5) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_5_k6_fwd : Entry := escEntry "esc-0134" (RNReps.q8.ifThen RNReps.q5) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_5_k7_fwd : Entry := escEntry "esc-0135" (RNReps.q8.ifThen RNReps.q5) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_5_k8_fwd : Entry := escEntry "esc-0136" (RNReps.q8.ifThen RNReps.q5) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_5_k9_fwd : Entry := escEntry "esc-0137" (RNReps.q8.ifThen RNReps.q5) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_5_k10_bwd : Entry := escEntry "esc-0138" (RNReps.q10) (RNReps.q8.ifThen RNReps.q5) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_5_k11_bwd : Entry := escEntry "esc-0139" (RNReps.q11) (RNReps.q8.ifThen RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_5_k12_fwd : Entry := escEntry "esc-0140" (RNReps.q8.ifThen RNReps.q5) (RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_5_k13_fwd : Entry := escEntry "esc-0141" (RNReps.q8.ifThen RNReps.q5) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_5_k14_fwd : Entry := escEntry "esc-0142" (RNReps.q8.ifThen RNReps.q5) (RNReps.q14) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_5_k15_fwd : Entry := escEntry "esc-0143" (RNReps.q8.ifThen RNReps.q5) (RNReps.q15) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_13_k0_fwd : Entry := escEntry "esc-0144" (RNReps.q10.or RNReps.q13) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_13_k1_bwd : Entry := escEntry "esc-0145" (RNReps.q1) (RNReps.q10.or RNReps.q13) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_13_k2_fwd : Entry := escEntry "esc-0146" (RNReps.q10.or RNReps.q13) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_13_k3_fwd : Entry := escEntry "esc-0147" (RNReps.q10.or RNReps.q13) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_13_k4_fwd : Entry := escEntry "esc-0148" (RNReps.q10.or RNReps.q13) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_13_k5_fwd : Entry := escEntry "esc-0149" (RNReps.q10.or RNReps.q13) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_13_k6_fwd : Entry := escEntry "esc-0150" (RNReps.q10.or RNReps.q13) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_13_k7_fwd : Entry := escEntry "esc-0151" (RNReps.q10.or RNReps.q13) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_13_k8_fwd : Entry := escEntry "esc-0152" (RNReps.q10.or RNReps.q13) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_13_k9_fwd : Entry := escEntry "esc-0153" (RNReps.q10.or RNReps.q13) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_13_k10_fwd : Entry := escEntry "esc-0154" (RNReps.q10.or RNReps.q13) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_13_k11_fwd : Entry := escEntry "esc-0155" (RNReps.q10.or RNReps.q13) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_13_k12_fwd : Entry := escEntry "esc-0156" (RNReps.q10.or RNReps.q13) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_13_k13_fwd : Entry := escEntry "esc-0157" (RNReps.q10.or RNReps.q13) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_13_k14_fwd : Entry := escEntry "esc-0158" (RNReps.q10.or RNReps.q13) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_13_k15_fwd : Entry := escEntry "esc-0159" (RNReps.q10.or RNReps.q13) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_14_k0_fwd : Entry := escEntry "esc-0160" (RNReps.q11.or RNReps.q14) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_14_k1_bwd : Entry := escEntry "esc-0161" (RNReps.q1) (RNReps.q11.or RNReps.q14) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_14_k2_fwd : Entry := escEntry "esc-0162" (RNReps.q11.or RNReps.q14) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_14_k3_fwd : Entry := escEntry "esc-0163" (RNReps.q11.or RNReps.q14) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_14_k4_fwd : Entry := escEntry "esc-0164" (RNReps.q11.or RNReps.q14) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_14_k5_fwd : Entry := escEntry "esc-0165" (RNReps.q11.or RNReps.q14) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_14_k6_fwd : Entry := escEntry "esc-0166" (RNReps.q11.or RNReps.q14) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_14_k7_fwd : Entry := escEntry "esc-0167" (RNReps.q11.or RNReps.q14) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_14_k8_fwd : Entry := escEntry "esc-0168" (RNReps.q11.or RNReps.q14) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_14_k9_fwd : Entry := escEntry "esc-0169" (RNReps.q11.or RNReps.q14) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_14_k10_fwd : Entry := escEntry "esc-0170" (RNReps.q11.or RNReps.q14) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_14_k11_fwd : Entry := escEntry "esc-0171" (RNReps.q11.or RNReps.q14) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_14_k12_fwd : Entry := escEntry "esc-0172" (RNReps.q11.or RNReps.q14) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_14_k13_fwd : Entry := escEntry "esc-0173" (RNReps.q11.or RNReps.q14) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_14_k14_fwd : Entry := escEntry "esc-0174" (RNReps.q11.or RNReps.q14) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_14_k15_fwd : Entry := escEntry "esc-0175" (RNReps.q11.or RNReps.q14) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_15_k0_fwd : Entry := escEntry "esc-0176" (RNReps.q5.or RNReps.q15) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_15_k1_bwd : Entry := escEntry "esc-0177" (RNReps.q1) (RNReps.q5.or RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_15_k2_fwd : Entry := escEntry "esc-0178" (RNReps.q5.or RNReps.q15) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_15_k3_fwd : Entry := escEntry "esc-0179" (RNReps.q5.or RNReps.q15) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_15_k4_fwd : Entry := escEntry "esc-0180" (RNReps.q5.or RNReps.q15) (RNReps.q4) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_15_k5_fwd : Entry := escEntry "esc-0181" (RNReps.q5.or RNReps.q15) (RNReps.q5) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_15_k6_fwd : Entry := escEntry "esc-0182" (RNReps.q5.or RNReps.q15) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_15_k7_fwd : Entry := escEntry "esc-0183" (RNReps.q5.or RNReps.q15) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_15_k8_fwd : Entry := escEntry "esc-0184" (RNReps.q5.or RNReps.q15) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_15_k9_fwd : Entry := escEntry "esc-0185" (RNReps.q5.or RNReps.q15) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_15_k10_bwd : Entry := escEntry "esc-0186" (RNReps.q10) (RNReps.q5.or RNReps.q15) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_15_k11_bwd : Entry := escEntry "esc-0187" (RNReps.q11) (RNReps.q5.or RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_15_k12_fwd : Entry := escEntry "esc-0188" (RNReps.q5.or RNReps.q15) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_15_k13_bwd : Entry := escEntry "esc-0189" (RNReps.q13) (RNReps.q5.or RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_15_k14_fwd : Entry := escEntry "esc-0190" (RNReps.q5.or RNReps.q15) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_15_k15_fwd : Entry := escEntry "esc-0191" (RNReps.q5.or RNReps.q15) (RNReps.q15) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_10_k0_fwd : Entry := escEntry "esc-0192" (RNReps.q8.or RNReps.q10) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_10_k1_bwd : Entry := escEntry "esc-0193" (RNReps.q1) (RNReps.q8.or RNReps.q10) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_10_k2_fwd : Entry := escEntry "esc-0194" (RNReps.q8.or RNReps.q10) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_10_k3_fwd : Entry := escEntry "esc-0195" (RNReps.q8.or RNReps.q10) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_10_k4_fwd : Entry := escEntry "esc-0196" (RNReps.q8.or RNReps.q10) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_10_k5_fwd : Entry := escEntry "esc-0197" (RNReps.q8.or RNReps.q10) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_10_k6_fwd : Entry := escEntry "esc-0198" (RNReps.q8.or RNReps.q10) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_10_k7_fwd : Entry := escEntry "esc-0199" (RNReps.q8.or RNReps.q10) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_10_k8_fwd : Entry := escEntry "esc-0200" (RNReps.q8.or RNReps.q10) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_10_k9_fwd : Entry := escEntry "esc-0201" (RNReps.q8.or RNReps.q10) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_10_k10_fwd : Entry := escEntry "esc-0202" (RNReps.q8.or RNReps.q10) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_10_k11_fwd : Entry := escEntry "esc-0203" (RNReps.q8.or RNReps.q10) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_10_k12_fwd : Entry := escEntry "esc-0204" (RNReps.q8.or RNReps.q10) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_10_k13_fwd : Entry := escEntry "esc-0205" (RNReps.q8.or RNReps.q10) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_10_k14_fwd : Entry := escEntry "esc-0206" (RNReps.q8.or RNReps.q10) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_10_k15_fwd : Entry := escEntry "esc-0207" (RNReps.q8.or RNReps.q10) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_9_k0_fwd : Entry := escEntry "esc-0208" (RNReps.q8.or RNReps.q9) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_9_k1_bwd : Entry := escEntry "esc-0209" (RNReps.q1) (RNReps.q8.or RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_9_k2_fwd : Entry := escEntry "esc-0210" (RNReps.q8.or RNReps.q9) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_9_k3_fwd : Entry := escEntry "esc-0211" (RNReps.q8.or RNReps.q9) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_9_k4_fwd : Entry := escEntry "esc-0212" (RNReps.q8.or RNReps.q9) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_9_k5_fwd : Entry := escEntry "esc-0213" (RNReps.q8.or RNReps.q9) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_9_k6_fwd : Entry := escEntry "esc-0214" (RNReps.q8.or RNReps.q9) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_9_k7_fwd : Entry := escEntry "esc-0215" (RNReps.q8.or RNReps.q9) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_9_k8_fwd : Entry := escEntry "esc-0216" (RNReps.q8.or RNReps.q9) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_9_k9_fwd : Entry := escEntry "esc-0217" (RNReps.q8.or RNReps.q9) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_9_k10_fwd : Entry := escEntry "esc-0218" (RNReps.q8.or RNReps.q9) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_9_k11_fwd : Entry := escEntry "esc-0219" (RNReps.q8.or RNReps.q9) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_9_k12_fwd : Entry := escEntry "esc-0220" (RNReps.q8.or RNReps.q9) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_9_k13_bwd : Entry := escEntry "esc-0221" (RNReps.q13) (RNReps.q8.or RNReps.q9) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(0, 2), (1, 4), (3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_9_k14_fwd : Entry := escEntry "esc-0222" (RNReps.q8.or RNReps.q9) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_9_k15_fwd : Entry := escEntry "esc-0223" (RNReps.q8.or RNReps.q9) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_10_13_k0_fwd : Entry := escEntry "esc-0224" (RNReps.q10.and RNReps.q13) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_10_13_k1_bwd : Entry := escEntry "esc-0225" (RNReps.q1) (RNReps.q10.and RNReps.q13) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_10_13_k2_fwd : Entry := escEntry "esc-0226" (RNReps.q10.and RNReps.q13) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_10_13_k3_fwd : Entry := escEntry "esc-0227" (RNReps.q10.and RNReps.q13) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_10_13_k4_fwd : Entry := escEntry "esc-0228" (RNReps.q10.and RNReps.q13) (RNReps.q4) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_10_13_k5_fwd : Entry := escEntry "esc-0229" (RNReps.q10.and RNReps.q13) (RNReps.q5) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_10_13_k6_fwd : Entry := escEntry "esc-0230" (RNReps.q10.and RNReps.q13) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_10_13_k7_fwd : Entry := escEntry "esc-0231" (RNReps.q10.and RNReps.q13) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_10_13_k8_fwd : Entry := escEntry "esc-0232" (RNReps.q10.and RNReps.q13) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_10_13_k9_fwd : Entry := escEntry "esc-0233" (RNReps.q10.and RNReps.q13) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_10_13_k10_bwd : Entry := escEntry "esc-0234" (RNReps.q10) (RNReps.q10.and RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_10_13_k11_bwd : Entry := escEntry "esc-0235" (RNReps.q11) (RNReps.q10.and RNReps.q13) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_10_13_k12_fwd : Entry := escEntry "esc-0236" (RNReps.q10.and RNReps.q13) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_10_13_k13_bwd : Entry := escEntry "esc-0237" (RNReps.q13) (RNReps.q10.and RNReps.q13) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_10_13_k14_fwd : Entry := escEntry "esc-0238" (RNReps.q10.and RNReps.q13) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_10_13_k15_fwd : Entry := escEntry "esc-0239" (RNReps.q10.and RNReps.q13) (RNReps.q15) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_12_k0_fwd : Entry := escEntry "esc-0240" (RNReps.q8.and RNReps.q12) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_12_k1_bwd : Entry := escEntry "esc-0241" (RNReps.q1) (RNReps.q8.and RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_12_k2_fwd : Entry := escEntry "esc-0242" (RNReps.q8.and RNReps.q12) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_12_k3_fwd : Entry := escEntry "esc-0243" (RNReps.q8.and RNReps.q12) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_12_k4_fwd : Entry := escEntry "esc-0244" (RNReps.q8.and RNReps.q12) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_12_k5_fwd : Entry := escEntry "esc-0245" (RNReps.q8.and RNReps.q12) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_12_k6_fwd : Entry := escEntry "esc-0246" (RNReps.q8.and RNReps.q12) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_12_k7_fwd : Entry := escEntry "esc-0247" (RNReps.q8.and RNReps.q12) (RNReps.q7) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(0, 1), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_12_k8_bwd : Entry := escEntry "esc-0248" (RNReps.q8) (RNReps.q8.and RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_12_k9_fwd : Entry := escEntry "esc-0249" (RNReps.q8.and RNReps.q12) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(0, 1), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_12_k10_fwd : Entry := escEntry "esc-0250" (RNReps.q8.and RNReps.q12) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_12_k11_fwd : Entry := escEntry "esc-0251" (RNReps.q8.and RNReps.q12) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(0, 1), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_12_k12_bwd : Entry := escEntry "esc-0252" (RNReps.q12) (RNReps.q8.and RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_12_k13_bwd : Entry := escEntry "esc-0253" (RNReps.q13) (RNReps.q8.and RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_12_k14_bwd : Entry := escEntry "esc-0254" (RNReps.q14) (RNReps.q8.and RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_12_k15_fwd : Entry := escEntry "esc-0255" (RNReps.q8.and RNReps.q12) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_13_k0_fwd : Entry := escEntry "esc-0256" (RNReps.q10.ifThen RNReps.q13) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_13_k1_bwd : Entry := escEntry "esc-0257" (RNReps.q1) (RNReps.q10.ifThen RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_13_k2_fwd : Entry := escEntry "esc-0258" (RNReps.q10.ifThen RNReps.q13) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_13_k3_fwd : Entry := escEntry "esc-0259" (RNReps.q10.ifThen RNReps.q13) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_13_k4_fwd : Entry := escEntry "esc-0260" (RNReps.q10.ifThen RNReps.q13) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_13_k5_fwd : Entry := escEntry "esc-0261" (RNReps.q10.ifThen RNReps.q13) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_13_k6_fwd : Entry := escEntry "esc-0262" (RNReps.q10.ifThen RNReps.q13) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_13_k7_fwd : Entry := escEntry "esc-0263" (RNReps.q10.ifThen RNReps.q13) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_13_k8_fwd : Entry := escEntry "esc-0264" (RNReps.q10.ifThen RNReps.q13) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_13_k9_fwd : Entry := escEntry "esc-0265" (RNReps.q10.ifThen RNReps.q13) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_13_k10_fwd : Entry := escEntry "esc-0266" (RNReps.q10.ifThen RNReps.q13) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_13_k11_fwd : Entry := escEntry "esc-0267" (RNReps.q10.ifThen RNReps.q13) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_13_k12_fwd : Entry := escEntry "esc-0268" (RNReps.q10.ifThen RNReps.q13) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_13_k13_fwd : Entry := escEntry "esc-0269" (RNReps.q10.ifThen RNReps.q13) (RNReps.q13) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_13_k14_fwd : Entry := escEntry "esc-0270" (RNReps.q10.ifThen RNReps.q13) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_13_k15_fwd : Entry := escEntry "esc-0271" (RNReps.q10.ifThen RNReps.q13) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_7_k0_fwd : Entry := escEntry "esc-0272" (RNReps.q11.ifThen RNReps.q7) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_7_k1_bwd : Entry := escEntry "esc-0273" (RNReps.q1) (RNReps.q11.ifThen RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_7_k2_fwd : Entry := escEntry "esc-0274" (RNReps.q11.ifThen RNReps.q7) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_7_k3_fwd : Entry := escEntry "esc-0275" (RNReps.q11.ifThen RNReps.q7) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_7_k4_fwd : Entry := escEntry "esc-0276" (RNReps.q11.ifThen RNReps.q7) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_7_k5_fwd : Entry := escEntry "esc-0277" (RNReps.q11.ifThen RNReps.q7) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_7_k6_fwd : Entry := escEntry "esc-0278" (RNReps.q11.ifThen RNReps.q7) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_7_k7_fwd : Entry := escEntry "esc-0279" (RNReps.q11.ifThen RNReps.q7) (RNReps.q7) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_7_k8_bwd : Entry := escEntry "esc-0280" (RNReps.q8) (RNReps.q11.ifThen RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_7_k9_fwd : Entry := escEntry "esc-0281" (RNReps.q11.ifThen RNReps.q7) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_7_k10_fwd : Entry := escEntry "esc-0282" (RNReps.q11.ifThen RNReps.q7) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_7_k11_fwd : Entry := escEntry "esc-0283" (RNReps.q11.ifThen RNReps.q7) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_7_k12_fwd : Entry := escEntry "esc-0284" (RNReps.q11.ifThen RNReps.q7) (RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_7_k13_bwd : Entry := escEntry "esc-0285" (RNReps.q13) (RNReps.q11.ifThen RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_7_k14_bwd : Entry := escEntry "esc-0286" (RNReps.q14) (RNReps.q11.ifThen RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_11_7_k15_fwd : Entry := escEntry "esc-0287" (RNReps.q11.ifThen RNReps.q7) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_12_k0_fwd : Entry := escEntry "esc-0288" (RNReps.q13.ifThen RNReps.q12) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_12_k1_bwd : Entry := escEntry "esc-0289" (RNReps.q1) (RNReps.q13.ifThen RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_12_k2_fwd : Entry := escEntry "esc-0290" (RNReps.q13.ifThen RNReps.q12) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_12_k3_fwd : Entry := escEntry "esc-0291" (RNReps.q13.ifThen RNReps.q12) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_12_k4_fwd : Entry := escEntry "esc-0292" (RNReps.q13.ifThen RNReps.q12) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_12_k5_fwd : Entry := escEntry "esc-0293" (RNReps.q13.ifThen RNReps.q12) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_12_k6_fwd : Entry := escEntry "esc-0294" (RNReps.q13.ifThen RNReps.q12) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_12_k7_fwd : Entry := escEntry "esc-0295" (RNReps.q13.ifThen RNReps.q12) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_12_k8_fwd : Entry := escEntry "esc-0296" (RNReps.q13.ifThen RNReps.q12) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_12_k9_fwd : Entry := escEntry "esc-0297" (RNReps.q13.ifThen RNReps.q12) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(0, 1), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_12_k10_fwd : Entry := escEntry "esc-0298" (RNReps.q13.ifThen RNReps.q12) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_12_k11_fwd : Entry := escEntry "esc-0299" (RNReps.q13.ifThen RNReps.q12) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(0, 1), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_12_k12_fwd : Entry := escEntry "esc-0300" (RNReps.q13.ifThen RNReps.q12) (RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_12_k13_fwd : Entry := escEntry "esc-0301" (RNReps.q13.ifThen RNReps.q12) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_12_k14_fwd : Entry := escEntry "esc-0302" (RNReps.q13.ifThen RNReps.q12) (RNReps.q14) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_12_k15_fwd : Entry := escEntry "esc-0303" (RNReps.q13.ifThen RNReps.q12) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_11_k0_fwd : Entry := escEntry "esc-0304" (RNReps.q14.ifThen RNReps.q11) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_11_k1_bwd : Entry := escEntry "esc-0305" (RNReps.q1) (RNReps.q14.ifThen RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_11_k2_fwd : Entry := escEntry "esc-0306" (RNReps.q14.ifThen RNReps.q11) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_11_k3_fwd : Entry := escEntry "esc-0307" (RNReps.q14.ifThen RNReps.q11) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_11_k4_fwd : Entry := escEntry "esc-0308" (RNReps.q14.ifThen RNReps.q11) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_11_k5_fwd : Entry := escEntry "esc-0309" (RNReps.q14.ifThen RNReps.q11) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_11_k6_fwd : Entry := escEntry "esc-0310" (RNReps.q14.ifThen RNReps.q11) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_11_k7_fwd : Entry := escEntry "esc-0311" (RNReps.q14.ifThen RNReps.q11) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_11_k8_fwd : Entry := escEntry "esc-0312" (RNReps.q14.ifThen RNReps.q11) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_11_k9_fwd : Entry := escEntry "esc-0313" (RNReps.q14.ifThen RNReps.q11) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_11_k10_fwd : Entry := escEntry "esc-0314" (RNReps.q14.ifThen RNReps.q11) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_11_k11_fwd : Entry := escEntry "esc-0315" (RNReps.q14.ifThen RNReps.q11) (RNReps.q11) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_11_k12_fwd : Entry := escEntry "esc-0316" (RNReps.q14.ifThen RNReps.q11) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_11_k13_fwd : Entry := escEntry "esc-0317" (RNReps.q14.ifThen RNReps.q11) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_11_k14_fwd : Entry := escEntry "esc-0318" (RNReps.q14.ifThen RNReps.q11) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_11_k15_fwd : Entry := escEntry "esc-0319" (RNReps.q14.ifThen RNReps.q11) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_9_k0_fwd : Entry := escEntry "esc-0320" (RNReps.q14.ifThen RNReps.q9) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_9_k1_bwd : Entry := escEntry "esc-0321" (RNReps.q1) (RNReps.q14.ifThen RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_9_k2_fwd : Entry := escEntry "esc-0322" (RNReps.q14.ifThen RNReps.q9) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_9_k3_fwd : Entry := escEntry "esc-0323" (RNReps.q14.ifThen RNReps.q9) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_9_k4_fwd : Entry := escEntry "esc-0324" (RNReps.q14.ifThen RNReps.q9) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_9_k5_fwd : Entry := escEntry "esc-0325" (RNReps.q14.ifThen RNReps.q9) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_9_k6_fwd : Entry := escEntry "esc-0326" (RNReps.q14.ifThen RNReps.q9) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_9_k7_fwd : Entry := escEntry "esc-0327" (RNReps.q14.ifThen RNReps.q9) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_9_k8_fwd : Entry := escEntry "esc-0328" (RNReps.q14.ifThen RNReps.q9) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_9_k9_fwd : Entry := escEntry "esc-0329" (RNReps.q14.ifThen RNReps.q9) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_9_k10_fwd : Entry := escEntry "esc-0330" (RNReps.q14.ifThen RNReps.q9) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_9_k11_fwd : Entry := escEntry "esc-0331" (RNReps.q14.ifThen RNReps.q9) (RNReps.q11) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_9_k12_fwd : Entry := escEntry "esc-0332" (RNReps.q14.ifThen RNReps.q9) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_9_k13_fwd : Entry := escEntry "esc-0333" (RNReps.q14.ifThen RNReps.q9) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_9_k14_fwd : Entry := escEntry "esc-0334" (RNReps.q14.ifThen RNReps.q9) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_9_k15_fwd : Entry := escEntry "esc-0335" (RNReps.q14.ifThen RNReps.q9) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_5_k0_fwd : Entry := escEntry "esc-0336" (RNReps.q15.ifThen RNReps.q5) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_5_k1_bwd : Entry := escEntry "esc-0337" (RNReps.q1) (RNReps.q15.ifThen RNReps.q5) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_5_k2_fwd : Entry := escEntry "esc-0338" (RNReps.q15.ifThen RNReps.q5) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_5_k3_fwd : Entry := escEntry "esc-0339" (RNReps.q15.ifThen RNReps.q5) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_5_k4_fwd : Entry := escEntry "esc-0340" (RNReps.q15.ifThen RNReps.q5) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_5_k5_fwd : Entry := escEntry "esc-0341" (RNReps.q15.ifThen RNReps.q5) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_5_k6_fwd : Entry := escEntry "esc-0342" (RNReps.q15.ifThen RNReps.q5) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_5_k7_fwd : Entry := escEntry "esc-0343" (RNReps.q15.ifThen RNReps.q5) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_5_k8_fwd : Entry := escEntry "esc-0344" (RNReps.q15.ifThen RNReps.q5) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_5_k9_fwd : Entry := escEntry "esc-0345" (RNReps.q15.ifThen RNReps.q5) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_5_k10_fwd : Entry := escEntry "esc-0346" (RNReps.q15.ifThen RNReps.q5) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_5_k11_fwd : Entry := escEntry "esc-0347" (RNReps.q15.ifThen RNReps.q5) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_5_k12_fwd : Entry := escEntry "esc-0348" (RNReps.q15.ifThen RNReps.q5) (RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_5_k13_fwd : Entry := escEntry "esc-0349" (RNReps.q15.ifThen RNReps.q5) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_5_k14_fwd : Entry := escEntry "esc-0350" (RNReps.q15.ifThen RNReps.q5) (RNReps.q14) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_5_k15_fwd : Entry := escEntry "esc-0351" (RNReps.q15.ifThen RNReps.q5) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_12_k0_fwd : Entry := escEntry "esc-0352" (RNReps.q8.ifThen RNReps.q12) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_12_k1_bwd : Entry := escEntry "esc-0353" (RNReps.q1) (RNReps.q8.ifThen RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_12_k2_fwd : Entry := escEntry "esc-0354" (RNReps.q8.ifThen RNReps.q12) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_12_k3_fwd : Entry := escEntry "esc-0355" (RNReps.q8.ifThen RNReps.q12) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_12_k4_fwd : Entry := escEntry "esc-0356" (RNReps.q8.ifThen RNReps.q12) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_12_k5_fwd : Entry := escEntry "esc-0357" (RNReps.q8.ifThen RNReps.q12) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_12_k6_fwd : Entry := escEntry "esc-0358" (RNReps.q8.ifThen RNReps.q12) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_12_k7_fwd : Entry := escEntry "esc-0359" (RNReps.q8.ifThen RNReps.q12) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_12_k8_fwd : Entry := escEntry "esc-0360" (RNReps.q8.ifThen RNReps.q12) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_12_k9_fwd : Entry := escEntry "esc-0361" (RNReps.q8.ifThen RNReps.q12) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(0, 1), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_12_k10_fwd : Entry := escEntry "esc-0362" (RNReps.q8.ifThen RNReps.q12) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_12_k11_fwd : Entry := escEntry "esc-0363" (RNReps.q8.ifThen RNReps.q12) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(0, 1), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_12_k12_fwd : Entry := escEntry "esc-0364" (RNReps.q8.ifThen RNReps.q12) (RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_12_k13_fwd : Entry := escEntry "esc-0365" (RNReps.q8.ifThen RNReps.q12) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_12_k14_fwd : Entry := escEntry "esc-0366" (RNReps.q8.ifThen RNReps.q12) (RNReps.q14) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_12_k15_fwd : Entry := escEntry "esc-0367" (RNReps.q8.ifThen RNReps.q12) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_7_k0_fwd : Entry := escEntry "esc-0368" (RNReps.q8.ifThen RNReps.q7) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_7_k1_bwd : Entry := escEntry "esc-0369" (RNReps.q1) (RNReps.q8.ifThen RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_7_k2_fwd : Entry := escEntry "esc-0370" (RNReps.q8.ifThen RNReps.q7) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_7_k3_fwd : Entry := escEntry "esc-0371" (RNReps.q8.ifThen RNReps.q7) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_7_k4_fwd : Entry := escEntry "esc-0372" (RNReps.q8.ifThen RNReps.q7) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_7_k5_fwd : Entry := escEntry "esc-0373" (RNReps.q8.ifThen RNReps.q7) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_7_k6_fwd : Entry := escEntry "esc-0374" (RNReps.q8.ifThen RNReps.q7) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_7_k7_fwd : Entry := escEntry "esc-0375" (RNReps.q8.ifThen RNReps.q7) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_7_k8_fwd : Entry := escEntry "esc-0376" (RNReps.q8.ifThen RNReps.q7) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_7_k9_fwd : Entry := escEntry "esc-0377" (RNReps.q8.ifThen RNReps.q7) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_7_k10_fwd : Entry := escEntry "esc-0378" (RNReps.q8.ifThen RNReps.q7) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_7_k11_fwd : Entry := escEntry "esc-0379" (RNReps.q8.ifThen RNReps.q7) (RNReps.q11) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_7_k12_fwd : Entry := escEntry "esc-0380" (RNReps.q8.ifThen RNReps.q7) (RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_7_k13_fwd : Entry := escEntry "esc-0381" (RNReps.q8.ifThen RNReps.q7) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_7_k14_fwd : Entry := escEntry "esc-0382" (RNReps.q8.ifThen RNReps.q7) (RNReps.q14) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_7_k15_fwd : Entry := escEntry "esc-0383" (RNReps.q8.ifThen RNReps.q7) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_14_k0_fwd : Entry := escEntry "esc-0384" (RNReps.q10.or RNReps.q14) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_14_k1_bwd : Entry := escEntry "esc-0385" (RNReps.q1) (RNReps.q10.or RNReps.q14) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_14_k2_fwd : Entry := escEntry "esc-0386" (RNReps.q10.or RNReps.q14) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_14_k3_fwd : Entry := escEntry "esc-0387" (RNReps.q10.or RNReps.q14) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_14_k4_fwd : Entry := escEntry "esc-0388" (RNReps.q10.or RNReps.q14) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_14_k5_fwd : Entry := escEntry "esc-0389" (RNReps.q10.or RNReps.q14) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_14_k6_fwd : Entry := escEntry "esc-0390" (RNReps.q10.or RNReps.q14) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_14_k7_fwd : Entry := escEntry "esc-0391" (RNReps.q10.or RNReps.q14) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_14_k8_fwd : Entry := escEntry "esc-0392" (RNReps.q10.or RNReps.q14) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_14_k9_fwd : Entry := escEntry "esc-0393" (RNReps.q10.or RNReps.q14) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_14_k10_fwd : Entry := escEntry "esc-0394" (RNReps.q10.or RNReps.q14) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_14_k11_fwd : Entry := escEntry "esc-0395" (RNReps.q10.or RNReps.q14) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_14_k12_fwd : Entry := escEntry "esc-0396" (RNReps.q10.or RNReps.q14) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_14_k13_fwd : Entry := escEntry "esc-0397" (RNReps.q10.or RNReps.q14) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_14_k14_fwd : Entry := escEntry "esc-0398" (RNReps.q10.or RNReps.q14) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_14_k15_fwd : Entry := escEntry "esc-0399" (RNReps.q10.or RNReps.q14) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_12_15_k0_fwd : Entry := escEntry "esc-0400" (RNReps.q12.or RNReps.q15) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_12_15_k1_bwd : Entry := escEntry "esc-0401" (RNReps.q1) (RNReps.q12.or RNReps.q15) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_12_15_k2_fwd : Entry := escEntry "esc-0402" (RNReps.q12.or RNReps.q15) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_12_15_k3_fwd : Entry := escEntry "esc-0403" (RNReps.q12.or RNReps.q15) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_12_15_k4_fwd : Entry := escEntry "esc-0404" (RNReps.q12.or RNReps.q15) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_12_15_k5_fwd : Entry := escEntry "esc-0405" (RNReps.q12.or RNReps.q15) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_12_15_k6_fwd : Entry := escEntry "esc-0406" (RNReps.q12.or RNReps.q15) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_12_15_k7_fwd : Entry := escEntry "esc-0407" (RNReps.q12.or RNReps.q15) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_12_15_k8_fwd : Entry := escEntry "esc-0408" (RNReps.q12.or RNReps.q15) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_12_15_k9_fwd : Entry := escEntry "esc-0409" (RNReps.q12.or RNReps.q15) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_12_15_k10_fwd : Entry := escEntry "esc-0410" (RNReps.q12.or RNReps.q15) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_12_15_k11_fwd : Entry := escEntry "esc-0411" (RNReps.q12.or RNReps.q15) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(0, 1), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_12_15_k12_fwd : Entry := escEntry "esc-0412" (RNReps.q12.or RNReps.q15) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_12_15_k13_bwd : Entry := escEntry "esc-0413" (RNReps.q13) (RNReps.q12.or RNReps.q15) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_12_15_k14_fwd : Entry := escEntry "esc-0414" (RNReps.q12.or RNReps.q15) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_12_15_k15_fwd : Entry := escEntry "esc-0415" (RNReps.q12.or RNReps.q15) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_8_k0_fwd : Entry := escEntry "esc-0416" (RNReps.q5.or RNReps.q8) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_8_k1_bwd : Entry := escEntry "esc-0417" (RNReps.q1) (RNReps.q5.or RNReps.q8) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_8_k2_fwd : Entry := escEntry "esc-0418" (RNReps.q5.or RNReps.q8) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_8_k3_fwd : Entry := escEntry "esc-0419" (RNReps.q5.or RNReps.q8) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_8_k4_fwd : Entry := escEntry "esc-0420" (RNReps.q5.or RNReps.q8) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_8_k5_fwd : Entry := escEntry "esc-0421" (RNReps.q5.or RNReps.q8) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_8_k6_fwd : Entry := escEntry "esc-0422" (RNReps.q5.or RNReps.q8) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_8_k7_fwd : Entry := escEntry "esc-0423" (RNReps.q5.or RNReps.q8) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_8_k8_fwd : Entry := escEntry "esc-0424" (RNReps.q5.or RNReps.q8) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_8_k9_fwd : Entry := escEntry "esc-0425" (RNReps.q5.or RNReps.q8) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_8_k10_fwd : Entry := escEntry "esc-0426" (RNReps.q5.or RNReps.q8) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_8_k11_fwd : Entry := escEntry "esc-0427" (RNReps.q5.or RNReps.q8) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_8_k12_fwd : Entry := escEntry "esc-0428" (RNReps.q5.or RNReps.q8) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_8_k13_bwd : Entry := escEntry "esc-0429" (RNReps.q13) (RNReps.q5.or RNReps.q8) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(0, 2), (1, 4), (3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_8_k14_fwd : Entry := escEntry "esc-0430" (RNReps.q5.or RNReps.q8) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_5_8_k15_fwd : Entry := escEntry "esc-0431" (RNReps.q5.or RNReps.q8) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_11_k0_fwd : Entry := escEntry "esc-0432" (RNReps.q8.or RNReps.q11) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_11_k1_bwd : Entry := escEntry "esc-0433" (RNReps.q1) (RNReps.q8.or RNReps.q11) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_11_k2_fwd : Entry := escEntry "esc-0434" (RNReps.q8.or RNReps.q11) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_11_k3_fwd : Entry := escEntry "esc-0435" (RNReps.q8.or RNReps.q11) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_11_k4_fwd : Entry := escEntry "esc-0436" (RNReps.q8.or RNReps.q11) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_11_k5_fwd : Entry := escEntry "esc-0437" (RNReps.q8.or RNReps.q11) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_11_k6_fwd : Entry := escEntry "esc-0438" (RNReps.q8.or RNReps.q11) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_11_k7_fwd : Entry := escEntry "esc-0439" (RNReps.q8.or RNReps.q11) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_11_k8_fwd : Entry := escEntry "esc-0440" (RNReps.q8.or RNReps.q11) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_11_k9_fwd : Entry := escEntry "esc-0441" (RNReps.q8.or RNReps.q11) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_11_k10_fwd : Entry := escEntry "esc-0442" (RNReps.q8.or RNReps.q11) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_11_k11_fwd : Entry := escEntry "esc-0443" (RNReps.q8.or RNReps.q11) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_11_k12_fwd : Entry := escEntry "esc-0444" (RNReps.q8.or RNReps.q11) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_11_k13_fwd : Entry := escEntry "esc-0445" (RNReps.q8.or RNReps.q11) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_11_k14_fwd : Entry := escEntry "esc-0446" (RNReps.q8.or RNReps.q11) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_11_k15_fwd : Entry := escEntry "esc-0447" (RNReps.q8.or RNReps.q11) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_9_15_k0_fwd : Entry := escEntry "esc-0448" (RNReps.q9.or RNReps.q15) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_9_15_k1_bwd : Entry := escEntry "esc-0449" (RNReps.q1) (RNReps.q9.or RNReps.q15) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_9_15_k2_fwd : Entry := escEntry "esc-0450" (RNReps.q9.or RNReps.q15) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_9_15_k3_fwd : Entry := escEntry "esc-0451" (RNReps.q9.or RNReps.q15) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_9_15_k4_fwd : Entry := escEntry "esc-0452" (RNReps.q9.or RNReps.q15) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_9_15_k5_fwd : Entry := escEntry "esc-0453" (RNReps.q9.or RNReps.q15) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_9_15_k6_fwd : Entry := escEntry "esc-0454" (RNReps.q9.or RNReps.q15) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_9_15_k7_fwd : Entry := escEntry "esc-0455" (RNReps.q9.or RNReps.q15) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_9_15_k8_fwd : Entry := escEntry "esc-0456" (RNReps.q9.or RNReps.q15) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_9_15_k9_fwd : Entry := escEntry "esc-0457" (RNReps.q9.or RNReps.q15) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_9_15_k10_fwd : Entry := escEntry "esc-0458" (RNReps.q9.or RNReps.q15) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_9_15_k11_bwd : Entry := escEntry "esc-0459" (RNReps.q11) (RNReps.q9.or RNReps.q15) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_9_15_k12_fwd : Entry := escEntry "esc-0460" (RNReps.q9.or RNReps.q15) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_9_15_k13_bwd : Entry := escEntry "esc-0461" (RNReps.q13) (RNReps.q9.or RNReps.q15) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_9_15_k14_fwd : Entry := escEntry "esc-0462" (RNReps.q9.or RNReps.q15) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_9_15_k15_fwd : Entry := escEntry "esc-0463" (RNReps.q9.or RNReps.q15) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_11_13_k0_fwd : Entry := escEntry "esc-0464" (RNReps.q11.and RNReps.q13) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_11_13_k1_bwd : Entry := escEntry "esc-0465" (RNReps.q1) (RNReps.q11.and RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_11_13_k2_fwd : Entry := escEntry "esc-0466" (RNReps.q11.and RNReps.q13) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_11_13_k3_fwd : Entry := escEntry "esc-0467" (RNReps.q11.and RNReps.q13) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_11_13_k4_fwd : Entry := escEntry "esc-0468" (RNReps.q11.and RNReps.q13) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_11_13_k5_fwd : Entry := escEntry "esc-0469" (RNReps.q11.and RNReps.q13) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_11_13_k6_fwd : Entry := escEntry "esc-0470" (RNReps.q11.and RNReps.q13) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_11_13_k7_fwd : Entry := escEntry "esc-0471" (RNReps.q11.and RNReps.q13) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_11_13_k8_fwd : Entry := escEntry "esc-0472" (RNReps.q11.and RNReps.q13) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_11_13_k9_fwd : Entry := escEntry "esc-0473" (RNReps.q11.and RNReps.q13) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_11_13_k10_fwd : Entry := escEntry "esc-0474" (RNReps.q11.and RNReps.q13) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_11_13_k11_bwd : Entry := escEntry "esc-0475" (RNReps.q11) (RNReps.q11.and RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_11_13_k12_fwd : Entry := escEntry "esc-0476" (RNReps.q11.and RNReps.q13) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_11_13_k13_bwd : Entry := escEntry "esc-0477" (RNReps.q13) (RNReps.q11.and RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_11_13_k14_fwd : Entry := escEntry "esc-0478" (RNReps.q11.and RNReps.q13) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_11_13_k15_fwd : Entry := escEntry "esc-0479" (RNReps.q11.and RNReps.q13) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_14_k0_fwd : Entry := escEntry "esc-0480" (RNReps.q8.and RNReps.q14) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_14_k1_bwd : Entry := escEntry "esc-0481" (RNReps.q1) (RNReps.q8.and RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_14_k2_fwd : Entry := escEntry "esc-0482" (RNReps.q8.and RNReps.q14) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_14_k3_fwd : Entry := escEntry "esc-0483" (RNReps.q8.and RNReps.q14) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_14_k4_fwd : Entry := escEntry "esc-0484" (RNReps.q8.and RNReps.q14) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_14_k5_fwd : Entry := escEntry "esc-0485" (RNReps.q8.and RNReps.q14) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_14_k6_fwd : Entry := escEntry "esc-0486" (RNReps.q8.and RNReps.q14) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_14_k7_fwd : Entry := escEntry "esc-0487" (RNReps.q8.and RNReps.q14) (RNReps.q7) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_14_k8_bwd : Entry := escEntry "esc-0488" (RNReps.q8) (RNReps.q8.and RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_14_k9_fwd : Entry := escEntry "esc-0489" (RNReps.q8.and RNReps.q14) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_14_k10_fwd : Entry := escEntry "esc-0490" (RNReps.q8.and RNReps.q14) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_14_k11_fwd : Entry := escEntry "esc-0491" (RNReps.q8.and RNReps.q14) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_14_k12_fwd : Entry := escEntry "esc-0492" (RNReps.q8.and RNReps.q14) (RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_14_k13_bwd : Entry := escEntry "esc-0493" (RNReps.q13) (RNReps.q8.and RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_14_k14_bwd : Entry := escEntry "esc-0494" (RNReps.q14) (RNReps.q8.and RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_8_14_k15_fwd : Entry := escEntry "esc-0495" (RNReps.q8.and RNReps.q14) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_4_k0_fwd : Entry := escEntry "esc-0496" (RNReps.q10.ifThen RNReps.q4) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_4_k1_bwd : Entry := escEntry "esc-0497" (RNReps.q1) (RNReps.q10.ifThen RNReps.q4) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_4_k2_fwd : Entry := escEntry "esc-0498" (RNReps.q10.ifThen RNReps.q4) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_4_k3_fwd : Entry := escEntry "esc-0499" (RNReps.q10.ifThen RNReps.q4) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_4_k4_fwd : Entry := escEntry "esc-0500" (RNReps.q10.ifThen RNReps.q4) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_4_k5_fwd : Entry := escEntry "esc-0501" (RNReps.q10.ifThen RNReps.q4) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_4_k6_fwd : Entry := escEntry "esc-0502" (RNReps.q10.ifThen RNReps.q4) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_4_k7_fwd : Entry := escEntry "esc-0503" (RNReps.q10.ifThen RNReps.q4) (RNReps.q7) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_4_k8_bwd : Entry := escEntry "esc-0504" (RNReps.q8) (RNReps.q10.ifThen RNReps.q4) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_4_k9_fwd : Entry := escEntry "esc-0505" (RNReps.q10.ifThen RNReps.q4) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_4_k10_fwd : Entry := escEntry "esc-0506" (RNReps.q10.ifThen RNReps.q4) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_4_k11_fwd : Entry := escEntry "esc-0507" (RNReps.q10.ifThen RNReps.q4) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_4_k12_fwd : Entry := escEntry "esc-0508" (RNReps.q10.ifThen RNReps.q4) (RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_4_k13_bwd : Entry := escEntry "esc-0509" (RNReps.q13) (RNReps.q10.ifThen RNReps.q4) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_4_k14_bwd : Entry := escEntry "esc-0510" (RNReps.q14) (RNReps.q10.ifThen RNReps.q4) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_4_k15_fwd : Entry := escEntry "esc-0511" (RNReps.q10.ifThen RNReps.q4) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_11_k0_fwd : Entry := escEntry "esc-0512" (RNReps.q12.ifThen RNReps.q11) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_11_k1_bwd : Entry := escEntry "esc-0513" (RNReps.q1) (RNReps.q12.ifThen RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(0, 1), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_11_k2_fwd : Entry := escEntry "esc-0514" (RNReps.q12.ifThen RNReps.q11) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_11_k3_fwd : Entry := escEntry "esc-0515" (RNReps.q12.ifThen RNReps.q11) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_11_k4_fwd : Entry := escEntry "esc-0516" (RNReps.q12.ifThen RNReps.q11) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_11_k5_fwd : Entry := escEntry "esc-0517" (RNReps.q12.ifThen RNReps.q11) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_11_k6_fwd : Entry := escEntry "esc-0518" (RNReps.q12.ifThen RNReps.q11) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_11_k7_fwd : Entry := escEntry "esc-0519" (RNReps.q12.ifThen RNReps.q11) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_11_k8_fwd : Entry := escEntry "esc-0520" (RNReps.q12.ifThen RNReps.q11) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_11_k9_fwd : Entry := escEntry "esc-0521" (RNReps.q12.ifThen RNReps.q11) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_11_k10_fwd : Entry := escEntry "esc-0522" (RNReps.q12.ifThen RNReps.q11) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_11_k11_fwd : Entry := escEntry "esc-0523" (RNReps.q12.ifThen RNReps.q11) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_11_k12_fwd : Entry := escEntry "esc-0524" (RNReps.q12.ifThen RNReps.q11) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_11_k13_fwd : Entry := escEntry "esc-0525" (RNReps.q12.ifThen RNReps.q11) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_11_k14_fwd : Entry := escEntry "esc-0526" (RNReps.q12.ifThen RNReps.q11) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_11_k15_fwd : Entry := escEntry "esc-0527" (RNReps.q12.ifThen RNReps.q11) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_14_k0_fwd : Entry := escEntry "esc-0528" (RNReps.q13.ifThen RNReps.q14) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_14_k1_bwd : Entry := escEntry "esc-0529" (RNReps.q1) (RNReps.q13.ifThen RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_14_k2_fwd : Entry := escEntry "esc-0530" (RNReps.q13.ifThen RNReps.q14) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_14_k3_fwd : Entry := escEntry "esc-0531" (RNReps.q13.ifThen RNReps.q14) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_14_k4_fwd : Entry := escEntry "esc-0532" (RNReps.q13.ifThen RNReps.q14) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_14_k5_fwd : Entry := escEntry "esc-0533" (RNReps.q13.ifThen RNReps.q14) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_14_k6_fwd : Entry := escEntry "esc-0534" (RNReps.q13.ifThen RNReps.q14) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_14_k7_fwd : Entry := escEntry "esc-0535" (RNReps.q13.ifThen RNReps.q14) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_14_k8_fwd : Entry := escEntry "esc-0536" (RNReps.q13.ifThen RNReps.q14) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_14_k9_fwd : Entry := escEntry "esc-0537" (RNReps.q13.ifThen RNReps.q14) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_14_k10_fwd : Entry := escEntry "esc-0538" (RNReps.q13.ifThen RNReps.q14) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_14_k11_fwd : Entry := escEntry "esc-0539" (RNReps.q13.ifThen RNReps.q14) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_14_k12_fwd : Entry := escEntry "esc-0540" (RNReps.q13.ifThen RNReps.q14) (RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_14_k13_fwd : Entry := escEntry "esc-0541" (RNReps.q13.ifThen RNReps.q14) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_14_k14_fwd : Entry := escEntry "esc-0542" (RNReps.q13.ifThen RNReps.q14) (RNReps.q14) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_14_k15_fwd : Entry := escEntry "esc-0543" (RNReps.q13.ifThen RNReps.q14) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_12_k0_fwd : Entry := escEntry "esc-0544" (RNReps.q14.ifThen RNReps.q12) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_12_k1_bwd : Entry := escEntry "esc-0545" (RNReps.q1) (RNReps.q14.ifThen RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_12_k2_fwd : Entry := escEntry "esc-0546" (RNReps.q14.ifThen RNReps.q12) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_12_k3_fwd : Entry := escEntry "esc-0547" (RNReps.q14.ifThen RNReps.q12) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_12_k4_fwd : Entry := escEntry "esc-0548" (RNReps.q14.ifThen RNReps.q12) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_12_k5_fwd : Entry := escEntry "esc-0549" (RNReps.q14.ifThen RNReps.q12) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_12_k6_fwd : Entry := escEntry "esc-0550" (RNReps.q14.ifThen RNReps.q12) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_12_k7_fwd : Entry := escEntry "esc-0551" (RNReps.q14.ifThen RNReps.q12) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_12_k8_fwd : Entry := escEntry "esc-0552" (RNReps.q14.ifThen RNReps.q12) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_12_k9_fwd : Entry := escEntry "esc-0553" (RNReps.q14.ifThen RNReps.q12) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_12_k10_fwd : Entry := escEntry "esc-0554" (RNReps.q14.ifThen RNReps.q12) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_12_k11_fwd : Entry := escEntry "esc-0555" (RNReps.q14.ifThen RNReps.q12) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(0, 1), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_12_k12_fwd : Entry := escEntry "esc-0556" (RNReps.q14.ifThen RNReps.q12) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_12_k13_fwd : Entry := escEntry "esc-0557" (RNReps.q14.ifThen RNReps.q12) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_12_k14_fwd : Entry := escEntry "esc-0558" (RNReps.q14.ifThen RNReps.q12) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_12_k15_fwd : Entry := escEntry "esc-0559" (RNReps.q14.ifThen RNReps.q12) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_12_k0_fwd : Entry := escEntry "esc-0560" (RNReps.q15.ifThen RNReps.q12) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_12_k1_bwd : Entry := escEntry "esc-0561" (RNReps.q1) (RNReps.q15.ifThen RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_12_k2_fwd : Entry := escEntry "esc-0562" (RNReps.q15.ifThen RNReps.q12) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_12_k3_fwd : Entry := escEntry "esc-0563" (RNReps.q15.ifThen RNReps.q12) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_12_k4_fwd : Entry := escEntry "esc-0564" (RNReps.q15.ifThen RNReps.q12) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_12_k5_fwd : Entry := escEntry "esc-0565" (RNReps.q15.ifThen RNReps.q12) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_12_k6_fwd : Entry := escEntry "esc-0566" (RNReps.q15.ifThen RNReps.q12) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_12_k7_fwd : Entry := escEntry "esc-0567" (RNReps.q15.ifThen RNReps.q12) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_12_k8_fwd : Entry := escEntry "esc-0568" (RNReps.q15.ifThen RNReps.q12) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_12_k9_fwd : Entry := escEntry "esc-0569" (RNReps.q15.ifThen RNReps.q12) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_12_k10_fwd : Entry := escEntry "esc-0570" (RNReps.q15.ifThen RNReps.q12) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_12_k11_fwd : Entry := escEntry "esc-0571" (RNReps.q15.ifThen RNReps.q12) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_12_k12_fwd : Entry := escEntry "esc-0572" (RNReps.q15.ifThen RNReps.q12) (RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_12_k13_fwd : Entry := escEntry "esc-0573" (RNReps.q15.ifThen RNReps.q12) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_12_k14_fwd : Entry := escEntry "esc-0574" (RNReps.q15.ifThen RNReps.q12) (RNReps.q14) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_12_k15_fwd : Entry := escEntry "esc-0575" (RNReps.q15.ifThen RNReps.q12) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_7_k0_fwd : Entry := escEntry "esc-0576" (RNReps.q15.ifThen RNReps.q7) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_7_k1_bwd : Entry := escEntry "esc-0577" (RNReps.q1) (RNReps.q15.ifThen RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_7_k2_fwd : Entry := escEntry "esc-0578" (RNReps.q15.ifThen RNReps.q7) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_7_k3_fwd : Entry := escEntry "esc-0579" (RNReps.q15.ifThen RNReps.q7) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_7_k4_fwd : Entry := escEntry "esc-0580" (RNReps.q15.ifThen RNReps.q7) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_7_k5_fwd : Entry := escEntry "esc-0581" (RNReps.q15.ifThen RNReps.q7) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_7_k6_fwd : Entry := escEntry "esc-0582" (RNReps.q15.ifThen RNReps.q7) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_7_k7_fwd : Entry := escEntry "esc-0583" (RNReps.q15.ifThen RNReps.q7) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_7_k8_fwd : Entry := escEntry "esc-0584" (RNReps.q15.ifThen RNReps.q7) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_7_k9_fwd : Entry := escEntry "esc-0585" (RNReps.q15.ifThen RNReps.q7) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_7_k10_fwd : Entry := escEntry "esc-0586" (RNReps.q15.ifThen RNReps.q7) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_7_k11_fwd : Entry := escEntry "esc-0587" (RNReps.q15.ifThen RNReps.q7) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_7_k12_fwd : Entry := escEntry "esc-0588" (RNReps.q15.ifThen RNReps.q7) (RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_7_k13_fwd : Entry := escEntry "esc-0589" (RNReps.q15.ifThen RNReps.q7) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_7_k14_fwd : Entry := escEntry "esc-0590" (RNReps.q15.ifThen RNReps.q7) (RNReps.q14) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_7_k15_fwd : Entry := escEntry "esc-0591" (RNReps.q15.ifThen RNReps.q7) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_14_k0_fwd : Entry := escEntry "esc-0592" (RNReps.q8.ifThen RNReps.q14) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_14_k1_bwd : Entry := escEntry "esc-0593" (RNReps.q1) (RNReps.q8.ifThen RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_14_k2_fwd : Entry := escEntry "esc-0594" (RNReps.q8.ifThen RNReps.q14) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_14_k3_fwd : Entry := escEntry "esc-0595" (RNReps.q8.ifThen RNReps.q14) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_14_k4_fwd : Entry := escEntry "esc-0596" (RNReps.q8.ifThen RNReps.q14) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_14_k5_fwd : Entry := escEntry "esc-0597" (RNReps.q8.ifThen RNReps.q14) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_14_k6_fwd : Entry := escEntry "esc-0598" (RNReps.q8.ifThen RNReps.q14) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_14_k7_fwd : Entry := escEntry "esc-0599" (RNReps.q8.ifThen RNReps.q14) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_14_k8_fwd : Entry := escEntry "esc-0600" (RNReps.q8.ifThen RNReps.q14) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_14_k9_fwd : Entry := escEntry "esc-0601" (RNReps.q8.ifThen RNReps.q14) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_14_k10_fwd : Entry := escEntry "esc-0602" (RNReps.q8.ifThen RNReps.q14) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_14_k11_fwd : Entry := escEntry "esc-0603" (RNReps.q8.ifThen RNReps.q14) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_14_k12_fwd : Entry := escEntry "esc-0604" (RNReps.q8.ifThen RNReps.q14) (RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_14_k13_fwd : Entry := escEntry "esc-0605" (RNReps.q8.ifThen RNReps.q14) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_14_k14_fwd : Entry := escEntry "esc-0606" (RNReps.q8.ifThen RNReps.q14) (RNReps.q14) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_14_k15_fwd : Entry := escEntry "esc-0607" (RNReps.q8.ifThen RNReps.q14) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_9_k0_fwd : Entry := escEntry "esc-0608" (RNReps.q8.ifThen RNReps.q9) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_9_k1_bwd : Entry := escEntry "esc-0609" (RNReps.q1) (RNReps.q8.ifThen RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_9_k2_fwd : Entry := escEntry "esc-0610" (RNReps.q8.ifThen RNReps.q9) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_9_k3_fwd : Entry := escEntry "esc-0611" (RNReps.q8.ifThen RNReps.q9) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_9_k4_fwd : Entry := escEntry "esc-0612" (RNReps.q8.ifThen RNReps.q9) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_9_k5_fwd : Entry := escEntry "esc-0613" (RNReps.q8.ifThen RNReps.q9) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_9_k6_fwd : Entry := escEntry "esc-0614" (RNReps.q8.ifThen RNReps.q9) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_9_k7_fwd : Entry := escEntry "esc-0615" (RNReps.q8.ifThen RNReps.q9) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_9_k8_fwd : Entry := escEntry "esc-0616" (RNReps.q8.ifThen RNReps.q9) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_9_k9_fwd : Entry := escEntry "esc-0617" (RNReps.q8.ifThen RNReps.q9) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_9_k10_fwd : Entry := escEntry "esc-0618" (RNReps.q8.ifThen RNReps.q9) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_9_k11_fwd : Entry := escEntry "esc-0619" (RNReps.q8.ifThen RNReps.q9) (RNReps.q11) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_9_k12_fwd : Entry := escEntry "esc-0620" (RNReps.q8.ifThen RNReps.q9) (RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_9_k13_fwd : Entry := escEntry "esc-0621" (RNReps.q8.ifThen RNReps.q9) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_9_k14_fwd : Entry := escEntry "esc-0622" (RNReps.q8.ifThen RNReps.q9) (RNReps.q14) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_9_k15_fwd : Entry := escEntry "esc-0623" (RNReps.q8.ifThen RNReps.q9) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_12_k0_fwd : Entry := escEntry "esc-0624" (RNReps.q11.or RNReps.q12) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_12_k1_bwd : Entry := escEntry "esc-0625" (RNReps.q1) (RNReps.q11.or RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_12_k2_fwd : Entry := escEntry "esc-0626" (RNReps.q11.or RNReps.q12) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_12_k3_fwd : Entry := escEntry "esc-0627" (RNReps.q11.or RNReps.q12) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_12_k4_fwd : Entry := escEntry "esc-0628" (RNReps.q11.or RNReps.q12) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_12_k5_fwd : Entry := escEntry "esc-0629" (RNReps.q11.or RNReps.q12) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_12_k6_fwd : Entry := escEntry "esc-0630" (RNReps.q11.or RNReps.q12) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_12_k7_fwd : Entry := escEntry "esc-0631" (RNReps.q11.or RNReps.q12) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_12_k8_fwd : Entry := escEntry "esc-0632" (RNReps.q11.or RNReps.q12) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_12_k9_fwd : Entry := escEntry "esc-0633" (RNReps.q11.or RNReps.q12) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_12_k10_fwd : Entry := escEntry "esc-0634" (RNReps.q11.or RNReps.q12) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_12_k11_fwd : Entry := escEntry "esc-0635" (RNReps.q11.or RNReps.q12) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(0, 1), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_12_k12_fwd : Entry := escEntry "esc-0636" (RNReps.q11.or RNReps.q12) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_12_k13_fwd : Entry := escEntry "esc-0637" (RNReps.q11.or RNReps.q12) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_12_k14_fwd : Entry := escEntry "esc-0638" (RNReps.q11.or RNReps.q12) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_12_k15_fwd : Entry := escEntry "esc-0639" (RNReps.q11.or RNReps.q12) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_13_14_k0_fwd : Entry := escEntry "esc-0640" (RNReps.q13.or RNReps.q14) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_13_14_k1_bwd : Entry := escEntry "esc-0641" (RNReps.q1) (RNReps.q13.or RNReps.q14) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_13_14_k2_fwd : Entry := escEntry "esc-0642" (RNReps.q13.or RNReps.q14) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_13_14_k3_fwd : Entry := escEntry "esc-0643" (RNReps.q13.or RNReps.q14) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_13_14_k4_fwd : Entry := escEntry "esc-0644" (RNReps.q13.or RNReps.q14) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_13_14_k5_fwd : Entry := escEntry "esc-0645" (RNReps.q13.or RNReps.q14) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_13_14_k6_fwd : Entry := escEntry "esc-0646" (RNReps.q13.or RNReps.q14) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_13_14_k7_fwd : Entry := escEntry "esc-0647" (RNReps.q13.or RNReps.q14) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_13_14_k8_fwd : Entry := escEntry "esc-0648" (RNReps.q13.or RNReps.q14) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_13_14_k9_fwd : Entry := escEntry "esc-0649" (RNReps.q13.or RNReps.q14) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_13_14_k10_fwd : Entry := escEntry "esc-0650" (RNReps.q13.or RNReps.q14) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_13_14_k11_fwd : Entry := escEntry "esc-0651" (RNReps.q13.or RNReps.q14) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_13_14_k12_fwd : Entry := escEntry "esc-0652" (RNReps.q13.or RNReps.q14) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_13_14_k13_fwd : Entry := escEntry "esc-0653" (RNReps.q13.or RNReps.q14) (RNReps.q13) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_13_14_k14_fwd : Entry := escEntry "esc-0654" (RNReps.q13.or RNReps.q14) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_13_14_k15_fwd : Entry := escEntry "esc-0655" (RNReps.q13.or RNReps.q14) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_6_15_k0_fwd : Entry := escEntry "esc-0656" (RNReps.q6.or RNReps.q15) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_6_15_k1_bwd : Entry := escEntry "esc-0657" (RNReps.q1) (RNReps.q6.or RNReps.q15) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_6_15_k2_fwd : Entry := escEntry "esc-0658" (RNReps.q6.or RNReps.q15) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_6_15_k3_fwd : Entry := escEntry "esc-0659" (RNReps.q6.or RNReps.q15) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_6_15_k4_fwd : Entry := escEntry "esc-0660" (RNReps.q6.or RNReps.q15) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_6_15_k5_fwd : Entry := escEntry "esc-0661" (RNReps.q6.or RNReps.q15) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_6_15_k6_fwd : Entry := escEntry "esc-0662" (RNReps.q6.or RNReps.q15) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_6_15_k7_fwd : Entry := escEntry "esc-0663" (RNReps.q6.or RNReps.q15) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_6_15_k8_bwd : Entry := escEntry "esc-0664" (RNReps.q8) (RNReps.q6.or RNReps.q15) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_6_15_k9_fwd : Entry := escEntry "esc-0665" (RNReps.q6.or RNReps.q15) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_6_15_k10_fwd : Entry := escEntry "esc-0666" (RNReps.q6.or RNReps.q15) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_6_15_k11_bwd : Entry := escEntry "esc-0667" (RNReps.q11) (RNReps.q6.or RNReps.q15) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_6_15_k12_fwd : Entry := escEntry "esc-0668" (RNReps.q6.or RNReps.q15) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_6_15_k13_bwd : Entry := escEntry "esc-0669" (RNReps.q13) (RNReps.q6.or RNReps.q15) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_6_15_k14_fwd : Entry := escEntry "esc-0670" (RNReps.q6.or RNReps.q15) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_6_15_k15_fwd : Entry := escEntry "esc-0671" (RNReps.q6.or RNReps.q15) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_12_k0_fwd : Entry := escEntry "esc-0672" (RNReps.q8.or RNReps.q12) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_12_k1_bwd : Entry := escEntry "esc-0673" (RNReps.q1) (RNReps.q8.or RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_12_k2_fwd : Entry := escEntry "esc-0674" (RNReps.q8.or RNReps.q12) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_12_k3_fwd : Entry := escEntry "esc-0675" (RNReps.q8.or RNReps.q12) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_12_k4_fwd : Entry := escEntry "esc-0676" (RNReps.q8.or RNReps.q12) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_12_k5_fwd : Entry := escEntry "esc-0677" (RNReps.q8.or RNReps.q12) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_12_k6_fwd : Entry := escEntry "esc-0678" (RNReps.q8.or RNReps.q12) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_12_k7_fwd : Entry := escEntry "esc-0679" (RNReps.q8.or RNReps.q12) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_12_k8_fwd : Entry := escEntry "esc-0680" (RNReps.q8.or RNReps.q12) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_12_k9_fwd : Entry := escEntry "esc-0681" (RNReps.q8.or RNReps.q12) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_12_k10_fwd : Entry := escEntry "esc-0682" (RNReps.q8.or RNReps.q12) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_12_k11_fwd : Entry := escEntry "esc-0683" (RNReps.q8.or RNReps.q12) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_12_k12_fwd : Entry := escEntry "esc-0684" (RNReps.q8.or RNReps.q12) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_12_k13_bwd : Entry := escEntry "esc-0685" (RNReps.q13) (RNReps.q8.or RNReps.q12) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4)], [(0, 2), (1, 4), (3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_12_k14_fwd : Entry := escEntry "esc-0686" (RNReps.q8.or RNReps.q12) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_12_k15_fwd : Entry := escEntry "esc-0687" (RNReps.q8.or RNReps.q12) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_11_k0_fwd : Entry := escEntry "esc-0688" (RNReps.q13.ifThen RNReps.q11) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_11_k1_bwd : Entry := escEntry "esc-0689" (RNReps.q1) (RNReps.q13.ifThen RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_11_k2_fwd : Entry := escEntry "esc-0690" (RNReps.q13.ifThen RNReps.q11) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_11_k3_fwd : Entry := escEntry "esc-0691" (RNReps.q13.ifThen RNReps.q11) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_11_k4_fwd : Entry := escEntry "esc-0692" (RNReps.q13.ifThen RNReps.q11) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_11_k5_fwd : Entry := escEntry "esc-0693" (RNReps.q13.ifThen RNReps.q11) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_11_k6_fwd : Entry := escEntry "esc-0694" (RNReps.q13.ifThen RNReps.q11) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_11_k7_fwd : Entry := escEntry "esc-0695" (RNReps.q13.ifThen RNReps.q11) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_11_k8_fwd : Entry := escEntry "esc-0696" (RNReps.q13.ifThen RNReps.q11) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_11_k9_fwd : Entry := escEntry "esc-0697" (RNReps.q13.ifThen RNReps.q11) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_11_k10_fwd : Entry := escEntry "esc-0698" (RNReps.q13.ifThen RNReps.q11) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_11_k11_fwd : Entry := escEntry "esc-0699" (RNReps.q13.ifThen RNReps.q11) (RNReps.q11) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_11_k12_fwd : Entry := escEntry "esc-0700" (RNReps.q13.ifThen RNReps.q11) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_11_k13_fwd : Entry := escEntry "esc-0701" (RNReps.q13.ifThen RNReps.q11) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_11_k14_fwd : Entry := escEntry "esc-0702" (RNReps.q13.ifThen RNReps.q11) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_11_k15_fwd : Entry := escEntry "esc-0703" (RNReps.q13.ifThen RNReps.q11) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_13_14_k0_fwd : Entry := escEntry "esc-0704" (RNReps.q13.and RNReps.q14) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_13_14_k1_bwd : Entry := escEntry "esc-0705" (RNReps.q1) (RNReps.q13.and RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_13_14_k2_fwd : Entry := escEntry "esc-0706" (RNReps.q13.and RNReps.q14) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_13_14_k3_fwd : Entry := escEntry "esc-0707" (RNReps.q13.and RNReps.q14) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_13_14_k4_fwd : Entry := escEntry "esc-0708" (RNReps.q13.and RNReps.q14) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_13_14_k5_fwd : Entry := escEntry "esc-0709" (RNReps.q13.and RNReps.q14) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_13_14_k6_fwd : Entry := escEntry "esc-0710" (RNReps.q13.and RNReps.q14) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_13_14_k7_fwd : Entry := escEntry "esc-0711" (RNReps.q13.and RNReps.q14) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_13_14_k8_fwd : Entry := escEntry "esc-0712" (RNReps.q13.and RNReps.q14) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_13_14_k9_fwd : Entry := escEntry "esc-0713" (RNReps.q13.and RNReps.q14) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_13_14_k10_fwd : Entry := escEntry "esc-0714" (RNReps.q13.and RNReps.q14) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_13_14_k11_fwd : Entry := escEntry "esc-0715" (RNReps.q13.and RNReps.q14) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_13_14_k12_fwd : Entry := escEntry "esc-0716" (RNReps.q13.and RNReps.q14) (RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_13_14_k13_bwd : Entry := escEntry "esc-0717" (RNReps.q13) (RNReps.q13.and RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_13_14_k14_bwd : Entry := escEntry "esc-0718" (RNReps.q14) (RNReps.q13.and RNReps.q14) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cAnd_13_14_k15_fwd : Entry := escEntry "esc-0719" (RNReps.q13.and RNReps.q14) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_11_k0_fwd : Entry := escEntry "esc-0720" (RNReps.q11.somehow) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_11_k1_bwd : Entry := escEntry "esc-0721" (RNReps.q1) (RNReps.q11.somehow) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_11_k2_fwd : Entry := escEntry "esc-0722" (RNReps.q11.somehow) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_11_k3_fwd : Entry := escEntry "esc-0723" (RNReps.q11.somehow) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_11_k4_fwd : Entry := escEntry "esc-0724" (RNReps.q11.somehow) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_11_k5_fwd : Entry := escEntry "esc-0725" (RNReps.q11.somehow) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_11_k6_fwd : Entry := escEntry "esc-0726" (RNReps.q11.somehow) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_11_k7_fwd : Entry := escEntry "esc-0727" (RNReps.q11.somehow) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_11_k8_fwd : Entry := escEntry "esc-0728" (RNReps.q11.somehow) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_11_k9_fwd : Entry := escEntry "esc-0729" (RNReps.q11.somehow) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_11_k10_fwd : Entry := escEntry "esc-0730" (RNReps.q11.somehow) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_11_k11_fwd : Entry := escEntry "esc-0731" (RNReps.q11.somehow) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(0, 1), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_11_k12_fwd : Entry := escEntry "esc-0732" (RNReps.q11.somehow) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_11_k13_fwd : Entry := escEntry "esc-0733" (RNReps.q11.somehow) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_11_k14_fwd : Entry := escEntry "esc-0734" (RNReps.q11.somehow) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cBox_11_k15_fwd : Entry := escEntry "esc-0735" (RNReps.q11.somehow) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_7_k0_fwd : Entry := escEntry "esc-0736" (RNReps.q10.ifThen RNReps.q7) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_7_k1_bwd : Entry := escEntry "esc-0737" (RNReps.q1) (RNReps.q10.ifThen RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_7_k2_fwd : Entry := escEntry "esc-0738" (RNReps.q10.ifThen RNReps.q7) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_7_k3_fwd : Entry := escEntry "esc-0739" (RNReps.q10.ifThen RNReps.q7) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_7_k4_fwd : Entry := escEntry "esc-0740" (RNReps.q10.ifThen RNReps.q7) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_7_k5_fwd : Entry := escEntry "esc-0741" (RNReps.q10.ifThen RNReps.q7) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_7_k6_fwd : Entry := escEntry "esc-0742" (RNReps.q10.ifThen RNReps.q7) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_7_k7_fwd : Entry := escEntry "esc-0743" (RNReps.q10.ifThen RNReps.q7) (RNReps.q7) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_7_k8_bwd : Entry := escEntry "esc-0744" (RNReps.q8) (RNReps.q10.ifThen RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_7_k9_fwd : Entry := escEntry "esc-0745" (RNReps.q10.ifThen RNReps.q7) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_7_k10_fwd : Entry := escEntry "esc-0746" (RNReps.q10.ifThen RNReps.q7) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_7_k11_fwd : Entry := escEntry "esc-0747" (RNReps.q10.ifThen RNReps.q7) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_7_k12_fwd : Entry := escEntry "esc-0748" (RNReps.q10.ifThen RNReps.q7) (RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_7_k13_bwd : Entry := escEntry "esc-0749" (RNReps.q13) (RNReps.q10.ifThen RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_7_k14_bwd : Entry := escEntry "esc-0750" (RNReps.q14) (RNReps.q10.ifThen RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_10_7_k15_fwd : Entry := escEntry "esc-0751" (RNReps.q10.ifThen RNReps.q7) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_7_k0_fwd : Entry := escEntry "esc-0752" (RNReps.q12.ifThen RNReps.q7) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_7_k1_bwd : Entry := escEntry "esc-0753" (RNReps.q1) (RNReps.q12.ifThen RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_7_k2_fwd : Entry := escEntry "esc-0754" (RNReps.q12.ifThen RNReps.q7) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_7_k3_fwd : Entry := escEntry "esc-0755" (RNReps.q12.ifThen RNReps.q7) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_7_k4_fwd : Entry := escEntry "esc-0756" (RNReps.q12.ifThen RNReps.q7) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_7_k5_fwd : Entry := escEntry "esc-0757" (RNReps.q12.ifThen RNReps.q7) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_7_k6_fwd : Entry := escEntry "esc-0758" (RNReps.q12.ifThen RNReps.q7) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_7_k7_fwd : Entry := escEntry "esc-0759" (RNReps.q12.ifThen RNReps.q7) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_7_k8_bwd : Entry := escEntry "esc-0760" (RNReps.q8) (RNReps.q12.ifThen RNReps.q7) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(0, 1), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_7_k9_fwd : Entry := escEntry "esc-0761" (RNReps.q12.ifThen RNReps.q7) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_7_k10_fwd : Entry := escEntry "esc-0762" (RNReps.q12.ifThen RNReps.q7) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_7_k11_fwd : Entry := escEntry "esc-0763" (RNReps.q12.ifThen RNReps.q7) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_7_k12_fwd : Entry := escEntry "esc-0764" (RNReps.q12.ifThen RNReps.q7) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_7_k13_bwd : Entry := escEntry "esc-0765" (RNReps.q13) (RNReps.q12.ifThen RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_7_k14_fwd : Entry := escEntry "esc-0766" (RNReps.q12.ifThen RNReps.q7) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_12_7_k15_fwd : Entry := escEntry "esc-0767" (RNReps.q12.ifThen RNReps.q7) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_5_k0_fwd : Entry := escEntry "esc-0768" (RNReps.q13.ifThen RNReps.q5) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_5_k1_bwd : Entry := escEntry "esc-0769" (RNReps.q1) (RNReps.q13.ifThen RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_5_k2_fwd : Entry := escEntry "esc-0770" (RNReps.q13.ifThen RNReps.q5) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_5_k3_fwd : Entry := escEntry "esc-0771" (RNReps.q13.ifThen RNReps.q5) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_5_k4_fwd : Entry := escEntry "esc-0772" (RNReps.q13.ifThen RNReps.q5) (RNReps.q4) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_5_k5_fwd : Entry := escEntry "esc-0773" (RNReps.q13.ifThen RNReps.q5) (RNReps.q5) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_5_k6_fwd : Entry := escEntry "esc-0774" (RNReps.q13.ifThen RNReps.q5) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_5_k7_fwd : Entry := escEntry "esc-0775" (RNReps.q13.ifThen RNReps.q5) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_5_k8_fwd : Entry := escEntry "esc-0776" (RNReps.q13.ifThen RNReps.q5) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_5_k9_fwd : Entry := escEntry "esc-0777" (RNReps.q13.ifThen RNReps.q5) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_5_k10_bwd : Entry := escEntry "esc-0778" (RNReps.q10) (RNReps.q13.ifThen RNReps.q5) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_5_k11_bwd : Entry := escEntry "esc-0779" (RNReps.q11) (RNReps.q13.ifThen RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_5_k12_fwd : Entry := escEntry "esc-0780" (RNReps.q13.ifThen RNReps.q5) (RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_5_k13_fwd : Entry := escEntry "esc-0781" (RNReps.q13.ifThen RNReps.q5) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_5_k14_fwd : Entry := escEntry "esc-0782" (RNReps.q13.ifThen RNReps.q5) (RNReps.q14) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_13_5_k15_fwd : Entry := escEntry "esc-0783" (RNReps.q13.ifThen RNReps.q5) (RNReps.q15) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_13_k0_fwd : Entry := escEntry "esc-0784" (RNReps.q14.ifThen RNReps.q13) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_13_k1_bwd : Entry := escEntry "esc-0785" (RNReps.q1) (RNReps.q14.ifThen RNReps.q13) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_13_k2_fwd : Entry := escEntry "esc-0786" (RNReps.q14.ifThen RNReps.q13) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_13_k3_fwd : Entry := escEntry "esc-0787" (RNReps.q14.ifThen RNReps.q13) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_13_k4_fwd : Entry := escEntry "esc-0788" (RNReps.q14.ifThen RNReps.q13) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_13_k5_fwd : Entry := escEntry "esc-0789" (RNReps.q14.ifThen RNReps.q13) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_13_k6_fwd : Entry := escEntry "esc-0790" (RNReps.q14.ifThen RNReps.q13) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_13_k7_fwd : Entry := escEntry "esc-0791" (RNReps.q14.ifThen RNReps.q13) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_13_k8_fwd : Entry := escEntry "esc-0792" (RNReps.q14.ifThen RNReps.q13) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_13_k9_fwd : Entry := escEntry "esc-0793" (RNReps.q14.ifThen RNReps.q13) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_13_k10_fwd : Entry := escEntry "esc-0794" (RNReps.q14.ifThen RNReps.q13) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_13_k11_fwd : Entry := escEntry "esc-0795" (RNReps.q14.ifThen RNReps.q13) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_13_k12_fwd : Entry := escEntry "esc-0796" (RNReps.q14.ifThen RNReps.q13) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_13_k13_fwd : Entry := escEntry "esc-0797" (RNReps.q14.ifThen RNReps.q13) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_13_k14_fwd : Entry := escEntry "esc-0798" (RNReps.q14.ifThen RNReps.q13) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_14_13_k15_fwd : Entry := escEntry "esc-0799" (RNReps.q14.ifThen RNReps.q13) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_14_k0_fwd : Entry := escEntry "esc-0800" (RNReps.q15.ifThen RNReps.q14) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_14_k1_bwd : Entry := escEntry "esc-0801" (RNReps.q1) (RNReps.q15.ifThen RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_14_k2_fwd : Entry := escEntry "esc-0802" (RNReps.q15.ifThen RNReps.q14) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_14_k3_fwd : Entry := escEntry "esc-0803" (RNReps.q15.ifThen RNReps.q14) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_14_k4_fwd : Entry := escEntry "esc-0804" (RNReps.q15.ifThen RNReps.q14) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_14_k5_fwd : Entry := escEntry "esc-0805" (RNReps.q15.ifThen RNReps.q14) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_14_k6_fwd : Entry := escEntry "esc-0806" (RNReps.q15.ifThen RNReps.q14) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_14_k7_fwd : Entry := escEntry "esc-0807" (RNReps.q15.ifThen RNReps.q14) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_14_k8_fwd : Entry := escEntry "esc-0808" (RNReps.q15.ifThen RNReps.q14) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_14_k9_fwd : Entry := escEntry "esc-0809" (RNReps.q15.ifThen RNReps.q14) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_14_k10_fwd : Entry := escEntry "esc-0810" (RNReps.q15.ifThen RNReps.q14) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_14_k11_fwd : Entry := escEntry "esc-0811" (RNReps.q15.ifThen RNReps.q14) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_14_k12_fwd : Entry := escEntry "esc-0812" (RNReps.q15.ifThen RNReps.q14) (RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_14_k13_fwd : Entry := escEntry "esc-0813" (RNReps.q15.ifThen RNReps.q14) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_14_k14_fwd : Entry := escEntry "esc-0814" (RNReps.q15.ifThen RNReps.q14) (RNReps.q14) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_14_k15_fwd : Entry := escEntry "esc-0815" (RNReps.q15.ifThen RNReps.q14) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_9_k0_fwd : Entry := escEntry "esc-0816" (RNReps.q15.ifThen RNReps.q9) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_9_k1_bwd : Entry := escEntry "esc-0817" (RNReps.q1) (RNReps.q15.ifThen RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_9_k2_fwd : Entry := escEntry "esc-0818" (RNReps.q15.ifThen RNReps.q9) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_9_k3_fwd : Entry := escEntry "esc-0819" (RNReps.q15.ifThen RNReps.q9) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_9_k4_fwd : Entry := escEntry "esc-0820" (RNReps.q15.ifThen RNReps.q9) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_9_k5_fwd : Entry := escEntry "esc-0821" (RNReps.q15.ifThen RNReps.q9) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_9_k6_fwd : Entry := escEntry "esc-0822" (RNReps.q15.ifThen RNReps.q9) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_9_k7_fwd : Entry := escEntry "esc-0823" (RNReps.q15.ifThen RNReps.q9) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_9_k8_fwd : Entry := escEntry "esc-0824" (RNReps.q15.ifThen RNReps.q9) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_9_k9_fwd : Entry := escEntry "esc-0825" (RNReps.q15.ifThen RNReps.q9) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_9_k10_fwd : Entry := escEntry "esc-0826" (RNReps.q15.ifThen RNReps.q9) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_9_k11_fwd : Entry := escEntry "esc-0827" (RNReps.q15.ifThen RNReps.q9) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_9_k12_fwd : Entry := escEntry "esc-0828" (RNReps.q15.ifThen RNReps.q9) (RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_9_k13_fwd : Entry := escEntry "esc-0829" (RNReps.q15.ifThen RNReps.q9) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_9_k14_fwd : Entry := escEntry "esc-0830" (RNReps.q15.ifThen RNReps.q9) (RNReps.q14) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_15_9_k15_fwd : Entry := escEntry "esc-0831" (RNReps.q15.ifThen RNReps.q9) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_4_k0_fwd : Entry := escEntry "esc-0832" (RNReps.q8.ifThen RNReps.q4) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_4_k1_bwd : Entry := escEntry "esc-0833" (RNReps.q1) (RNReps.q8.ifThen RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_4_k2_fwd : Entry := escEntry "esc-0834" (RNReps.q8.ifThen RNReps.q4) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_4_k3_fwd : Entry := escEntry "esc-0835" (RNReps.q8.ifThen RNReps.q4) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_4_k4_fwd : Entry := escEntry "esc-0836" (RNReps.q8.ifThen RNReps.q4) (RNReps.q4) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_4_k5_fwd : Entry := escEntry "esc-0837" (RNReps.q8.ifThen RNReps.q4) (RNReps.q5) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_4_k6_fwd : Entry := escEntry "esc-0838" (RNReps.q8.ifThen RNReps.q4) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_4_k7_fwd : Entry := escEntry "esc-0839" (RNReps.q8.ifThen RNReps.q4) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_4_k8_fwd : Entry := escEntry "esc-0840" (RNReps.q8.ifThen RNReps.q4) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_4_k9_fwd : Entry := escEntry "esc-0841" (RNReps.q8.ifThen RNReps.q4) (RNReps.q9) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_4_k10_bwd : Entry := escEntry "esc-0842" (RNReps.q10) (RNReps.q8.ifThen RNReps.q4) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_4_k11_bwd : Entry := escEntry "esc-0843" (RNReps.q11) (RNReps.q8.ifThen RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_4_k12_fwd : Entry := escEntry "esc-0844" (RNReps.q8.ifThen RNReps.q4) (RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_4_k13_fwd : Entry := escEntry "esc-0845" (RNReps.q8.ifThen RNReps.q4) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_4_k14_fwd : Entry := escEntry "esc-0846" (RNReps.q8.ifThen RNReps.q4) (RNReps.q14) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cImp_8_4_k15_fwd : Entry := escEntry "esc-0847" (RNReps.q8.ifThen RNReps.q4) (RNReps.q15) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_12_k0_fwd : Entry := escEntry "esc-0848" (RNReps.q10.or RNReps.q12) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_12_k1_bwd : Entry := escEntry "esc-0849" (RNReps.q1) (RNReps.q10.or RNReps.q12) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_12_k2_fwd : Entry := escEntry "esc-0850" (RNReps.q10.or RNReps.q12) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_12_k3_fwd : Entry := escEntry "esc-0851" (RNReps.q10.or RNReps.q12) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_12_k4_fwd : Entry := escEntry "esc-0852" (RNReps.q10.or RNReps.q12) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_12_k5_fwd : Entry := escEntry "esc-0853" (RNReps.q10.or RNReps.q12) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_12_k6_fwd : Entry := escEntry "esc-0854" (RNReps.q10.or RNReps.q12) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_12_k7_fwd : Entry := escEntry "esc-0855" (RNReps.q10.or RNReps.q12) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_12_k8_fwd : Entry := escEntry "esc-0856" (RNReps.q10.or RNReps.q12) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_12_k9_fwd : Entry := escEntry "esc-0857" (RNReps.q10.or RNReps.q12) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_12_k10_fwd : Entry := escEntry "esc-0858" (RNReps.q10.or RNReps.q12) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_12_k11_fwd : Entry := escEntry "esc-0859" (RNReps.q10.or RNReps.q12) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(0, 1), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_12_k12_fwd : Entry := escEntry "esc-0860" (RNReps.q10.or RNReps.q12) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_12_k13_fwd : Entry := escEntry "esc-0861" (RNReps.q10.or RNReps.q12) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_12_k14_fwd : Entry := escEntry "esc-0862" (RNReps.q10.or RNReps.q12) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_10_12_k15_fwd : Entry := escEntry "esc-0863" (RNReps.q10.or RNReps.q12) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_13_k0_fwd : Entry := escEntry "esc-0864" (RNReps.q11.or RNReps.q13) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_13_k1_bwd : Entry := escEntry "esc-0865" (RNReps.q1) (RNReps.q11.or RNReps.q13) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_13_k2_fwd : Entry := escEntry "esc-0866" (RNReps.q11.or RNReps.q13) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_13_k3_fwd : Entry := escEntry "esc-0867" (RNReps.q11.or RNReps.q13) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_13_k4_fwd : Entry := escEntry "esc-0868" (RNReps.q11.or RNReps.q13) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_13_k5_fwd : Entry := escEntry "esc-0869" (RNReps.q11.or RNReps.q13) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_13_k6_fwd : Entry := escEntry "esc-0870" (RNReps.q11.or RNReps.q13) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_13_k7_fwd : Entry := escEntry "esc-0871" (RNReps.q11.or RNReps.q13) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_13_k8_fwd : Entry := escEntry "esc-0872" (RNReps.q11.or RNReps.q13) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_13_k9_fwd : Entry := escEntry "esc-0873" (RNReps.q11.or RNReps.q13) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_13_k10_fwd : Entry := escEntry "esc-0874" (RNReps.q11.or RNReps.q13) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_13_k11_fwd : Entry := escEntry "esc-0875" (RNReps.q11.or RNReps.q13) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_13_k12_fwd : Entry := escEntry "esc-0876" (RNReps.q11.or RNReps.q13) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_13_k13_fwd : Entry := escEntry "esc-0877" (RNReps.q11.or RNReps.q13) (RNReps.q13) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_13_k14_fwd : Entry := escEntry "esc-0878" (RNReps.q11.or RNReps.q13) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_11_13_k15_fwd : Entry := escEntry "esc-0879" (RNReps.q11.or RNReps.q13) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_14_15_k0_fwd : Entry := escEntry "esc-0880" (RNReps.q14.or RNReps.q15) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_14_15_k1_bwd : Entry := escEntry "esc-0881" (RNReps.q1) (RNReps.q14.or RNReps.q15) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_14_15_k2_fwd : Entry := escEntry "esc-0882" (RNReps.q14.or RNReps.q15) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_14_15_k3_fwd : Entry := escEntry "esc-0883" (RNReps.q14.or RNReps.q15) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_14_15_k4_fwd : Entry := escEntry "esc-0884" (RNReps.q14.or RNReps.q15) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_14_15_k5_fwd : Entry := escEntry "esc-0885" (RNReps.q14.or RNReps.q15) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_14_15_k6_fwd : Entry := escEntry "esc-0886" (RNReps.q14.or RNReps.q15) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_14_15_k7_fwd : Entry := escEntry "esc-0887" (RNReps.q14.or RNReps.q15) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_14_15_k8_fwd : Entry := escEntry "esc-0888" (RNReps.q14.or RNReps.q15) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_14_15_k9_fwd : Entry := escEntry "esc-0889" (RNReps.q14.or RNReps.q15) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_14_15_k10_fwd : Entry := escEntry "esc-0890" (RNReps.q14.or RNReps.q15) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_14_15_k11_fwd : Entry := escEntry "esc-0891" (RNReps.q14.or RNReps.q15) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_14_15_k12_fwd : Entry := escEntry "esc-0892" (RNReps.q14.or RNReps.q15) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_14_15_k13_fwd : Entry := escEntry "esc-0893" (RNReps.q14.or RNReps.q15) (RNReps.q13) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_14_15_k14_fwd : Entry := escEntry "esc-0894" (RNReps.q14.or RNReps.q15) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_14_15_k15_fwd : Entry := escEntry "esc-0895" (RNReps.q14.or RNReps.q15) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_7_15_k0_fwd : Entry := escEntry "esc-0896" (RNReps.q7.or RNReps.q15) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_7_15_k1_bwd : Entry := escEntry "esc-0897" (RNReps.q1) (RNReps.q7.or RNReps.q15) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_7_15_k2_fwd : Entry := escEntry "esc-0898" (RNReps.q7.or RNReps.q15) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_7_15_k3_fwd : Entry := escEntry "esc-0899" (RNReps.q7.or RNReps.q15) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_7_15_k4_fwd : Entry := escEntry "esc-0900" (RNReps.q7.or RNReps.q15) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_7_15_k5_fwd : Entry := escEntry "esc-0901" (RNReps.q7.or RNReps.q15) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_7_15_k6_fwd : Entry := escEntry "esc-0902" (RNReps.q7.or RNReps.q15) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_7_15_k7_fwd : Entry := escEntry "esc-0903" (RNReps.q7.or RNReps.q15) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_7_15_k8_bwd : Entry := escEntry "esc-0904" (RNReps.q8) (RNReps.q7.or RNReps.q15) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_7_15_k9_fwd : Entry := escEntry "esc-0905" (RNReps.q7.or RNReps.q15) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_7_15_k10_fwd : Entry := escEntry "esc-0906" (RNReps.q7.or RNReps.q15) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_7_15_k11_bwd : Entry := escEntry "esc-0907" (RNReps.q11) (RNReps.q7.or RNReps.q15) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_7_15_k12_fwd : Entry := escEntry "esc-0908" (RNReps.q7.or RNReps.q15) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_7_15_k13_bwd : Entry := escEntry "esc-0909" (RNReps.q13) (RNReps.q7.or RNReps.q15) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_7_15_k14_fwd : Entry := escEntry "esc-0910" (RNReps.q7.or RNReps.q15) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_7_15_k15_fwd : Entry := escEntry "esc-0911" (RNReps.q7.or RNReps.q15) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_14_k0_fwd : Entry := escEntry "esc-0912" (RNReps.q8.or RNReps.q14) (RNReps.q0) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_14_k1_bwd : Entry := escEntry "esc-0913" (RNReps.q1) (RNReps.q8.or RNReps.q14) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3)], [(1, 3), (2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_14_k2_fwd : Entry := escEntry "esc-0914" (RNReps.q8.or RNReps.q14) (RNReps.q2) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_14_k3_fwd : Entry := escEntry "esc-0915" (RNReps.q8.or RNReps.q14) (RNReps.q3) 2 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_14_k4_fwd : Entry := escEntry "esc-0916" (RNReps.q8.or RNReps.q14) (RNReps.q4) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_14_k5_fwd : Entry := escEntry "esc-0917" (RNReps.q8.or RNReps.q14) (RNReps.q5) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_14_k6_fwd : Entry := escEntry "esc-0918" (RNReps.q8.or RNReps.q14) (RNReps.q6) 1 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨1, [], [], [], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_14_k7_fwd : Entry := escEntry "esc-0919" (RNReps.q8.or RNReps.q14) (RNReps.q7) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_14_k8_fwd : Entry := escEntry "esc-0920" (RNReps.q8.or RNReps.q14) (RNReps.q8) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (0, 3), (1, 2)], [(0, 2), (1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_14_k9_fwd : Entry := escEntry "esc-0921" (RNReps.q8.or RNReps.q14) (RNReps.q9) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_14_k10_fwd : Entry := escEntry "esc-0922" (RNReps.q8.or RNReps.q14) (RNReps.q10) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_14_k11_fwd : Entry := escEntry "esc-0923" (RNReps.q8.or RNReps.q14) (RNReps.q11) 5 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (2, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_14_k12_fwd : Entry := escEntry "esc-0924" (RNReps.q8.or RNReps.q14) (RNReps.q12) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_14_k13_fwd : Entry := escEntry "esc-0925" (RNReps.q8.or RNReps.q14) (RNReps.q13) 6 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨6, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (3, 4)], [(1, 4), (3, 4)], [4], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_14_k14_fwd : Entry := escEntry "esc-0926" (RNReps.q8.or RNReps.q14) (RNReps.q14) 4 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨4, [(0, 1), (0, 2), (2, 3), (0, 3)], [(2, 3)], [3], []⟩) (w := 0) (by decide) hd)
def r2e_cOr_8_14_k15_fwd : Entry := escEntry "esc-0927" (RNReps.q8.or RNReps.q14) (RNReps.q15) 3 (by decide)
  (fun hd => FinCM.not_provable_of_check (M := ⟨3, [(0, 1), (1, 2), (0, 2)], [(1, 2)], [2], []⟩) (w := 0) (by decide) hd)

def escEntries : List Entry :=
  [ r2e_cAnd_8_11_k0_fwd,
    r2e_cAnd_8_11_k1_bwd,
    r2e_cAnd_8_11_k2_fwd,
    r2e_cAnd_8_11_k3_fwd,
    r2e_cAnd_8_11_k4_fwd,
    r2e_cAnd_8_11_k5_fwd,
    r2e_cAnd_8_11_k6_fwd,
    r2e_cAnd_8_11_k7_fwd,
    r2e_cAnd_8_11_k8_bwd,
    r2e_cAnd_8_11_k9_fwd,
    r2e_cAnd_8_11_k10_fwd,
    r2e_cAnd_8_11_k11_bwd,
    r2e_cAnd_8_11_k12_fwd,
    r2e_cAnd_8_11_k13_bwd,
    r2e_cAnd_8_11_k14_fwd,
    r2e_cAnd_8_11_k15_fwd,
    r2e_cBox_15_k0_fwd,
    r2e_cBox_15_k1_bwd,
    r2e_cBox_15_k2_fwd,
    r2e_cBox_15_k3_fwd,
    r2e_cBox_15_k4_fwd,
    r2e_cBox_15_k5_fwd,
    r2e_cBox_15_k6_fwd,
    r2e_cBox_15_k7_fwd,
    r2e_cBox_15_k8_fwd,
    r2e_cBox_15_k9_fwd,
    r2e_cBox_15_k10_bwd,
    r2e_cBox_15_k11_bwd,
    r2e_cBox_15_k12_fwd,
    r2e_cBox_15_k13_bwd,
    r2e_cBox_15_k14_fwd,
    r2e_cBox_15_k15_fwd,
    r2e_cImp_11_13_k0_fwd,
    r2e_cImp_11_13_k1_bwd,
    r2e_cImp_11_13_k2_fwd,
    r2e_cImp_11_13_k3_fwd,
    r2e_cImp_11_13_k4_fwd,
    r2e_cImp_11_13_k5_fwd,
    r2e_cImp_11_13_k6_fwd,
    r2e_cImp_11_13_k7_fwd,
    r2e_cImp_11_13_k8_fwd,
    r2e_cImp_11_13_k9_fwd,
    r2e_cImp_11_13_k10_fwd,
    r2e_cImp_11_13_k11_fwd,
    r2e_cImp_11_13_k12_fwd,
    r2e_cImp_11_13_k13_fwd,
    r2e_cImp_11_13_k14_fwd,
    r2e_cImp_11_13_k15_fwd,
    r2e_cImp_12_9_k0_fwd,
    r2e_cImp_12_9_k1_bwd,
    r2e_cImp_12_9_k2_fwd,
    r2e_cImp_12_9_k3_fwd,
    r2e_cImp_12_9_k4_fwd,
    r2e_cImp_12_9_k5_fwd,
    r2e_cImp_12_9_k6_fwd,
    r2e_cImp_12_9_k7_fwd,
    r2e_cImp_12_9_k8_fwd,
    r2e_cImp_12_9_k9_fwd,
    r2e_cImp_12_9_k10_fwd,
    r2e_cImp_12_9_k11_fwd,
    r2e_cImp_12_9_k12_fwd,
    r2e_cImp_12_9_k13_fwd,
    r2e_cImp_12_9_k14_fwd,
    r2e_cImp_12_9_k15_fwd,
    r2e_cImp_13_9_k0_fwd,
    r2e_cImp_13_9_k1_bwd,
    r2e_cImp_13_9_k2_fwd,
    r2e_cImp_13_9_k3_fwd,
    r2e_cImp_13_9_k4_fwd,
    r2e_cImp_13_9_k5_fwd,
    r2e_cImp_13_9_k6_fwd,
    r2e_cImp_13_9_k7_fwd,
    r2e_cImp_13_9_k8_fwd,
    r2e_cImp_13_9_k9_fwd,
    r2e_cImp_13_9_k10_fwd,
    r2e_cImp_13_9_k11_fwd,
    r2e_cImp_13_9_k12_fwd,
    r2e_cImp_13_9_k13_fwd,
    r2e_cImp_13_9_k14_fwd,
    r2e_cImp_13_9_k15_fwd,
    r2e_cImp_14_7_k0_fwd,
    r2e_cImp_14_7_k1_bwd,
    r2e_cImp_14_7_k2_fwd,
    r2e_cImp_14_7_k3_fwd,
    r2e_cImp_14_7_k4_fwd,
    r2e_cImp_14_7_k5_fwd,
    r2e_cImp_14_7_k6_fwd,
    r2e_cImp_14_7_k7_fwd,
    r2e_cImp_14_7_k8_bwd,
    r2e_cImp_14_7_k9_fwd,
    r2e_cImp_14_7_k10_fwd,
    r2e_cImp_14_7_k11_fwd,
    r2e_cImp_14_7_k12_fwd,
    r2e_cImp_14_7_k13_bwd,
    r2e_cImp_14_7_k14_fwd,
    r2e_cImp_14_7_k15_fwd,
    r2e_cImp_15_4_k0_fwd,
    r2e_cImp_15_4_k1_bwd,
    r2e_cImp_15_4_k2_fwd,
    r2e_cImp_15_4_k3_fwd,
    r2e_cImp_15_4_k4_fwd,
    r2e_cImp_15_4_k5_fwd,
    r2e_cImp_15_4_k6_fwd,
    r2e_cImp_15_4_k7_fwd,
    r2e_cImp_15_4_k8_fwd,
    r2e_cImp_15_4_k9_fwd,
    r2e_cImp_15_4_k10_fwd,
    r2e_cImp_15_4_k11_fwd,
    r2e_cImp_15_4_k12_fwd,
    r2e_cImp_15_4_k13_fwd,
    r2e_cImp_15_4_k14_fwd,
    r2e_cImp_15_4_k15_fwd,
    r2e_cImp_8_11_k0_fwd,
    r2e_cImp_8_11_k1_bwd,
    r2e_cImp_8_11_k2_fwd,
    r2e_cImp_8_11_k3_fwd,
    r2e_cImp_8_11_k4_fwd,
    r2e_cImp_8_11_k5_fwd,
    r2e_cImp_8_11_k6_fwd,
    r2e_cImp_8_11_k7_fwd,
    r2e_cImp_8_11_k8_fwd,
    r2e_cImp_8_11_k9_fwd,
    r2e_cImp_8_11_k10_fwd,
    r2e_cImp_8_11_k11_fwd,
    r2e_cImp_8_11_k12_fwd,
    r2e_cImp_8_11_k13_fwd,
    r2e_cImp_8_11_k14_fwd,
    r2e_cImp_8_11_k15_fwd,
    r2e_cImp_8_5_k0_fwd,
    r2e_cImp_8_5_k1_bwd,
    r2e_cImp_8_5_k2_fwd,
    r2e_cImp_8_5_k3_fwd,
    r2e_cImp_8_5_k4_fwd,
    r2e_cImp_8_5_k5_fwd,
    r2e_cImp_8_5_k6_fwd,
    r2e_cImp_8_5_k7_fwd,
    r2e_cImp_8_5_k8_fwd,
    r2e_cImp_8_5_k9_fwd,
    r2e_cImp_8_5_k10_bwd,
    r2e_cImp_8_5_k11_bwd,
    r2e_cImp_8_5_k12_fwd,
    r2e_cImp_8_5_k13_fwd,
    r2e_cImp_8_5_k14_fwd,
    r2e_cImp_8_5_k15_fwd,
    r2e_cOr_10_13_k0_fwd,
    r2e_cOr_10_13_k1_bwd,
    r2e_cOr_10_13_k2_fwd,
    r2e_cOr_10_13_k3_fwd,
    r2e_cOr_10_13_k4_fwd,
    r2e_cOr_10_13_k5_fwd,
    r2e_cOr_10_13_k6_fwd,
    r2e_cOr_10_13_k7_fwd,
    r2e_cOr_10_13_k8_fwd,
    r2e_cOr_10_13_k9_fwd,
    r2e_cOr_10_13_k10_fwd,
    r2e_cOr_10_13_k11_fwd,
    r2e_cOr_10_13_k12_fwd,
    r2e_cOr_10_13_k13_fwd,
    r2e_cOr_10_13_k14_fwd,
    r2e_cOr_10_13_k15_fwd,
    r2e_cOr_11_14_k0_fwd,
    r2e_cOr_11_14_k1_bwd,
    r2e_cOr_11_14_k2_fwd,
    r2e_cOr_11_14_k3_fwd,
    r2e_cOr_11_14_k4_fwd,
    r2e_cOr_11_14_k5_fwd,
    r2e_cOr_11_14_k6_fwd,
    r2e_cOr_11_14_k7_fwd,
    r2e_cOr_11_14_k8_fwd,
    r2e_cOr_11_14_k9_fwd,
    r2e_cOr_11_14_k10_fwd,
    r2e_cOr_11_14_k11_fwd,
    r2e_cOr_11_14_k12_fwd,
    r2e_cOr_11_14_k13_fwd,
    r2e_cOr_11_14_k14_fwd,
    r2e_cOr_11_14_k15_fwd,
    r2e_cOr_5_15_k0_fwd,
    r2e_cOr_5_15_k1_bwd,
    r2e_cOr_5_15_k2_fwd,
    r2e_cOr_5_15_k3_fwd,
    r2e_cOr_5_15_k4_fwd,
    r2e_cOr_5_15_k5_fwd,
    r2e_cOr_5_15_k6_fwd,
    r2e_cOr_5_15_k7_fwd,
    r2e_cOr_5_15_k8_fwd,
    r2e_cOr_5_15_k9_fwd,
    r2e_cOr_5_15_k10_bwd,
    r2e_cOr_5_15_k11_bwd,
    r2e_cOr_5_15_k12_fwd,
    r2e_cOr_5_15_k13_bwd,
    r2e_cOr_5_15_k14_fwd,
    r2e_cOr_5_15_k15_fwd,
    r2e_cOr_8_10_k0_fwd,
    r2e_cOr_8_10_k1_bwd,
    r2e_cOr_8_10_k2_fwd,
    r2e_cOr_8_10_k3_fwd,
    r2e_cOr_8_10_k4_fwd,
    r2e_cOr_8_10_k5_fwd,
    r2e_cOr_8_10_k6_fwd,
    r2e_cOr_8_10_k7_fwd,
    r2e_cOr_8_10_k8_fwd,
    r2e_cOr_8_10_k9_fwd,
    r2e_cOr_8_10_k10_fwd,
    r2e_cOr_8_10_k11_fwd,
    r2e_cOr_8_10_k12_fwd,
    r2e_cOr_8_10_k13_fwd,
    r2e_cOr_8_10_k14_fwd,
    r2e_cOr_8_10_k15_fwd,
    r2e_cOr_8_9_k0_fwd,
    r2e_cOr_8_9_k1_bwd,
    r2e_cOr_8_9_k2_fwd,
    r2e_cOr_8_9_k3_fwd,
    r2e_cOr_8_9_k4_fwd,
    r2e_cOr_8_9_k5_fwd,
    r2e_cOr_8_9_k6_fwd,
    r2e_cOr_8_9_k7_fwd,
    r2e_cOr_8_9_k8_fwd,
    r2e_cOr_8_9_k9_fwd,
    r2e_cOr_8_9_k10_fwd,
    r2e_cOr_8_9_k11_fwd,
    r2e_cOr_8_9_k12_fwd,
    r2e_cOr_8_9_k13_bwd,
    r2e_cOr_8_9_k14_fwd,
    r2e_cOr_8_9_k15_fwd,
    r2e_cAnd_10_13_k0_fwd,
    r2e_cAnd_10_13_k1_bwd,
    r2e_cAnd_10_13_k2_fwd,
    r2e_cAnd_10_13_k3_fwd,
    r2e_cAnd_10_13_k4_fwd,
    r2e_cAnd_10_13_k5_fwd,
    r2e_cAnd_10_13_k6_fwd,
    r2e_cAnd_10_13_k7_fwd,
    r2e_cAnd_10_13_k8_fwd,
    r2e_cAnd_10_13_k9_fwd,
    r2e_cAnd_10_13_k10_bwd,
    r2e_cAnd_10_13_k11_bwd,
    r2e_cAnd_10_13_k12_fwd,
    r2e_cAnd_10_13_k13_bwd,
    r2e_cAnd_10_13_k14_fwd,
    r2e_cAnd_10_13_k15_fwd,
    r2e_cAnd_8_12_k0_fwd,
    r2e_cAnd_8_12_k1_bwd,
    r2e_cAnd_8_12_k2_fwd,
    r2e_cAnd_8_12_k3_fwd,
    r2e_cAnd_8_12_k4_fwd,
    r2e_cAnd_8_12_k5_fwd,
    r2e_cAnd_8_12_k6_fwd,
    r2e_cAnd_8_12_k7_fwd,
    r2e_cAnd_8_12_k8_bwd,
    r2e_cAnd_8_12_k9_fwd,
    r2e_cAnd_8_12_k10_fwd,
    r2e_cAnd_8_12_k11_fwd,
    r2e_cAnd_8_12_k12_bwd,
    r2e_cAnd_8_12_k13_bwd,
    r2e_cAnd_8_12_k14_bwd,
    r2e_cAnd_8_12_k15_fwd,
    r2e_cImp_10_13_k0_fwd,
    r2e_cImp_10_13_k1_bwd,
    r2e_cImp_10_13_k2_fwd,
    r2e_cImp_10_13_k3_fwd,
    r2e_cImp_10_13_k4_fwd,
    r2e_cImp_10_13_k5_fwd,
    r2e_cImp_10_13_k6_fwd,
    r2e_cImp_10_13_k7_fwd,
    r2e_cImp_10_13_k8_fwd,
    r2e_cImp_10_13_k9_fwd,
    r2e_cImp_10_13_k10_fwd,
    r2e_cImp_10_13_k11_fwd,
    r2e_cImp_10_13_k12_fwd,
    r2e_cImp_10_13_k13_fwd,
    r2e_cImp_10_13_k14_fwd,
    r2e_cImp_10_13_k15_fwd,
    r2e_cImp_11_7_k0_fwd,
    r2e_cImp_11_7_k1_bwd,
    r2e_cImp_11_7_k2_fwd,
    r2e_cImp_11_7_k3_fwd,
    r2e_cImp_11_7_k4_fwd,
    r2e_cImp_11_7_k5_fwd,
    r2e_cImp_11_7_k6_fwd,
    r2e_cImp_11_7_k7_fwd,
    r2e_cImp_11_7_k8_bwd,
    r2e_cImp_11_7_k9_fwd,
    r2e_cImp_11_7_k10_fwd,
    r2e_cImp_11_7_k11_fwd,
    r2e_cImp_11_7_k12_fwd,
    r2e_cImp_11_7_k13_bwd,
    r2e_cImp_11_7_k14_bwd,
    r2e_cImp_11_7_k15_fwd,
    r2e_cImp_13_12_k0_fwd,
    r2e_cImp_13_12_k1_bwd,
    r2e_cImp_13_12_k2_fwd,
    r2e_cImp_13_12_k3_fwd,
    r2e_cImp_13_12_k4_fwd,
    r2e_cImp_13_12_k5_fwd,
    r2e_cImp_13_12_k6_fwd,
    r2e_cImp_13_12_k7_fwd,
    r2e_cImp_13_12_k8_fwd,
    r2e_cImp_13_12_k9_fwd,
    r2e_cImp_13_12_k10_fwd,
    r2e_cImp_13_12_k11_fwd,
    r2e_cImp_13_12_k12_fwd,
    r2e_cImp_13_12_k13_fwd,
    r2e_cImp_13_12_k14_fwd,
    r2e_cImp_13_12_k15_fwd,
    r2e_cImp_14_11_k0_fwd,
    r2e_cImp_14_11_k1_bwd,
    r2e_cImp_14_11_k2_fwd,
    r2e_cImp_14_11_k3_fwd,
    r2e_cImp_14_11_k4_fwd,
    r2e_cImp_14_11_k5_fwd,
    r2e_cImp_14_11_k6_fwd,
    r2e_cImp_14_11_k7_fwd,
    r2e_cImp_14_11_k8_fwd,
    r2e_cImp_14_11_k9_fwd,
    r2e_cImp_14_11_k10_fwd,
    r2e_cImp_14_11_k11_fwd,
    r2e_cImp_14_11_k12_fwd,
    r2e_cImp_14_11_k13_fwd,
    r2e_cImp_14_11_k14_fwd,
    r2e_cImp_14_11_k15_fwd,
    r2e_cImp_14_9_k0_fwd,
    r2e_cImp_14_9_k1_bwd,
    r2e_cImp_14_9_k2_fwd,
    r2e_cImp_14_9_k3_fwd,
    r2e_cImp_14_9_k4_fwd,
    r2e_cImp_14_9_k5_fwd,
    r2e_cImp_14_9_k6_fwd,
    r2e_cImp_14_9_k7_fwd,
    r2e_cImp_14_9_k8_fwd,
    r2e_cImp_14_9_k9_fwd,
    r2e_cImp_14_9_k10_fwd,
    r2e_cImp_14_9_k11_fwd,
    r2e_cImp_14_9_k12_fwd,
    r2e_cImp_14_9_k13_fwd,
    r2e_cImp_14_9_k14_fwd,
    r2e_cImp_14_9_k15_fwd,
    r2e_cImp_15_5_k0_fwd,
    r2e_cImp_15_5_k1_bwd,
    r2e_cImp_15_5_k2_fwd,
    r2e_cImp_15_5_k3_fwd,
    r2e_cImp_15_5_k4_fwd,
    r2e_cImp_15_5_k5_fwd,
    r2e_cImp_15_5_k6_fwd,
    r2e_cImp_15_5_k7_fwd,
    r2e_cImp_15_5_k8_fwd,
    r2e_cImp_15_5_k9_fwd,
    r2e_cImp_15_5_k10_fwd,
    r2e_cImp_15_5_k11_fwd,
    r2e_cImp_15_5_k12_fwd,
    r2e_cImp_15_5_k13_fwd,
    r2e_cImp_15_5_k14_fwd,
    r2e_cImp_15_5_k15_fwd,
    r2e_cImp_8_12_k0_fwd,
    r2e_cImp_8_12_k1_bwd,
    r2e_cImp_8_12_k2_fwd,
    r2e_cImp_8_12_k3_fwd,
    r2e_cImp_8_12_k4_fwd,
    r2e_cImp_8_12_k5_fwd,
    r2e_cImp_8_12_k6_fwd,
    r2e_cImp_8_12_k7_fwd,
    r2e_cImp_8_12_k8_fwd,
    r2e_cImp_8_12_k9_fwd,
    r2e_cImp_8_12_k10_fwd,
    r2e_cImp_8_12_k11_fwd,
    r2e_cImp_8_12_k12_fwd,
    r2e_cImp_8_12_k13_fwd,
    r2e_cImp_8_12_k14_fwd,
    r2e_cImp_8_12_k15_fwd,
    r2e_cImp_8_7_k0_fwd,
    r2e_cImp_8_7_k1_bwd,
    r2e_cImp_8_7_k2_fwd,
    r2e_cImp_8_7_k3_fwd,
    r2e_cImp_8_7_k4_fwd,
    r2e_cImp_8_7_k5_fwd,
    r2e_cImp_8_7_k6_fwd,
    r2e_cImp_8_7_k7_fwd,
    r2e_cImp_8_7_k8_fwd,
    r2e_cImp_8_7_k9_fwd,
    r2e_cImp_8_7_k10_fwd,
    r2e_cImp_8_7_k11_fwd,
    r2e_cImp_8_7_k12_fwd,
    r2e_cImp_8_7_k13_fwd,
    r2e_cImp_8_7_k14_fwd,
    r2e_cImp_8_7_k15_fwd,
    r2e_cOr_10_14_k0_fwd,
    r2e_cOr_10_14_k1_bwd,
    r2e_cOr_10_14_k2_fwd,
    r2e_cOr_10_14_k3_fwd,
    r2e_cOr_10_14_k4_fwd,
    r2e_cOr_10_14_k5_fwd,
    r2e_cOr_10_14_k6_fwd,
    r2e_cOr_10_14_k7_fwd,
    r2e_cOr_10_14_k8_fwd,
    r2e_cOr_10_14_k9_fwd,
    r2e_cOr_10_14_k10_fwd,
    r2e_cOr_10_14_k11_fwd,
    r2e_cOr_10_14_k12_fwd,
    r2e_cOr_10_14_k13_fwd,
    r2e_cOr_10_14_k14_fwd,
    r2e_cOr_10_14_k15_fwd,
    r2e_cOr_12_15_k0_fwd,
    r2e_cOr_12_15_k1_bwd,
    r2e_cOr_12_15_k2_fwd,
    r2e_cOr_12_15_k3_fwd,
    r2e_cOr_12_15_k4_fwd,
    r2e_cOr_12_15_k5_fwd,
    r2e_cOr_12_15_k6_fwd,
    r2e_cOr_12_15_k7_fwd,
    r2e_cOr_12_15_k8_fwd,
    r2e_cOr_12_15_k9_fwd,
    r2e_cOr_12_15_k10_fwd,
    r2e_cOr_12_15_k11_fwd,
    r2e_cOr_12_15_k12_fwd,
    r2e_cOr_12_15_k13_bwd,
    r2e_cOr_12_15_k14_fwd,
    r2e_cOr_12_15_k15_fwd,
    r2e_cOr_5_8_k0_fwd,
    r2e_cOr_5_8_k1_bwd,
    r2e_cOr_5_8_k2_fwd,
    r2e_cOr_5_8_k3_fwd,
    r2e_cOr_5_8_k4_fwd,
    r2e_cOr_5_8_k5_fwd,
    r2e_cOr_5_8_k6_fwd,
    r2e_cOr_5_8_k7_fwd,
    r2e_cOr_5_8_k8_fwd,
    r2e_cOr_5_8_k9_fwd,
    r2e_cOr_5_8_k10_fwd,
    r2e_cOr_5_8_k11_fwd,
    r2e_cOr_5_8_k12_fwd,
    r2e_cOr_5_8_k13_bwd,
    r2e_cOr_5_8_k14_fwd,
    r2e_cOr_5_8_k15_fwd,
    r2e_cOr_8_11_k0_fwd,
    r2e_cOr_8_11_k1_bwd,
    r2e_cOr_8_11_k2_fwd,
    r2e_cOr_8_11_k3_fwd,
    r2e_cOr_8_11_k4_fwd,
    r2e_cOr_8_11_k5_fwd,
    r2e_cOr_8_11_k6_fwd,
    r2e_cOr_8_11_k7_fwd,
    r2e_cOr_8_11_k8_fwd,
    r2e_cOr_8_11_k9_fwd,
    r2e_cOr_8_11_k10_fwd,
    r2e_cOr_8_11_k11_fwd,
    r2e_cOr_8_11_k12_fwd,
    r2e_cOr_8_11_k13_fwd,
    r2e_cOr_8_11_k14_fwd,
    r2e_cOr_8_11_k15_fwd,
    r2e_cOr_9_15_k0_fwd,
    r2e_cOr_9_15_k1_bwd,
    r2e_cOr_9_15_k2_fwd,
    r2e_cOr_9_15_k3_fwd,
    r2e_cOr_9_15_k4_fwd,
    r2e_cOr_9_15_k5_fwd,
    r2e_cOr_9_15_k6_fwd,
    r2e_cOr_9_15_k7_fwd,
    r2e_cOr_9_15_k8_fwd,
    r2e_cOr_9_15_k9_fwd,
    r2e_cOr_9_15_k10_fwd,
    r2e_cOr_9_15_k11_bwd,
    r2e_cOr_9_15_k12_fwd,
    r2e_cOr_9_15_k13_bwd,
    r2e_cOr_9_15_k14_fwd,
    r2e_cOr_9_15_k15_fwd,
    r2e_cAnd_11_13_k0_fwd,
    r2e_cAnd_11_13_k1_bwd,
    r2e_cAnd_11_13_k2_fwd,
    r2e_cAnd_11_13_k3_fwd,
    r2e_cAnd_11_13_k4_fwd,
    r2e_cAnd_11_13_k5_fwd,
    r2e_cAnd_11_13_k6_fwd,
    r2e_cAnd_11_13_k7_fwd,
    r2e_cAnd_11_13_k8_fwd,
    r2e_cAnd_11_13_k9_fwd,
    r2e_cAnd_11_13_k10_fwd,
    r2e_cAnd_11_13_k11_bwd,
    r2e_cAnd_11_13_k12_fwd,
    r2e_cAnd_11_13_k13_bwd,
    r2e_cAnd_11_13_k14_fwd,
    r2e_cAnd_11_13_k15_fwd,
    r2e_cAnd_8_14_k0_fwd,
    r2e_cAnd_8_14_k1_bwd,
    r2e_cAnd_8_14_k2_fwd,
    r2e_cAnd_8_14_k3_fwd,
    r2e_cAnd_8_14_k4_fwd,
    r2e_cAnd_8_14_k5_fwd,
    r2e_cAnd_8_14_k6_fwd,
    r2e_cAnd_8_14_k7_fwd,
    r2e_cAnd_8_14_k8_bwd,
    r2e_cAnd_8_14_k9_fwd,
    r2e_cAnd_8_14_k10_fwd,
    r2e_cAnd_8_14_k11_fwd,
    r2e_cAnd_8_14_k12_fwd,
    r2e_cAnd_8_14_k13_bwd,
    r2e_cAnd_8_14_k14_bwd,
    r2e_cAnd_8_14_k15_fwd,
    r2e_cImp_10_4_k0_fwd,
    r2e_cImp_10_4_k1_bwd,
    r2e_cImp_10_4_k2_fwd,
    r2e_cImp_10_4_k3_fwd,
    r2e_cImp_10_4_k4_fwd,
    r2e_cImp_10_4_k5_fwd,
    r2e_cImp_10_4_k6_fwd,
    r2e_cImp_10_4_k7_fwd,
    r2e_cImp_10_4_k8_bwd,
    r2e_cImp_10_4_k9_fwd,
    r2e_cImp_10_4_k10_fwd,
    r2e_cImp_10_4_k11_fwd,
    r2e_cImp_10_4_k12_fwd,
    r2e_cImp_10_4_k13_bwd,
    r2e_cImp_10_4_k14_bwd,
    r2e_cImp_10_4_k15_fwd,
    r2e_cImp_12_11_k0_fwd,
    r2e_cImp_12_11_k1_bwd,
    r2e_cImp_12_11_k2_fwd,
    r2e_cImp_12_11_k3_fwd,
    r2e_cImp_12_11_k4_fwd,
    r2e_cImp_12_11_k5_fwd,
    r2e_cImp_12_11_k6_fwd,
    r2e_cImp_12_11_k7_fwd,
    r2e_cImp_12_11_k8_fwd,
    r2e_cImp_12_11_k9_fwd,
    r2e_cImp_12_11_k10_fwd,
    r2e_cImp_12_11_k11_fwd,
    r2e_cImp_12_11_k12_fwd,
    r2e_cImp_12_11_k13_fwd,
    r2e_cImp_12_11_k14_fwd,
    r2e_cImp_12_11_k15_fwd,
    r2e_cImp_13_14_k0_fwd,
    r2e_cImp_13_14_k1_bwd,
    r2e_cImp_13_14_k2_fwd,
    r2e_cImp_13_14_k3_fwd,
    r2e_cImp_13_14_k4_fwd,
    r2e_cImp_13_14_k5_fwd,
    r2e_cImp_13_14_k6_fwd,
    r2e_cImp_13_14_k7_fwd,
    r2e_cImp_13_14_k8_fwd,
    r2e_cImp_13_14_k9_fwd,
    r2e_cImp_13_14_k10_fwd,
    r2e_cImp_13_14_k11_fwd,
    r2e_cImp_13_14_k12_fwd,
    r2e_cImp_13_14_k13_fwd,
    r2e_cImp_13_14_k14_fwd,
    r2e_cImp_13_14_k15_fwd,
    r2e_cImp_14_12_k0_fwd,
    r2e_cImp_14_12_k1_bwd,
    r2e_cImp_14_12_k2_fwd,
    r2e_cImp_14_12_k3_fwd,
    r2e_cImp_14_12_k4_fwd,
    r2e_cImp_14_12_k5_fwd,
    r2e_cImp_14_12_k6_fwd,
    r2e_cImp_14_12_k7_fwd,
    r2e_cImp_14_12_k8_fwd,
    r2e_cImp_14_12_k9_fwd,
    r2e_cImp_14_12_k10_fwd,
    r2e_cImp_14_12_k11_fwd,
    r2e_cImp_14_12_k12_fwd,
    r2e_cImp_14_12_k13_fwd,
    r2e_cImp_14_12_k14_fwd,
    r2e_cImp_14_12_k15_fwd,
    r2e_cImp_15_12_k0_fwd,
    r2e_cImp_15_12_k1_bwd,
    r2e_cImp_15_12_k2_fwd,
    r2e_cImp_15_12_k3_fwd,
    r2e_cImp_15_12_k4_fwd,
    r2e_cImp_15_12_k5_fwd,
    r2e_cImp_15_12_k6_fwd,
    r2e_cImp_15_12_k7_fwd,
    r2e_cImp_15_12_k8_fwd,
    r2e_cImp_15_12_k9_fwd,
    r2e_cImp_15_12_k10_fwd,
    r2e_cImp_15_12_k11_fwd,
    r2e_cImp_15_12_k12_fwd,
    r2e_cImp_15_12_k13_fwd,
    r2e_cImp_15_12_k14_fwd,
    r2e_cImp_15_12_k15_fwd,
    r2e_cImp_15_7_k0_fwd,
    r2e_cImp_15_7_k1_bwd,
    r2e_cImp_15_7_k2_fwd,
    r2e_cImp_15_7_k3_fwd,
    r2e_cImp_15_7_k4_fwd,
    r2e_cImp_15_7_k5_fwd,
    r2e_cImp_15_7_k6_fwd,
    r2e_cImp_15_7_k7_fwd,
    r2e_cImp_15_7_k8_fwd,
    r2e_cImp_15_7_k9_fwd,
    r2e_cImp_15_7_k10_fwd,
    r2e_cImp_15_7_k11_fwd,
    r2e_cImp_15_7_k12_fwd,
    r2e_cImp_15_7_k13_fwd,
    r2e_cImp_15_7_k14_fwd,
    r2e_cImp_15_7_k15_fwd,
    r2e_cImp_8_14_k0_fwd,
    r2e_cImp_8_14_k1_bwd,
    r2e_cImp_8_14_k2_fwd,
    r2e_cImp_8_14_k3_fwd,
    r2e_cImp_8_14_k4_fwd,
    r2e_cImp_8_14_k5_fwd,
    r2e_cImp_8_14_k6_fwd,
    r2e_cImp_8_14_k7_fwd,
    r2e_cImp_8_14_k8_fwd,
    r2e_cImp_8_14_k9_fwd,
    r2e_cImp_8_14_k10_fwd,
    r2e_cImp_8_14_k11_fwd,
    r2e_cImp_8_14_k12_fwd,
    r2e_cImp_8_14_k13_fwd,
    r2e_cImp_8_14_k14_fwd,
    r2e_cImp_8_14_k15_fwd,
    r2e_cImp_8_9_k0_fwd,
    r2e_cImp_8_9_k1_bwd,
    r2e_cImp_8_9_k2_fwd,
    r2e_cImp_8_9_k3_fwd,
    r2e_cImp_8_9_k4_fwd,
    r2e_cImp_8_9_k5_fwd,
    r2e_cImp_8_9_k6_fwd,
    r2e_cImp_8_9_k7_fwd,
    r2e_cImp_8_9_k8_fwd,
    r2e_cImp_8_9_k9_fwd,
    r2e_cImp_8_9_k10_fwd,
    r2e_cImp_8_9_k11_fwd,
    r2e_cImp_8_9_k12_fwd,
    r2e_cImp_8_9_k13_fwd,
    r2e_cImp_8_9_k14_fwd,
    r2e_cImp_8_9_k15_fwd,
    r2e_cOr_11_12_k0_fwd,
    r2e_cOr_11_12_k1_bwd,
    r2e_cOr_11_12_k2_fwd,
    r2e_cOr_11_12_k3_fwd,
    r2e_cOr_11_12_k4_fwd,
    r2e_cOr_11_12_k5_fwd,
    r2e_cOr_11_12_k6_fwd,
    r2e_cOr_11_12_k7_fwd,
    r2e_cOr_11_12_k8_fwd,
    r2e_cOr_11_12_k9_fwd,
    r2e_cOr_11_12_k10_fwd,
    r2e_cOr_11_12_k11_fwd,
    r2e_cOr_11_12_k12_fwd,
    r2e_cOr_11_12_k13_fwd,
    r2e_cOr_11_12_k14_fwd,
    r2e_cOr_11_12_k15_fwd,
    r2e_cOr_13_14_k0_fwd,
    r2e_cOr_13_14_k1_bwd,
    r2e_cOr_13_14_k2_fwd,
    r2e_cOr_13_14_k3_fwd,
    r2e_cOr_13_14_k4_fwd,
    r2e_cOr_13_14_k5_fwd,
    r2e_cOr_13_14_k6_fwd,
    r2e_cOr_13_14_k7_fwd,
    r2e_cOr_13_14_k8_fwd,
    r2e_cOr_13_14_k9_fwd,
    r2e_cOr_13_14_k10_fwd,
    r2e_cOr_13_14_k11_fwd,
    r2e_cOr_13_14_k12_fwd,
    r2e_cOr_13_14_k13_fwd,
    r2e_cOr_13_14_k14_fwd,
    r2e_cOr_13_14_k15_fwd,
    r2e_cOr_6_15_k0_fwd,
    r2e_cOr_6_15_k1_bwd,
    r2e_cOr_6_15_k2_fwd,
    r2e_cOr_6_15_k3_fwd,
    r2e_cOr_6_15_k4_fwd,
    r2e_cOr_6_15_k5_fwd,
    r2e_cOr_6_15_k6_fwd,
    r2e_cOr_6_15_k7_fwd,
    r2e_cOr_6_15_k8_bwd,
    r2e_cOr_6_15_k9_fwd,
    r2e_cOr_6_15_k10_fwd,
    r2e_cOr_6_15_k11_bwd,
    r2e_cOr_6_15_k12_fwd,
    r2e_cOr_6_15_k13_bwd,
    r2e_cOr_6_15_k14_fwd,
    r2e_cOr_6_15_k15_fwd,
    r2e_cOr_8_12_k0_fwd,
    r2e_cOr_8_12_k1_bwd,
    r2e_cOr_8_12_k2_fwd,
    r2e_cOr_8_12_k3_fwd,
    r2e_cOr_8_12_k4_fwd,
    r2e_cOr_8_12_k5_fwd,
    r2e_cOr_8_12_k6_fwd,
    r2e_cOr_8_12_k7_fwd,
    r2e_cOr_8_12_k8_fwd,
    r2e_cOr_8_12_k9_fwd,
    r2e_cOr_8_12_k10_fwd,
    r2e_cOr_8_12_k11_fwd,
    r2e_cOr_8_12_k12_fwd,
    r2e_cOr_8_12_k13_bwd,
    r2e_cOr_8_12_k14_fwd,
    r2e_cOr_8_12_k15_fwd,
    r2e_cImp_13_11_k0_fwd,
    r2e_cImp_13_11_k1_bwd,
    r2e_cImp_13_11_k2_fwd,
    r2e_cImp_13_11_k3_fwd,
    r2e_cImp_13_11_k4_fwd,
    r2e_cImp_13_11_k5_fwd,
    r2e_cImp_13_11_k6_fwd,
    r2e_cImp_13_11_k7_fwd,
    r2e_cImp_13_11_k8_fwd,
    r2e_cImp_13_11_k9_fwd,
    r2e_cImp_13_11_k10_fwd,
    r2e_cImp_13_11_k11_fwd,
    r2e_cImp_13_11_k12_fwd,
    r2e_cImp_13_11_k13_fwd,
    r2e_cImp_13_11_k14_fwd,
    r2e_cImp_13_11_k15_fwd,
    r2e_cAnd_13_14_k0_fwd,
    r2e_cAnd_13_14_k1_bwd,
    r2e_cAnd_13_14_k2_fwd,
    r2e_cAnd_13_14_k3_fwd,
    r2e_cAnd_13_14_k4_fwd,
    r2e_cAnd_13_14_k5_fwd,
    r2e_cAnd_13_14_k6_fwd,
    r2e_cAnd_13_14_k7_fwd,
    r2e_cAnd_13_14_k8_fwd,
    r2e_cAnd_13_14_k9_fwd,
    r2e_cAnd_13_14_k10_fwd,
    r2e_cAnd_13_14_k11_fwd,
    r2e_cAnd_13_14_k12_fwd,
    r2e_cAnd_13_14_k13_bwd,
    r2e_cAnd_13_14_k14_bwd,
    r2e_cAnd_13_14_k15_fwd,
    r2e_cBox_11_k0_fwd,
    r2e_cBox_11_k1_bwd,
    r2e_cBox_11_k2_fwd,
    r2e_cBox_11_k3_fwd,
    r2e_cBox_11_k4_fwd,
    r2e_cBox_11_k5_fwd,
    r2e_cBox_11_k6_fwd,
    r2e_cBox_11_k7_fwd,
    r2e_cBox_11_k8_fwd,
    r2e_cBox_11_k9_fwd,
    r2e_cBox_11_k10_fwd,
    r2e_cBox_11_k11_fwd,
    r2e_cBox_11_k12_fwd,
    r2e_cBox_11_k13_fwd,
    r2e_cBox_11_k14_fwd,
    r2e_cBox_11_k15_fwd,
    r2e_cImp_10_7_k0_fwd,
    r2e_cImp_10_7_k1_bwd,
    r2e_cImp_10_7_k2_fwd,
    r2e_cImp_10_7_k3_fwd,
    r2e_cImp_10_7_k4_fwd,
    r2e_cImp_10_7_k5_fwd,
    r2e_cImp_10_7_k6_fwd,
    r2e_cImp_10_7_k7_fwd,
    r2e_cImp_10_7_k8_bwd,
    r2e_cImp_10_7_k9_fwd,
    r2e_cImp_10_7_k10_fwd,
    r2e_cImp_10_7_k11_fwd,
    r2e_cImp_10_7_k12_fwd,
    r2e_cImp_10_7_k13_bwd,
    r2e_cImp_10_7_k14_bwd,
    r2e_cImp_10_7_k15_fwd,
    r2e_cImp_12_7_k0_fwd,
    r2e_cImp_12_7_k1_bwd,
    r2e_cImp_12_7_k2_fwd,
    r2e_cImp_12_7_k3_fwd,
    r2e_cImp_12_7_k4_fwd,
    r2e_cImp_12_7_k5_fwd,
    r2e_cImp_12_7_k6_fwd,
    r2e_cImp_12_7_k7_fwd,
    r2e_cImp_12_7_k8_bwd,
    r2e_cImp_12_7_k9_fwd,
    r2e_cImp_12_7_k10_fwd,
    r2e_cImp_12_7_k11_fwd,
    r2e_cImp_12_7_k12_fwd,
    r2e_cImp_12_7_k13_bwd,
    r2e_cImp_12_7_k14_fwd,
    r2e_cImp_12_7_k15_fwd,
    r2e_cImp_13_5_k0_fwd,
    r2e_cImp_13_5_k1_bwd,
    r2e_cImp_13_5_k2_fwd,
    r2e_cImp_13_5_k3_fwd,
    r2e_cImp_13_5_k4_fwd,
    r2e_cImp_13_5_k5_fwd,
    r2e_cImp_13_5_k6_fwd,
    r2e_cImp_13_5_k7_fwd,
    r2e_cImp_13_5_k8_fwd,
    r2e_cImp_13_5_k9_fwd,
    r2e_cImp_13_5_k10_bwd,
    r2e_cImp_13_5_k11_bwd,
    r2e_cImp_13_5_k12_fwd,
    r2e_cImp_13_5_k13_fwd,
    r2e_cImp_13_5_k14_fwd,
    r2e_cImp_13_5_k15_fwd,
    r2e_cImp_14_13_k0_fwd,
    r2e_cImp_14_13_k1_bwd,
    r2e_cImp_14_13_k2_fwd,
    r2e_cImp_14_13_k3_fwd,
    r2e_cImp_14_13_k4_fwd,
    r2e_cImp_14_13_k5_fwd,
    r2e_cImp_14_13_k6_fwd,
    r2e_cImp_14_13_k7_fwd,
    r2e_cImp_14_13_k8_fwd,
    r2e_cImp_14_13_k9_fwd,
    r2e_cImp_14_13_k10_fwd,
    r2e_cImp_14_13_k11_fwd,
    r2e_cImp_14_13_k12_fwd,
    r2e_cImp_14_13_k13_fwd,
    r2e_cImp_14_13_k14_fwd,
    r2e_cImp_14_13_k15_fwd,
    r2e_cImp_15_14_k0_fwd,
    r2e_cImp_15_14_k1_bwd,
    r2e_cImp_15_14_k2_fwd,
    r2e_cImp_15_14_k3_fwd,
    r2e_cImp_15_14_k4_fwd,
    r2e_cImp_15_14_k5_fwd,
    r2e_cImp_15_14_k6_fwd,
    r2e_cImp_15_14_k7_fwd,
    r2e_cImp_15_14_k8_fwd,
    r2e_cImp_15_14_k9_fwd,
    r2e_cImp_15_14_k10_fwd,
    r2e_cImp_15_14_k11_fwd,
    r2e_cImp_15_14_k12_fwd,
    r2e_cImp_15_14_k13_fwd,
    r2e_cImp_15_14_k14_fwd,
    r2e_cImp_15_14_k15_fwd,
    r2e_cImp_15_9_k0_fwd,
    r2e_cImp_15_9_k1_bwd,
    r2e_cImp_15_9_k2_fwd,
    r2e_cImp_15_9_k3_fwd,
    r2e_cImp_15_9_k4_fwd,
    r2e_cImp_15_9_k5_fwd,
    r2e_cImp_15_9_k6_fwd,
    r2e_cImp_15_9_k7_fwd,
    r2e_cImp_15_9_k8_fwd,
    r2e_cImp_15_9_k9_fwd,
    r2e_cImp_15_9_k10_fwd,
    r2e_cImp_15_9_k11_fwd,
    r2e_cImp_15_9_k12_fwd,
    r2e_cImp_15_9_k13_fwd,
    r2e_cImp_15_9_k14_fwd,
    r2e_cImp_15_9_k15_fwd,
    r2e_cImp_8_4_k0_fwd,
    r2e_cImp_8_4_k1_bwd,
    r2e_cImp_8_4_k2_fwd,
    r2e_cImp_8_4_k3_fwd,
    r2e_cImp_8_4_k4_fwd,
    r2e_cImp_8_4_k5_fwd,
    r2e_cImp_8_4_k6_fwd,
    r2e_cImp_8_4_k7_fwd,
    r2e_cImp_8_4_k8_fwd,
    r2e_cImp_8_4_k9_fwd,
    r2e_cImp_8_4_k10_bwd,
    r2e_cImp_8_4_k11_bwd,
    r2e_cImp_8_4_k12_fwd,
    r2e_cImp_8_4_k13_fwd,
    r2e_cImp_8_4_k14_fwd,
    r2e_cImp_8_4_k15_fwd,
    r2e_cOr_10_12_k0_fwd,
    r2e_cOr_10_12_k1_bwd,
    r2e_cOr_10_12_k2_fwd,
    r2e_cOr_10_12_k3_fwd,
    r2e_cOr_10_12_k4_fwd,
    r2e_cOr_10_12_k5_fwd,
    r2e_cOr_10_12_k6_fwd,
    r2e_cOr_10_12_k7_fwd,
    r2e_cOr_10_12_k8_fwd,
    r2e_cOr_10_12_k9_fwd,
    r2e_cOr_10_12_k10_fwd,
    r2e_cOr_10_12_k11_fwd,
    r2e_cOr_10_12_k12_fwd,
    r2e_cOr_10_12_k13_fwd,
    r2e_cOr_10_12_k14_fwd,
    r2e_cOr_10_12_k15_fwd,
    r2e_cOr_11_13_k0_fwd,
    r2e_cOr_11_13_k1_bwd,
    r2e_cOr_11_13_k2_fwd,
    r2e_cOr_11_13_k3_fwd,
    r2e_cOr_11_13_k4_fwd,
    r2e_cOr_11_13_k5_fwd,
    r2e_cOr_11_13_k6_fwd,
    r2e_cOr_11_13_k7_fwd,
    r2e_cOr_11_13_k8_fwd,
    r2e_cOr_11_13_k9_fwd,
    r2e_cOr_11_13_k10_fwd,
    r2e_cOr_11_13_k11_fwd,
    r2e_cOr_11_13_k12_fwd,
    r2e_cOr_11_13_k13_fwd,
    r2e_cOr_11_13_k14_fwd,
    r2e_cOr_11_13_k15_fwd,
    r2e_cOr_14_15_k0_fwd,
    r2e_cOr_14_15_k1_bwd,
    r2e_cOr_14_15_k2_fwd,
    r2e_cOr_14_15_k3_fwd,
    r2e_cOr_14_15_k4_fwd,
    r2e_cOr_14_15_k5_fwd,
    r2e_cOr_14_15_k6_fwd,
    r2e_cOr_14_15_k7_fwd,
    r2e_cOr_14_15_k8_fwd,
    r2e_cOr_14_15_k9_fwd,
    r2e_cOr_14_15_k10_fwd,
    r2e_cOr_14_15_k11_fwd,
    r2e_cOr_14_15_k12_fwd,
    r2e_cOr_14_15_k13_fwd,
    r2e_cOr_14_15_k14_fwd,
    r2e_cOr_14_15_k15_fwd,
    r2e_cOr_7_15_k0_fwd,
    r2e_cOr_7_15_k1_bwd,
    r2e_cOr_7_15_k2_fwd,
    r2e_cOr_7_15_k3_fwd,
    r2e_cOr_7_15_k4_fwd,
    r2e_cOr_7_15_k5_fwd,
    r2e_cOr_7_15_k6_fwd,
    r2e_cOr_7_15_k7_fwd,
    r2e_cOr_7_15_k8_bwd,
    r2e_cOr_7_15_k9_fwd,
    r2e_cOr_7_15_k10_fwd,
    r2e_cOr_7_15_k11_bwd,
    r2e_cOr_7_15_k12_fwd,
    r2e_cOr_7_15_k13_bwd,
    r2e_cOr_7_15_k14_fwd,
    r2e_cOr_7_15_k15_fwd,
    r2e_cOr_8_14_k0_fwd,
    r2e_cOr_8_14_k1_bwd,
    r2e_cOr_8_14_k2_fwd,
    r2e_cOr_8_14_k3_fwd,
    r2e_cOr_8_14_k4_fwd,
    r2e_cOr_8_14_k5_fwd,
    r2e_cOr_8_14_k6_fwd,
    r2e_cOr_8_14_k7_fwd,
    r2e_cOr_8_14_k8_fwd,
    r2e_cOr_8_14_k9_fwd,
    r2e_cOr_8_14_k10_fwd,
    r2e_cOr_8_14_k11_fwd,
    r2e_cOr_8_14_k12_fwd,
    r2e_cOr_8_14_k13_fwd,
    r2e_cOr_8_14_k14_fwd,
    r2e_cOr_8_14_k15_fwd ]

set_option maxRecDepth 65536 in
theorem escEntries_length : escEntries.length = 928 := rfl

/-! ## Pins — UNGUARDED as emitted; guard via tools/pin-backfill.py -/

/-- info: 'RNDB.escEntries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escEntries

/-- info: 'RNDB.escEntries_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escEntries_length

end RNDB