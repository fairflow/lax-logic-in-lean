import wip.rnc_probe

/-!
# `lake exe rncprobe` — the entry point for the RNC(◯,{}) probe

Split out on 2026-09-04.  `wip/rnc_probe.lean` carries content that
`wip/rncCert.lean` and `wip/rncCertPos.lean` import, so it is a LIBRARY
module; it also declared a root-level `main`, which made it an executable
root as well.  A module cannot be both: two root-level `main`s cannot
share an environment, so importing two such modules fails outright, and
that is what blocked auditing the estate by import.

The house convention is already this shape (`oracle2_run`, `rho_order_run`,
`two_sided_run`): content in the library module, entry point in a thin
`_run` root beside it.
-/
def main (args : List String) : IO Unit :=
  match args with
  | "c" :: rest :: _ => PLLND.RNC.phaseC (PLLND.RNC.parseIdx rest)
  | "r" :: rest :: _ => PLLND.RNC.phaseR (PLLND.RNC.parseCells rest)
  | "p" :: rest :: _ => PLLND.RNC.phaseP (PLLND.RNC.parseCells rest)
  | _ => PLLND.RNC.mainLoop
