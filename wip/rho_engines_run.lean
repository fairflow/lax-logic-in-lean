/- Executable wrapper for `wip/rho_engines.lean`. -/
import wip.rho_engines

def main (args : List String) : IO Unit := RhoEngines.main args
