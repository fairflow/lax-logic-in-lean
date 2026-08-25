/- Executable wrapper for `wip/two_sided.lean`. -/
import wip.two_sided

def main (args : List String) : IO Unit := TwoSided.main args
