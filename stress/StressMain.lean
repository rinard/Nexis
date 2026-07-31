-- Copyright (c) 2026 Martin Rinard
import GenGeneralStress
/-! `gengen-stress` standalone entry point. The gate itself is `runStress` in `GenGeneralStress`, so the
    `lake test` driver can run it too. -/
def main : IO UInt32 := runStress
