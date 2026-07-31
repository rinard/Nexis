-- Copyright (c) 2026 Martin Rinard
import GenGeneralCheck
/-! `gengen-check` standalone entry point. The gate itself is `runCheck` in `GenGeneralCheck`, so the
    `lake test` driver can run it too — a gate nothing runs is not a gate (it silently broke once). -/
def main : IO Unit := runCheck
