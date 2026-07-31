-- Copyright (c) 2026 Martin Rinard
import GenGeneral.Driver
/-! `lake exe gen` — the analysis generator's entry point. All logic lives in the pure-data `GenGeneral`
    pipeline (`GenGeneral.runGen` in `GenGeneral/Driver.lean`); this is just the executable shim. -/

def main : IO Unit := GenGeneral.runGen
