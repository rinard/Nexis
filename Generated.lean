-- Copyright (c) 2026 Martin Rinard
/-!
# `Generated` — the generated-output library root.

Every file under `Generated/` is emitted by `lake exe gen` from the `.gsl` specs (do not edit by hand).
The generated modules live under the dedicated `Generated.*` namespace, physically separate from all
authored code; `gengen-check` verifies they are byte-identical to the generator's output.
-/
