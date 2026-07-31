-- Copyright (c) 2026 Martin Rinard
import Generated.Seam.anticdefs.ValidExtremal
import Generated.Seam.available.ValidExtremal
import Generated.Seam.availdefs.ValidExtremal
import Generated.Seam.bwdchain.ValidExtremal
import Generated.Seam.bwdmay.ValidExtremal
import Generated.Seam.bwdslice.ValidExtremal
import Seam.compile.CompileCorrect
import Seam.constprop.Adapter
import Generated.Seam.constprop.ValidExtremal
import Generated.Seam.definiteassign.ValidExtremal
import Generated.Seam.gatedlive.ValidExtremal
import Seam.lcm.Adapter
import Generated.Seam.lcm.ValidExtremal
import Generated.Seam.live.ValidExtremal
import Generated.Seam.maybeassign.ValidExtremal
import Generated.Seam.partialavail.ValidExtremal
import Seam.pdce.Adapter
import Generated.Seam.pdce.ValidExtremal
import Generated.Seam.primeadd.ValidExtremal
import Seam.reachable.Adapter
import Generated.Seam.reachable.ValidExtremal
import Generated.Seam.reaching.ValidExtremal
import Generated.Seam.structavail.ValidExtremal
import Generated.Seam.taint.ValidExtremal
import Generated.Seam.verybusy.ValidExtremal

/-! # `Seam` — the analysis interface: `*Clauses` predicates, `*SpecOf` adapters, and the concrete
    valid+extremal spec instances (`reachSpec`/`cpSpec`/`lcmSolved`/`pdceSolved`). The ONLY layer that
    imports the `Solver/` directory; the compiler above is quantified over an arbitrary valid+extremal
    solution. Substitute a new solver by replacing `Solver/` and re-wiring these instances.

    This root re-exports every seam module, so `import Seam` is the single entry point to the whole
    interface. The invariant `nothing outside Seam/ imports Solver/` is checked by `script/check-seam.sh`. -/
