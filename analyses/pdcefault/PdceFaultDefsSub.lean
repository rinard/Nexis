-- Copyright (c) 2026 Martin Rinard
import analyses.pdcefault.PdceFaultDefs
import analyses.pdce.PdceDefsSub

/-! # `PDCEFault.PdceFaultDefsSub` — universe-bound lemmas, re-exported into the `PDCEFault` namespace.
    `liveFloorF_sub` is the one the widened floor needs; the rest are the classical analysis's. -/

namespace BaseLanguage.Analyses.PDCEFault

export BaseLanguage.Analyses.PDCE
  (born_sub pass_sub sinkSeed_sub condVars_sub defVars_sub rhsVars_sub liveSeed_sub
   faultingRhsVars_sub liveFloorF_sub)

end BaseLanguage.Analyses.PDCEFault
