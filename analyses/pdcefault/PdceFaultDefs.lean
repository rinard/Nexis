-- Copyright (c) 2026 Martin Rinard
import analyses.pdce.PdceDefs

/-!
# `PDCEFault.PdceFaultDefs` — the node-locals of the fault-preserving PDCE analysis

The fault-preserving analysis is the classical one with a **widened floor**: `condVars` becomes
`liveFloorF = condVars ∪ faultingRhsVars`. It reads the *same* node-locals, so this module re-exports
them into the `PDCEFault` namespace rather than restating them — the generator names its module after
the analysis, and every node-local it emits must resolve there.

Nothing here is new mathematics; `faultingRhsVars`/`liveFloorF` are authored beside `condVars` in
`analyses/pdce/PdceDefs.lean`.
-/

namespace BaseLanguage.Analyses.PDCEFault

export BaseLanguage.Analyses.PDCE
  (Asgn Assignments Variables
   born allAsgns useV defV usedVars rhsVars faultingRhsVars defVars condVars liveFloorF
   kills pass allVars liveSeed sinkSeed Greatest Least)

-- Qualified uses like `Variables.Subset …` need the *namespace* re-exported too: exporting the type
-- alone does not chain namespace resolution.
namespace Variables
export BaseLanguage.Analyses.PDCE.Variables
  (Subset union empty singleton ofList has mem_union mem_singleton mem_ofList
   subset_refl subset_trans union_subset_union has_iff)
end Variables

namespace Assignments
export BaseLanguage.Analyses.PDCE.Assignments
  (Subset subset union inter sdiff empty singleton ofList)
end Assignments

end BaseLanguage.Analyses.PDCEFault
