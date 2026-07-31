-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.TAC

/-!
# `IR.Hashable` — `Hashable` instances for the IR vocabulary

Shared by the analyses (`LCM`, `PDCE`) so their fact domains can be efficient `Std.HashSet`s of
expressions / variables. Derived once here to avoid duplicate instances.
-/

namespace BaseLanguage
open Tac

deriving instance Hashable for Var, Atom, Unop, Binop, Expr

end BaseLanguage
