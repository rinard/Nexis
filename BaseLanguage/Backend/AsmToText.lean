-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Backend.TacToAsm
import BaseLanguage.Backend.AsmEnc

namespace BaseLanguage

/-!
# `AsmToText` — the printer: `Asm.Prog` → AArch64 (Apple/macOS Mach-O) assembler text

The tail of the pipeline. `TacToAsm.codegen` (verified) selects *modelled* AArch64 instructions
(`Asm.Prog`); this turns them into Apple-`arm64` assembler text for `clang` to assemble + link.

The computational instructions now go through the **verified encoder** `AsmEnc` (`instrText` →
`cmdText` → `AsmEnc.emitCmd` then `renderLine`): `emitCmd` legalizes offsets and is *proved* to emit
only encodable lines (`emitCmd_wf` / `codegen_emits_wf`) that faithfully round-trip
(`decode_emitCmd`). What stays **trusted** here is small and inspectable: the 1:1 syntactic
`renderLine` (`AsmLine → String`); the ABI-terminal scaffolding for `halt`/`print` (the
`_printf`/`ret`/`_abort` sequences — external calls, axiomatized by every verified compiler); and the
frame prologue/epilogue text. The residual encoding semantics (that these well-formed lines *run*
as the `Asm` model says) is the remaining machine-model step.

Conventions (shared with the frame layout in `TacToAsm`):
* **storage** — spill everything: each `Var` lives in an 8-byte frame slot at `[x29, #(16 + 8·idx)]`
  (above the saved `fp`/`lr`), all slots zero-initialised (`Store.init = 0`).
* **labels** — one label `L<k>` per model pc (= array index), so branches `b L<target>` resolve.
* **output** — at `halt`, each observable `obs` var prints `name=value` via `_printf`, Apple arm64
  **variadic ABI (varargs on the stack)**; `abort` is the `div`/`mod`-by-zero fault trap.

Inputs default to 0 (`Store.init`); a real CLI would seed them from argv.
-/

open Tac Asm

namespace AsmToText

/-! ## Frame layout + output scaffolding (shared with the `_main` prologue/epilogue). -/

def varName : Var → String
  | .orig s => s
  | .tmp i  => s!"t{i}"

def roundUp (n a : Nat) : Nat := ((n + a - 1) / a) * a

/-- Adjust `sp` by `frame` bytes — `verb` is `"sub"` on entry, `"add"` on exit.
    Frame allocation must NOT ride on the `stp`/`ldp` pre/post-index immediate,
    whose signed range is only `[-512, 504]` (a frame of ≥ ~61 vars overflows it
    and `clang` rejects the prologue). We adjust `sp` separately: a direct 12-bit
    `sub`/`add` immediate when the frame fits (`< 4096`), otherwise materialize the
    size in `x16` (IP0 — a scratch register the emitted body never uses) via a
    literal-pool load and adjust by register, which encodes for any frame.
    `fp`/`lr` are then saved at `[sp]`. -/
def spAdjust (verb : String) (frame : Nat) : List String :=
  if frame < 4096 then [s!"  {verb} sp, sp, #{frame}"]
  else [s!"  ldr x16, ={frame}", s!"  {verb} sp, sp, x16"]

/-! ## Per-instruction printing — via the verified encoder `AsmEnc` -/

def regName (n : Nat) : String := if n == 31 then "xzr" else s!"x{n}"

def condName : Cond → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le" | .gt => "gt"
  | .ge => "ge" | .lo => "lo" | .ls => "ls" | .hi => "hi" | .hs => "hs"

def aluName : ALU → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .sdiv => "sdiv" | .and_ => "and"
  | .orr => "orr" | .eor => "eor" | .lsl => "lsl" | .lsr => "lsr" | .asr => "asr"

/-- **The one trusted syntactic step.** Render a verified `AsmEnc.AsmLine` to its 1:1 assembler text.
    Every encoding decision — offset legalization (register-offset for slots past the 32760 immediate
    ceiling), register/immediate legality — was already made and *proved* in `AsmEnc` (`emitCmd_wf`,
    `decode_emitCmd`); this only fixes the surface syntax. -/
def renderLine : AsmEnc.AsmLine → String
  | .alu op rd rn rm    => s!"  {aluName op} {regName rd}, {regName rn}, {regName rm}"
  | .msub rd rn rm ra   => s!"  msub {regName rd}, {regName rn}, {regName rm}, {regName ra}"
  | .neg rd rn          => s!"  neg {regName rd}, {regName rn}"
  | .mvn rd rn          => s!"  mvn {regName rd}, {regName rn}"
  | .ldrImmOff rd off   => s!"  ldr {regName rd}, [x29, #{off}]"
  | .strImmOff rs off   => s!"  str {regName rs}, [x29, #{off}]"
  | .strZeroImmOff off  => s!"  str xzr, [x29, #{off}]"
  | .ldrRegOff rd idx   => s!"  ldr {regName rd}, [x29, {regName idx}]"
  | .strRegOff rs idx   => s!"  str {regName rs}, [x29, {regName idx}]"
  | .strZeroRegOff idx  => s!"  str xzr, [x29, {regName idx}]"
  | .litWord rd w       => s!"  ldr {regName rd}, ={w.toInt}"
  | .litOff rd off      => s!"  ldr {regName rd}, ={off}"
  | .cmp rn rm          => s!"  cmp {regName rn}, {regName rm}"
  | .cset rd c          => s!"  cset {regName rd}, {condName c}"
  | .b t                => s!"  b L{t}"
  | .cbz rn t           => s!"  cbz {regName rn}, L{t}"
  | .abort              => "  bl _abort"

/-- A modelled instruction as assembler text: through the verified `AsmEnc.emitCmd` (which legalizes
    offsets and is proved to emit only encodable lines, `emitCmd_wf`) then `renderLine`. -/
def cmdText (c : Asm.Cmd) : List String := (AsmEnc.emitCmd c).map renderLine

/-- Print one observable `name=value` via `_printf`, Apple arm64 variadic ABI (args on the stack). -/
def emitPrint (vs : List Var) (k : Nat) (v : Var) : List String :=
  [ "  adrp x0, lfmt@PAGE", "  add x0, x0, lfmt@PAGEOFF",
    s!"  adrp x8, ostr{k}@PAGE", s!"  add x8, x8, ostr{k}@PAGEOFF" ]
    ++ cmdText (.ldrSlot 9 (TacToAsm.slotOff vs v))
    ++ [ "  sub sp, sp, #16", "  str x8, [sp]", "  str x9, [sp, #8]",
         "  bl _printf", "  add sp, sp, #16" ]

/-- The `halt` expansion: print every observable, then the `_main` epilogue + `ret`. -/
def emitHalt (P : Program) (vs : List Var) (frame : Nat) : List String :=
  (P.obs.zipIdx.flatMap (fun (v, k) => emitPrint vs k v))
    ++ ["  mov w0, #0", "  ldp x29, x30, [sp]"] ++ spAdjust "add" frame ++ ["  ret"]

/-- One modelled instruction → assembler line(s). The computational instructions route through the
    verified encoder (`cmdText`); the ABI terminals `halt`/`print` expand in the (trusted) scaffolding. -/
def instrText (P : Program) (vs : List Var) (frame : Nat) : Asm.Cmd → List String
  | .halt     => emitHalt P vs frame
  | .print rs => [s!"  /* print {regName rs} */"]
  | c         => cmdText c

/-- The whole Mach-O assembly text for `codegen P`. -/
def emitText (P : Program) : String :=
  let vs    := TacToAsm.collectVars P
  let frame := roundUp (16 + 8 * vs.length) 16
  let prog  := TacToAsm.codegen P
  let header := [".text", ".globl _main", ".p2align 2", "_main:"]
                 ++ spAdjust "sub" frame
                 ++ ["  stp x29, x30, [sp]", "  mov x29, sp"]
  let zero  := (List.range vs.length).flatMap (fun k => cmdText (.strZero (16 + 8 * k)))
  let entry := [s!"  b L{P.entry * TacToAsm.B}"]
  let body  := (List.range prog.size).flatMap
                 (fun k => s!"L{k}:" :: instrText P vs frame (prog[k]!))
  let strs  := P.obs.zipIdx.map (fun (v, k) => s!"ostr{k}: .asciz \"{varName v}\"")
  let data  := [".section __TEXT,__cstring", "lfmt: .asciz \"%s=%lld\\n\""] ++ strs
  String.intercalate "\n" (header ++ zero ++ entry ++ body ++ data) ++ "\n"

end AsmToText

end BaseLanguage
