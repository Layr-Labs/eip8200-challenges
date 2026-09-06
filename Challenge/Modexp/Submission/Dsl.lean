import YulEvmCompiler.AsmSem
set_option warningAsError true

/-!
# The MODEXP expression DSL and memory map

The straight-line word-computation DSL and the fixed memory map shared by the
MODEXP program (`Submission/Program.lean`) and its Asm-level correctness
lemmas (`Submission/AsmLib.lean`). Kept in this light module — importing only
the labeled-assembly semantics — so the proof library does not depend on the
program generator or the challenge bridge.
-/

namespace Challenge.Modexp.Submission

open YulEvmCompiler
open YulSemantics.EVM (U256 Op)

/-! ### Memory map -/

-- big-path limb regions (32 limbs each)
def MOD : Nat := 0x0000
def BASE : Nat := 0x0400
def ACC : Nat := 0x0800
def OUT : Nat := 0x0c00
def ONE : Nat := 0x1000
def SUBC : Nat := 0x1400
def RET : Nat := 0x1800
-- scalars (all words)
def BS : Nat := 0x1c00
def ES : Nat := 0x1c20
def MS : Nat := 0x1c40
def BO : Nat := 0x1c60
def EO : Nat := 0x1c80
def MO : Nat := 0x1ca0
def Ncell : Nat := 0x1cc0
def Icell : Nat := 0x1ce0
def Jcell : Nat := 0x1d00
def Wcell : Nat := 0x1d20
def C1 : Nat := 0x1d40
def C2 : Nat := 0x1d60
def HIcell : Nat := 0x1d80
def BPTR : Nat := 0x1da0
def T0 : Nat := 0x1dc0
def T1 : Nat := 0x1de0
def T2 : Nat := 0x1e00
def ADST : Nat := 0x1e20
def ASRC : Nat := 0x1e40
def I2 : Nat := 0x1e60
def AOFF : Nat := 0x1e80
def AX : Nat := 0x1ea0
def AY : Nat := 0x1ec0
def AS : Nat := 0x1ee0
def AZ : Nat := 0x1f00
/-- The highest cell touched; each compute path's preamble zeroes it so every
later memory touch is an `activeWords` no-op. -/
def TOP : Nat := 0x1f20

/-! ### Expression DSL -/

/-- Straight-line word computations; `compileExpr e` leaves the value on top
of the stack. All ops used are pure; `load`/`cdload`/`cdb` read only. -/
inductive Expr where
  | imm : Nat → Expr
  | load : Nat → Expr
  | mload : Expr → Expr           -- mload e
  | cdload : Expr → Expr
  | cdb : Expr → Expr            -- byte(0, calldataload e)
  | bin : Op → Expr → Expr → Expr   -- bin op a b = op(a, b), Yul argument order
  | ter : Op → Expr → Expr → Expr → Expr  -- ter op a b c = op(a, b, c)
  | un : Op → Expr → Expr

/-- Compile `e` to code leaving its value on the stack top. -/
def compileExpr : Expr → List Asm
  | .imm k => [.push (BitVec.ofNat 256 k)]
  | .load c => [.push (BitVec.ofNat 256 c), .op .mload]
  | .mload e => compileExpr e ++ [.op .mload]
  | .cdb e => compileExpr e ++ [.op .calldataload, .push (BitVec.ofNat 256 0), .op .byte]
  | .cdload e => compileExpr e ++ [.op .calldataload]
  | .bin o a b => compileExpr b ++ compileExpr a ++ [.op o]
  | .ter o a b c => compileExpr c ++ compileExpr b ++ compileExpr a ++ [.op o]
  | .un o a => compileExpr a ++ [.op o]

/-- Store `e`'s value at constant cell `c`. -/
def store (c : Nat) (e : Expr) : List Asm :=
  compileExpr e ++ [.push (BitVec.ofNat 256 c), .op .mstore]

/-- Store `valE`'s value at the computed address `addrE`. -/
def storeAt (addrE valE : Expr) : List Asm :=
  compileExpr valE ++ compileExpr addrE ++ [.op .mstore]

/-- Store `valE`'s low byte at the computed address `addrE`. -/
def storeAt8 (addrE valE : Expr) : List Asm :=
  compileExpr valE ++ compileExpr addrE ++ [.op .mstore8]

/-- Load the word at the computed address `addrE`. -/
def loadAt (addrE : Expr) : Expr := .mload addrE

/-- `if e ≠ 0 then jump l`; falls through on zero. -/
def jumpIfNz (e : Expr) (l : Nat) : List Asm :=
  compileExpr e ++ [.jumpi l]

/-- `if e = 0 then jump l`. -/
def jumpIfZ (e : Expr) (l : Nat) : List Asm :=
  compileExpr e ++ [.op .iszero, .jumpi l]

/-- `if ¬ (e₁ < e₂) then jump l` — the loop-exit test (`e₁` counter, `e₂`
bound). -/
def jumpUnlessLt (e₁ e₂ : Expr) (l : Nat) : List Asm :=
  compileExpr e₂ ++ compileExpr e₁ ++ [.op .lt, .op .iszero, .jumpi l]

/-- The `Icell`-th calldata byte at `load base + load Icell`. -/
def cdbCell (base : Nat) : Expr := .cdb (.bin .add (.load base) (.load Icell))

/-- Bit `load Jcell` of `load Wcell`. -/
def bitTest : Expr := .bin .and (.bin .shr (.load Jcell) (.load Wcell)) (.imm 1)

end Challenge.Modexp.Submission
