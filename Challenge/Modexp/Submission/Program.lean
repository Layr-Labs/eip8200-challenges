import Challenge.Modexp.Submission.Bridge
import Challenge.Modexp.Submission.Dsl
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-!
# The phase-1 MODEXP program (value-dependent control flow)

Written in the verified compiler's labeled-assembly IR (`YulEvmCompiler.Asm`)
via a small expression DSL that fixes stack discipline. Correctness is proved
at the `ASteps` level; the artifact comes from the kernel-reducible structural
lowering (`Submission/Lowering.lowerProg'`).

Algorithm (Osaka/EIP-7823 domain, operand sizes ≤ 1024):

* header: load the three EIP-198 size words, `invalid` on overflow, empty
  return for `msize = 0`, dispatch on `msize ≤ 32`;
* word path: `MULMOD` Horner base reduction and square-and-multiply,
  value-dependent (leading zero exponent bytes skipped, accumulator seeded
  with the base at the top set bit, multiply skipped on zero bits);
* big path: little-endian 256-bit limbs, two-pass add-with-carry +
  conditional-subtract `addMod` (branchy final copy), MSB-first `mulModBig`
  that stops at the multiplier's top set bit, value-dependent exponent loop.

Both compute paths open with `mstore(TOP, 0)` so every later memory touch is
an `activeWords` no-op, keeping the Asm-level functional proof exact.
-/

namespace Challenge.Modexp.Submission

open YulEvmCompiler
open YulSemantics.EVM (U256 Op)

/-- Label-supplying generator monad. -/
abbrev Gen := StateM Nat

/-- A fresh code label. -/
def fresh : Gen Nat := do
  let n ← get
  set (n + 1)
  return n


/-! ### The program -/

/-- Call the `addMod` procedure: `mload ADST`-region `+= mload ASRC`-region,
mod the MOD region. -/
def callAddMod (dst src lret laddMod : Nat) : List Asm :=
  store ADST (.imm dst) ++ store ASRC (.imm src) ++
  [.pushLabel lret, .jump laddMod, .label lret]

/-- Call `mulModBig`: `ACC := ACC · (BPTR region) mod MOD`. -/
def callMulMod (bptr lret lmmEntry : Nat) : List Asm :=
  store BPTR (.imm bptr) ++ [.pushLabel lret, .jump lmmEntry, .label lret]

/-- Bit `load j` of `load w`. General form of Dsl's `bitTest` (which fixes the
caller's `Wcell`/`Jcell`); `mulModBig` needs it over its own registers. -/
def bitTestOf (w j : Nat) : Expr :=
  .bin .and (.bin .shr (.load j) (.load w)) (.imm 1)

/-- The complete phase-1 program. -/
def genProgram : Gen (List Asm) := do
  -- header
  let linvalid ← fresh
  let lretEmpty ← fresh
  let lbig ← fresh
  -- word path
  let lwZeroMod ← fresh
  let lwbLoop ← fresh
  let lwbDone ← fresh
  let lweScan ← fresh
  let lweExpZero ← fresh
  let lwInit ← fresh
  let lweTop ← fresh
  let lweBits ← fresh
  let lweBitsInit ← fresh
  let lweRest ← fresh
  let lweBytes ← fresh
  let lweByteBits ← fresh
  let lweNext ← fresh
  let lweSer ← fresh
  -- big path
  let lbLoad ← fresh
  let lbLoadDone ← fresh
  let lbMScan ← fresh
  let lbMScanDone ← fresh
  let lbBase ← fresh
  let lbBaseBits ← fresh
  let lbBaseBitsSkip ← fresh
  let lbBaseNext ← fresh
  let lbBaseDone ← fresh
  let lbEScan ← fresh
  let lbInit ← fresh
  let lbTop ← fresh
  let lbInitAcc ← fresh
  let lbAccInit ← fresh
  let lbAccInitDone ← fresh
  let lbTopBits ← fresh
  let lbTopBitsSkip ← fresh
  let lbRest ← fresh
  let lbBytes ← fresh
  let lbByteBits ← fresh
  let lbByteBitsSkip ← fresh
  let lbNextByte ← fresh
  let lbSer ← fresh
  let lbSerLoop ← fresh
  let lbReturn ← fresh
  -- addMod procedure
  let lamEntry ← fresh
  let lamAdd ← fresh
  let lamSubStart ← fresh
  let amSub ← fresh
  let lamSel ← fresh
  let lamDoCopy ← fresh
  let lamCopy ← fresh
  let lamDone ← fresh
  -- mulModBig procedure
  let lmmEntry ← fresh
  let lmScanTop ← fresh
  let lmTopBit ← fresh
  let lmCopy ← fresh
  let lmBits ← fresh
  let lmNextLimb ← fresh
  let lmZero ← fresh
  let lmZeroLoop ← fresh
  let lmDone ← fresh
  let lmRetCopy ← fresh
  let lmExit ← fresh
  -- call return labels
  let lamCallBase1 ← fresh
  let lamCallBase2 ← fresh
  let lamCallAccInit ← fresh
  let lsqRet1 ← fresh
  let lmulRet1 ← fresh
  let lsqRet2 ← fresh
  let lmulRet2 ← fresh
  let lmSqRet ← fresh
  let lmAddRet ← fresh

  let header :=
    store BS (.cdload (.imm 0)) ++
    store ES (.cdload (.imm 32)) ++
    store MS (.cdload (.imm 64)) ++
    jumpIfNz (.bin .or (.bin .or (.bin .lt (.imm 1024) (.load BS))
        (.bin .lt (.imm 1024) (.load ES))) (.bin .lt (.imm 1024) (.load MS))) linvalid ++
    jumpIfZ (.load MS) lretEmpty ++
    store BO (.imm 96) ++
    store EO (.bin .add (.imm 96) (.load BS)) ++
    store MO (.bin .add (.load EO) (.load ES)) ++
    jumpIfNz (.bin .lt (.imm 32) (.load MS)) lbig

  let wordPath :=
    store TOP (.imm 0) ++
    store T0 (.bin .shr (.bin .mul (.bin .sub (.imm 32) (.load MS)) (.imm 8))
      (.cdload (.load MO))) ++
    jumpIfZ (.load T0) lwZeroMod ++
    store T1 (.imm 0) ++
    store Icell (.imm 0) ++
    -- base reduction
    [.label lwbLoop] ++
    jumpUnlessLt (.load Icell) (.load BS) lwbDone ++
    store T1 (.ter .addmod (.ter .mulmod (.load T1) (.imm 256) (.load T0))
      (cdbCell BO) (.load T0)) ++
    store Icell (.bin .add (.load Icell) (.imm 1)) ++
    [.jump lwbLoop] ++
    [.label lwbDone] ++
    -- scan exponent for first nonzero byte
    store Icell (.imm 0) ++
    [.label lweScan] ++
    jumpUnlessLt (.load Icell) (.load ES) lweExpZero ++
    store Wcell (cdbCell EO) ++
    jumpIfNz (.load Wcell) lwInit ++
    store Icell (.bin .add (.load Icell) (.imm 1)) ++
    [.jump lweScan] ++
    -- exponent zero: acc := 1 mod m
    [.label lweExpZero] ++
    store T2 (.bin .mod (.imm 1) (.load T0)) ++
    [.jump lweSer] ++
    -- found: seed acc with the base at the top set bit
    [.label lwInit] ++
    store Jcell (.imm 7) ++
    [.label lweTop] ++
    jumpIfNz bitTest lweBitsInit ++
    store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
    [.jump lweTop] ++
    [.label lweBitsInit] ++
    store T2 (.load T1) ++
    [.label lweBits] ++
    jumpIfZ (.load Jcell) lweRest ++
    store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
    store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
    jumpIfZ bitTest lweBits ++
    store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
    [.jump lweBits] ++
    -- remaining bytes
    [.label lweRest] ++
    store Icell (.bin .add (.load Icell) (.imm 1)) ++
    [.label lweBytes] ++
    jumpUnlessLt (.load Icell) (.load ES) lweSer ++
    store Wcell (cdbCell EO) ++
    store Jcell (.imm 8) ++
    [.label lweByteBits] ++
    jumpIfZ (.load Jcell) lweNext ++
    store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
    store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
    jumpIfZ bitTest lweByteBits ++
    store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
    [.jump lweByteBits] ++
    [.label lweNext] ++
    store Icell (.bin .add (.load Icell) (.imm 1)) ++
    [.jump lweBytes] ++
    -- zero modulus: result zero
    [.label lwZeroMod] ++
    store T2 (.imm 0) ++
    -- serialize: RET word := acc << ((32 - msize) * 8); return RET, msize
    [.label lweSer] ++
    store RET (.bin .shl (.bin .mul (.bin .sub (.imm 32) (.load MS)) (.imm 8))
      (.load T2)) ++
    (compileExpr (.load MS) ++ compileExpr (.imm RET) ++ [.op .ret])

  let bigPath :=
    [.label lbig] ++
    store TOP (.imm 0) ++
    store Ncell (.bin .div (.bin .add (.load MS) (.imm 31)) (.imm 32)) ++
    -- load modulus big-endian into MOD limbs
    store Icell (.imm 0) ++
    [.label lbLoad] ++
    jumpUnlessLt (.load Icell) (.load MS) lbLoadDone ++
    store T0 (.bin .sub (.bin .sub (.load MS) (.imm 1)) (.load Icell)) ++
    store T1 (.bin .mul (.imm 32) (.bin .div (.load T0) (.imm 32))) ++
    storeAt (.load T1) (.bin .or (loadAt (.load T1))
      (.bin .shl (.bin .mul (.imm 8) (.bin .mod (.load T0) (.imm 32))) (cdbCell MO))) ++
    store Icell (.bin .add (.load Icell) (.imm 1)) ++
    [.jump lbLoad] ++
    [.label lbLoadDone] ++
    -- modulus zero scan
    store T0 (.imm 0) ++
    store Icell (.imm 0) ++
    [.label lbMScan] ++
    jumpUnlessLt (.load Icell) (.load Ncell) lbMScanDone ++
    store T0 (.bin .or (.load T0) (loadAt (.bin .mul (.imm 32) (.load Icell)))) ++
    store Icell (.bin .add (.load Icell) (.imm 1)) ++
    [.jump lbMScan] ++
    [.label lbMScanDone] ++
    jumpIfZ (.load T0) lbSer ++
    -- ONE := 1
    store ONE (.imm 1) ++
    -- base reduction (bitwise Horner)
    store Icell (.imm 0) ++
    [.label lbBase] ++
    jumpUnlessLt (.load Icell) (.load BS) lbBaseDone ++
    store Wcell (cdbCell BO) ++
    store Jcell (.imm 8) ++
    [.label lbBaseBits] ++
    jumpIfZ (.load Jcell) lbBaseNext ++
    store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
    callAddMod BASE BASE lamCallBase1 lamEntry ++
    jumpIfZ bitTest lbBaseBitsSkip ++
    callAddMod BASE ONE lamCallBase2 lamEntry ++
    [.label lbBaseBitsSkip] ++
    [.jump lbBaseBits] ++
    [.label lbBaseNext] ++
    store Icell (.bin .add (.load Icell) (.imm 1)) ++
    [.jump lbBase] ++
    [.label lbBaseDone] ++
    -- ACC := 1 mod m
    callAddMod ACC ONE lamCallAccInit lamEntry ++
    -- exponent scan
    store Icell (.imm 0) ++
    [.label lbEScan] ++
    jumpUnlessLt (.load Icell) (.load ES) lbSer ++
    store Wcell (cdbCell EO) ++
    jumpIfNz (.load Wcell) lbInit ++
    store Icell (.bin .add (.load Icell) (.imm 1)) ++
    [.jump lbEScan] ++
    -- found: top set bit
    [.label lbInit] ++
    store Jcell (.imm 7) ++
    [.label lbTop] ++
    jumpIfNz bitTest lbInitAcc ++
    store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
    [.jump lbTop] ++
    [.label lbInitAcc] ++
    -- acc := base
    store I2 (.imm 0) ++
    [.label lbAccInit] ++
    jumpUnlessLt (.load I2) (.load Ncell) lbAccInitDone ++
    storeAt (.bin .add (.imm ACC) (.bin .mul (.imm 32) (.load I2)))
      (loadAt (.bin .add (.imm BASE) (.bin .mul (.imm 32) (.load I2)))) ++
    store I2 (.bin .add (.load I2) (.imm 1)) ++
    [.jump lbAccInit] ++
    [.label lbAccInitDone] ++
    -- top byte's remaining bits
    [.label lbTopBits] ++
    jumpIfZ (.load Jcell) lbRest ++
    store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
    callMulMod ACC lsqRet1 lmmEntry ++
    jumpIfZ bitTest lbTopBitsSkip ++
    callMulMod BASE lmulRet1 lmmEntry ++
    [.label lbTopBitsSkip] ++
    [.jump lbTopBits] ++
    -- remaining bytes
    [.label lbRest] ++
    store Icell (.bin .add (.load Icell) (.imm 1)) ++
    [.label lbBytes] ++
    jumpUnlessLt (.load Icell) (.load ES) lbSer ++
    store Wcell (cdbCell EO) ++
    store Jcell (.imm 8) ++
    [.label lbByteBits] ++
    jumpIfZ (.load Jcell) lbNextByte ++
    store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
    callMulMod ACC lsqRet2 lmmEntry ++
    jumpIfZ bitTest lbByteBitsSkip ++
    callMulMod BASE lmulRet2 lmmEntry ++
    [.label lbByteBitsSkip] ++
    [.jump lbByteBits] ++
    [.label lbNextByte] ++
    store Icell (.bin .add (.load Icell) (.imm 1)) ++
    [.jump lbBytes] ++
    -- serialize
    [.label lbSer] ++
    store Icell (.imm 0) ++
    [.label lbSerLoop] ++
    jumpUnlessLt (.load Icell) (.load MS) lbReturn ++
    store T0 (.bin .sub (.bin .sub (.load MS) (.imm 1)) (.load Icell)) ++
    storeAt8 (.bin .add (.imm RET) (.load Icell))
      (.bin .shr (.bin .mul (.imm 8) (.bin .mod (.load T0) (.imm 32)))
        (loadAt (.bin .add (.imm ACC) (.bin .mul (.imm 32) (.bin .div (.load T0) (.imm 32)))))) ++
    store Icell (.bin .add (.load Icell) (.imm 1)) ++
    [.jump lbSerLoop] ++
    [.label lbReturn] ++
    (compileExpr (.load MS) ++ compileExpr (.imm RET) ++ [.op .ret])

  let addModProc :=
    [.label lamEntry] ++
    store C1 (.imm 0) ++
    store I2 (.imm 0) ++
    [.label lamAdd] ++
    jumpUnlessLt (.load I2) (.load Ncell) lamSubStart ++
    store AOFF (.bin .mul (.imm 32) (.load I2)) ++
    store AX (loadAt (.bin .add (.load ADST) (.load AOFF))) ++
    store AY (loadAt (.bin .add (.load ASRC) (.load AOFF))) ++
    store AS (.bin .add (.load AX) (.load AY)) ++
    store AZ (.bin .add (.load AS) (.load C1)) ++
    store C1 (.bin .or (.bin .lt (.load AS) (.load AX)) (.bin .lt (.load AZ) (.load AS))) ++
    storeAt (.bin .add (.load ADST) (.load AOFF)) (.load AZ) ++
    store I2 (.bin .add (.load I2) (.imm 1)) ++
    [.jump lamAdd] ++
    [.label lamSubStart] ++
    store C2 (.imm 0) ++
    store I2 (.imm 0) ++
    [.label amSub] ++
    jumpUnlessLt (.load I2) (.load Ncell) lamSel ++
    store AOFF (.bin .mul (.imm 32) (.load I2)) ++
    store AX (loadAt (.bin .add (.load ADST) (.load AOFF))) ++
    store AY (loadAt (.load AOFF)) ++
    store AS (.bin .sub (.load AX) (.load AY)) ++
    store AZ (.bin .sub (.load AS) (.load C2)) ++
    store C2 (.bin .or (.bin .lt (.load AX) (.load AY)) (.bin .lt (.load AS) (.load C2))) ++
    storeAt (.bin .add (.imm SUBC) (.load AOFF)) (.load AZ) ++
    store I2 (.bin .add (.load I2) (.imm 1)) ++
    [.jump amSub] ++
    [.label lamSel] ++
    jumpIfNz (.bin .or (.load C1) (.un .iszero (.load C2))) lamDoCopy ++
    [.jump lamDone] ++
    [.label lamDoCopy] ++
    store I2 (.imm 0) ++
    [.label lamCopy] ++
    jumpUnlessLt (.load I2) (.load Ncell) lamDone ++
    storeAt (.bin .add (.load ADST) (.bin .mul (.imm 32) (.load I2)))
      (loadAt (.bin .add (.imm SUBC) (.bin .mul (.imm 32) (.load I2)))) ++
    store I2 (.bin .add (.load I2) (.imm 1)) ++
    [.jump lamCopy] ++
    [.label lamDone] ++
    [.dynJump]

  let mulModProc :=
    [.label lmmEntry] ++
    store HIcell (.load Ncell) ++
    [.label lmScanTop] ++
    jumpIfZ (.load HIcell) lmZero ++
    store HIcell (.bin .sub (.load HIcell) (.imm 1)) ++
    jumpIfZ (loadAt (.bin .add (.load BPTR) (.bin .mul (.imm 32) (.load HIcell)))) lmScanTop ++
    store T0 (loadAt (.bin .add (.load BPTR) (.bin .mul (.imm 32) (.load HIcell)))) ++
    store T1 (.imm 256) ++
    [.label lmTopBit] ++
    store T1 (.bin .sub (.load T1) (.imm 1)) ++
    jumpIfZ (bitTestOf T0 T1) lmTopBit ++
    -- out := a
    store I2 (.imm 0) ++
    [.label lmCopy] ++
    jumpUnlessLt (.load I2) (.load Ncell) lmBits ++
    storeAt (.bin .add (.imm OUT) (.bin .mul (.imm 32) (.load I2)))
      (loadAt (.bin .add (.imm ACC) (.bin .mul (.imm 32) (.load I2)))) ++
    store I2 (.bin .add (.load I2) (.imm 1)) ++
    [.jump lmCopy] ++
    [.label lmBits] ++
    jumpIfZ (.load T1) lmNextLimb ++
    store T1 (.bin .sub (.load T1) (.imm 1)) ++
    store ADST (.imm OUT) ++ store ASRC (.imm OUT) ++
    [.pushLabel lmSqRet, .jump lamEntry, .label lmSqRet] ++
    jumpIfZ (bitTestOf T0 T1) lmBits ++
    store ADST (.imm OUT) ++ store ASRC (.imm ACC) ++
    [.pushLabel lmAddRet, .jump lamEntry, .label lmAddRet] ++
    [.jump lmBits] ++
    [.label lmNextLimb] ++
    jumpIfZ (.load HIcell) lmDone ++
    store HIcell (.bin .sub (.load HIcell) (.imm 1)) ++
    store T1 (.imm 256) ++
    store T0 (loadAt (.bin .add (.load BPTR) (.bin .mul (.imm 32) (.load HIcell)))) ++
    [.jump lmBits] ++
    [.label lmZero] ++
    store I2 (.imm 0) ++
    [.label lmZeroLoop] ++
    jumpUnlessLt (.load I2) (.load Ncell) lmDone ++
    storeAt (.bin .add (.imm OUT) (.bin .mul (.imm 32) (.load I2))) (.imm 0) ++
    store I2 (.bin .add (.load I2) (.imm 1)) ++
    [.jump lmZeroLoop] ++
    -- ACC := OUT: the product lands in OUT, but the documented call contract
    -- (`ACC := ACC · BPTR mod MOD`) and every caller expect it in ACC.
    [.label lmDone] ++
    store I2 (.imm 0) ++
    [.label lmRetCopy] ++
    jumpUnlessLt (.load I2) (.load Ncell) lmExit ++
    storeAt (.bin .add (.imm ACC) (.bin .mul (.imm 32) (.load I2)))
      (loadAt (.bin .add (.imm OUT) (.bin .mul (.imm 32) (.load I2)))) ++
    store I2 (.bin .add (.load I2) (.imm 1)) ++
    [.jump lmRetCopy] ++
    [.label lmExit] ++
    [.dynJump]

  let haltSections :=
    [.label linvalid, .op .invalid] ++
    [.label lretEmpty, .push (BitVec.ofNat 256 0), .push (BitVec.ofNat 256 0), .op .ret] ++
    [.jump lretEmpty]

  return header ++ wordPath ++ bigPath ++ haltSections ++ addModProc ++ mulModProc

/-- The program as an Asm list. -/
def programAsm : List Asm := (genProgram 0).1

/-- The lowered instruction list (kernel-computed). -/
def programInstrs : List Instr := (lowerProg' programAsm).get (by decide)

/-- The artifact bytes (kernel-computed). -/
def programBytecode : ByteArray := assemble programInstrs

end Challenge.Modexp.Submission
