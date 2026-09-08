import Challenge.Modexp.Submission.Proofs.Fast.MonproCoreModel

set_option warningAsError true

/-! The unchanged CIOS row memory recursion, independent of an Artifact. -/

namespace Challenge.Modexp.Submission.Proofs.Fast.Monpro

open EvmSemantics EvmSemantics.EVM YulEvmCompiler

/-- The `b` limb consumed by row `i`. -/
def rowBi (mem : ByteArray) (pb n i : Nat) : UInt256 :=
  MachineState.readWord mem (pb + 32 * (n - 1 - i))

/-- `t[n] := t[n] + C`. -/
def midMem1 (mem : ByteArray) (c : UInt256) : ByteArray :=
  MachineState.writeBytes mem
    (Data.Bytes.natToBytesPadded (MachineState.readWord mem 8224 + c).toNat 32) 8224

/-- `t[n] := t[n] + C`, then `t[n+1] := carry`. -/
def midMem (mem : ByteArray) (c : UInt256) : ByteArray :=
  MachineState.writeBytes (midMem1 mem c)
    (Data.Bytes.natToBytesPadded
      (UInt256.lt (MachineState.readWord mem 8224 + c) c).toNat 32) 8192

/-- `mu = minv * t[0]` truncated to one limb. -/
def rowMu (mem : ByteArray) (n : Nat) : UInt256 :=
  MachineState.readWord mem 9376 * MachineState.readWord mem (8224 + 32 * n)

/-- The carry into the second limb loop: `t[0] + mu * m[0] = C * radix`. -/
def rowC0 (mem : ByteArray) (n : Nat) : UInt256 :=
  UInt256.isZero
      (UInt256.isZero (MachineState.readWord mem (32 * n - 32) * rowMu mem n)) +
    mulHi (MachineState.readWord mem (32 * n - 32)) (rowMu mem n)

theorem zero_lt_eq_double_isZero (x : UInt256) :
    UInt256.lt ({ val := 0 } : UInt256) x = UInt256.isZero (UInt256.isZero x) := by
  unfold UInt256.lt UInt256.isZero
  have hzero : ({ val := 0 } : UInt256).toNat = 0 := rfl
  by_cases h : x.toNat = 0
  · simp [h, hzero]
  · have hp : 0 < x.toNat := Nat.pos_of_ne_zero h
    simp [h, hzero, Nat.not_le_of_gt hp]

/-- `t[n-1] := t[n] + C`. -/
def tailMem1 (mem : ByteArray) (c : UInt256) : ByteArray :=
  MachineState.writeBytes mem
    (Data.Bytes.natToBytesPadded (MachineState.readWord mem 8224 + c).toNat 32) 8256

/-- `t[n-1] := t[n] + C`, then `t[n] := t[n+1] + carry`. -/
def tailMem (mem : ByteArray) (c : UInt256) : ByteArray :=
  MachineState.writeBytes (tailMem1 mem c)
    (Data.Bytes.natToBytesPadded
      (MachineState.readWord (tailMem1 mem c) 8192 +
        UInt256.lt (MachineState.readWord mem 8224 + c) c).toNat 32) 8224

/-- The first limb loop of row `i`, run to completion. -/
def rowL1 (mem : ByteArray) (pa pb n i : Nat) : MacState :=
  l1Step mem (rowBi mem pb n i) pa n n

/-- Memory after the middle block of row `i`. -/
def rowMid (mem : ByteArray) (pa pb n i : Nat) : ByteArray :=
  midMem (rowL1 mem pa pb n i).memory (rowL1 mem pa pb n i).carry

/-- The second limb loop of row `i`, run to completion. -/
def rowL2 (mem : ByteArray) (pa pb n i : Nat) : MacState :=
  l2Step (rowMid mem pa pb n i) (rowMu (rowL1 mem pa pb n i).memory n)
    (rowC0 (rowL1 mem pa pb n i).memory n) n (n - 1)

/-- Memory after row `i`. -/
def rowMem (mem : ByteArray) (pa pb n i : Nat) : ByteArray :=
  tailMem (rowL2 mem pa pb n i).memory (rowL2 mem pa pb n i).carry

/-- Memory after `i` complete CIOS rows. -/
def rowsMem (mem : ByteArray) (pa pb n : Nat) : Nat → ByteArray
  | 0 => mem
  | i + 1 => rowMem (rowsMem mem pa pb n i) pa pb n i

/-- The prologue zeroes `t[n .. 0]` with `CALLDATACOPY` from the end of the
calldata. Slot `8192` is the carry flag and is overwritten by `midMem` before
any read, so the clear starts at `8224`. -/
def mpZeroed (s : State) (mem : ByteArray) (n : Nat) : ByteArray :=
  MachineState.writeBytes mem
    (MachineState.readPadded s.executionEnv.calldata s.executionEnv.calldata.size
      (32 + 32 * n)) 8224

end Challenge.Modexp.Submission.Proofs.Fast.Monpro
