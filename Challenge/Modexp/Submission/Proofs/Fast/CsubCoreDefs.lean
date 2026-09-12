import Challenge.Modexp.Submission.Proofs.Fast.CsubCoreAmTail
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
attribute [local simp] jumpDestCopyResume
/-- The state of memory and borrow after `j` limb steps of `CSUB`, counted from
the least significant limb.  Step `j` reads limb `j` of `t_low` at `TS` and of
the modulus at `0`, and writes limb `j` of the candidate at `SUBB`. -/
def csStep (memory : ByteArray) (n : Nat) : Nat → LimbState
  | 0 => ⟨memory, UInt256.ofNat 0⟩
  | j + 1 =>
      let prev := csStep memory n j
      let t := MachineState.readWord prev.memory (2112 + 32 * (n - 1 - j))
      let md := MachineState.readWord prev.memory (32 * (n - 1 - j))
      let d1 := t - md
      let d2 := d1 - prev.flag
      { memory := MachineState.writeBytes prev.memory
          (Data.Bytes.natToBytesPadded d2.toNat 32) (1792 + 32 * (n - 1 - j))
        flag := UInt256.lor (UInt256.lt t md) (UInt256.lt d1 prev.flag) }

/-- The `CSUB` loop head (pc 2225) after `j` limb steps. -/
def csLoopState (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2026
           stack := [UInt256.ofNat (ptrAt (2080 + 32 * n) j),
                     UInt256.ofNat (ptrAt (32 * n - 32) j),
                     UInt256.ofNat (ptrAt (1760 + 32 * n) j),
                     (csStep memory n j).flag, pdst, ret] ++ rest
           memory := (csStep memory n j).memory }

/-- The `CSUB` loop exit (pc 2273). -/
def csTailState (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2074
           stack := [UInt256.ofNat (ptrAt (2080 + 32 * n) j),
                     UInt256.ofNat (ptrAt (32 * n - 32) j),
                     UInt256.ofNat (ptrAt (1760 + 32 * n) j),
                     (csStep memory n j).flag, pdst, ret] ++ rest
           memory := (csStep memory n j).memory }


end Challenge.Modexp.Submission.Proofs.Fast.Csub
