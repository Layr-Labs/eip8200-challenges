import Challenge.Modexp.Submission.Proofs.Fast.FullBaseTraceCore

set_option warningAsError true
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.FullBase

open EvmSemantics EvmSemantics.EVM YulEvmCompiler

def guardProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩), .op .EQ,
   .push ⟨0, by decide⟩ (UInt256.ofNat 0), .op .MLOAD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 255), .op .SHR,
   .op .AND, .op .ISZERO,
   .push ⟨2, by decide⟩ (UInt256.ofNat 1802), .op .JUMPI]

def guardWord (memory : ByteArray) (n bsize : Nat) : UInt256 :=
  UInt256.isZero (UInt256.land
    (UInt256.shiftRight (MachineState.readWord memory 0) (UInt256.ofNat 255))
    (UInt256.eq (UInt256.ofNat bsize) (UInt256.ofNat (32 * n))))

theorem topShift_toNat (memory : ByteArray) :
    (UInt256.shiftRight (MachineState.readWord memory 0) (UInt256.ofNat 255)).toNat =
      if R1.TopBitSet memory then 1 else 0 := by
  rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by decide)]
  simp only [Nat.shiftRight_eq_div_pow]
  have hlt : (MachineState.readWord memory 0).toNat < 2 ^ 256 :=
    (MachineState.readWord memory 0).val.isLt
  unfold R1.TopBitSet
  split <;> omega

theorem guardWord_eq (memory : ByteArray) (n bsize : Nat)
    (hn32 : n ≤ 8) (hb : bsize < 2 ^ 256) :
    guardWord memory n bsize =
      if Matches memory n bsize then UInt256.ofNat 0 else UInt256.ofNat 1 := by
  have hsize : 32 * n < 2 ^ 256 :=
    lt_of_le_of_lt (show 32 * n ≤ 256 by omega) (by decide)
  unfold guardWord UInt256.isZero
  rw [Challenge.EvmProof.Word.word_toNat_land, topShift_toNat]
  simp only [UInt256.eq, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hsize]
  by_cases heq : bsize = 32 * n <;> by_cases htop : R1.TopBitSet memory <;>
    simp [Matches, heq, htop, Challenge.EvmProof.Word.word_toNat_ofNat]
end Challenge.Modexp.Submission.Proofs.Fast.FullBase
