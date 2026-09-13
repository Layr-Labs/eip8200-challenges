import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneGarbageSchedule
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Prefix
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Round

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Semantics
open EvmSemantics PairedLaneUInt256Bridge PairedLaneCore
open PairedHelperBooleanTrace PairedSynthCoreTrace Strip78Prefix Strip78Round

theorem resultMemory_prefix_strip (memory : ByteArray) (words : Nat → UInt32)
    (left right : PairedLaneCryptoBridge.CryptoLane)
    (hready : NormalizedScheduleReady memory words) :
    PairedTailTrace.resultMemory memory
      (TerminalRound.modifiedFrame memory (dirtyFrame memory
        (corePrefix77Chain.eval memory ⟨PairedLaneWordRound.packCrypto left right, 0⟩))) =
      PairedTailTrace.resultMemory memory
        (TerminalRound.modifiedFrame memory
          (PairedAllInlineCoreTrace.corePrefixChain.eval memory
            ⟨PairedLaneWordRound.packCrypto left right, 0⟩).frame) := by
  rw [← prefix78_eq]
  rw [corePrefix77Chain_eval]
  rw [hoistedAlgorithmFold_crypto memory words 78 (by decide) left right
    (fun i hi => algorithmMessage_of_normalized memory words hready i (by omega))]
  apply resultMemory_strip_eq
  · exact normalize_pack _ _
  · exact normalize_pack _ _
  · exact normalize_pack _ _
  · change normalize (bits (physicalKey 4)) = bits (physicalKey 4)
    decide
  · change normalize (bits (algorithmMessage memory 79)) = bits (algorithmMessage memory 79)
    rw [algorithmMessage_of_normalized memory words hready 79 (by decide)]
    exact normalize_pack _ _

theorem resultMemory_prefix_strip_garbage (memory : ByteArray) (words : Nat → UInt32)
    (left right : PairedLaneCryptoBridge.CryptoLane)
    (g : Nat → Nat) (hready : GarbageScheduleReady memory words g)
    (h13 : g 13 = 0) (h11 : g 11 = 0) :
    PairedTailTrace.resultMemory memory
      (TerminalRound.modifiedFrame memory (dirtyFrame memory
        (corePrefix77Chain.eval memory ⟨PairedLaneWordRound.packCrypto left right, 0⟩))) =
      PairedTailTrace.resultMemory memory
        (TerminalRound.modifiedFrame memory
          (PairedAllInlineCoreTrace.corePrefixChain.eval memory
            ⟨PairedLaneWordRound.packCrypto left right, 0⟩).frame) := by
  rw [← prefix78_eq]
  rw [corePrefix77Chain_eval]
  have hbound (k : Nat) (hk : k < 80) :
      g Crypto.Ripemd160.r[k]! % 2 ^ 32 = 0 ∧ g Crypto.Ripemd160.r[k]! < 2 ^ 96 ∧
        g Crypto.Ripemd160.rP[k]! / 2 ^ 32 < 2 ^ 64 := by
    have hb := algorithmIndex_bounds ⟨k, hk⟩
    have hlo := hready.1 Crypto.Ripemd160.r[k]! hb.1
    have hhi := hready.1 Crypto.Ripemd160.rP[k]! hb.2
    refine ⟨hlo.1, hlo.2, ?_⟩
    have : g Crypto.Ripemd160.rP[k]! < 2 ^ 96 := hhi.2
    omega
  rw [hoistedAlgorithmFold_crypto_garbage memory words
    (fun k => g Crypto.Ripemd160.r[k]!)
    (fun k => g Crypto.Ripemd160.rP[k]! / 2 ^ 32) 78 (by decide) left right
    (fun k hk => hbound k (by omega))
    (fun k hk => algorithmMessage_of_garbage_add memory words g hready k (by omega))]
  apply resultMemory_strip_eq
  · exact normalize_pack _ _
  · exact normalize_pack _ _
  · exact normalize_pack _ _
  · change normalize (bits (physicalKey 4)) = bits (physicalKey 4)
    decide
  · change normalize (bits (algorithmMessage memory 79)) = bits (algorithmMessage memory 79)
    have hlo : Crypto.Ripemd160.r[79]! = 13 := by decide
    have hhi : Crypto.Ripemd160.rP[79]! = 11 := by decide
    rw [algorithmMessage_of_garbage_add memory words g hready 79 (by decide)]
    simp only [hlo, hhi, h13, h11, Nat.zero_div, Nat.zero_mul, Nat.zero_add]
    have hz (v : UInt256) : UInt256.add v (UInt256.ofNat 0) = v := by
      apply bits_injective
      exact BitVec.add_zero (bits v)
    rw [hz]
    exact normalize_pack (words 13).toBitVec (words 11).toBitVec



#print axioms resultMemory_prefix_strip_garbage
#print axioms resultMemory_prefix_strip
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Semantics
