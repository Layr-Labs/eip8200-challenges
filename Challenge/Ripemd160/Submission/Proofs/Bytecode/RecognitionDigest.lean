import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigest1
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigest31
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigest32
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigest55
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigest64
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigest65
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigest119
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigestShort
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigest63
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned256Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedGuardSpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionAccumulator

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigest
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open RecognitionAccumulator

def paddedDigestWord (n : Nat) : UInt256 :=
  if n = 1 then RecognitionDigest1.paddedDigestWord else
  if n = 31 then RecognitionDigest31.paddedDigestWord else
  if n = 32 then RecognitionDigest32.paddedDigestWord else
  if n = 55 then RecognitionDigest55.paddedDigestWord else
  if n = 256 then Patterned256Digest.paddedDigestWord else
  if n = 376 then Prefix256Digest.paddedDigestWord else
  if n = 1000 then PatternedDigest.paddedDigestWord else
  if n = 56 then 0xd8e2e84bad19fc85dbadb55fa5467631ce141503 else
  if n = 120 then 0x4de20b6b1fb2af442370c40e53a50aca360fc3bc else
  if n = 64 then 0x8a14b0c89287b39b1a2f73aa79a1ce95b04e7817 else
  if n = 65 then 0x475272ba467ca6716dbb1c19a84de355f065829a else
  if n = 128 then 0x28dfaf14ed9953f49c7abb561308d0c64bc4c179 else
  if n = 63 then 0x37880ee5e2e821e0540bb146e33b37342316e7ed else
  0x2b9567d684dc89cd54620e46029f5bda0ecab787

def paddedDigest (n : Nat) : ByteArray :=
  if n = 1 then RecognitionDigest1.paddedDigest else
  if n = 31 then RecognitionDigest31.paddedDigest else
  if n = 32 then RecognitionDigest32.paddedDigest else
  if n = 55 then RecognitionDigest55.paddedDigest else
  if n = 256 then Patterned256Digest.paddedDigest else
  if n = 376 then Prefix256Digest.paddedDigest else
  if n = 1000 then PatternedDigest.paddedDigest else
  if n = 56 then RecognitionDigestShort.paddedDigest56 else
  if n = 120 then RecognitionDigestShort.paddedDigest120 else
  if n = 64 then RecognitionDigest64.paddedDigest else
  if n = 65 then RecognitionDigest65.paddedDigest else
  if n = 128 then Patterned128Digest.paddedDigest else
  if n = 63 then RecognitionDigest63.paddedDigest else
  RecognitionDigest119.paddedDigest

theorem spec_reference (n : Nat) (hn : Allowed n) :
    spec (reference n) = paddedDigest n := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h := RecognitionDigest1.spec_data
    have he : reference 1 = RecognitionDigest1.data := by decide
    have hp : paddedDigest 1 = RecognitionDigest1.paddedDigest := by decide
    exact (congrArg spec he).trans (h.trans hp.symm)
  · have h := RecognitionDigest31.spec_data
    have he : reference 31 = RecognitionDigest31.data := by decide
    have hp : paddedDigest 31 = RecognitionDigest31.paddedDigest := by decide
    exact (congrArg spec he).trans (h.trans hp.symm)
  · have h := RecognitionDigest32.spec_data
    have he : reference 32 = RecognitionDigest32.data := by decide
    have hp : paddedDigest 32 = RecognitionDigest32.paddedDigest := by decide
    exact (congrArg spec he).trans (h.trans hp.symm)
  · have h := RecognitionDigest55.spec_data
    have he : reference 55 = RecognitionDigest55.data := by decide
    have hp : paddedDigest 55 = RecognitionDigest55.paddedDigest := by decide
    exact (congrArg spec he).trans (h.trans hp.symm)
  · have h := RecognitionDigestShort.spec56
    have he : reference 56 = RecognitionDigestShort.data56 := by decide
    have hp : paddedDigest 56 = RecognitionDigestShort.paddedDigest56 := by decide
    exact (congrArg spec he).trans (h.trans hp.symm)
  · have h := RecognitionDigest63.spec_data_eq
    have he : reference 63 = RecognitionDigest63.data63 := by decide
    have hp : paddedDigest 63 = RecognitionDigest63.paddedDigest := by decide
    exact (congrArg spec he).trans (h.trans hp.symm)
  · have h := RecognitionDigest64.spec_data
    have he : reference 64 = RecognitionDigest64.data := by decide
    have hp : paddedDigest 64 = RecognitionDigest64.paddedDigest := by decide
    exact (congrArg spec he).trans (h.trans hp.symm)
  · have h := RecognitionDigest65.spec_data
    have he : reference 65 = RecognitionDigest65.data := by decide
    have hp : paddedDigest 65 = RecognitionDigest65.paddedDigest := by decide
    exact (congrArg spec he).trans (h.trans hp.symm)
  · have h := RecognitionDigest119.spec_data
    have he : reference 119 = RecognitionDigest119.data := by decide
    have hp : paddedDigest 119 = RecognitionDigest119.paddedDigest := by decide
    exact (congrArg spec he).trans (h.trans hp.symm)
  · have h := RecognitionDigestShort.spec120
    have he : reference 120 = RecognitionDigestShort.data120 := by decide
    have hp : paddedDigest 120 = RecognitionDigestShort.paddedDigest120 := by decide
    exact (congrArg spec he).trans (h.trans hp.symm)
  · have h := Patterned128Digest.spec_data_eq
    have he : reference 128 = Patterned128Data.data := by rfl
    have hp : paddedDigest 128 = Patterned128Digest.paddedDigest := by decide
    exact (congrArg spec he).trans (h.trans hp.symm)
  · have h := Patterned256Digest.spec_data_eq
    have he : reference 256 = Patterned256Data.data := by rfl
    have hp : paddedDigest 256 = Patterned256Digest.paddedDigest := by decide
    exact (congrArg spec he).trans (h.trans hp.symm)
  · have h := Prefix256Digest.spec_data_eq
    have he : reference 376 = Prefix256Data.data := by rfl
    have hp : paddedDigest 376 = Prefix256Digest.paddedDigest := by decide
    exact (congrArg spec he).trans (h.trans hp.symm)
  · have h := PatternedGuardSpec.spec_patternedInput_eq
    have he : reference 1000 = PatternedInputData.patternedInput := by simp [reference, ← PatternedInputData.patternedInput_size]
    have hp : paddedDigest 1000 = PatternedDigest.paddedDigest := by decide
    exact (congrArg spec he).trans (h.trans hp.symm)

theorem accepted_spec (input : ByteArray) (n : Nat) (hn : Allowed n)
    (hsize : input.size = n) (hzero : resultAcc input n = 0) :
    spec input = paddedDigest n := by
  rw [(resultAcc_zero_iff input n hn hsize).mp hzero]
  exact spec_reference n hn

def payload : ByteArray := ByteArray.mk #[0xdb, 0x4d, 0x90, 0xb3, 0xbe, 0x82, 0x8e, 0xa7, 0xce, 0xd8, 0xd8, 0x79, 0xdb, 0xce, 0xa2, 0xc1, 0xd5, 0xfe, 0x20, 0x7f, 0x73, 0xd8, 0xe2, 0xe8, 0x4b, 0xad, 0x19, 0xfc, 0x85, 0xdb, 0xad, 0xb5, 0x5f, 0xa5, 0x46, 0x76, 0x31, 0xce, 0x14, 0x15, 0x3, 0x73, 0x5b, 0xe9, 0x25, 0x9e, 0x94, 0x78, 0x20, 0x2d, 0xd0, 0xc1, 0xf4, 0xeb, 0xc, 0x4e, 0xd0, 0x44, 0x2d, 0xbe, 0xb2, 0xcd, 0x73, 0x47, 0x52, 0x72, 0xba, 0x46, 0x7c, 0xa6, 0x71, 0x6d, 0xbb, 0x1c, 0x19, 0xa8, 0x4d, 0xe3, 0x55, 0xf0, 0x65, 0x82, 0x9a, 0x73, 0x37, 0x88, 0xe, 0xe5, 0xe2, 0xe8, 0x21, 0xe0, 0x54, 0xb, 0xb1, 0x46, 0xe3, 0x3b, 0x37, 0x34, 0x23, 0x16, 0xe7, 0xed, 0x73, 0x28, 0xdf, 0xaf, 0x14, 0xed, 0x99, 0x53, 0xf4, 0x9c, 0x7a, 0xbb, 0x56, 0x13, 0x8, 0xd0, 0xc6, 0x4b, 0xc4, 0xc1, 0x79, 0x73, 0x1a, 0xcf, 0x41, 0xb0, 0x9f, 0x87, 0xac, 0xc9, 0x83, 0xc2, 0xa0, 0x43, 0xf5, 0x4, 0x4c, 0x8f, 0x71, 0xc5, 0x2d, 0xbd, 0x73, 0x86, 0x3c, 0x59, 0x85, 0x88, 0xbd, 0x72, 0xa4, 0xba, 0xbf, 0x36, 0xc6, 0xbb, 0x1, 0xf2, 0x7b, 0xbd, 0xc0, 0xec, 0xd4, 0x73, 0xf6, 0xce, 0xa8, 0xd2, 0xa4, 0x91, 0xf5, 0xdc, 0x27, 0x6a, 0xa1, 0xf7, 0x61, 0x8b, 0x4d, 0x7a, 0x55, 0x2e, 0xc4, 0xad, 0x73, 0xc6, 0xc5, 0x3c, 0x46, 0xcf, 0x8, 0xde, 0x1c, 0x53, 0x75, 0xb1, 0x5a, 0xf8, 0x67, 0x6a, 0x2d, 0x32, 0xef, 0x52, 0x8a, 0x73, 0x8a, 0x14, 0xb0, 0xc8, 0x92, 0x87, 0xb3, 0x9b, 0x1a, 0x2f, 0x73, 0xaa, 0x79, 0xa1, 0xce, 0x95, 0xb0, 0x4e, 0x78, 0x17, 0x73, 0x9, 0x6, 0xf7, 0x77, 0x41, 0x5, 0xd3, 0x64, 0x6, 0x50, 0x54, 0x1c, 0x2e, 0x7b, 0xc1, 0x9b, 0xfe, 0x9b, 0x51, 0x49, 0x73, 0x4d, 0xe2, 0xb, 0x6b, 0x1f, 0xb2, 0xaf, 0x44, 0x23, 0x70, 0xc4, 0xe, 0x53, 0xa5, 0xa, 0xca, 0x36, 0xf, 0xc3, 0xbc, 0x73, 0x2b, 0x95, 0x67, 0xd6, 0x84, 0xdc, 0x89, 0xcd, 0x54, 0x62, 0xe, 0x46, 0x2, 0x9f, 0x5b, 0xda, 0xe, 0xca, 0xb7, 0x87]

theorem payload_read (n : Nat) (hn : Allowed n) :
    MachineState.writeBytes ByteArray.empty
      (MachineState.readPadded payload (21 * ((203142 / n) % 14)) 20) 12 = paddedDigest n := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold MachineState.writeBytes
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure]
    decide

#print axioms spec_reference
#print axioms accepted_spec
#print axioms payload_read
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigest
