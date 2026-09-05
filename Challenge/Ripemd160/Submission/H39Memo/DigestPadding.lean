import Challenge.Ripemd160.Submission.H39Memo.DigestBridge

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open Proofs.Bytecode

/-- Expand only the eight length bytes; keep the message buffer opaque. -/
theorem lengthBytes_expand (input : ByteArray) :
    Padding.lengthBytes input = ByteArray.mk #[
      UInt8.ofNat (((input.size * 8) / 2 ^ 0) % 256),
      UInt8.ofNat (((input.size * 8) / 2 ^ 8) % 256),
      UInt8.ofNat (((input.size * 8) / 2 ^ 16) % 256),
      UInt8.ofNat (((input.size * 8) / 2 ^ 24) % 256),
      UInt8.ofNat (((input.size * 8) / 2 ^ 32) % 256),
      UInt8.ofNat (((input.size * 8) / 2 ^ 40) % 256),
      UInt8.ofNat (((input.size * 8) / 2 ^ 48) % 256),
      UInt8.ofNat (((input.size * 8) / 2 ^ 56) % 256)]
    := by
  simp only [Padding.lengthBytes, ByteArray.ofFn_succ, ByteArray.ofFn_zero]
  rfl

end Challenge.Ripemd160.Submission.H39Memo

