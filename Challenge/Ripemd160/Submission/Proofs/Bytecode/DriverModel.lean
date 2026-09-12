import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverTrace
open EvmSemantics EvmSemantics.EVM

def blockCount (input : ByteArray) : Nat :=
  Padding.paddedLength input.size / 64

def blockOffset (i : Nat) : Nat := i * 64

def blockOffsetWord (i : Nat) : UInt256 := UInt256.ofNat (blockOffset i)

def messageOffsetWord (i : Nat) : UInt256 :=
  UInt256.ofNat (Padding.messageOffset + blockOffset i)

theorem paddedLength_eq_blockCount (input : ByteArray) :
    Padding.paddedLength input.size = blockCount input * 64 := by
  exact Padding.paddedLength_eq_blocks input.size

/-- RIPEMD padding always contributes at least one block.  The driver may
therefore enter the compression call before performing its first completion
test. -/
theorem blockCount_pos (input : ByteArray) : 0 < blockCount input := by
  have hpad := Padding.paddedLength_pos input.size
  have heq := paddedLength_eq_blockCount input
  unfold blockCount at *
  omega


end Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverTrace
