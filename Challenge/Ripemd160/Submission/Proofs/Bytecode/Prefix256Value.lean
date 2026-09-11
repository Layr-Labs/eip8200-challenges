import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned256Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Value

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof StackRoundTrace

def digest1000 : UInt256 :=
  UInt256.ofNat 0x863c598588bd72a4babf36c6bb01f27bbdc0ecd4

def digestDifference : UInt256 :=
  UInt256.ofNat 0x70f2f1572c2c87789dd59731da8abf01e8ee2879

def digestDifference256 : UInt256 := UInt256.ofNat 370937159678419008737987698595703314930111331934

def selected (input : ByteArray) : UInt256 :=
  UInt256.xor digest1000
    (UInt256.xor (digestDifference256 * UInt256.eq 256 (UInt256.ofNat input.size))
      (digestDifference * UInt256.eq 376 (UInt256.ofNat input.size)))

theorem selected_256 (input : ByteArray) (hsize : input.size = 376) :
    selected input = Prefix256Digest.paddedDigestWord := by
  simp only [selected, hsize]
  decide

theorem selected_1000 (input : ByteArray) (hsize : input.size = 1000) :
    selected input = PatternedDigest.paddedDigestWord := by
  simp only [selected, hsize]
  decide

theorem selected_short (input : ByteArray) (hsize : input.size = 256) :
    selected input = Patterned256Digest.paddedDigestWord := by
  simp only [selected, hsize]
  decide

def template : List Instr :=
  [.op .CALLDATASIZE, .op .CALLDATASIZE,
   .push ⟨2, by decide⟩ 376, .op .EQ,
   .push ⟨20, by decide⟩ digestDifference, .op .MUL,
   .op (.Swap ⟨0, by decide⟩), .push ⟨2, by decide⟩ 256, .op .EQ,
   .push ⟨20, by decide⟩ digestDifference256, .op .MUL, .op .XOR,
   .push ⟨20, by decide⟩ digest1000, .op .XOR]

theorem template_length : template.length = 14 := rfl

theorem template_bytes : (template.map Instr.size).sum = 78 := by decide

set_option linter.unusedSimpArgs false in
theorem run_template (s : State) (pc : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1020) (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := pc, stack := rest} =
      some {s with pc := pcAfter pc template, stack := selected s.executionEnv.calldata :: rest} := by
  have hcap (n : Nat) (hn : n ≤ 4) : rest.length + n < 1024 := by omega
  have h0 : rest.length < 1024 := by omega
  simp [template, selected, runInstrSeq, Stepper.runInstr, pcAfter,
    hrun, hcap, h0, List.exchange, List.length_cons, Nat.add_assoc, UInt256.succ,
    Instr.size, Word.literal_eq_ofNat, Word.word_toNat_ofNat,
    Word.ofNat_add_mod]
  constructor

#print axioms selected_256
#print axioms selected_1000
#print axioms run_template

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Value
