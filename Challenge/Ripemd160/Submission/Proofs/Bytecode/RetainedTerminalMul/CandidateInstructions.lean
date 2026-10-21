import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_prefix0
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_prefix1
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_prefix2
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_prefix3
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_prefix4
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_prefix5
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_prefix6
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_prefix7
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_prefix8
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_prefix9
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_prefix10
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_prefix11
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_prefix12
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_prefix13
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_prefix14
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_prefix15
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_prefix16
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_prefix17
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_prefix18
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_prefix19
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_literal0
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Candidate_suffix0
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace RetainedBridge111.Candidate
open EvmSemantics EvmSemantics.EVM YulEvmCompiler

/-- Pure opcode rendering, not a decoder certificate. -/
def op (byte : UInt8) : Instr :=
  match Decode.opcodeOf byte with
  | some decoded => .op decoded
  | none => .op .INVALID

def prefixInstructions : List Instr := prefix0 ++ prefix1 ++ prefix2 ++ prefix3 ++ prefix4 ++ prefix5 ++ prefix6 ++ prefix7 ++ prefix8 ++ prefix9 ++ prefix10 ++ prefix11 ++ prefix12 ++ prefix13 ++ prefix14 ++ prefix15 ++ prefix16 ++ prefix17 ++ prefix18 ++ prefix19
theorem prefix_count : prefixInstructions.length = 5059 := by
  simp only [prefixInstructions, List.length_append, prefix0_count, prefix1_count, prefix2_count, prefix3_count, prefix4_count, prefix5_count, prefix6_count, prefix7_count, prefix8_count, prefix9_count, prefix10_count, prefix11_count, prefix12_count, prefix13_count, prefix14_count, prefix15_count, prefix16_count, prefix17_count, prefix18_count, prefix19_count]


def literalInstructions : List Instr := literal0
theorem literal_count : literalInstructions.length = 161 := by
  simp only [literalInstructions, List.length_append, literal0_count]


def suffixInstructions : List Instr := suffix0
theorem suffix_count : suffixInstructions.length = 228 := by
  simp only [suffixInstructions, List.length_append, suffix0_count]


/-- All 5448 typed instructions decoded from the supplied iter107 image.
This is NOT the installed root Artifact and carries no whole-image DataCert. -/
def instructions : List Instr := prefixInstructions ++ literalInstructions ++ suffixInstructions

theorem instruction_count : instructions.length = 5448 := by
  simp only [instructions, List.length_append, prefix_count, literal_count, suffix_count]

/-- Exact candidate instruction-vector slice, not just an assembly byte match. -/
theorem actual_data_slice :
    (instructions.drop 5059).take 161 = literalInstructions := by
  rw [instructions, List.append_assoc, ← prefix_count, List.drop_left]
  rw [← literal_count, List.take_left]

#print axioms actual_data_slice
end RetainedBridge111.Candidate
