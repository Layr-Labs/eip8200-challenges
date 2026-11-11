import Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentProgram
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasRoute
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
namespace CycleSubmission.FixedDispatch
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel CycleSubmission.SharedStackArgs

def exponent : UInt256 := UInt256.ofNat 21888242871839275222246405745257275088696311157297823662689037894645226208581
def guardProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup dA1), .push 32 exponent, .op .XOR, .push 2 717, .op .JUMPI]
def frame (s : State) (pc : Nat) (m e b : UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat pc, stack := [m,e,b] ++ rest}
 theorem run_guard (s : State) (m e b : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 590) (hrun : s.halt = .Running)
    (hj : Decode.isValidJumpDest s.executionEnv.code 717 = true) :
    runInstructions guardProgram (frame s 10943 m e b rest) =
      some (frame s (if (UInt256.xor exponent e).toNat = 0 then 10983 else 717) m e b rest) := by
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  by_cases he : (UInt256.xor exponent e).toNat = 0 <;>
    simp [guardProgram, frame, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      h3,h4,h5,hrun,hj,he, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod]
 theorem xor_zero_iff (e : UInt256) : (UInt256.xor exponent e).toNat = 0 ↔ e = exponent := by
  constructor
  · intro h
    have hw : UInt256.xor exponent e = UInt256.ofNat 0 := Challenge.EvmProof.Word.word_ext h
    exact ((WindowGuardLogic.wordXor_eq_zero_iff exponent e).mp hw).symm
  · intro h
    subst e
    exact congrArg UInt256.toNat ((WindowGuardLogic.wordXor_eq_zero_iff exponent exponent).mpr rfl)
 theorem value_zero (b : UInt256) : HistoricalSearch.FixedExponent.value b (UInt256.ofNat 0) = UInt256.ofNat 0 := by
  simp only [HistoricalSearch.FixedExponent.value, UInt256.mulMod]
  rfl
theorem value_spec (input : ByteArray) (hmatch : WindowTwentyOneInput.Matches input)
    (he : WindowTwentyOneInput.exponentWord input = exponent) :
    Precompile.natToBytes
      (HistoricalSearch.FixedExponent.value (WindowTwentyOneInput.baseWord input)
        (WindowTwentyOneInput.modulusWord input)).toNat 32 = Challenge.Modexp.spec input := by
  have hE : exponent.toNat = 21888242871839275222246405745257275088696311157297823662689037894645226208581 := by decide
  have heval := congrArg UInt256.toNat he
  rw [WindowTwentyOneInput.exponentWord_toNat, hE] at heval
  rw [WindowTwentyOneInput.spec_eq input hmatch]
  apply congrArg (fun z : Nat => Precompile.natToBytes z 32)
  rw [Challenge.Modexp.Submission.Proofs.Algorithm.modPow_eq]
  by_cases hm : WindowTwentyOneInput.modulusValue input = 0
  · rw [if_pos hm]
    have hmw : WindowTwentyOneInput.modulusWord input = UInt256.ofNat 0 := by
      apply Challenge.EvmProof.Word.word_ext
      rw [WindowTwentyOneInput.modulusWord_toNat, hm]
      rfl
    rw [hmw, value_zero]
    rfl
  · rw [if_neg hm, HistoricalSearch.FixedExponent.value_toNat _ _
      (by rw [WindowTwentyOneInput.modulusWord_toNat]; exact Nat.pos_of_ne_zero hm),
      WindowTwentyOneInput.baseWord_toNat_of_le input hmatch.1,
      WindowTwentyOneInput.modulusWord_toNat, heval]

end CycleSubmission.FixedDispatch

