import Challenge.Modexp.Submission.Proofs.Fast.SquareRowFusedSteps

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareRow

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached SquareModel
theorem run_B (s : State) (tb x P hd w3 ent w5 M : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      ((1600 : UInt256) + P).toNat 32) = s.activeWords)
    (hjump : Decode.isValidJumpDest s.executionEnv.code ent.toNat = true) :
    runInstructions programB
      { s with pc := UInt256.ofNat 4717,
               stack := tb :: x :: P :: hd :: w3 :: ent :: w5 :: M :: rest } =
    some { s with pc := ent,
                  stack := (UInt256.lt (loOf x tb + MachineState.readWord s.memory ((1600 : UInt256) + P).toNat)
                      (loOf x tb) + hiOf x tb M) ::
                    ((x + tb) + x) :: P :: hd :: w3 :: (ent + UInt256.ofNat 38) :: w5 :: M :: rest,
                  memory := MachineState.writeBytes s.memory
                    (Data.Bytes.natToBytesPadded
                      (loOf x tb + MachineState.readWord s.memory ((1600 : UInt256) + P).toNat).toNat 32)
                    ((1600 : UInt256) + P).toNat } := by
  have h1 := run_B1 s tb x P hd w3 ent w5 M rest (by omega)
  have h23 := run_B23 s (UInt256.mulMod x (x + tb) M) x (x + tb) ((x + tb) + x) P
    (hd :: w3 :: ent :: w5 :: M :: rest)
    (by simp only [List.length_cons]; omega) hact
  have h4 := run_B4
    { s with memory := (MachineState.writeBytes s.memory
        (Data.Bytes.natToBytesPadded
          (loOf x tb + MachineState.readWord s.memory ((1600 : UInt256) + P).toNat).toNat 32)
        ((1600 : UInt256) + P).toNat) }
    (UInt256.lt (loOf x tb + MachineState.readWord s.memory ((1600 : UInt256) + P).toNat)
      (loOf x tb) + hiOf x tb M) ((x + tb) + x) P hd w3 ent (w5 :: M :: rest)
    (by simp only [List.length_cons]; omega) hjump
  exact runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _ h1 h23) h4


end Challenge.Modexp.Submission.Proofs.Fast.SquareRow
