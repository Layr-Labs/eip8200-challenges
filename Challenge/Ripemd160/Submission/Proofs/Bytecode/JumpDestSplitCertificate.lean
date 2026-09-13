import Challenge.Ripemd160.Submission.Proofs.Bytecode.JumpDestSuffixWalk

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.JumpDestSplitCertificate

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Ripemd160
open Challenge.Ripemd160.Submission.Proofs.Bytecode

abbrev artifact := Artifact.submissionArtifact

theorem prefix_length :
    (assembleBytes artifact.instructions).length = 4951 := by
  rw [← ArtifactByteLength.byteLength_eq_assemble]
  rfl

theorem data_length : artifact.data.length = 313 := by
  rfl

theorem data_take_length : (artifact.data.take 280).length = 280 := by
  rw [List.length_take, data_length]
  decide

theorem data_drop_length : (artifact.data.drop 280).length = 33 := by
  rw [List.length_drop, data_length]

theorem data_drop_nonempty : artifact.data.drop 280 ≠ [] := by
  intro h
  have hd := data_drop_length
  rw [h] at hd
  simp at hd

theorem data_suffix_decision :
    Decode.validJumpDestFrom
      (mkCode (artifact.data.take 280 ++ artifact.data.drop 280))
      280 0 1378 = true := by
  rw [List.take_append_drop]
  decide

theorem valid_5231_split :
    Decode.isValidJumpDest submissionBytecode 5231 = true := by
  have hcode :
      mkCode (assembleBytes artifact.instructions ++ artifact.data) =
        submissionBytecode := artifact.assembly_eq
  have hsize : submissionBytecode.size = 5264 := by
    simp
  have hpre : (assembleBytes artifact.instructions).length = 4951 :=
    prefix_length
  have hdata_take : (artifact.data.take 280).length = 280 :=
    data_take_length
  have hi : artifact.instructions.length = 3887 := by
    change Artifact.submissionInstructions.length = 3887
    exact Artifact.referenceInstructions_count
  have hp := JumpDestSuffixWalk.typed_prefix_shift artifact.instructions [] artifact.data
      5231 5265
      (by simp only [List.length_nil, Nat.zero_add, hpre]; omega)
      (by omega)
  have hs := JumpDestSuffixWalk.valid_shift (assembleBytes artifact.instructions)
      (artifact.data.take 280) (artifact.data.drop 280) 5231
      data_drop_nonempty (5265 - artifact.instructions.length) 0
      (by omega)
      (by omega)
  have hfuel : 5265 - artifact.instructions.length = 1378 := by omega
  unfold Decode.isValidJumpDest
  rw [hsize, ← hcode]
  calc
    Decode.validJumpDestFrom
        (mkCode (assembleBytes artifact.instructions ++ artifact.data))
        5231 0 5265 =
      Decode.validJumpDestFrom
        (mkCode (assembleBytes artifact.instructions ++ artifact.data))
        5231 (assembleBytes artifact.instructions).length
          (5265 - artifact.instructions.length) := by
            simpa [artifact, List.append_assoc] using hp
    _ = Decode.validJumpDestFrom
        (mkCode (assembleBytes artifact.instructions ++
          artifact.data.take 280 ++ artifact.data.drop 280))
        5231 (assembleBytes artifact.instructions).length
          (5265 - artifact.instructions.length) := by
            have hcode_split :
                mkCode (assembleBytes artifact.instructions ++ artifact.data) =
                  mkCode (assembleBytes artifact.instructions ++
                    artifact.data.take 280 ++ artifact.data.drop 280) := by
              congr 1
            exact congrArg
              (fun c => Decode.validJumpDestFrom c 5231
                (assembleBytes artifact.instructions).length
                (5265 - artifact.instructions.length)) hcode_split
    _ = Decode.validJumpDestFrom
        (mkCode (artifact.data.take 280 ++ artifact.data.drop 280))
        280 0 (5265 - artifact.instructions.length) := by
            simpa [hdata_take, List.append_assoc] using hs
    _ = true := by
      rw [hfuel]
      exact data_suffix_decision

end Challenge.Ripemd160.Submission.Proofs.Bytecode.JumpDestSplitCertificate
