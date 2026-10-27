import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreEntry
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 500000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreAnchor
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open HoistedStoreSites

theorem valid_data : Decode.isValidJumpDest HoistedStoreArtifact.code 9394 = true := by
  have hp : HoistedStoreArtifact.artifact.instructionPC 6537 = 9394 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := HoistedStoreArtifact.artifact.isValidJumpDest_index 6537 (by rfl)
  rw [hp] at h
  exact h

def taken (s : State) (rho : List UInt256) (e : Env s) (hs : rho.length ≤ 976)
    (hne : Low64RepeatMath.condition s.executionEnv.calldata ≠ 0) :
    GasSteps {s with pc := UInt256.ofNat 21, stack := rho}
      {s with pc := UInt256.ofNat 9394, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} :=
  HoistedStoreEntry.lift .anchor s _ e rho
    (HoistedStoreAnchorRaw.run_anchor_taken s rho (by omega) e.run hne
      (by rw [e.code]; exact valid_data))

#print axioms taken
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreAnchor
