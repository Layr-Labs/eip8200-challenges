import Challenge.Ripemd160.Submission.Local20261028.CoreGas
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.ControlSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof StackRoundTemplate
def copyTemplate : List Instr := [.op .JUMPDEST, .push ⟨30, by decide⟩ (UInt256.ofNat 1766820105243087041267848467410591083712559083657179364930612997358944255), .push ⟨31, by decide⟩ (UInt256.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455), .op .CALLDATASIZE, .push ⟨0, by decide⟩ (UInt256.ofNat 0), .push ⟨2, by decide⟩ (UInt256.ofNat 1056), .op .CALLDATACOPY]
def copySite : GenericRoundSite CandidateArtifact.artifact .Osaka copyTemplate :=
  StackSiteBuilder.ofSlice copyTemplate 133 (by rfl)
    (by change 133 + copyTemplate.length ≤ CandidateArtifact.instructions.length
        rw [CandidateArtifact.instruction_count]; decide +kernel)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check _ (by decide +kernel)) (by decide +kernel)
theorem copy_pc : copySite.startPC = UInt256.ofNat 245 := by
  change UInt256.ofNat (CandidateArtifact.artifact.instructionPC 133) = UInt256.ofNat 245
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel
def frameTemplate : List Instr := [.op .CALLDATASIZE, .push ⟨2, by decide⟩ (UInt256.ofNat 1056), .push ⟨4, by decide⟩ (UInt256.ofNat 1732584193), .push ⟨4, by decide⟩ (UInt256.ofNat 4023233417), .push ⟨4, by decide⟩ (UInt256.ofNat 2562383102), .push ⟨4, by decide⟩ (UInt256.ofNat 271733878), .push ⟨4, by decide⟩ (UInt256.ofNat 3285377520), .push ⟨13, by decide⟩ (UInt256.ofNat 475368975196266490007815979009), .push ⟨13, by decide⟩ (UInt256.ofNat 1109194275457955143345843994625), .push ⟨27, by decide⟩ (UInt256.ofNat 822752278660603021099785336477205875632903651089438293180284928), .push ⟨27, by decide⟩ (UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324096), .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), .push ⟨13, by decide⟩ (UInt256.ofNat 158456325065422163343096938498)]
def frameSite : GenericRoundSite CandidateArtifact.artifact .Osaka frameTemplate :=
  StackSiteBuilder.ofSlice frameTemplate 140 (by rfl)
    (by change 140 + frameTemplate.length ≤ CandidateArtifact.instructions.length
        rw [CandidateArtifact.instruction_count]; decide +kernel)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check _ (by decide +kernel)) (by decide +kernel)
theorem frame_pc : frameSite.startPC = UInt256.ofNat 315 := by
  change UInt256.ofNat (CandidateArtifact.artifact.instructionPC 140) = UInt256.ofNat 315
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel
def alignTemplate : List Instr := [.push ⟨8, by decide⟩ (UInt256.ofNat 18446744073709551423), .op .CALLDATASIZE, .op .AND, .push ⟨1, by decide⟩ (UInt256.ofNat 143), .op .JUMPI]
def alignSite : GenericRoundSite CandidateArtifact.artifact .Osaka alignTemplate :=
  StackSiteBuilder.ofSlice alignTemplate 153 (by rfl)
    (by change 153 + alignTemplate.length ≤ CandidateArtifact.instructions.length
        rw [CandidateArtifact.instruction_count]; decide +kernel)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check _ (by decide +kernel)) (by decide +kernel)
theorem align_pc : alignSite.startPC = UInt256.ofNat 447 := by
  change UInt256.ofNat (CandidateArtifact.artifact.instructionPC 153) = UInt256.ofNat 447
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel
def specialTemplate : List Instr := [.op .JUMPDEST, .push ⟨2, by decide⟩ (UInt256.ofNat 9949), .op (.Swap ⟨12, by decide⟩), .push ⟨1, by decide⟩ (UInt256.ofNat 32), .op .EQ, .push ⟨29, by decide⟩ (UInt256.ofNat 3450873173395281893717377931138512726225554486085193277582361623527424), .push ⟨1, by decide⟩ (UInt256.ofNat 162), .op .MSTORE, .push ⟨2, by decide⟩ (UInt256.ofNat 10108), .op .JUMPI]
def specialSite : GenericRoundSite CandidateArtifact.artifact .Osaka specialTemplate :=
  StackSiteBuilder.ofSlice specialTemplate 81 (by rfl)
    (by change 81 + specialTemplate.length ≤ CandidateArtifact.instructions.length
        rw [CandidateArtifact.instruction_count]; decide +kernel)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check _ (by decide +kernel)) (by decide +kernel)
theorem special_pc : specialSite.startPC = UInt256.ofNat 143 := by
  change UInt256.ofNat (CandidateArtifact.artifact.instructionPC 81) = UInt256.ofNat 143
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel
def dispatchTemplate : List Instr := [.op (.Swap ⟨12, by decide⟩), .op .JUMP]
def dispatchSite : GenericRoundSite CandidateArtifact.artifact .Osaka dispatchTemplate :=
  StackSiteBuilder.ofSlice dispatchTemplate 3345 (by rfl)
    (by change 3345 + dispatchTemplate.length ≤ CandidateArtifact.instructions.length
        rw [CandidateArtifact.instruction_count]; decide +kernel)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check _ (by decide +kernel)) (by decide +kernel)
theorem dispatch_pc : dispatchSite.startPC = UInt256.ofNat 4578 := by
  change UInt256.ofNat (CandidateArtifact.artifact.instructionPC 3345) = UInt256.ofNat 4578
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel
theorem valid143 : Decode.isValidJumpDest CandidateArtifact.artifact.code 143 = true := by
  have hpc : CandidateArtifact.artifact.instructionPC 81 = 143 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide +kernel
  have h := CandidateArtifact.artifact.isValidJumpDest_index 81 (by rfl)
  rw [hpc] at h
  exact h
#print axioms valid143
theorem valid9949 : Decode.isValidJumpDest CandidateArtifact.artifact.code 9949 = true := by
  have hpc : CandidateArtifact.artifact.instructionPC 6773 = 9949 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide +kernel
  have h := CandidateArtifact.artifact.isValidJumpDest_index 6773 (by rfl)
  rw [hpc] at h
  exact h
#print axioms valid9949
theorem valid10108 : Decode.isValidJumpDest CandidateArtifact.artifact.code 10108 = true := by
  have hpc : CandidateArtifact.artifact.instructionPC 6896 = 10108 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide +kernel
  have h := CandidateArtifact.artifact.isValidJumpDest_index 6896 (by rfl)
  rw [hpc] at h
  exact h
#print axioms valid10108
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.ControlSites
