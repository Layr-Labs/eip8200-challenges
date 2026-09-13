import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardAppendBridge
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open DirectGuard KnownInputCompactState

def pairedEntry (input : ByteArray) : State :=
  { DirectGuard.loopState input 0 with pc := UInt256.ofNat 5231 }

def pairedExit (input : ByteArray) : State :=
  { DirectGuard.loopExitState input with pc := UInt256.ofNat 67 }

def entryPath : List DirectGuard.Located :=
  [DirectGuard.opAt 34 .JUMPDEST, DirectGuard.pushAt 35 2 5231,
   DirectGuard.opAt 36 .JUMP]

def exitPath : List DirectGuard.Located := [DirectGuard.opAt 48 .JUMPDEST]

@[simp] theorem pc35 : Artifact.submissionArtifact.instructionPC 35 = 50 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc36 : Artifact.submissionArtifact.instructionPC 36 = 53 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc48 : Artifact.submissionArtifact.instructionPC 48 = 67 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

def gasSteps_entry (input : ByteArray)
    (hdest : Decode.isValidJumpDest submissionBytecode 5231 = true) :
    GasSteps (DirectGuard.loopState input 0) (pairedEntry input) := by
  let stk := [UInt256.ofNat 32, KnownInputCompactState.loopAcc input 0, referenceWord input]
  change GasSteps (stG input 49 stk) (stG input 5231 stk)
  have step0 := soundG (opAt 34 .JUMPDEST)
    (blockOf _ (pcFactG input 34 49 stk (by norm_num) pc2828)
      (stepG_jumpdest input 49 stk (by simp [stk]) (by norm_num)))
  have step1 := soundG (pushAt 35 2 (UInt256.ofNat 5231))
    (blockOf _ (pcFactG input 35 50 stk (by norm_num) pc35)
      (stepG_push input 50 2 (UInt256.ofNat 5231) stk
        (by simp [stk]) (by decide) (by decide) (by norm_num)))
  have step2 := soundG (opAt 36 .JUMP)
    (blockOf _ (pcFactG input 36 53 (UInt256.ofNat 5231 :: stk) (by norm_num) pc36)
      (stepG_jump input 53 5231 stk (by simp [stk]) (by norm_num) hdest))
  exact step0.trans (step1.trans step2)

def gasSteps_exit (input : ByteArray) :
    GasSteps (pairedExit input) (DirectGuard.loopExitState input) := by
  let stk := [UInt256.ofNat 992, KnownInputCompactState.loopAcc input 30, referenceWord input]
  change GasSteps (stG input 67 stk) (stG input 68 stk)
  exact soundG (opAt 48 .JUMPDEST)
    (blockOf _ (pcFactG input 48 67 stk (by norm_num) pc48)
      (stepG_jumpdest input 67 stk (by simp [stk]) (by norm_num)))

#print axioms gasSteps_entry
#print axioms gasSteps_exit
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardAppendBridge
