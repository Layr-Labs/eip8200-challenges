import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Memory
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.EmptySpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.EmptyFastPath

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Ripemd160

def emptyInput : ByteArray := ByteArray.empty

@[simp] theorem emptyInput_size : emptyInput.size = 0 := by rfl

theorem empty_fits : CalldataFits emptyInput := by
  unfold CalldataFits
  simp [emptyInput]

def emptyFinal : State :=
  { Execution.atPC emptyInput 0x1361 with
    stack := []
    halt := .Returned
    hReturn :=
      MachineState.readPadded
        (MachineState.writeBytes ByteArray.empty EmptySpec.emptyOutput 0) 0 32
    memory := MachineState.writeBytes ByteArray.empty EmptySpec.emptyOutput 0
    activeWords := UInt256.ofNat 1 }

private theorem digest_padded_eq :
    EvmSemantics.Data.Bytes.natToBytesPadded Execution.emptyDigestNat 32 =
      EmptySpec.emptyOutput := by
  rw [Challenge.EvmProof.Memory.natToBytesPadded_eq_natToBE]
  unfold Execution.emptyDigestNat EmptySpec.emptyOutput
  decide

private theorem digest_lt : Execution.emptyDigestNat < 256 ^ 20 := by
  unfold Execution.emptyDigestNat
  decide

private theorem hfalse_empty :
    (UInt256.ofNat 0).isTrue = false := by
  decide

private theorem hmod_empty :
    Execution.emptyDigestNat % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      Execution.emptyDigestNat := by
  apply Nat.mod_eq_of_lt
  unfold Execution.emptyDigestNat
  decide

def gasSteps_dispatch_empty :
    Challenge.EvmProof.GasSteps (Execution.atPC emptyInput 0x1341)
      (Execution.atPC emptyInput 0x1347) := by
  have hfalse : (UInt256.ofNat 0).isTrue = false := hfalse_empty
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock Execution.path_dispatch
      (Execution.atPC emptyInput 0x1341) =
      some (Execution.atPC emptyInput 0x1347) := by
    simp [Execution.path_dispatch,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Execution.atPC, initialState, emptyInput,
      hfalse]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka Execution.path_dispatch
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def s1_push20 : State :=
  { Execution.atPC emptyInput 0x135c with
    stack := [UInt256.ofNat Execution.emptyDigestNat] }

def s2_push0 : State :=
  { Execution.atPC emptyInput 0x135d with
    stack := [UInt256.ofNat 0, UInt256.ofNat Execution.emptyDigestNat] }

def mstoreState : State :=
  { Execution.atPC emptyInput 0x135e with
    stack := []
    memory := MachineState.writeBytes ByteArray.empty EmptySpec.emptyOutput 0
    activeWords := UInt256.ofNat 1 }

def s4_push1 : State :=
  { mstoreState with
    pc := UInt256.ofNat 0x1360
    stack := [UInt256.ofNat 32] }

def s5_push0 : State :=
  { s4_push1 with
    pc := UInt256.ofNat 0x1361
    stack := [UInt256.ofNat 0, UInt256.ofNat 32] }

private def path_2876 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  Execution.path_empty_tail.take 1

private def path_2877 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  (Execution.path_empty_tail.drop 1).take 1

private def path_2878 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  (Execution.path_empty_tail.drop 2).take 1

private def path_2879 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  (Execution.path_empty_tail.drop 3).take 1

private def path_2880 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  (Execution.path_empty_tail.drop 4).take 1

private def path_2881 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  Execution.path_empty_tail.drop 5

private theorem path_tail_single_split :
    Execution.path_empty_tail =
      path_2876 ++ path_2877 ++ path_2878 ++ path_2879 ++ path_2880 ++ path_2881 := by
  rfl

def gasSteps_2876 :
    Challenge.EvmProof.GasSteps (Execution.atPC emptyInput 0x1347) s1_push20 := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_2876
      (Execution.atPC emptyInput 0x1347) = some s1_push20 := by
    simp [path_2876, Execution.path_empty_tail,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Execution.atPC, initialState, emptyInput, s1_push20]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_2876
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_2877 :
    Challenge.EvmProof.GasSteps s1_push20 s2_push0 := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_2877
      s1_push20 = some s2_push0 := by
    simp [path_2877, Execution.path_empty_tail, s1_push20, s2_push0,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Execution.atPC, initialState, emptyInput]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_2877
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_2878 :
    Challenge.EvmProof.GasSteps s2_push0 mstoreState := by
  have hmod : Execution.emptyDigestNat % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      Execution.emptyDigestNat :=
    hmod_empty
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_2878
      s2_push0 = some mstoreState := by
    simp [path_2878, Execution.path_empty_tail, s2_push0, mstoreState,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Execution.atPC, initialState, emptyInput]
    constructor
    · rfl
    · rw [hmod, digest_padded_eq]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_2878
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_2879 :
    Challenge.EvmProof.GasSteps mstoreState s4_push1 := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_2879
      mstoreState = some s4_push1 := by
    simp [path_2879, Execution.path_empty_tail, mstoreState, s4_push1,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Execution.atPC, initialState, emptyInput,
      EmptySpec.emptyOutput]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_2879
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_2880 :
    Challenge.EvmProof.GasSteps s4_push1 s5_push0 := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_2880
      s4_push1 = some s5_push0 := by
    simp [path_2880, Execution.path_empty_tail, s4_push1, s5_push0,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_2880
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_2881 :
    Challenge.EvmProof.GasSteps s5_push0 emptyFinal := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_2881
      s5_push0 = some emptyFinal := by
    simp [path_2881, Execution.path_empty_tail, s5_push0, emptyFinal,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Execution.atPC, initialState, emptyInput, mstoreState, s4_push1,
      EmptySpec.emptyOutput]
    decide
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_2881
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_empty_tail :
    Challenge.EvmProof.GasSteps (Execution.atPC emptyInput 0x1347) emptyFinal :=
  (((((gasSteps_2876.trans gasSteps_2877).trans gasSteps_2878).trans
    gasSteps_2879).trans gasSteps_2880).trans gasSteps_2881)

def gasSteps_empty_dispatch :
    Challenge.EvmProof.GasSteps (Execution.atPC emptyInput 0x1341) emptyFinal :=
  gasSteps_dispatch_empty.trans gasSteps_empty_tail

def gasSteps_empty :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode emptyInput 0) emptyFinal :=
  (Execution.gasSteps_start emptyInput).trans gasSteps_empty_dispatch

theorem emptyFinal_halt : emptyFinal.halt = .Returned := by rfl

theorem emptyFinal_callStack : emptyFinal.callStack = [] := by rfl

theorem emptyFinal_toResult : emptyFinal.toResult = .returned (spec emptyInput) := by
  have hspec : spec emptyInput = EmptySpec.emptyOutput := by
    have h := EmptySpec.spec_empty
    simpa [emptyInput] using h
  have hsize : EmptySpec.emptyOutput.size = 32 := by rfl
  have hread : MachineState.readPadded
      (MachineState.writeBytes ByteArray.empty EmptySpec.emptyOutput 0) 0 32 =
      EmptySpec.emptyOutput := by
    have h := Challenge.EvmProof.Memory.readPadded_writeBytes_same
      ByteArray.empty EmptySpec.emptyOutput 0
    simpa [hsize] using h
  simp [emptyFinal, hspec, hread, EvmSemantics.EVM.State.toResult]

theorem correct_empty :
    ∃ g₀ : Nat, ∀ g : Nat, g₀ ≤ g →
      EvmSemantics.EVM.Eval (initialState submissionBytecode emptyInput g)
        (.returned (spec emptyInput)) := by
  let trace := gasSteps_empty
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have hsteps : EvmSemantics.EVM.Steps
      (Challenge.EvmProof.withGas (initialState submissionBytecode emptyInput 0) gas)
      (Challenge.EvmProof.withGas emptyFinal (gas - trace.cost)) :=
    trace.trace gas hgas
  have heval := Challenge.EvmProof.eval_of_steps hsteps (by
    simp [emptyFinal, Challenge.EvmProof.withGas, EvmSemantics.EVM.State.isDone,
      EvmSemantics.EVM.State.isHalted, EvmSemantics.EVM.State.isRunning]
    decide)
  have hres : (Challenge.EvmProof.withGas emptyFinal (gas - trace.cost)).toResult =
      .returned (spec emptyInput) := by
    simpa [Challenge.EvmProof.withGas, EvmSemantics.EVM.State.toResult] using emptyFinal_toResult
  have hwith : Challenge.EvmProof.withGas (initialState submissionBytecode emptyInput 0) gas =
      initialState submissionBytecode emptyInput gas := by
    rfl
  simpa [hres, hwith] using heval

end Challenge.Ripemd160.Submission.Proofs.Bytecode.EmptyFastPath
