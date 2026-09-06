import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitResult

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitReturn

open EvmSemantics EvmSemantics.EVM
open WindowControlDefs WindowHitStates WindowHitPaths

/-- RETURN retains its own pc; the output-memory bridge is pc-independent. -/
def normalReturnedState (input : ByteArray) (word : UInt256) : State :=
  { returnedState input word with pc := UInt256.ofNat 3562 }

private def framed (template : State) (pc : Nat) (stack : List UInt256) : State :=
  { template with pc := UInt256.ofNat pc, stack := stack }

private def outputState (template : State) (pc active : Nat)
    (word : UInt256) (rest : List UInt256) : State :=
  { template with
    pc := UInt256.ofNat pc
    stack := rest
    memory := WindowTableMemory.storeWord template.memory 0 word
    activeWords := UInt256.ofNat active
    halt := .Returned
    hReturn := MachineState.readPadded
      (WindowTableMemory.storeWord template.memory 0 word) 0 32 }

@[simp] private theorem zero_toNat : ({ val := 0 } : UInt256).toNat = 0 := rfl

@[simp] private theorem returnPCs (index : Nat)
    (hlo : 2324 ≤ index) (hhi : index ≤ 2337) :
    Artifact.submissionArtifact.instructionPC index =
      [3555, 3556, 3557, 3558, 3559, 3561, 3562,
       3563, 3564, 3565, 3566, 3567, 3569, 3570][index - 2324]! := by
  interval_cases index <;> decide

set_option linter.unusedSimpArgs false in
private theorem run_normal_generic (template : State) (pointer word : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hrun : template.halt = .Running)
    (hactive : template.activeWords = UInt256.ofNat 16) :
    Challenge.EvmProof.Stepper.runLocatedBlock normalReturnPath
      (framed template 3555 (pointer :: word :: rest)) =
    some (outputState template 3562 16 word rest) := by
  have hcap (n : Nat) (hn : n ≤ 4) : rest.length + n < 1024 := by omega
  have hcap0 : rest.length < 1024 := by omega
  simp (disch := omega) [normalReturnPath, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, framed, outputState,
    hrun, hactive, returnPCs, WindowTableMemory.storeWord,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
    List.getElem?_cons_zero, Option.getD_some, Nat.add_assoc, hcap, hcap0,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
private theorem run_zero_generic (template : State) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) (hrun : template.halt = .Running)
    (hactive : template.activeWords = UInt256.ofNat 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock zeroReturnPath
      (framed template 3563 rest) =
    some (outputState template 3570 1 0 rest) := by
  have hcap (n : Nat) (hn : n ≤ 4) : rest.length + n < 1024 := by omega
  have hcap0 : rest.length < 1024 := by omega
  simp (disch := omega) [zeroReturnPath, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, framed, outputState,
    hrun, hactive, returnPCs, WindowTableMemory.storeWord,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
    List.getElem?_cons_zero, Option.getD_some, Nat.add_assoc, hcap, hcap0,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_normalReturn (input : ByteArray) (word : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock normalReturnPath
      (finishState input word) = some (normalReturnedState input word) := by
  have h := run_normal_generic (loopState input 160 word) (UInt256.ofNat 160)
    word (modulusWord input :: routeStack input) (by simp [routeStack]) rfl rfl
  simpa only [framed, outputState, normalReturnedState, returnedState,
    finishState, loopState, normalOutputMemory, storeWord,
    List.cons_append, List.nil_append] using h

theorem run_zeroReturn (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock zeroReturnPath
      (zeroState input) = some (zeroReturnedState input) := by
  have h := run_zero_generic (zeroState input)
    (modulusWord input :: routeStack input) (by simp [routeStack]) rfl rfl
  have hmemory : (Dispatch.wordEntryState input).memory = ByteArray.empty := rfl
  simpa only [framed, outputState, zeroState, zeroReturnedState, outputMemory,
    storeWord, hmemory] using h

private def sound {s t : State}
    (path : List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka))
    (h : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running := by rfl)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

def gasSteps_normalReturn (input : ByteArray) (word : UInt256) :
    Challenge.EvmProof.GasSteps (finishState input word) (normalReturnedState input word) :=
  sound normalReturnPath (run_normalReturn input word)

def gasSteps_zeroReturn (input : ByteArray) :
    Challenge.EvmProof.GasSteps (zeroState input) (zeroReturnedState input) :=
  sound zeroReturnPath (run_zeroReturn input)

theorem normalReturnedState_result (input : ByteArray)
    (hmatch : WindowGuardLogic.Matches input)
    (hmodulus : 0 < WindowSpec.modulusValue input)
    (word : UInt256) (hword : word.toNat = WindowSpec.windowResult input) :
    (normalReturnedState input word).toResult = .returned (spec input) := by
  exact WindowHitResult.returnedState_result input hmatch hmodulus word hword

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitReturn
