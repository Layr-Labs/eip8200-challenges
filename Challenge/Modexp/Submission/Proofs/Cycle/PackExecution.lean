import Challenge.Modexp.Submission.Proofs.Cycle.ControlArithmetic
import Challenge.Modexp.Submission.Proofs.Cycle.FinalBlocks
import Challenge.Modexp.Submission.Proofs.Cycle.NormalizeMeaning
import Challenge.Modexp.Submission.Proofs.Prepared.OverlapPacking
import Challenge.Modexp.Submission.Proofs.Prepared.Arithmetic
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace CycleSubmission.PackExecution
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
open Challenge.EvmProof.Memory
open CycleSubmission.NormalizeMeaning
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs
def result (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256) : State :=
 {s with pc := UInt256.ofNat 8586,memory := OverlapPackingMemory.memory9 s.memory a,stack := frame a n slot0 slot1 rest}
theorem model_eq (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
 (hm : MemoryInput s.memory a n) :
 CycleSubmission.Execution.packFinalModel s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP
  (n 8) slot1 mask slot0 (n 3) (a 8) rest = result s a n slot0 slot1 rest := by
 simp (disch := decide) only [CycleSubmission.Execution.packFinalModel,result,OverlapPackingMemory.memory9,
   OverlapPackingMemory.store,frame,CycleSubmission.Prepared.Arithmetic.read_disjoint,
   List.cons_append,List.nil_append,readWord_writeWord,hm.a0,hm.a3,hm.a4,hm.a5,hm.a6,hm.a7]
theorem run (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
 (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions CycleSubmission.Execution.packFinalProgram
  {s with pc := UInt256.ofNat 8527,stack := frame a n slot0 slot1 rest} =
 some (result s a n slot0 slot1 rest) := by
 have h := CycleSubmission.Execution.packFinal_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP
  (n 8) slot1 mask slot0 (n 3) (a 8) rest hcap hact
 rw [model_eq s a n slot0 slot1 rest hm] at h
 exact h
theorem bytes (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
 (ha : ∀ i < 9,(a i).toNat < 2^240) (_hv : CycleSubmission.ControlArithmetic.value a < 2^2048) :
 MachineState.readPadded (result s a n slot0 slot1 rest).memory 2112 256 =
 Precompile.natToBytes (CycleSubmission.ControlArithmetic.value a) 256 := by
 have h := OverlapPackingMemory.returned9 s.memory a
  (by simpa only [show (256:Nat)^30 = 2^240 by decide] using ha)
 simpa only [result,Precompile.natToBytes,CycleSubmission.ControlArithmetic.value,
  show (256:Nat)^30 = 2^240 by decide] using h
#print axioms model_eq
#print axioms run
#print axioms bytes
noncomputable def gasSteps (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256)
    (rest : List UInt256) (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 8527,stack := frame a n slot0 slot1 rest}
      (result s a n slot0 slot1 rest) :=
  FinalBlocks.packFinalBlock.steps (env.transfer rfl rfl) rfl
    (run s a n slot0 slot1 rest hm hcap hact)
end CycleSubmission.PackExecution
