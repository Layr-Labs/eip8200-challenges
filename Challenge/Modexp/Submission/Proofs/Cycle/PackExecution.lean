import Challenge.Modexp.Submission.Proofs.Cycle.FinalBlocks
import Challenge.Modexp.Submission.Proofs.Cycle.Packing
import Challenge.Modexp.Submission.Proofs.Cycle.NormalizeMeaning
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
namespace CycleSubmission.PackExecution
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open CycleSubmission.NormalizeMeaning CycleSubmission.Execution CycleSubmission.Packing
open HistoricalSearch.CRTMemoryCells Challenge.EvmProof.Memory

def cells (a : Nat → UInt256) : List (Nat × UInt256) :=
  [(2336,outputWord a 0),(2304,outputWord a 1),(2272,outputWord a 2),
   (2240,outputWord a 3),(2208,outputWord a 4),(2176,outputWord a 5),
   (2144,outputWord a 6),(2112,outputWord a 7),
   (2080,UInt256.shiftRight (a 8) (UInt256.ofNat 128))]

def result (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 10542
    memory := storeCells s.memory (cells a)
    stack := frame a n slot0 slot1 rest}

theorem model_eq (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (hm : MemoryInput s.memory a n) :
    packFinalModel s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP
      (n 8) slot1 mask slot0 (n 3) (a 8) rest = result s a n slot0 slot1 rest := by
  simp (disch := decide) only [packFinalModel, readStore,
    hm.a0, hm.a3, hm.a4, hm.a5, hm.a6, hm.a7]
  rfl

theorem run (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions packFinalProgram
      {s with pc := UInt256.ofNat 10409, stack := frame a n slot0 slot1 rest} =
      some (result s a n slot0 slot1 rest) := by
  have h := packFinal_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP
    (n 8) slot1 mask slot0 (n 3) (a 8) rest hcap hact
  rw [model_eq s a n slot0 slot1 rest hm] at h
  exact h

noncomputable def gasSteps (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256)
    (rest : List UInt256) (env : Environment Artifact.artifact .Osaka s)
    (hm : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 10409, stack := frame a n slot0 slot1 rest}
      (result s a n slot0 slot1 rest) :=
  FinalBlocks.packFinalBlock.steps (env.transfer rfl rfl) rfl
    (run s a n slot0 slot1 rest hm hcap hact)

theorem memory_word (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 8) :
    MachineState.readWord (result s a n slot0 slot1 rest).memory (2112+32*(7-j)) = outputWord a j := by
  interval_cases j <;>
    simp (disch := decide) only [result, cells, storeCells, writeCell,
      show 7-0=7 from rfl, show 7-1=6 from rfl, show 7-2=5 from rfl,
      show 7-3=4 from rfl, show 7-4=3 from rfl, show 7-5=2 from rfl,
      show 7-6=1 from rfl, show 7-7=0 from rfl,
      readStore, readWord_writeWord]

theorem represents (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256)
    (rest : List UInt256) (ha : ∀ i < 9, (a i).toNat < 2^240)
    (hv : ControlArithmetic.value a < 2^2048) :
    Challenge.Modexp.Submission.Proofs.Fast.Model.FastRepresents
      (result s a n slot0 slot1 rest).memory 2112 8 (ControlArithmetic.value a) :=
  output_represents a _ ha hv (memory_word s a n slot0 slot1 rest)

end CycleSubmission.PackExecution
