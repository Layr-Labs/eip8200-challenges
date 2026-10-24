import Challenge.Modexp.Submission.Proofs.Cycle.NormalizeExecution
import Challenge.Modexp.Submission.Proofs.Cycle.NormalizationWord
import Challenge.Modexp.Submission.Proofs.CRT.CRTMemoryCells
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

namespace CycleSubmission.NormalizeMeaning
open EvmSemantics EvmSemantics.EVM
open HistoricalSearch.GeneratedColumns HistoricalSearch.CRTMemoryCells
open Challenge.EvmProof.Memory
open HistoricalSearch.MixedMontgomery
open CycleSubmission.Normalization

def mask : UInt256 := UInt256.ofNat (2^240-1)
def modulusP : UInt256 := UInt256.ofNat (2^251-1)

def frame (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256) : List UInt256 :=
  [n 2, n 6, n 4, a 1, a 2, n 5, n 7, modulusP, n 8, slot1, mask, slot0, n 3, a 8] ++ rest

def output (a n : Nat → UInt256) (i : Nat) : UInt256 :=
  if i < 8 then lowDigit a n i else a i - (n i + borrow a n i)

def cells (a n : Nat → UInt256) : List (Nat × UInt256) :=
  [(768, output a n 0), (32, output a n 3), (64, output a n 4),
   (96, output a n 5), (128, output a n 6), (160, output a n 7)]

def result (s : State) (a n : Nat → UInt256) (ret slot1 : UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 11155
    memory := storeCells s.memory (cells a n)
    stack := ret :: frame (output a n) n (n 0) slot1 rest}

structure MemoryInput (mem : ByteArray) (a n : Nat → UInt256) : Prop where
  a0 : MachineState.readWord mem 768 = a 0
  a3 : MachineState.readWord mem 32 = a 3
  a4 : MachineState.readWord mem 64 = a 4
  a5 : MachineState.readWord mem 96 = a 5
  a6 : MachineState.readWord mem 128 = a 6
  a7 : MachineState.readWord mem 160 = a 7
  n0 : MachineState.readWord mem 1344 = n 0
  n1 : MachineState.readWord mem 1376 = n 1

theorem readStore (mem : ByteArray) (word : UInt256) (dst src : Nat)
    (h : src+32 ≤ dst ∨ dst+32 ≤ src) :
    MachineState.readWord
      (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded word.toNat 32) dst) src =
      MachineState.readWord mem src := by
  apply readWord_writeBytes_disjoint
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using h

theorem model_eq (s : State) (a n : Nat → UInt256) (ret slot1 : UInt256) (rest : List UInt256)
    (h : MemoryInput s.memory a n) :
    normalizeModel s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP
      (n 8) slot1 mask ret (n 3) (a 8) rest = result s a n ret slot1 rest := by
  simp (disch := decide) only [normalizeModel, readStore,
    h.a0, h.a3, h.a4, h.a5, h.a6, h.a7, h.n0, h.n1]
  rfl

theorem run (s : State) (a n : Nat → UInt256) (ret slot1 : UInt256) (rest : List UInt256)
    (h : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel.runInstructions
      normalizeProgram {s with pc := UInt256.ofNat 11014, stack := frame a n ret slot1 rest} =
        some (result s a n ret slot1 rest) := by
  have hx := normalize_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP
    (n 8) slot1 mask ret (n 3) (a 8) rest hcap hact
  rw [model_eq s a n ret slot1 rest h] at hx
  exact hx

theorem preserves (s : State) (a n : Nat → UInt256) (ret slot1 : UInt256) (rest : List UInt256)
    (start count : Nat)
    (hlo : start+count ≤ 32 ∨ 192 ≤ start)
    (hhi : start+count ≤ 768 ∨ 800 ≤ start) :
    MachineState.readPadded (result s a n ret slot1 rest).memory start count =
      MachineState.readPadded s.memory start count := by
  apply readPadded_storeCells
  intro c hc
  simp only [cells, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp <;> omega

theorem memory_output (s : State) (a n : Nat → UInt256) (ret slot1 : UInt256) (rest : List UInt256)
    (h : MemoryInput s.memory a n) :
    MemoryInput (result s a n ret slot1 rest).memory (output a n) n := by
  constructor <;>
    simp (disch := omega) [result, cells, storeCells, writeCell, readStore,
      readWord_writeWord, h.n0, h.n1]

end CycleSubmission.NormalizeMeaning
