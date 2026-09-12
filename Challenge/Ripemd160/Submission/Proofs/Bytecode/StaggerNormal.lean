import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawNormalPool
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScratch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableLayout
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawNormalStore60
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawNormalStore44
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawNormalStore28
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawNormalStore12
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerNormal
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerTableMemory StaggerTableLayout
def poolStack (words : Nat → UInt256) : List UInt256 :=
  [ words 0, words 9, words 3, words 8, words 2, words 7, words 10, words 13, words 4, words 14, words 15, words 11, words 5, words 1, words 12, words 6 ]
def poolInput : StaggerRaw.Input := ⟨UInt256.ofNat 4294967295, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0⟩
theorem pool_output (memory : ByteArray) (rho : List UInt256) :
    StaggerRawNormalPool.outputStack memory poolInput rho = poolStack (StaggerScratch.poolWord memory) ++ rho := by
  simp only [StaggerRawNormalPool.outputStack, poolInput, poolStack, StaggerScratch.poolWord,
    Word.mask32, Word.land_comm]
  rfl

theorem run_pool (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat) :
    runInstrSeq StaggerRawNormalPool.template {s with pc := pc, stack := UInt256.ofNat 4294967295 :: rho} =
      some {s with pc := pcAfter pc StaggerRawNormalPool.template, stack := poolStack (StaggerScratch.poolWord s.memory) ++ rho} := by
  have h := StaggerRawNormalPool.run_actual s pc poolInput rho hs hr ha
  rw [pool_output] at h
  exact h
def NormalStore60Input (words : Nat → UInt256) : StaggerRaw.Input :=
  ⟨words 0, words 9, words 3, words 8, words 2, words 7, words 10, words 13, words 4, words 14, words 15, words 11, words 5, words 1, words 12, words 6, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0⟩
theorem NormalStore60_output (memory : ByteArray) (words : Nat → UInt256) (rho : List UInt256) :
    StaggerRawNormalStore60.outputStack memory (NormalStore60Input words) rho = [ words 9, words 3, words 8, words 2, words 7, words 10, words 13, words 4, words 14, words 15, words 11, words 5, words 1, words 12, words 6 ] ++ rho := by rfl

theorem NormalStore60_memory (memory : ByteArray) (words : Nat → UInt256) :
    StaggerRawNormalStore60.outputMemory memory (NormalStore60Input words) =
      storeDescending memory (tableWords words) 45 16 := by rfl

theorem run_NormalStore60 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat) :
    runInstrSeq StaggerRawNormalStore60.template {s with pc := pc, stack := [ words 0, words 9, words 3, words 8, words 2, words 7, words 10, words 13, words 4, words 14, words 15, words 11, words 5, words 1, words 12, words 6 ] ++ rho} =
      some {s with pc := pcAfter pc StaggerRawNormalStore60.template, stack := [ words 9, words 3, words 8, words 2, words 7, words 10, words 13, words 4, words 14, words 15, words 11, words 5, words 1, words 12, words 6 ] ++ rho, memory := storeDescending s.memory (tableWords words) 45 16} := by
  have h := StaggerRawNormalStore60.run_actual s pc (NormalStore60Input words) rho hs hr ha
  rw [NormalStore60_output, NormalStore60_memory] at h
  exact h
def NormalStore44Input (words : Nat → UInt256) : StaggerRaw.Input :=
  ⟨words 9, words 3, words 8, words 2, words 7, words 10, words 13, words 4, words 14, words 15, words 11, words 5, words 1, words 12, words 6, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0⟩
theorem NormalStore44_output (memory : ByteArray) (words : Nat → UInt256) (rho : List UInt256) :
    StaggerRawNormalStore44.outputStack memory (NormalStore44Input words) rho = [ words 3, words 8, words 2, words 7, words 10, words 13, words 4, words 14, words 15, words 11, words 5, words 1, words 12, words 6 ] ++ rho := by rfl

theorem NormalStore44_memory (memory : ByteArray) (words : Nat → UInt256) :
    StaggerRawNormalStore44.outputMemory memory (NormalStore44Input words) =
      storeDescending memory (tableWords words) 29 16 := by rfl

theorem run_NormalStore44 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat) :
    runInstrSeq StaggerRawNormalStore44.template {s with pc := pc, stack := [ words 9, words 3, words 8, words 2, words 7, words 10, words 13, words 4, words 14, words 15, words 11, words 5, words 1, words 12, words 6 ] ++ rho} =
      some {s with pc := pcAfter pc StaggerRawNormalStore44.template, stack := [ words 3, words 8, words 2, words 7, words 10, words 13, words 4, words 14, words 15, words 11, words 5, words 1, words 12, words 6 ] ++ rho, memory := storeDescending s.memory (tableWords words) 29 16} := by
  have h := StaggerRawNormalStore44.run_actual s pc (NormalStore44Input words) rho hs hr ha
  rw [NormalStore44_output, NormalStore44_memory] at h
  exact h
def NormalStore28Input (words : Nat → UInt256) : StaggerRaw.Input :=
  ⟨words 3, words 8, words 2, words 7, words 10, words 13, words 4, words 14, words 15, words 11, words 5, words 1, words 12, words 6, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0⟩
theorem NormalStore28_output (memory : ByteArray) (words : Nat → UInt256) (rho : List UInt256) :
    StaggerRawNormalStore28.outputStack memory (NormalStore28Input words) rho = [ words 4, words 14, words 15, words 11, words 5, words 1, words 12, words 6 ] ++ rho := by rfl

theorem NormalStore28_memory (memory : ByteArray) (words : Nat → UInt256) :
    StaggerRawNormalStore28.outputMemory memory (NormalStore28Input words) =
      storeDescending memory (tableWords words) 13 16 := by rfl

theorem run_NormalStore28 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat) :
    runInstrSeq StaggerRawNormalStore28.template {s with pc := pc, stack := [ words 3, words 8, words 2, words 7, words 10, words 13, words 4, words 14, words 15, words 11, words 5, words 1, words 12, words 6 ] ++ rho} =
      some {s with pc := pcAfter pc StaggerRawNormalStore28.template, stack := [ words 4, words 14, words 15, words 11, words 5, words 1, words 12, words 6 ] ++ rho, memory := storeDescending s.memory (tableWords words) 13 16} := by
  have h := StaggerRawNormalStore28.run_actual s pc (NormalStore28Input words) rho hs hr ha
  rw [NormalStore28_output, NormalStore28_memory] at h
  exact h
def NormalStore12Input (words : Nat → UInt256) : StaggerRaw.Input :=
  ⟨words 4, words 14, words 15, words 11, words 5, words 1, words 12, words 6, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0⟩
theorem NormalStore12_output (memory : ByteArray) (words : Nat → UInt256) (rho : List UInt256) :
    StaggerRawNormalStore12.outputStack memory (NormalStore12Input words) rho = [  ] ++ rho := by rfl

theorem NormalStore12_memory (memory : ByteArray) (words : Nat → UInt256) :
    StaggerRawNormalStore12.outputMemory memory (NormalStore12Input words) =
      storeDescending memory (tableWords words) 0 13 := by rfl

theorem run_NormalStore12 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat) :
    runInstrSeq StaggerRawNormalStore12.template {s with pc := pc, stack := [ words 4, words 14, words 15, words 11, words 5, words 1, words 12, words 6 ] ++ rho} =
      some {s with pc := pcAfter pc StaggerRawNormalStore12.template, stack := [  ] ++ rho, memory := storeDescending s.memory (tableWords words) 0 13} := by
  have h := StaggerRawNormalStore12.run_actual s pc (NormalStore12Input words) rho hs hr ha
  rw [NormalStore12_output, NormalStore12_memory] at h
  exact h
def storesTemplate : List Instr := StaggerRawNormalStore60.template ++ StaggerRawNormalStore44.template ++ StaggerRawNormalStore28.template ++ StaggerRawNormalStore12.template
theorem run_stores (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat) :
    runInstrSeq storesTemplate {s with pc := pc, stack := poolStack words ++ rho} =
      some {s with pc := pcAfter pc storesTemplate, stack := rho, memory := resultMemory s.memory words} := by
  let s0 := s
  let pc0 := pc
  let s1 := {s0 with memory := storeDescending s0.memory (tableWords words) 45 16}
  let pc1 := pcAfter pc0 StaggerRawNormalStore60.template
  have h0 := run_NormalStore60 s0 pc0 words rho hs hr ha
  let s2 := {s1 with memory := storeDescending s1.memory (tableWords words) 29 16}
  let pc2 := pcAfter pc1 StaggerRawNormalStore44.template
  have h1 := run_NormalStore44 s1 pc1 words rho hs hr ha
  let s3 := {s2 with memory := storeDescending s2.memory (tableWords words) 13 16}
  let pc3 := pcAfter pc2 StaggerRawNormalStore28.template
  have h2 := run_NormalStore28 s2 pc2 words rho hs hr ha
  let s4 := {s3 with memory := storeDescending s3.memory (tableWords words) 0 13}
  let pc4 := pcAfter pc3 StaggerRawNormalStore12.template
  have h3 := run_NormalStore12 s3 pc3 words rho hs hr ha
  have h01 := DenseScheduleTrace.runInstrSeq_append_running h0 (by exact hr) h1
  have h012 := DenseScheduleTrace.runInstrSeq_append_running h01 (by exact hr) h2
  have h := DenseScheduleTrace.runInstrSeq_append_running h012 (by exact hr) h3
  simpa only [storesTemplate, DenseScheduleTrace.pcAfter_append, s0, s1, s2, s3, pc0, pc1, pc2, pc3, poolStack, resultMemory, storeDescending, List.nil_append, List.append_assoc] using h
#print axioms run_pool
#print axioms run_stores
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerNormal
