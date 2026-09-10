import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCached.CachePrefix
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCached

def loadProgram : List Instr :=
  [.op .JUMPDEST, .push 2 9440, .op .MLOAD, .push 2 9376, .op .MLOAD, .push 2 9408, .op .MLOAD, .op .MLOAD,
   .push 1 31, .op .NOT, .push 2 9344, .op .MLOAD,
   .push 1 128, .op .EQ, .push 1 150, .op .MUL,
   .op (.Dup ⟨0, by decide⟩)]

def shuffleProgram : List Instr :=
  [.push 2 4239, .op .ADD, .op (.Swap ⟨0, by decide⟩),
   .push 2 4574, .op .ADD, .op (.Swap ⟨3, by decide⟩),
   .op (.Swap ⟨4, by decide⟩), .op (.Swap ⟨6, by decide⟩), .push 0 0, .op .NOT,
   .op (.Swap ⟨3, by decide⟩), .op (.Swap ⟨5, by decide⟩), .op (.Swap ⟨6, by decide⟩)]

def displacement (mem : ByteArray) : UInt256 :=
  UInt256.ofNat 150 * UInt256.eq (UInt256.ofNat 128) (MachineState.readWord mem 9344)

theorem run_load (s : State) (pa pb dst ret : UInt256) (rest : List UInt256)
    (addr : Nat) (hcap : rest.length ≤ 1002) (hact : 296 ≤ s.activeWords.toNat)
    (haddr : addr + 32 ≤ 9472)
    (hml : MachineState.readWord s.memory 9408 = UInt256.ofNat addr) :
    runInstructions loadProgram
      {s with pc := UInt256.ofNat 4160, stack := [pa, pb, dst, ret] ++ rest} =
    some {s with
        pc := UInt256.ofNat 4188
        stack := [displacement s.memory, displacement s.memory, negative32,
        MachineState.readWord s.memory addr, MachineState.readWord s.memory 9376, MachineState.readWord s.memory 9440, pa, pb, dst, ret] ++ rest} := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have htonat : (UInt256.ofNat addr).toNat = addr := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hact1 := activeWords_fix s 9408 32 (by decide) (by omega) hact
  have hact2 := activeWords_fix s addr 32 (by decide) haddr hact
  have hact3 := activeWords_fix s 9344 32 (by decide) (by omega) hact
  have hact4 := activeWords_fix s 9376 32 (by decide) (by omega) hact
  have hact5 := activeWords_fix s 9440 32 (by decide) (by omega) hact
  have h9440 : (9440 : UInt256).toNat = 9440 := by decide
  have h9376 : (9376 : UInt256).toNat = 9376 := by decide
  have h9408 : (9408 : UInt256).toNat = 9408 := by decide
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  simp [loadProgram, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, displacement,
    ← negative32_not, hml, htonat, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, h9408, h9344, h9376, h9440,
    State.activeWordsAfterUInt256, hact1, hact2, hact3, hact4, hact5,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  exact ⟨rfl, rfl⟩

theorem run_shuffle (s : State) (pa pb dst ret value inverse tailPointer delta : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) :
    runInstructions shuffleProgram
      {s with
        pc := UInt256.ofNat 4188
        stack := [delta, delta, negative32, value, inverse, tailPointer, pa, pb, dst, ret] ++ rest} =
    some {s with
        pc := UInt256.ofNat 4205
        stack := [pa, pb, UInt256.ofNat 4239 + delta, negative32, allOnes,
        UInt256.ofNat 4574 + delta, value, inverse, tailPointer, dst, ret] ++ rest} := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  simp [shuffleProgram, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, ← allOnes_not, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  exact ⟨rfl, rfl, rfl⟩

#print axioms run_load
#print axioms run_shuffle



end Challenge.Modexp.Submission.Proofs.Fast.CiosCached.CachePrefix
