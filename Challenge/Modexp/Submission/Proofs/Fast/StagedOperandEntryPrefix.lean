/- Entry permutation inherited from ercumentyildirim submission 9294f30d, source a2840b682fe59533669cba10a9f36eb39b2ab6bd. The 299 literal uses PUSH2 to fund the operand snapshot. -/
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.StagedOperand.EntryPrefix
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCached

def loadProgram : List Instr :=
  [.op .JUMPDEST,
   .push 1 64, .op .MLOAD, .push 1 96, .op .MLOAD,
   .push 2 2880, .op .MLOAD,
   .push 2 2848, .op .MLOAD, .op .MLOAD,
   .push 2 2816, .op .MLOAD,
   .push 2 2848, .op .MLOAD, .op (.Dup ⟨6, by decide⟩), .op .ADD,
   .push 1 32, .op .MLOAD,
   .push 1 31, .op .NOT, .push 2 2784, .op .MLOAD,
   .push 1 128, .op .EQ]

def shuffleProgram : List Instr :=
  [
   .op (.Dup ⟨0, by decide⟩),
   .push 1 143,
   .op .MUL,
   .push 2 4514,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 152,
   .op .MUL,
   .push 2 4200,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩),
   .op (.Swap ⟨10, by decide⟩),
   .push 0 0,
   .op .NOT,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Swap ⟨10, by decide⟩)]

def displacement (mem : ByteArray) : UInt256 :=
  UInt256.eq (UInt256.ofNat 128) (MachineState.readWord mem 2784)

def readsProgram : List Instr := loadProgram.take 18
def setupProgram : List Instr := loadProgram.drop 18

theorem run_reads (s : State) (pa pb dst ret : UInt256) (rest : List UInt256)
    (addr : Nat) (hcap : rest.length ≤ 998) (hact : 91 ≤ s.activeWords.toNat)
    (haddr : addr + 32 ≤ 2912)
    (hml : MachineState.readWord s.memory 2848 = UInt256.ofNat addr) :
    runInstructions readsProgram
      {s with pc := UInt256.ofNat 4076, stack := [pa, pb, dst, ret] ++ rest} =
    some {s with
        pc := UInt256.ofNat 4105
        stack := [MachineState.readWord s.memory 32, (pa + UInt256.ofNat addr), MachineState.readWord s.memory 2816, MachineState.readWord s.memory addr, MachineState.readWord s.memory 2880, MachineState.readWord s.memory 96, MachineState.readWord s.memory 64, pa, pb, dst, ret] ++ rest} := by
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
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have htonat : (UInt256.ofNat addr).toNat = addr := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hact1 := activeWords_fix s 2848 32 (by decide) (by omega) hact
  have hact2 := activeWords_fix s addr 32 (by decide) haddr hact
  have hact3 := activeWords_fix s 2784 32 (by decide) (by omega) hact
  have hact4 := activeWords_fix s 2816 32 (by decide) (by omega) hact
  have hact6 := activeWords_fix s 32 32 (by decide) (by omega) hact
  have hact7 := activeWords_fix s 64 32 (by decide) (by omega) hact
  have hact8 := activeWords_fix s 96 32 (by decide) (by omega) hact
  have h96 : (96 : UInt256).toNat = 96 := by decide
  have h128 : (128 : UInt256).toNat = 128 := by decide
  have hact9 := activeWords_fix s 128 32 (by decide) (by omega) hact
  have h64 : (64 : UInt256).toNat = 64 := by decide
  have h32 : (32 : UInt256).toNat = 32 := by decide
  have hact5 := activeWords_fix s 2880 32 (by decide) (by omega) hact
  have h9440 : (2880 : UInt256).toNat = 2880 := by decide
  have h9376 : (2816 : UInt256).toNat = 2816 := by decide
  have h9408 : (2848 : UInt256).toNat = 2848 := by decide
  have h9344 : (2784 : UInt256).toNat = 2784 := by decide
  simp [readsProgram, loadProgram, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, displacement,
    ← negative32_not, hml, htonat, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, h9408, h9344, h9376, h9440, h32, h64, h96, h128,
    State.activeWordsAfterUInt256, hact1, hact2, hact3, hact4, hact5, hact6, hact7, hact8, hact9,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, ← word_add_assoc]
  try exact ⟨rfl, rfl⟩

theorem run_setup (s : State) (pa pb dst ret value inverse aEnd tailPointer low96 low64 low32 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 91 ≤ s.activeWords.toNat) :
    runInstructions setupProgram
      {s with
        pc := UInt256.ofNat 4105
        stack := [low32, aEnd, inverse, value, tailPointer, low96, low64, pa, pb, dst, ret] ++ rest} =
    some {s with
      pc := UInt256.ofNat 4115
      stack := [displacement s.memory, negative32,
        low32, aEnd, inverse, value, tailPointer, low96, low64, pa, pb, dst, ret] ++ rest} := by
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
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have h9344 : (2784 : UInt256).toNat = 2784 := by decide
  have hact3 := activeWords_fix s 2784 32 (by decide) (by omega) hact
  simp [setupProgram, loadProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    displacement, ← negative32_not, h9344, State.activeWordsAfterUInt256, hact3,
    hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, ← word_add_assoc]
  exact ⟨rfl, rfl⟩

theorem run_load (s : State) (pa pb dst ret : UInt256) (rest : List UInt256)
    (addr : Nat) (hcap : rest.length ≤ 998) (hact : 91 ≤ s.activeWords.toNat)
    (haddr : addr + 32 ≤ 2912)
    (hml : MachineState.readWord s.memory 2848 = UInt256.ofNat addr) :
    runInstructions loadProgram
      {s with pc := UInt256.ofNat 4076, stack := [pa, pb, dst, ret] ++ rest} =
    some {s with
        pc := UInt256.ofNat 4115
        stack := [displacement s.memory, negative32,
        MachineState.readWord s.memory 32, (pa + UInt256.ofNat addr), MachineState.readWord s.memory 2816, MachineState.readWord s.memory addr, MachineState.readWord s.memory 2880, MachineState.readWord s.memory 96, MachineState.readWord s.memory 64, pa, pb, dst, ret] ++ rest} := by
  change runInstructions (readsProgram ++ setupProgram) _ = _
  have hr := run_reads s pa pb dst ret rest addr hcap hact haddr hml
  have hs := run_setup s pa pb dst ret (MachineState.readWord s.memory addr)
    (MachineState.readWord s.memory 2816) ((pa + UInt256.ofNat addr))
    (MachineState.readWord s.memory 2880) (MachineState.readWord s.memory 96) (MachineState.readWord s.memory 64)
    (MachineState.readWord s.memory 32) rest hcap hact
  exact runInstructions_append_some _ _ _ _ _ hr hs

theorem run_shuffle (s : State) (pa pb dst ret value inverse aEnd tailPointer low96 low64 low32 delta : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions shuffleProgram
      {s with
        pc := UInt256.ofNat 4115
        stack := [delta, negative32, low32, aEnd, inverse, value, tailPointer, low96, low64, pa, pb, dst, ret] ++ rest} =
    some {s with
        pc := UInt256.ofNat 4138
        stack := [pa, pb, UInt256.ofNat 4200 + UInt256.ofNat 152 * delta, negative32, allOnes,
        UInt256.ofNat 4514 + UInt256.ofNat 143 * delta, inverse, value, tailPointer, low96, low64, low32, aEnd, dst, ret] ++ rest} := by
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
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  simp [shuffleProgram, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ← allOnes_not, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, ← word_add_assoc]
  exact ⟨rfl, rfl, rfl⟩

#print axioms run_load
#print axioms run_shuffle



end Challenge.Modexp.Submission.Proofs.Fast.StagedOperand.EntryPrefix
