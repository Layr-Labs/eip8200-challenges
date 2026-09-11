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
   .push 2 9440, .op .MLOAD,
   .push 2 9408, .op .MLOAD, .op .MLOAD,
   .push 2 9376, .op .MLOAD,
   .push 2 9408, .op .MLOAD, .op (.Dup ⟨6, by decide⟩), .op .ADD, .op .MLOAD,
   .push 1 32, .op .MLOAD,
   .push 1 31, .op .NOT, .push 2 9344, .op .MLOAD,
   .push 1 128, .op .EQ, .push 1 152, .op .MUL]

def shuffleProgram : List Instr :=
  [
   .push 2 4195,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 314,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Swap ⟨10, by decide⟩),
   .push 0 0,
   .op .NOT,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Swap ⟨10, by decide⟩)]

def displacement (mem : ByteArray) : UInt256 :=
  UInt256.ofNat 152 * UInt256.eq (UInt256.ofNat 128) (MachineState.readWord mem 9344)

def readsProgram : List Instr := loadProgram.take 19
def setupProgram : List Instr := loadProgram.drop 19

theorem run_reads (s : State) (pa pb dst ret : UInt256) (rest : List UInt256)
    (addr : Nat) (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (haddr : addr + 32 ≤ 9472)
    (hml : MachineState.readWord s.memory 9408 = UInt256.ofNat addr)
    (hsource : (pa + UInt256.ofNat addr).toNat + 32 ≤ 9472) :
    runInstructions readsProgram
      {s with pc := UInt256.ofNat 4072, stack := [pa, pb, dst, ret] ++ rest} =
    some {s with
        pc := UInt256.ofNat 4102
        stack := [MachineState.readWord s.memory 32, MachineState.readWord s.memory (pa + UInt256.ofNat addr).toNat, MachineState.readWord s.memory 9376, MachineState.readWord s.memory addr, MachineState.readWord s.memory 9440, MachineState.readWord s.memory 96, MachineState.readWord s.memory 64, pa, pb, dst, ret] ++ rest} := by
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
  have hact1 := activeWords_fix s 9408 32 (by decide) (by omega) hact
  have hact2 := activeWords_fix s addr 32 (by decide) haddr hact
  have hact3 := activeWords_fix s 9344 32 (by decide) (by omega) hact
  have hact4 := activeWords_fix s 9376 32 (by decide) (by omega) hact
  have hact6 := activeWords_fix s 32 32 (by decide) (by omega) hact
  have hsourceNorm : (pa.toNat + addr) % 2 ^ 256 + 32 ≤ 9472 := by
    simpa only [Challenge.EvmProof.Word.word_toNat_add, htonat] using hsource
  have hactSource := activeWordsAfter_fix s.activeWords.toNat
    ((pa.toNat + addr) % 2 ^ 256) 32 (by decide) hsourceNorm hact
  have hactMod : s.activeWords.toNat % 2 ^ 256 = s.activeWords.toNat :=
    Nat.mod_eq_of_lt s.activeWords.val.isLt
  norm_num only at hactSource hactMod
  have hact7 := activeWords_fix s 64 32 (by decide) (by omega) hact
  have hact8 := activeWords_fix s 96 32 (by decide) (by omega) hact
  have h96 : (96 : UInt256).toNat = 96 := by decide
  have h128 : (128 : UInt256).toNat = 128 := by decide
  have hact9 := activeWords_fix s 128 32 (by decide) (by omega) hact
  have h64 : (64 : UInt256).toNat = 64 := by decide
  have h32 : (32 : UInt256).toNat = 32 := by decide
  have hact5 := activeWords_fix s 9440 32 (by decide) (by omega) hact
  have h9440 : (9440 : UInt256).toNat = 9440 := by decide
  have h9376 : (9376 : UInt256).toNat = 9376 := by decide
  have h9408 : (9408 : UInt256).toNat = 9408 := by decide
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  simp [readsProgram, loadProgram, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, displacement,
    ← negative32_not, hml, htonat, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, h9408, h9344, h9376, h9440, h32, h64, h96, h128,
    State.activeWordsAfterUInt256, hact1, hact2, hact3, hact4, hact5, hact6, hact7, hact8, hact9,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, ← word_add_assoc]
  rw [hactSource, hactMod, hact6]

theorem run_setup (s : State) (pa pb dst ret value inverse aEnd tailPointer low96 low64 low32 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions setupProgram
      {s with
        pc := UInt256.ofNat 4102
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
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  have hact3 := activeWords_fix s 9344 32 (by decide) (by omega) hact
  simp [setupProgram, loadProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    displacement, ← negative32_not, h9344, State.activeWordsAfterUInt256, hact3,
    hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, ← word_add_assoc]
  exact ⟨rfl, rfl⟩

theorem run_load (s : State) (pa pb dst ret : UInt256) (rest : List UInt256)
    (addr : Nat) (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (haddr : addr + 32 ≤ 9472)
    (hml : MachineState.readWord s.memory 9408 = UInt256.ofNat addr)
    (hsource : (pa + UInt256.ofNat addr).toNat + 32 ≤ 9472) :
    runInstructions loadProgram
      {s with pc := UInt256.ofNat 4072, stack := [pa, pb, dst, ret] ++ rest} =
    some {s with
        pc := UInt256.ofNat 4115
        stack := [displacement s.memory, negative32,
        MachineState.readWord s.memory 32, MachineState.readWord s.memory (pa + UInt256.ofNat addr).toNat, MachineState.readWord s.memory 9376, MachineState.readWord s.memory addr, MachineState.readWord s.memory 9440, MachineState.readWord s.memory 96, MachineState.readWord s.memory 64, pa, pb, dst, ret] ++ rest} := by
  change runInstructions (readsProgram ++ setupProgram) _ = _
  have hr := run_reads s pa pb dst ret rest addr hcap hact haddr hml hsource
  have hs := run_setup s pa pb dst ret (MachineState.readWord s.memory addr)
    (MachineState.readWord s.memory 9376) (MachineState.readWord s.memory (pa + UInt256.ofNat addr).toNat)
    (MachineState.readWord s.memory 9440) (MachineState.readWord s.memory 96) (MachineState.readWord s.memory 64)
    (MachineState.readWord s.memory 32) rest hcap hact
  exact runInstructions_append_some _ _ _ _ _ hr hs

theorem run_shuffle (s : State) (pa pb dst ret value inverse aEnd tailPointer low96 low64 low32 delta : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions shuffleProgram
      {s with
        pc := UInt256.ofNat 4115
        stack := [delta, negative32, low32, aEnd, inverse, value, tailPointer, low96, low64, pa, pb, dst, ret] ++ rest} =
    some {s with
        pc := UInt256.ofNat 4130
        stack := [pa, pb, UInt256.ofNat 4195 + delta, negative32, allOnes,
        UInt256.ofNat 4509 + delta, inverse, value, tailPointer, low96, low64, low32, aEnd, dst, ret] ++ rest} := by
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
