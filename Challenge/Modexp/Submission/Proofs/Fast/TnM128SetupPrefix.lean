/- Kernel `setup` (pc 4123, 0x0f6c) of sqCP1m: the 3-slot variant of the entry permutation
inherited from ercumentyildirim submission 9294f30d; the row head `hd` stays on top of the
call frame and becomes frame slot 2.  The 292 literal uses PUSH2 to fund the operand snapshot. -/
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SetupFrames
import Challenge.Modexp.Submission.Proofs.Fast.CapDispatch

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128Setup.EntryPrefix
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCached

def loadProgram : List Instr :=
  [.push 1 96, .op .MLOAD,
   .push 1 224, .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩), .push 1 1, .op .SHR, .push 1 32, .op .ADD, .op .MLOAD,
   .push 1 64, .op .MLOAD,
   .push 2 2752, .op .MLOAD, .op (.Dup ⟨6, by decide⟩), .op .ADD,
   .push 0 0, .push 1 32, .op .MLOAD, .push 2 3347]

def shuffleProgram : List Instr :=
  [
   .push 1 128,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Swap ⟨10, by decide⟩),
   .push 0 0,
   .op .NOT,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Swap ⟨10, by decide⟩)]

def lowProgram : List Instr :=
  [.push 2 2720, .op .MLOAD, .op (.Swap ⟨10, by decide⟩)]

def readsProgram : List Instr := loadProgram.take 16
def setupProgram : List Instr := loadProgram.drop 16

theorem run_reads (s : State) (hd pa pb dst ret : UInt256) (rest : List UInt256)
    (addr n : Nat) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (haddr : addr + 32 ≤ 2816) (hn4 : n = 4 ∨ n = 8)
    (hml : MachineState.readWord s.memory 2752 = UInt256.ofNat addr)
    (hw : rest[1]? = some (UInt256.ofNat (32*n))) :
    runInstructions readsProgram
      {s with pc := UInt256.ofNat 3182, stack := [hd, pa, pb, dst, ret] ++ rest} =
    some {s with
        pc := UInt256.ofNat 3205
        stack := [(pa + UInt256.ofNat addr), MachineState.readWord s.memory 64, MachineState.readWord s.memory (16*n+32), MachineState.readWord s.memory 224, MachineState.readWord s.memory 96, hd, pa, pb, dst, ret] ++ rest} := by
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  have hn8 : n ≤ 8 := by rcases hn4 with rfl | rfl <;> omega
  have htonat : (UInt256.ofNat addr).toNat = addr := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hslotAddr : (32 : UInt256) + UInt256.shiftRight (UInt256.ofNat (32*n)) (1 : UInt256) =
      UInt256.ofNat (16*n+32) := by
    rcases hn4 with rfl | rfl <;> decide
  have hslotAddr' : UInt256.shiftRight (UInt256.ofNat (32*n)) (1 : UInt256) + (32 : UInt256) =
      UInt256.ofNat (16*n+32) := by
    rcases hn4 with rfl | rfl <;> decide
  have htonat16 : (UInt256.ofNat (16*n+32)).toNat = 16*n+32 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hact1 := activeWords_fix s 2752 32 (by decide) (by omega) hact
  have hact2 := activeWords_fix s addr 32 (by decide) haddr hact
  have hact16 := activeWords_fix s (16*n+32) 32 (by decide) (by omega) hact
  have hact3 := activeWords_fix s 2688 32 (by decide) (by omega) hact
  have hact4 := activeWords_fix s 2720 32 (by decide) (by omega) hact
  have hact6 := activeWords_fix s 32 32 (by decide) (by omega) hact
  have hact7 := activeWords_fix s 64 32 (by decide) (by omega) hact
  have hact8 := activeWords_fix s 96 32 (by decide) (by omega) hact
  have h96 : (96 : UInt256).toNat = 96 := by decide
  have h128 : (128 : UInt256).toNat = 128 := by decide
  have hact9 := activeWords_fix s 128 32 (by decide) (by omega) hact
  have h64 : (64 : UInt256).toNat = 64 := by decide
  have h32 : (32 : UInt256).toNat = 32 := by decide
  have hact5 := activeWords_fix s 224 32 (by decide) (by omega) hact
  have h9440 : (224 : UInt256).toNat = 224 := by decide
  have h9376 : (2720 : UInt256).toNat = 2720 := by decide
  have h9408 : (2752 : UInt256).toNat = 2752 := by decide
  have h9344 : (2688 : UInt256).toNat = 2688 := by decide
  simp [readsProgram, loadProgram, runInstructions,
    Challenge.EvmProof.Stepper.runInstr,
     hml, hw, hslotAddr, hslotAddr', htonat, htonat16, hact16, capacity, Nat.add_assoc, h9408, h9344, h9376, h9440, h32, h64, h96, h128,
    State.activeWordsAfterUInt256, hact1, hact2, hact3, hact4, hact5, hact6, hact7, hact8, hact9,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, ← word_add_assoc]
  try exact ⟨rfl, rfl⟩

theorem run_setup (s : State) (hd pa pb dst ret value inverse aEnd tailPointer low96 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions setupProgram
      {s with
        pc := UInt256.ofNat 3205
        stack := [aEnd, inverse, value, tailPointer, low96, hd, pa, pb, dst, ret] ++ rest} =
    some {s with
      pc := UInt256.ofNat 3212
      stack := [UInt256.ofNat 3347,
        MachineState.readWord s.memory 32, zeroTn, aEnd, inverse, value, tailPointer, low96, hd, pa, pb, dst, ret] ++ rest} := by
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  have h32 : (32 : UInt256).toNat = 32 := by decide
  have hact32 := activeWords_fix s 32 32 (by decide) (by omega) hact
  simp [zeroTn, setupProgram, loadProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    State.activeWordsAfterUInt256,
    capacity, Nat.add_assoc, h32, hact32,
    State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, ← word_add_assoc]
  try exact ⟨rfl, rfl⟩

theorem run_load (s : State) (hd pa pb dst ret : UInt256) (rest : List UInt256)
    (addr n : Nat) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (haddr : addr + 32 ≤ 2816) (hn4 : n = 4 ∨ n = 8)
    (hml : MachineState.readWord s.memory 2752 = UInt256.ofNat addr)
    (hw : rest[1]? = some (UInt256.ofNat (32*n))) :
    runInstructions loadProgram
      {s with pc := UInt256.ofNat 3182, stack := [hd, pa, pb, dst, ret] ++ rest} =
    some {s with
        pc := UInt256.ofNat 3212
        stack := [UInt256.ofNat 3347,
        MachineState.readWord s.memory 32, zeroTn, (pa + UInt256.ofNat addr), MachineState.readWord s.memory 64, MachineState.readWord s.memory (16*n+32), MachineState.readWord s.memory 224, MachineState.readWord s.memory 96, hd, pa, pb, dst, ret] ++ rest} := by
  change runInstructions (readsProgram ++ setupProgram) _ = _
  have hr := run_reads s hd pa pb dst ret rest addr n hcap hact haddr hn4 hml hw
  have hs := run_setup s hd pa pb dst ret (MachineState.readWord s.memory (16*n+32))
    (MachineState.readWord s.memory 64) ((pa + UInt256.ofNat addr))
    (MachineState.readWord s.memory 224) (MachineState.readWord s.memory 96)
    rest hcap hact
  exact runInstructions_append_some _ _ _ _ _ hr hs

theorem run_shuffle (s : State) (hd pa pb dst ret value inverse aEnd tailPointer low96 low32 z ent : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions shuffleProgram
      {s with
        pc := UInt256.ofNat 3212
        stack := [ent, z, low32, aEnd, inverse, value, tailPointer, low96, hd, pa, pb, dst, ret] ++ rest} =
    some {s with
        pc := UInt256.ofNat 3221
        stack := [pa, pb, ent, z, allOnes,
        MachineState.readWord s.memory 128, inverse, value, tailPointer, low96, hd, low32, aEnd, dst, ret] ++ rest} := by
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  have h128 : (128 : UInt256).toNat = 128 := by decide
  have hact128 := activeWords_fix s 128 32 (by decide) (by decide) hact
  simp [shuffleProgram, h128, State.activeWordsAfterUInt256, hact128, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, capacity, Nat.add_assoc, ← allOnes_not, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, ← word_add_assoc]
  rfl

theorem run_low (s : State) (hd pa pb l1 l2 dst ret value inverse aEnd tailPointer low96 low32 z : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions lowProgram
      {s with
        pc := UInt256.ofNat 3221
        stack := [pa, pb, l1, z, allOnes, l2, inverse, value, tailPointer, low96, hd, low32, aEnd, dst, ret] ++ rest} =
    some {s with
        pc := UInt256.ofNat 3226
        stack := [hd, pa, pb, l1, z, allOnes, l2, inverse, value, tailPointer, low96,
          MachineState.readWord s.memory 2720, low32, aEnd, dst, ret] ++ rest} := by
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have h2720 : (2720 : UInt256).toNat = 2720 := by decide
  have hact7 := activeWords_fix s 2720 32 (by decide) (by omega) hact
  simp [lowProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, hc15, hc16, h2720,
    State.activeWordsAfterUInt256, hact7, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, ← word_add_assoc]

end Challenge.Modexp.Submission.Proofs.Fast.TnM128Setup.EntryPrefix
