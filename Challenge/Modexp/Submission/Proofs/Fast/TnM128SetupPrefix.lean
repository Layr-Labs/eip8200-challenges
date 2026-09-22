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
   .push 2 2784, .op .MLOAD,
   .push 2 2752, .op .MLOAD, .op .MLOAD,
   .push 2 2720, .op .MLOAD,
   .push 2 2752, .op .MLOAD, .op (.Dup ⟨6, by decide⟩), .op .ADD,
   .push 1 32, .op .MLOAD,
   .push 0 0, .op (.Dup ⟨14, by decide⟩),
   .push 1 128, .op .AND, .op .ISZERO, .op .ISZERO, .push 2 1747, .op .MUL]

def shuffleProgram : List Instr :=
  [
   .push 2 3562,
   .op .ADD,
   .push 1 128,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Swap ⟨10, by decide⟩),
   .push 0 0,
   .op .NOT,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Swap ⟨10, by decide⟩)]

/-- `PUSH1 0x40; MLOAD; SWAP11`: the low modulus word, loaded late, swaps `hd` back up. -/
def lowProgram : List Instr :=
  [.push 1 64, .op .MLOAD, .op (.Swap ⟨10, by decide⟩)]

/-- The four-limb displacement.  The selector word is no longer loaded: `DUP15` pulls the
F5[4] length slot off the riding frame (pinned to `readWord mem 2688` by `hslot`), then
`PUSH1 128 AND ISZERO ISZERO PUSH2 1747 MUL` normalizes its bit 7 to 0/1 before scaling,
so the distance is a free `PUSH2` literal rather than a multiple of 128.  It still agrees
with `1747 * isFour n` only for `n = 4` and `n = 8` (at `n = 5,6,7` the mask bit is
also set), so every consumer carries `n = 4 ∨ n = 8`. -/
def displacement (mem : ByteArray) : UInt256 :=
  UInt256.ofNat 1747 * CapDispatch.selectBit (MachineState.readWord mem 2688)

def readsProgram : List Instr := loadProgram.take 15
def setupProgram : List Instr := loadProgram.drop 15

theorem run_reads (s : State) (hd pa pb dst ret : UInt256) (rest : List UInt256)
    (addr : Nat) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (haddr : addr + 32 ≤ 2816)
    (hml : MachineState.readWord s.memory 2752 = UInt256.ofNat addr) :
    runInstructions readsProgram
      {s with pc := UInt256.ofNat 3388, stack := [hd, pa, pb, dst, ret] ++ rest} =
    some {s with
        pc := UInt256.ofNat 3413
        stack := [MachineState.readWord s.memory 32, (pa + UInt256.ofNat addr), MachineState.readWord s.memory 2720, MachineState.readWord s.memory addr, MachineState.readWord s.memory 2784, MachineState.readWord s.memory 96, hd, pa, pb, dst, ret] ++ rest} := by
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
  have hact1 := activeWords_fix s 2752 32 (by decide) (by omega) hact
  have hact2 := activeWords_fix s addr 32 (by decide) haddr hact
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
  have hact5 := activeWords_fix s 2784 32 (by decide) (by omega) hact
  have h9440 : (2784 : UInt256).toNat = 2784 := by decide
  have h9376 : (2720 : UInt256).toNat = 2720 := by decide
  have h9408 : (2752 : UInt256).toNat = 2752 := by decide
  have h9344 : (2688 : UInt256).toNat = 2688 := by decide
  simp [readsProgram, loadProgram, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, displacement,
     hml, htonat, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, h9408, h9344, h9376, h9440, h32, h64, h96, h128,
    State.activeWordsAfterUInt256, hact1, hact2, hact3, hact4, hact5, hact6, hact7, hact8, hact9,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, ← word_add_assoc]
  try exact ⟨rfl, rfl⟩

theorem run_setup (s : State) (hd pa pb dst ret value inverse aEnd tailPointer low96 low32 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hslot : rest[2]? = some (MachineState.readWord s.memory 2688)) :
    runInstructions setupProgram
      {s with
        pc := UInt256.ofNat 3413
        stack := [low32, aEnd, inverse, value, tailPointer, low96, hd, pa, pb, dst, ret] ++ rest} =
    some {s with
      pc := UInt256.ofNat 3424
      stack := [displacement s.memory, zeroTn,
        low32, aEnd, inverse, value, tailPointer, low96, hd, pa, pb, dst, ret] ++ rest} := by
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
  have h9344 : (2688 : UInt256).toNat = 2688 := by decide
  have hact3 := activeWords_fix s 2688 32 (by decide) (by omega) hact
  simp [zeroTn, setupProgram, loadProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    displacement,  h9344, State.activeWordsAfterUInt256, hact3, hslot,
    hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, ← word_add_assoc]
  try exact ⟨rfl, rfl⟩

/-- `run_setup` with the riding width slot pinned to an arbitrary word `w` instead of the
memory word at 2688: the square-loop frame rides the limb count there, for which the
normalized selector vanishes. -/
theorem run_setup_w (s : State) (hd pa pb dst ret value inverse aEnd tailPointer low96 low32
      w : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (_hact : 88 ≤ s.activeWords.toNat)
    (hslot : rest[2]? = some w) :
    runInstructions setupProgram
      {s with
        pc := UInt256.ofNat 3413
        stack := [low32, aEnd, inverse, value, tailPointer, low96, hd, pa, pb, dst, ret] ++ rest} =
    some {s with
      pc := UInt256.ofNat 3424
      stack := [UInt256.ofNat 1747 * CapDispatch.selectBit w, zeroTn,
        low32, aEnd, inverse, value, tailPointer, low96, hd, pa, pb, dst, ret] ++ rest} := by
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
  simp [zeroTn, setupProgram, loadProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    CapDispatch.selectBit, hslot,
    hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, ← word_add_assoc]
  try exact ⟨rfl, rfl⟩

theorem run_load (s : State) (hd pa pb dst ret : UInt256) (rest : List UInt256)
    (addr : Nat) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (haddr : addr + 32 ≤ 2816)
    (hml : MachineState.readWord s.memory 2752 = UInt256.ofNat addr)
    (hslot : rest[2]? = some (MachineState.readWord s.memory 2688)) :
    runInstructions loadProgram
      {s with pc := UInt256.ofNat 3388, stack := [hd, pa, pb, dst, ret] ++ rest} =
    some {s with
        pc := UInt256.ofNat 3424
        stack := [displacement s.memory, zeroTn,
        MachineState.readWord s.memory 32, (pa + UInt256.ofNat addr), MachineState.readWord s.memory 2720, MachineState.readWord s.memory addr, MachineState.readWord s.memory 2784, MachineState.readWord s.memory 96, hd, pa, pb, dst, ret] ++ rest} := by
  change runInstructions (readsProgram ++ setupProgram) _ = _
  have hr := run_reads s hd pa pb dst ret rest addr hcap hact haddr hml
  have hs := run_setup s hd pa pb dst ret (MachineState.readWord s.memory addr)
    (MachineState.readWord s.memory 2720) ((pa + UInt256.ofNat addr))
    (MachineState.readWord s.memory 2784) (MachineState.readWord s.memory 96)
    (MachineState.readWord s.memory 32) rest hcap hact hslot
  exact runInstructions_append_some _ _ _ _ _ hr hs

/-- `run_load` for a riding width slot pinned to an arbitrary word `w`. -/
theorem run_load_w (s : State) (hd pa pb dst ret : UInt256) (rest : List UInt256)
    (addr : Nat) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (haddr : addr + 32 ≤ 2816)
    (hml : MachineState.readWord s.memory 2752 = UInt256.ofNat addr)
    (w : UInt256) (hslot : rest[2]? = some w) :
    runInstructions loadProgram
      {s with pc := UInt256.ofNat 3388, stack := [hd, pa, pb, dst, ret] ++ rest} =
    some {s with
        pc := UInt256.ofNat 3424
        stack := [UInt256.ofNat 1747 * CapDispatch.selectBit w, zeroTn,
        MachineState.readWord s.memory 32, (pa + UInt256.ofNat addr), MachineState.readWord s.memory 2720, MachineState.readWord s.memory addr, MachineState.readWord s.memory 2784, MachineState.readWord s.memory 96, hd, pa, pb, dst, ret] ++ rest} := by
  change runInstructions (readsProgram ++ setupProgram) _ = _
  have hr := run_reads s hd pa pb dst ret rest addr hcap hact haddr hml
  have hs := run_setup_w s hd pa pb dst ret (MachineState.readWord s.memory addr)
    (MachineState.readWord s.memory 2720) ((pa + UInt256.ofNat addr))
    (MachineState.readWord s.memory 2784) (MachineState.readWord s.memory 96)
    (MachineState.readWord s.memory 32) w rest hcap hact hslot
  exact runInstructions_append_some _ _ _ _ _ hr hs

/-- `PUSH2 0x0fe4; ADD; DUP1; PUSH2 0x12b; ADD; SWAP4; SWAP11; PUSH0; NOT; SWAP4; SWAP11`
(pc 4162 → 4177): `ent = 4296 + delta` and `l2T = 292 + ent` enter the frame; `hd`
moves down to slot 10 (it is swapped back up by `lowProgram`). -/
theorem run_shuffle (s : State) (hd pa pb dst ret value inverse aEnd tailPointer low96 low32 delta : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions shuffleProgram
      {s with
        pc := UInt256.ofNat 3424
        stack := [delta, zeroTn, low32, aEnd, inverse, value, tailPointer, low96, hd, pa, pb, dst, ret] ++ rest} =
    some {s with
        pc := UInt256.ofNat 3437
        stack := [pa, pb, UInt256.ofNat 3562 + delta, zeroTn, allOnes,
        MachineState.readWord s.memory 128, inverse, value, tailPointer, low96, hd, low32, aEnd, dst, ret] ++ rest} := by
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
  have h128 : (128 : UInt256).toNat = 128 := by decide
  have hact128 := activeWords_fix s 128 32 (by decide) (by decide) hact
  simp [shuffleProgram, h128, State.activeWordsAfterUInt256, hact128, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ← allOnes_not, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, ← word_add_assoc]
  exact ⟨rfl, rfl⟩

theorem run_low (s : State) (hd pa pb l1 l2 dst ret value inverse aEnd tailPointer low96 low32 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions lowProgram
      {s with
        pc := UInt256.ofNat 3437
        stack := [pa, pb, l1, zeroTn, allOnes, l2, inverse, value, tailPointer, low96, hd, low32, aEnd, dst, ret] ++ rest} =
    some {s with
        pc := UInt256.ofNat 3441
        stack := [hd, pa, pb, l1, zeroTn, allOnes, l2, inverse, value, tailPointer, low96,
          MachineState.readWord s.memory 64, low32, aEnd, dst, ret] ++ rest} := by
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have h64 : (64 : UInt256).toNat = 64 := by decide
  have hact7 := activeWords_fix s 64 32 (by decide) (by omega) hact
  simp [lowProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, hc15, hc16, h64,
    State.activeWordsAfterUInt256, hact7, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, ← word_add_assoc]

end Challenge.Modexp.Submission.Proofs.Fast.TnM128Setup.EntryPrefix
