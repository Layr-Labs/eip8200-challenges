import Challenge.Modexp.Submission.Proofs.R5.PrologueRun
import Challenge.Modexp.Submission.Proofs.Prepared.Arithmetic
import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
namespace ConstantFold5349
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.EvmProof.Word Challenge.EvmProof.Stepper

private theorem compact_mask256 : UInt256.lnot (UInt256.ofNat 0) = UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide
private theorem compact_mask251 : UInt256.shiftRight (UInt256.lnot (UInt256.ofNat 0)) (UInt256.ofNat 5) = UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247 := by decide
private theorem compact_shift256 : UInt256.shiftRight (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (UInt256.ofNat 5) = UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247 := by decide
attribute [local simp] compact_mask256 compact_mask251 compact_shift256

def oldProgram : List Instr :=
  [.push 0 0,
   .op .NOT,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 16,
   .op .SHR,
   .push 1 224,
   .op .MSTORE,
   .push 1 5,
   .op .SHR]

def oldModel (s : State) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (UInt256.ofNat 16)
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 224
  let v2 : UInt256 := UInt256.shiftRight (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (UInt256.ofNat 5)
  {s with pc := UInt256.ofNat 5102, memory := v1, stack := v2 :: rest}

theorem old_run (s : State) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions oldProgram {s with pc := UInt256.ofNat 5090, stack := rest} =
      some (oldModel s rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 5) : rest.length + j < 1024 := by omega
  have capacity0 : rest.length < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Challenge.Modexp.Submission.Proofs.Fast.Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, oldProgram, oldModel, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, capacity0, ha224, hf224]

def newProgram : List Instr :=
  [.push 0 0,
   .op .NOT,
   .push 1 5,
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 11,
   .op .SHR,
   .push 1 224,
   .op .MSTORE]

def newModel (s : State) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) (UInt256.ofNat 11)
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 224
  {s with pc := UInt256.ofNat 5102, memory := v1, stack := (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: rest}

theorem new_run (s : State) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newProgram {s with pc := UInt256.ofNat 5090, stack := rest} =
      some (newModel s rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 5) : rest.length + j < 1024 := by omega
  have capacity0 : rest.length < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Challenge.Modexp.Submission.Proofs.Fast.Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, newProgram, newModel, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, capacity0, ha224, hf224]

theorem mask_old : UInt256.shiftRight (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (UInt256.ofNat 16) = UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775 := by decide
theorem modulus_old : UInt256.shiftRight (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (UInt256.ofNat 5) = UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247 := by decide
theorem mask_new : UInt256.shiftRight (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) (UInt256.ofNat 11) = UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775 := by decide

/-- Identical entire output state, including opaque tail and memory, for arbitrary input memory. -/
theorem boundary_eq (s : State) (rest : List UInt256) :
    newModel s rest = oldModel s rest := by
  simp only [newModel, oldModel, mask_old, modulus_old, mask_new]

/-- All entry stack words are opaque; neither window inspects them. -/
theorem replacement_run (s : State) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newProgram {s with pc := UInt256.ofNat 5090, stack := rest} =
    runInstructions oldProgram {s with pc := UInt256.ofNat 5090, stack := rest} := by
  rw [old_run s rest hcap hact, new_run s rest hcap hact, boundary_eq]
#print axioms replacement_run


def tailProgram : List Instr :=
  [.push 0 0,
   .op .MLOAD,
   .push 1 192,
   .op .SHR,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩)]

open CycleSubmission.R5.PrologueRun

/-- The historical proof splits the constant window just before its final SHR.
This exact list identity reconnects both sides of that split. -/
theorem historical_partition : oldProgram ++ tailProgram =
    preparedProloguepart1Program ++ preparedProloguepart2Program := by rfl

def prologuePairProgram : List Instr := newProgram ++ tailProgram

/-- This is a congruence theorem for the complete historical two-part prologue,
not merely an isolated arithmetic identity. -/
theorem prologue_pair_run_eq (s : State) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prologuePairProgram {s with pc := UInt256.ofNat 5090, stack := rest} =
    runInstructions (preparedProloguepart1Program ++ preparedProloguepart2Program)
      {s with pc := UInt256.ofNat 5090, stack := rest} := by
  rw [← historical_partition, prologuePairProgram,
    runInstructions_append, runInstructions_append, replacement_run s rest hcap hact]

#print axioms prologue_pair_run_eq

/-- Unchanged continuation after the historical two-part constant setup. -/
def prologueSuffixProgram : List Instr :=
    preparedProloguepart3Program ++
    preparedProloguepart4Program ++
    preparedProloguepart5Program ++
    preparedProloguepart6Program ++
    preparedProloguepart7Program ++
    preparedProloguepart8Program ++
    preparedProloguepart9Program ++
    preparedProloguepart10Program

/-- Complete folded prologue: bytes 5334 through 5489. -/
def foldedPrologueProgram : List Instr :=
  preparedProloguepart0Program ++ (prologuePairProgram ++ prologueSuffixProgram)

theorem historical_full_partition : preparedPrologueProgram =
    preparedProloguepart0Program ++
      ((preparedProloguepart1Program ++ preparedProloguepart2Program) ++ prologueSuffixProgram) := by rfl

#check historical_full_partition

/-- Opaque composition prevents reduction of the full interpreter during splicing. -/
theorem compose_splice (pre old new suffix : List Instr) (entry middle : State)
    (hprefix : runInstructions pre entry = some middle)
    (hbody : runInstructions new middle = runInstructions old middle) :
    runInstructions (pre ++ (new ++ suffix)) entry =
    runInstructions (pre ++ (old ++ suffix)) entry := by
  simp only [runInstructions_append, hprefix, Option.bind_some, hbody]

/-- The prefix establishes the exact entry contract for the proved constant fold. -/
theorem prefix_model_pair_eq (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prologuePairProgram (preparedProloguepart0Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest) =
    runInstructions (preparedProloguepart1Program ++ preparedProloguepart2Program)
      (preparedProloguepart0Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest) := by
  let v0 : UInt256 := UInt256.shiftLeft f11 (UInt256.ofNat 16)
  let mem : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 192
  have hc : (v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest).length ≤ 1018 := by
    simp only [List.length_cons]
    omega
  simpa only [preparedProloguepart0Model, v0, mem] using
    prologue_pair_run_eq ({s with memory := mem})
      (v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest) hc hact

#print axioms prefix_model_pair_eq

/-- Whole prologue state equality at its real entry, including the prefix store.
The 960-tail capacity and 88-word memory bound are exactly the existing contract. -/
theorem full_prologue_run_eq (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions foldedPrologueProgram
      {s with pc := UInt256.ofNat 5080, stack := f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} =
    runInstructions preparedPrologueProgram
      {s with pc := UInt256.ofNat 5080, stack := f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} := by
  rw [foldedPrologueProgram, historical_full_partition]
  exact compose_splice _ _ _ _ _ _
    (preparedProloguepart0_run s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact)
    (prefix_model_pair_eq s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact)

/-- Folded bytes implement the complete pre-existing 5334..5489 state model. -/
theorem folded_prologue_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions foldedPrologueProgram
      {s with pc := UInt256.ofNat 5080, stack := f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} =
      some (preparedPrologueModel s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest) := by
  rw [full_prologue_run_eq s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact]
  exact preparedPrologue_run s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact

#print axioms full_prologue_run_eq
#print axioms folded_prologue_run

/-- Drop-in executor theorem for the existing R5 proSeg caller contract. -/
theorem folded_proSeg_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions foldedPrologueProgram {s with pc := UInt256.ofNat 5080, stack := f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} =
      some {s with pc := UInt256.ofNat 5198, memory := (proSegM7 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15), stack := (proSegV8_0 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV8_1 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_0 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_1 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_2 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_3 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_4 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV0_0 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} := by
  rw [full_prologue_run_eq s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact]
  exact proSeg_run s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact

#print axioms folded_proSeg_run
end ConstantFold5349
