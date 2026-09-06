import Challenge.EvmProof.Stepper
import Challenge.Modexp.Submission.Proofs.Fast.RrLeadingLogic

set_option warningAsError true
set_option maxHeartbeats 4000000

/-!
# Artifact-independent execution core for the direct RR counter helper

This file deliberately proves only the symbolic `runInstr` computation.
Decoder/location facts and the `runInstr_sound` lift belong to the future
candidate Artifact and are listed as bridge obligations below.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.RrLeadingTraceCore

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast.RrLeadingLogic

def runInstructions : List Instr → State → Option State
  | [], state => some state
  | instruction :: rest, state => do
      let next ← Challenge.EvmProof.Stepper.runInstr instruction state
      runInstructions rest next

theorem runInstructions_append (left right : List Instr) (state : State) :
    runInstructions (left ++ right) state =
      (runInstructions left state).bind (runInstructions right) := by
  induction left generalizing state with
  | nil => rfl
  | cons instruction left ih =>
      simp [runInstructions, ih, Option.bind_assoc]

theorem runInstructions_append_some (left right : List Instr)
    (start middle finish : State)
    (hleft : runInstructions left start = some middle)
    (hright : runInstructions right middle = some finish) :
    runInstructions (left ++ right) start = some finish := by
  rw [runInstructions_append, hleft]
  exact hright

/-- The exact inherited stack frame at the helper entry and RR-loop rejoin. -/
def outer (n bsize esize msize : Nat) : List UInt256 :=
  [UInt256.ofNat (32 * n), UInt256.ofNat n, UInt256.ofNat bsize,
   UInt256.ofNat esize, UInt256.ofNat msize]

/-- pc 3741..3752: load the established size word and copy CC to RR. -/
def copyProgram : List Instr :=
  [.op .JUMPDEST,
   .push ⟨2, by decide⟩ (UInt256.ofNat 9344), .op .MLOAD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 5120),
   .push ⟨2, by decide⟩ (UInt256.ofNat 6144), .op .MCOPY]

/-- pc 3753..3771: four threshold comparisons and their sum. -/
def counterProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .push ⟨1, by decide⟩ (UInt256.ofNat 3), .op .LT,
   .op (.Dup ⟨2, by decide⟩), .push ⟨1, by decide⟩ (UInt256.ofNat 7), .op .LT,
   .op (.Dup ⟨3, by decide⟩), .push ⟨1, by decide⟩ (UInt256.ofNat 15), .op .LT,
   .op (.Dup ⟨4, by decide⟩), .push ⟨1, by decide⟩ (UInt256.ofNat 31), .op .LT,
   .op .ADD, .op .ADD, .op .ADD]

/-- pc 3772..3775: rejoin the inherited RR head at pc 1569. -/
def jumpProgram : List Instr :=
  [.push ⟨2, by decide⟩ (UInt256.ofNat 1569), .op .JUMP]

def helperProgram : List Instr := copyProgram ++ counterProgram ++ jumpProgram

def copiedMemory (mem : ByteArray) (n : Nat) : ByteArray :=
  MachineState.writeBytes mem
    (MachineState.readPadded mem 5120 (32 * n)) 6144

def loadActiveWords (template : State) : UInt256 :=
  template.activeWordsAfterUInt256 9344 32

def copiedActiveWords (template : State) (n : Nat) : UInt256 :=
  State.activeWordsAfterUInt256_2
    ({template with activeWords := loadActiveWords template} : State)
    6144 (32 * n) 5120 (32 * n)

def entryState (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { template with
    pc := UInt256.ofNat 3741
    stack := outer n bsize esize msize
    memory := mem }

def copiedState (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { template with
    pc := UInt256.ofNat 3753
    stack := outer n bsize esize msize
    memory := copiedMemory mem n
    activeWords := copiedActiveWords template n }

def counterState (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { template with
    pc := UInt256.ofNat 3772
    stack := UInt256.ofNat (directCounter n) :: outer n bsize esize msize
    memory := copiedMemory mem n
    activeWords := copiedActiveWords template n }

/-- Exact state expected by the current inherited `Fast.Exp.rrHead`. -/
def exitState (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { template with
    pc := UInt256.ofNat 1569
    stack := UInt256.ofNat (directCounter n) :: outer n bsize esize msize
    memory := copiedMemory mem n
    activeWords := copiedActiveWords template n }

theorem sizeWord_toNat {n : Nat} (hn32 : n ≤ 32) :
    (UInt256.ofNat (32 * n)).toNat = 32 * n := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
  have hpow : 1024 < 2 ^ 256 := by norm_num
  omega

theorem wordLt_ofNat (threshold n : Nat)
    (hthreshold : threshold < 2 ^ 256) (hn : n < 2 ^ 256) :
    UInt256.lt (UInt256.ofNat threshold) (UInt256.ofNat n) =
      UInt256.ofNat (ltWord threshold n) := by
  simp only [UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hthreshold, Nat.mod_eq_of_lt hn]
  unfold ltWord
  split <;> rfl

theorem counterWord (n : Nat) (hn32 : n ≤ 32) :
    ((UInt256.lt (UInt256.ofNat 31) (UInt256.ofNat n) +
          UInt256.lt (UInt256.ofNat 15) (UInt256.ofNat n)) +
        UInt256.lt (UInt256.ofNat 7) (UInt256.ofNat n)) +
      UInt256.lt (UInt256.ofNat 3) (UInt256.ofNat n) =
        UInt256.ofNat (directCounter n) := by
  have hn : n < 2 ^ 256 := by
    have hpow : 32 < 2 ^ 256 := by norm_num
    omega
  rw [wordLt_ofNat 31 n (by norm_num) hn,
    wordLt_ofNat 15 n (by norm_num) hn,
    wordLt_ofNat 7 n (by norm_num) hn,
    wordLt_ofNat 3 n (by norm_num) hn,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]
  congr 1
  unfold directCounter
  omega

/-- Functional copy leaf.  Its only semantic input is the already-established
size word `32*n` at memory address 9344. -/
theorem run_copy (template : State) (mem : ByteArray)
    (n bsize esize msize : Nat) (hn32 : n ≤ 32)
    (hsize : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n)) :
    runInstructions copyProgram (entryState template mem n bsize esize msize) =
      some (copiedState template mem n bsize esize msize) := by
  have hpc :
      (((UInt256.ofNat 3741).succ + UInt256.ofNat 3).succ +
        UInt256.ofNat 3 + UInt256.ofNat 3).succ = UInt256.ofNat 3753 := by
    decide
  simp [copyProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    entryState, copiedState, copiedMemory, copiedActiveWords, loadActiveWords,
    State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
    outer, hsize, sizeWord_toNat hn32, hpc]

end Challenge.Modexp.Submission.Proofs.Fast.RrLeadingTraceCore

