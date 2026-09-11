import Challenge.Modexp.Submission.Proofs.Fast.SquareWords
import Challenge.Modexp.Submission.Proofs.Fast.EarlyCsubInstructions

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareInit
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.SquareWords
open Challenge.EvmProof.Word

def storeWord (mem : ByteArray) (addr : Nat) (x : UInt256) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded x.toNat 32) addr

def stateAt (s : State) (mem : ByteArray) (pc : Nat) (stack : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc, memory := mem, stack := stack }

def doubleProgram (addr : UInt256) : List Instr :=
  [.push 2 addr, .op .MLOAD, .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op .ADD, .op .OR,
   .push 2 addr, .op .MSTORE, .push 1 255, .op .SHR]

theorem run_double (s : State) (mem : ByteArray) (pc addr : Nat)
    (c : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1018)
    (hact : 296 ≤ s.activeWords.toNat) (haddr : addr+32 ≤ 9472) :
    runInstructions (doubleProgram (UInt256.ofNat addr)) (stateAt s mem pc (c :: rest)) =
      some (stateAt s (storeWord mem addr (doubled (MachineState.readWord mem addr) c))
        (pc+16) (highBit (MachineState.readWord mem addr) :: rest)) := by
  have hc1 : rest.length+1 < 1024 := by omega
  have hc2 : rest.length+2 < 1024 := by omega
  have hc3 : rest.length+3 < 1024 := by omega
  have hc4 : rest.length+4 < 1024 := by omega
  have hn : addr % 2^256 = addr := Nat.mod_eq_of_lt (by omega)
  norm_num only [Nat.reducePow] at hn
  have ha := EarlyCsub.activeWords_fix s addr 32 (by decide) haddr hact
  have hw : (255 : UInt256) = UInt256.ofNat 255 := by decide
  simp [doubleProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    stateAt, storeWord, doubled, highBit, hc1, hc2, hc3, hc4, hn, hw,
    State.activeWordsAfterUInt256, ha, List.exchange, Nat.add_assoc,
    word_toNat_ofNat, succ_ofNat_mod, ofNat_add_mod]

structure Doubling where
  memory : ByteArray
  carry : UInt256

def doubleWords (mem : ByteArray) : Nat → Doubling
  | 0 => ⟨mem, UInt256.ofNat 0⟩
  | j+1 =>
    let d := doubleWords mem j
    let addr := 8960 + 32*(7-j)
    let x := MachineState.readWord d.memory addr
    ⟨storeWord d.memory addr (doubled x d.carry), highBit x⟩

def wordsProgram : Nat → List Instr
  | 0 => []
  | j+1 => wordsProgram j ++ doubleProgram (UInt256.ofNat (8960+32*(7-j)))

theorem run_words (s : State) (mem : ByteArray) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) (hact : 296 ≤ s.activeWords.toNat) :
    ∀ j, j ≤ 8 →
      runInstructions (wordsProgram j) (stateAt s mem 5051 (UInt256.ofNat 0 :: rest)) =
        some (stateAt s (doubleWords mem j).memory (5051+16*j)
          ((doubleWords mem j).carry :: rest)) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have h := run_double s (doubleWords mem j).memory (5051+16*j)
      (8960+32*(7-j)) (doubleWords mem j).carry rest hcap hact (by omega)
    have prev := ih (by omega)
    have hp : 5051+16*j+16 = 5051+16*(j+1) := by omega
    simpa only [wordsProgram, doubleWords, hp] using
      runInstructions_append_some _ _ _ _ _ prev h

def initMemory (mem : ByteArray) : ByteArray :=
  storeWord (storeWord (doubleWords mem 8).memory 8928 (doubleWords mem 8).carry)
    9280 (UInt256.ofNat 5191)

def doubleFrom (d : Doubling) (start : Nat) : Nat → Doubling
  | 0 => d
  | j+1 =>
    let x := doubleFrom d start j
    let addr := 8960+32*(7-(start+j))
    let a := MachineState.readWord x.memory addr
    ⟨storeWord x.memory addr (doubled a x.carry), highBit a⟩

def fromProgram (start : Nat) : Nat → List Instr
  | 0 => []
  | j+1 => fromProgram start j ++ doubleProgram (UInt256.ofNat (8960+32*(7-(start+j))))

theorem doubleFrom_words (mem : ByteArray) (start : Nat) (j : Nat) :
    doubleFrom (doubleWords mem start) start j = doubleWords mem (start+j) := by
  induction j with
  | zero => simp only [doubleFrom, Nat.add_zero]
  | succ j ih =>
    simp only [doubleFrom, ih, Nat.add_succ, doubleWords]
    rfl

theorem run_from (s : State) (d : Doubling) (start pc : Nat) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) (hact : 296 ≤ s.activeWords.toNat) :
    ∀ j, start+j ≤ 8 →
      runInstructions (fromProgram start j) (stateAt s d.memory pc (d.carry :: rest)) =
        some (stateAt s (doubleFrom d start j).memory (pc+16*j)
          ((doubleFrom d start j).carry :: rest)) := by
  intro j
  induction j with
  | zero => intro _; simp only [fromProgram, runInstructions, doubleFrom, Nat.mul_zero, Nat.add_zero]
  | succ j ih =>
    intro hj
    have h := run_double s (doubleFrom d start j).memory (pc+16*j)
      (8960+32*(7-(start+j))) (doubleFrom d start j).carry rest hcap hact (by omega)
    have prev := ih (by omega)
    have hp : pc+16*j+16 = pc+16*(j+1) := by omega
    simpa only [fromProgram, doubleFrom, hp] using
      runInstructions_append_some _ _ _ _ _ prev h

def finishProgram : List Instr :=
  [.push 2 8928, .op .MSTORE, .push 2 5191, .push 2 9280, .op .MSTORE]

def finishMemory (d : Doubling) : ByteArray :=
  storeWord (storeWord d.memory 8928 d.carry) 9280 (UInt256.ofNat 5191)

theorem run_finish (s : State) (d : Doubling) (pc : Nat) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions finishProgram (stateAt s d.memory pc (d.carry :: rest)) =
      some (stateAt s (finishMemory d) (pc+11) rest) := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length+1 < 1024 := by omega
  have hc2 : rest.length+2 < 1024 := by omega
  have haD := EarlyCsub.activeWords_fix s 8928 32 (by decide) (by decide) hact
  have haR := EarlyCsub.activeWords_fix s 9280 32 (by decide) (by decide) hact
  have hd : (8928 : UInt256).toNat = 8928 := by decide
  have hr : (9280 : UInt256).toNat = 9280 := by decide
  have hv : (5191 : UInt256) = UInt256.ofNat 5191 := by decide
  simp [finishProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    stateAt, finishMemory, storeWord, hc0, hc1, hc2, haD, haR, hd, hr, hv,
    State.activeWordsAfterUInt256, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc]

end Challenge.Modexp.Submission.Proofs.Fast.SquareInit
