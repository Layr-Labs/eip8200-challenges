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
    9280 (UInt256.ofNat 5190)

def prefixProgram : List Instr := [.op .JUMPDEST, .push 0 0]
def finishProgram : List Instr :=
  [.push 2 8928, .op .MSTORE, .push 2 5190, .push 2 9280, .op .MSTORE]
def initProgram : List Instr := prefixProgram ++ wordsProgram 8 ++ finishProgram

theorem run_prefix (s : State) (mem : ByteArray) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) :
    runInstructions prefixProgram (stateAt s mem 5049 rest) =
      some (stateAt s mem 5051 (UInt256.ofNat 0 :: rest)) := by
  simp [prefixProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, stateAt,
    show rest.length < 1024 by omega, succ_ofNat_mod, ofNat_add_mod]
  rfl

theorem run_finish (s : State) (mem : ByteArray) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions finishProgram
      (stateAt s (doubleWords mem 8).memory 5179 ((doubleWords mem 8).carry :: rest)) =
      some (stateAt s (initMemory mem) 5190 rest) := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length+1 < 1024 := by omega
  have hc2 : rest.length+2 < 1024 := by omega
  have haD := EarlyCsub.activeWords_fix s 8928 32 (by decide) (by decide) hact
  have haR := EarlyCsub.activeWords_fix s 9280 32 (by decide) (by decide) hact
  have hd : (8928 : UInt256).toNat = 8928 := by decide
  have hr : (9280 : UInt256).toNat = 9280 := by decide
  have hv : (5190 : UInt256) = UInt256.ofNat 5190 := by decide
  simp [finishProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    stateAt, initMemory, storeWord, hc0, hc1, hc2, haD, haR, hd, hr, hv,
    State.activeWordsAfterUInt256, succ_ofNat_mod, ofNat_add_mod]

theorem run_init (s : State) (mem : ByteArray) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions initProgram (stateAt s mem 5049 rest) =
      some (stateAt s (initMemory mem) 5190 rest) := by
  have p := run_prefix s mem rest hcap
  have w := run_words s mem rest hcap hact 8 (by decide)
  have f := run_finish s mem rest hcap hact
  exact runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _ p w) f

end Challenge.Modexp.Submission.Proofs.Fast.SquareInit
