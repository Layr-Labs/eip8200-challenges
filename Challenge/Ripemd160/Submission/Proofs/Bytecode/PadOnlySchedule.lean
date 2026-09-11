import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedSchedule
import Challenge.EvmProof.Memory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadOnlySchedule
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace
open DenseScheduleTemplate PairedScheduleMemory PairedMask32Cache

def zeroBytes : ByteArray := ByteArray.mk (Array.replicate 512 0)

def lowLength (n : UInt256) : UInt256 :=
  UInt256.land (UInt256.ofNat 0xffffffff)
    (UInt256.shiftLeft n (UInt256.ofNat 3))
def highLength (n : UInt256) : UInt256 :=
  UInt256.land (UInt256.ofNat 0xffffffff)
    (UInt256.shiftRight n (UInt256.ofNat 29))

def resultMemory (memory : ByteArray) (n : UInt256) : ByteArray :=
  writeWord (writeWord (writeWord
    (MachineState.writeBytes memory zeroBytes 0) 0 (UInt256.ofNat 128))
    448 (lowLength n)) 480 (highLength n)

def template : List Instr :=
 [ .push ⟨2, by decide⟩ (UInt256.ofNat 512), .op .CALLDATASIZE,
   .push ⟨0, by decide⟩ (UInt256.ofNat 0), .op .CALLDATACOPY,
   .push ⟨1, by decide⟩ (UInt256.ofNat 128),
   .push ⟨0, by decide⟩ (UInt256.ofNat 0), .op .MSTORE,
   .op .CALLDATASIZE, .push ⟨1, by decide⟩ (UInt256.ofNat 3), .op .SHL,
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 448), .op .MSTORE,
   .op .CALLDATASIZE, .push ⟨1, by decide⟩ (UInt256.ofNat 29), .op .SHR,
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 480), .op .MSTORE,
   .push ⟨0, by decide⟩ (UInt256.ofNat 0),
   .push ⟨0, by decide⟩ (UInt256.ofNat 0),
   .push ⟨0, by decide⟩ (UInt256.ofNat 0),
   .push ⟨0, by decide⟩ (UInt256.ofNat 0),
   .push ⟨0, by decide⟩ (UInt256.ofNat 0),
   .push ⟨1, by decide⟩ (UInt256.ofNat 22) ]

theorem readPadded_end (input : ByteArray) :
    MachineState.readPadded input input.size 512 = zeroBytes := by
  simp [MachineState.readPadded, zeroBytes]

theorem run_template (s : State) (pc returnPC : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256) :
    runInstrSeq template {s with pc := pc, stack := returnPC :: rest} =
      some {s with pc := pcAfter pc template, stack := [UInt256.ofNat 22, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0] ++ (returnPC :: rest), memory := resultMemory s.memory (UInt256.ofNat s.executionEnv.calldata.size)} := by
  have hcap (n : Nat) (hn : n ≤ 26) : rest.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_schedule_preserved s.activeWords address hactive haddress
  have hcopyActive :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 0 512) = s.activeWords := by
    have hm : max s.activeWords.toNat 16 = s.activeWords.toNat := Nat.max_eq_left (by omega)
    simpa [MachineState.activeWordsAfter, hm] using (Word.word_eq_ofNat_toNat s.activeWords).symm
  have hsize : (UInt256.ofNat s.executionEnv.calldata.size).toNat = s.executionEnv.calldata.size := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfit]
  simp (discharger := omega) [PairedHelperBooleanTrace.push0_toNat, template, resultMemory,
    lowLength, highLength, writeWord, runInstrSeq, Stepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero, Nat.add_assoc,
    hrun, hcap, State.activeWordsAfterUInt256, hactiveAt, hcopyActive, hsize,
    readPadded_end, Word.word_toNat_ofNat]
  all_goals repeat first | apply And.intro | rfl


#print axioms run_template
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadOnlySchedule
