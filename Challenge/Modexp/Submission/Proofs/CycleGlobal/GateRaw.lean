import Challenge.Modexp.Submission.Proofs.Bytecode.WindowGuardLogic
import Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
noncomputable section
set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.GateRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast

def guardProgram : List Instr :=
 [.op .JUMPDEST, .op (.Dup ⟨2, by decide⟩), .push 1 96, .op .ADD,
  .op .CALLDATALOAD, .push 1 232, .op .SHR, .push 3 65537, .op .XOR,
  .op (.Dup ⟨4, by decide⟩), .push 1 3, .op .XOR, .op .OR,
  .push 1 207, .op .JUMPI]
def hitProgram : List Instr := guardProgram ++ [.push 1 16]
def frame (s : State) (mem : ByteArray) (pc n bsize esize msize : Nat) : State :=
 {s with memory := mem, pc := UInt256.ofNat pc, stack := Exp.outer n bsize esize msize}
def exponentWord (s : State) (bsize : Nat) : UInt256 :=
 UInt256.shiftRight (MachineState.readWord s.executionEnv.calldata (96+bsize)) (UInt256.ofNat 232)
def guardValue (s : State) (bsize esize : Nat) : UInt256 :=
 UInt256.lor (UInt256.xor (UInt256.ofNat 3) (UInt256.ofNat esize))
   (UInt256.xor (UInt256.ofNat 65537) (exponentWord s bsize))

def entryState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
 frame s mem 2312 n bsize esize msize
def e3go (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
 frame s mem 2304 n bsize esize msize
def e3Program : List Instr := [.op .JUMPDEST, .push 1 1, .push 2 2336, .op .JUMP]
theorem run_e3 (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
 (hd : Decode.isValidJumpDest s.executionEnv.code 2336 = true) :
 runInstructions e3Program (e3go s mem n bsize esize msize) =
   some (FixedDirectStates.special s mem n bsize esize msize 1) := by
 simp [e3Program, e3go, frame, runInstructions, Stepper.runInstr,
  FixedDirectStates.special, Exp.outer, hd, Word.literal_eq_ofNat,
  Word.word_toNat_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod]

theorem pointer (bsize : Nat) (hb : bsize ≤ 1024) :
 (UInt256.ofNat 96 + UInt256.ofNat bsize).toNat = 96+bsize := by
 rw [Word.ofNat_add_mod, Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem run_hit (s : State) (mem : ByteArray) (n bsize msize : Nat)
 (hb : bsize ≤ 1024) (he : exponentWord s bsize = UInt256.ofNat 65537) :
 runInstructions hitProgram (frame s mem 2312 n bsize 3 msize) =
   some (FixedDirectStates.special s mem n bsize 3 msize 16) := by
 have hp : (96+bsize) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 96+bsize := Nat.mod_eq_of_lt (by omega)
 have he' := he
 simp only [exponentWord] at he'
 have hx : UInt256.xor (UInt256.ofNat 65537) (UInt256.ofNat 65537) = UInt256.ofNat 0 := by decide
 have hs : UInt256.xor (UInt256.ofNat 3) (UInt256.ofNat 3) = UInt256.ofNat 0 := by decide
 have ho : UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by decide
 simp [hitProgram, guardProgram, runInstructions, Stepper.runInstr, frame,
   FixedDirectStates.special, Exp.outer, pointer bsize hb, hp, he', hx, hs, ho,
   UInt256.isTrue, Word.literal_eq_ofNat, Word.word_toNat_ofNat,
   Word.succ_ofNat_mod, Word.ofNat_add_mod]

theorem run_guard_hit (s : State) (mem : ByteArray) (n bsize msize : Nat)
 (hb : bsize ≤ 1024) (he : exponentWord s bsize = UInt256.ofNat 65537) :
 runInstructions guardProgram (frame s mem 2312 n bsize 3 msize) =
   some (frame s mem 2334 n bsize 3 msize) := by
 have hp : (96+bsize) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 96+bsize := Nat.mod_eq_of_lt (by omega)
 have he' := he
 simp only [exponentWord] at he'
 have hx : UInt256.xor (UInt256.ofNat 65537) (UInt256.ofNat 65537) = UInt256.ofNat 0 := by decide
 have hs : UInt256.xor (UInt256.ofNat 3) (UInt256.ofNat 3) = UInt256.ofNat 0 := by decide
 have ho : UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by decide
 simp [hitProgram, guardProgram, runInstructions, Stepper.runInstr, frame,
   FixedDirectStates.special, Exp.outer, pointer bsize hb, hp, he', hx, hs, ho,
   UInt256.isTrue, Word.literal_eq_ofNat, Word.word_toNat_ofNat,
   Word.succ_ofNat_mod, Word.ofNat_add_mod]

theorem run_miss (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
 (hb : bsize ≤ 1024) (hc : UInt256.isTrue (guardValue s bsize esize))
 (hd : Decode.isValidJumpDest s.executionEnv.code 207 = true) :
 runInstructions guardProgram (frame s mem 2312 n bsize esize msize) =
   some (frame s mem 207 n bsize esize msize) := by
 have hp : (96+bsize) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 96+bsize := Nat.mod_eq_of_lt (by omega)
 have hc' := hc
 simp only [guardValue, exponentWord] at hc'
 simp [guardProgram, runInstructions, Stepper.runInstr, frame, Exp.outer,
   pointer bsize hb, hp, hc', hd,
   Word.literal_eq_ofNat, Word.word_toNat_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod]

theorem miss_size (s : State) (bsize esize : Nat)
 (he : UInt256.ofNat esize ≠ UInt256.ofNat 3) : UInt256.isTrue (guardValue s bsize esize) := by
 show (guardValue s bsize esize).toNat ≠ 0
 intro h
 have hz : guardValue s bsize esize = 0 := Word.word_ext (h.trans (by decide))
 have hx := (WindowGuardLogic.wordOr_eq_zero_iff _ _).1 hz
 have heq := (WindowGuardLogic.wordXor_eq_zero_iff _ _).1 hx.1
 exact he heq.symm

theorem miss_exponent (s : State) (bsize esize : Nat)
 (he : exponentWord s bsize ≠ UInt256.ofNat 65537) : UInt256.isTrue (guardValue s bsize esize) := by
 show (guardValue s bsize esize).toNat ≠ 0
 intro h
 have hz : guardValue s bsize esize = 0 := Word.word_ext (h.trans (by decide))
 have hx := (WindowGuardLogic.wordOr_eq_zero_iff _ _).1 hz
 have heq := (WindowGuardLogic.wordXor_eq_zero_iff _ _).1 hx.2
 exact he heq.symm
theorem run_hitPush (s : State) (mem : ByteArray) (n bsize msize : Nat) :
 runInstructions [.push 1 16] (frame s mem 2334 n bsize 3 msize) =
 some (FixedDirectStates.special s mem n bsize 3 msize 16) := by
 simp [runInstructions, Stepper.runInstr, frame, FixedDirectStates.special, Exp.outer,
 Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod]
end CycleSubmission.Global.GateRaw
#print axioms CycleSubmission.Global.GateRaw.run_hit
#print axioms CycleSubmission.Global.GateRaw.run_miss
#print axioms CycleSubmission.Global.GateRaw.miss_size
#print axioms CycleSubmission.Global.GateRaw.miss_exponent
