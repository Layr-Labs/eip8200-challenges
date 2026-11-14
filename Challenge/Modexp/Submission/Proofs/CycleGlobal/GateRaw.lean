import Challenge.Modexp.Submission.Proofs.CycleGlobal.DirectWordMath
import Challenge.Modexp.Submission.Proofs.CycleGlobal.GateScratch
import Challenge.Modexp.Submission.Proofs.CycleGlobal.SlimFrames
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
theorem booleanMiss (a b c d : UInt256)
 (hc : UInt256.isTrue (UInt256.lor (UInt256.xor a b) (UInt256.xor c d))) :
 UInt256.land (UInt256.eq a b) (UInt256.eq c d) = UInt256.ofNat 0 := by
 by_cases h1 : a = b
 · by_cases h2 : c = d
   · have hz1 : UInt256.xor a b = UInt256.ofNat 0 := (WindowGuardLogic.wordXor_eq_zero_iff _ _).2 h1
     have hz2 : UInt256.xor c d = UInt256.ofNat 0 := (WindowGuardLogic.wordXor_eq_zero_iff _ _).2 h2
     have hz3 : UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by decide
     rw [hz1,hz2,hz3] at hc
     exact False.elim (hc (by decide))
   · simp [CycleSubmission.Global.DirectWordMath.eq_word,h1,h2]
     decide
 · by_cases h2 : c = d <;> simp [CycleSubmission.Global.DirectWordMath.eq_word,h1,h2] <;> decide
def prefixProgram : List Instr := [.op .JUMPDEST]
def testProgram : List Instr :=
 [.push 2 2656,.op .MLOAD,.op .CALLDATALOAD,
  .push 1 232,.op .SHR,.push 3 65537,.op .EQ,
  .push 1 32,.op .CALLDATALOAD,.push 1 3,.op .EQ,.op .AND,
  .push 1 15,.op (.Dup ⟨15,by decide⟩),.op (.Swap ⟨1,by decide⟩),
  .push 2 8585,.op .JUMPI]
def guardProgram : List Instr := prefixProgram++testProgram
def frame (s : State) (mem : ByteArray) (pc n bsize esize msize : Nat) : State :=
 {s with memory := mem,pc := UInt256.ofNat pc,stack := CycleSubmission.Global.SlimFrames.outer mem n bsize esize msize}
def exponentWord (s : State) (bsize : Nat) : UInt256 :=
 UInt256.shiftRight (MachineState.readWord s.executionEnv.calldata (96+bsize)) (UInt256.ofNat 232)
def guardValue (s : State) (bsize esize : Nat) : UInt256 :=
 UInt256.lor (UInt256.xor (UInt256.ofNat 3) (UInt256.ofNat esize))
   (UInt256.xor (UInt256.ofNat 65537) (exponentWord s bsize))
def entryState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
 frame s mem 2534 n bsize esize msize
def e3go (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
 frame s mem 2527 n bsize esize msize
def e3Program : List Instr := [
  .op .JUMPDEST,
   .op (.Dup ⟨13,by decide⟩),
   .push 0 0,
   .push 2 8585,
   .op .JUMP]
theorem run_e3 (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
 (hd : Decode.isValidJumpDest s.executionEnv.code 8585 = true) :
 runInstructions e3Program (e3go s mem n bsize esize msize) =
   some (CycleSubmission.Global.SlimFrames.special s mem n bsize esize msize 1) := by
 simp [Exp.push0_word,e3Program,e3go,frame,runInstructions,Stepper.runInstr,
  CycleSubmission.Global.SlimFrames.special,CycleSubmission.Global.SlimFrames.outer,CycleSubmission.Global.Fast.Shift.entrySlots,CycleSubmission.Global.Fast.Shift.aprevSlot,CycleSubmission.Global.Fast.Shift.hdSlot,Exp.outer,hd,Word.literal_eq_ofNat,
  Word.word_toNat_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod]
theorem pointer (bsize : Nat) (hb : bsize ≤ 1024) :
 (UInt256.ofNat 96 + UInt256.ofNat bsize).toNat = 96+bsize := by
 rw [Word.ofNat_add_mod,Word.word_toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
def storedFrame (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
 {s with
   pc := UInt256.ofNat 2535
   memory := GateScratch.memory mem esize
   stack := SlimFrames.outer mem n bsize esize msize}
theorem run_prefix (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
 (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions prefixProgram (frame s mem 2534 n bsize esize msize) =
 some (storedFrame s mem n bsize esize msize) := by
 have haw : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2656 32) = s.activeWords :=
  Monpro.activeWords_fix s 2656 32 (by decide) (by norm_num) hact
 simp [prefixProgram,runInstructions,Stepper.runInstr,frame,storedFrame,List.exchange,
  SlimFrames.outer,CycleSubmission.Global.Fast.Shift.entrySlots,
  CycleSubmission.Global.Fast.Shift.aprevSlot,CycleSubmission.Global.Fast.Shift.hdSlot,
  Exp.outer,GateScratch.memory,GateScratch.value,State.activeWordsAfterUInt256,haw,
  Word.literal_eq_ofNat,Word.word_toNat_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod]
theorem run_test_hit (s : State) (mem : ByteArray) (n bsize msize : Nat)
 (hb : bsize ≤ 1024) (hact : 88 ≤ s.activeWords.toNat)
 (he : exponentWord s bsize = UInt256.ofNat 65537)
 (hd : Decode.isValidJumpDest s.executionEnv.code 8585 = true)
 (hsize : MachineState.readWord s.executionEnv.calldata 32 = UInt256.ofNat 3)
 (hptr : MachineState.readWord mem 2656 = UInt256.ofNat (96+bsize)) :
 runInstructions testProgram (storedFrame s mem n bsize 3 msize) =
   some (CycleSubmission.Global.SlimFrames.special s (GateScratch.memory mem 3) n bsize 3 msize 16) := by
 simp only [CycleSubmission.Global.SlimFrames.special,CycleSubmission.Global.SlimFrames.guardFrame,GateScratch.memory]
 have haw : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2656 32) = s.activeWords :=
  Monpro.activeWords_fix s 2656 32 (by decide) (by norm_num) hact
 have hp : (96+bsize) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 96+bsize := Nat.mod_eq_of_lt (by omega)
 have he' := he
 simp only [exponentWord] at he'
 have hx : UInt256.xor (UInt256.ofNat 65537) (UInt256.ofNat 65537) = UInt256.ofNat 0 := by decide
 have hs : UInt256.xor (UInt256.ofNat 3) (UInt256.ofNat 3) = UInt256.ofNat 0 := by decide
 have ho : UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by decide
 simp [testProgram,storedFrame,List.exchange,CycleSubmission.Global.SlimFrames.special,runInstructions,Stepper.runInstr,frame,
   CycleSubmission.Global.SlimFrames.special,CycleSubmission.Global.SlimFrames.outer,CycleSubmission.Global.Fast.Shift.entrySlots,CycleSubmission.Global.Fast.Shift.aprevSlot,CycleSubmission.Global.Fast.Shift.hdSlot,Exp.outer,CycleSubmission.Global.DirectWordMath.eq_word,GateScratch.value,GateScratch.memory,Memory.readWord_writeWord,State.activeWordsAfterUInt256,haw,pointer bsize hb,hp,hsize,hptr,he',hx,hs,ho,
   hd,UInt256.isZero,UInt256.isTrue,Word.literal_eq_ofNat,Word.word_toNat_ofNat,
   Word.succ_ofNat_mod,Word.ofNat_add_mod]
theorem run_test_miss (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
 (hb : bsize ≤ 1024) (hact : 88 ≤ s.activeWords.toNat)
 (hc : UInt256.isTrue (guardValue s bsize esize))
 (hsize : MachineState.readWord s.executionEnv.calldata 32 = UInt256.ofNat esize)
 (hptr : MachineState.readWord mem 2656 = UInt256.ofNat (96+bsize)) :
 runInstructions testProgram (storedFrame s mem n bsize esize msize) =
   some (CycleSubmission.Global.SlimFrames.guardFrame s (GateScratch.memory mem esize) 2563 n bsize esize msize) := by
 simp only [CycleSubmission.Global.SlimFrames.special,CycleSubmission.Global.SlimFrames.guardFrame,GateScratch.memory]
 have haw : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2656 32) = s.activeWords :=
  Monpro.activeWords_fix s 2656 32 (by decide) (by norm_num) hact
 have hp : (96+bsize) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 96+bsize := Nat.mod_eq_of_lt (by omega)
 have hmask := booleanMiss (UInt256.ofNat 3) (UInt256.ofNat esize)
   (UInt256.ofNat 65537) (exponentWord s bsize) hc
 simp only [exponentWord] at hmask
 simp [testProgram,storedFrame,List.exchange,runInstructions,Stepper.runInstr,frame,CycleSubmission.Global.SlimFrames.bailState,SlimFrames.guardFrame,SlimFrames.ridingFrame,CycleSubmission.Global.SlimFrames.ridingFrame,CycleSubmission.Global.SlimFrames.outer,CycleSubmission.Global.Fast.Shift.entrySlots,CycleSubmission.Global.Fast.Shift.aprevSlot,CycleSubmission.Global.Fast.Shift.hdSlot,Exp.outer,
   GateScratch.value,GateScratch.memory,Memory.readWord_writeWord,State.activeWordsAfterUInt256,haw,pointer bsize hb,hp,hsize,hptr,hmask,UInt256.isZero,UInt256.isTrue,
   Word.literal_eq_ofNat,Word.word_toNat_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod]
theorem run_guard_hit (s : State) (mem : ByteArray) (n bsize msize : Nat)
 (hb : bsize ≤ 1024) (hact : 88 ≤ s.activeWords.toNat)
 (he : exponentWord s bsize = UInt256.ofNat 65537)
 (hd : Decode.isValidJumpDest s.executionEnv.code 8585 = true)
 (hsize : MachineState.readWord s.executionEnv.calldata 32 = UInt256.ofNat 3)
 (hptr : MachineState.readWord mem 2656 = UInt256.ofNat (96+bsize)) :
 runInstructions guardProgram (frame s mem 2534 n bsize 3 msize) =
 some (SlimFrames.special s (GateScratch.memory mem 3) n bsize 3 msize 16) := by
 exact runInstructions_append_some _ _ _ _ _ (run_prefix s mem n bsize 3 msize hact)
  (run_test_hit s mem n bsize msize hb hact he hd hsize hptr)
theorem run_guard_miss (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
 (hb : bsize ≤ 1024) (hact : 88 ≤ s.activeWords.toNat)
 (hc : UInt256.isTrue (guardValue s bsize esize))
 (hsize : MachineState.readWord s.executionEnv.calldata 32 = UInt256.ofNat esize)
 (hptr : MachineState.readWord mem 2656 = UInt256.ofNat (96+bsize)) :
 runInstructions guardProgram (frame s mem 2534 n bsize esize msize) =
 some (SlimFrames.guardFrame s (GateScratch.memory mem esize) 2563 n bsize esize msize) := by
 exact runInstructions_append_some _ _ _ _ _ (run_prefix s mem n bsize esize msize hact)
  (run_test_miss s mem n bsize esize msize hb hact hc hsize hptr)
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
def bailProgram : List Instr := [
  .push 1 207,
   .op .JUMP]
theorem run_bail (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
 (hd : Decode.isValidJumpDest s.executionEnv.code 207 = true) :
 runInstructions bailProgram (CycleSubmission.Global.SlimFrames.guardFrame s mem 2563 n bsize esize msize) =
 some (CycleSubmission.Global.SlimFrames.bailState s mem n bsize esize msize) := by
 simp [bailProgram,CycleSubmission.Global.SlimFrames.guardFrame,CycleSubmission.Global.SlimFrames.bailState,SlimFrames.guardFrame,
  CycleSubmission.Global.SlimFrames.outer,CycleSubmission.Global.Fast.Shift.entrySlots,CycleSubmission.Global.Fast.Shift.aprevSlot,CycleSubmission.Global.Fast.Shift.hdSlot,Exp.outer,
  runInstructions,Stepper.runInstr,hd,Word.literal_eq_ofNat,Word.word_toNat_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod]
end CycleSubmission.Global.GateRaw
#print axioms CycleSubmission.Global.GateRaw.run_guard_hit
#print axioms CycleSubmission.Global.GateRaw.run_guard_miss
#print axioms CycleSubmission.Global.GateRaw.miss_size
#print axioms CycleSubmission.Global.GateRaw.miss_exponent
