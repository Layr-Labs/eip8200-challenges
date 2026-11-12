import Challenge.Modexp.Submission.Proofs.CycleGlobal.DirectBoundMath
import Challenge.Modexp.Submission.Proofs.CycleGlobal.SlimFrames
import Challenge.Modexp.Submission.Proofs.Cycle.EntryMeaning
import Challenge.Modexp.Submission.Proofs.CycleCaller.Memory
noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.DirectEightRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission.EntryMeaning
def guardWord (mem : ByteArray) : UInt256 :=
 UInt256.shiftRight (UInt256.lnot (MachineState.readWord mem 2112)) (UInt256.ofNat 146)
def memory (mem : ByteArray) : ByteArray := StagedOperand.stage mem 2112 8
def frame (mem : ByteArray) (count width : UInt256) (bsize esize : Nat) : Caller where
 pbi := MachineState.readWord mem 1376
 hd := CycleSubmission.Global.Fast.Shift.hdSlot mem
 w3 := width
 ent := MachineState.readWord mem 1312
 m32 := MachineState.readWord mem 1344
 m128 := MachineState.readWord mem 1408
 m64 := MachineState.readWord mem 1440
 m0 := MachineState.readWord mem 1472
 tl := MachineState.readWord mem 1504
 m96 := MachineState.readWord mem 1632
 inv := MachineState.readWord mem 1664
 tn := MachineState.readWord mem 1568
 aprev := CycleSubmission.Global.Fast.Shift.aprevSlot mem
 counter := count
 ret := CycleSubmission.Global.Fast.Shift.headWord mem 8
 tail := (SlimFrames.outer mem 8 bsize esize 256).drop 13
def state (s : State) (mem : ByteArray) (pc : Nat) (count width : UInt256) (bsize esize : Nat) : State :=
 {s with pc := UInt256.ofNat pc, memory := mem, stack := [count,width]++SlimFrames.outer mem 8 bsize esize 256}
def guardProgram : List Instr :=
 [.op .JUMPDEST,.push 2 2112,.op .MLOAD,.push 32 (UInt256.ofNat (2^256-2^146-1)),
 .op .LT,.push 2 207,.op .JUMPI]
def finishProgram : List Instr :=
 [.push 2 256,.push 2 2112,.push 2 2368,.op .MCOPY,.op (.Swap ⟨12,by decide⟩),
 .push 0 0,.op .NOT,.op (.Swap ⟨4,by decide⟩),.push 4 5411,.op .JUMP]
def entered (s : State) (mem : ByteArray) (count width : UInt256) (bsize esize : Nat) : State :=
 {s with pc := UInt256.ofNat 5411, memory := memory mem, stack := saved (frame mem count width bsize esize)}
theorem run_hit (s : State) (mem : ByteArray) (count width : UInt256) (bsize esize : Nat)
 (hact : 88 ≤ s.activeWords.toNat) (hg : (guardWord mem).toNat ≠ 0) :
 runInstructions guardProgram (state s mem 3150 count width bsize esize) =
 some (state s mem 3193 count width bsize esize) := by
 have hf := Monpro.activeWords_fix s 2112 32 (by decide) (by norm_num) hact
 have hb : ¬ (2^256-2^146-1 < (MachineState.readWord mem 2112).toNat) := by
  intro h
  exact hg ((CycleSubmission.Global.DirectBoundMath.zero_iff _).mpr h)
 simp only [guardWord] at hg
 simp [CycleSubmission.Global.DirectBoundMath.guard_eq,hb,guardProgram,state,SlimFrames.outer,CycleSubmission.Global.Fast.Shift.entrySlots,CycleSubmission.Global.Fast.Shift.aprevSlot,CycleSubmission.Global.Fast.Shift.hdSlot,Exp.outer,
  runInstructions,Stepper.runInstr,UInt256.isZero,UInt256.isTrue,State.activeWordsAfterUInt256,hf,hg,
  Word.literal_eq_ofNat,Word.word_toNat_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod]
 all_goals omega
theorem run_miss (s : State) (mem : ByteArray) (count width : UInt256) (bsize esize : Nat)
 (hact : 88 ≤ s.activeWords.toNat) (hg : (guardWord mem).toNat = 0)
 (hd : Decode.isValidJumpDest s.executionEnv.code 207 = true) :
 runInstructions guardProgram (state s mem 3150 count width bsize esize) =
 some (state s mem 207 count width bsize esize) := by
 have hf := Monpro.activeWords_fix s 2112 32 (by decide) (by norm_num) hact
 have hb : 2^256-2^146-1 < (MachineState.readWord mem 2112).toNat :=
  (CycleSubmission.Global.DirectBoundMath.zero_iff _).mp hg
 simp only [guardWord] at hg
 simp [CycleSubmission.Global.DirectBoundMath.guard_eq,hb,guardProgram,state,SlimFrames.outer,CycleSubmission.Global.Fast.Shift.entrySlots,CycleSubmission.Global.Fast.Shift.aprevSlot,CycleSubmission.Global.Fast.Shift.hdSlot,Exp.outer,
  runInstructions,Stepper.runInstr,UInt256.isZero,UInt256.isTrue,State.activeWordsAfterUInt256,hf,hg,hd,
  Word.literal_eq_ofNat,Word.word_toNat_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod]
 all_goals omega
theorem run_finish (s : State) (mem : ByteArray) (count width : UInt256) (bsize esize : Nat)
 (hact : 88 ≤ s.activeWords.toNat)
 (hd : Decode.isValidJumpDest s.executionEnv.code 5411 = true) :
 runInstructions finishProgram (state s mem 3193 count width bsize esize) =
 some (entered s mem count width bsize esize) := by
 have hmax : UInt256.lnot (UInt256.ofNat 0) = UInt256.ofNat (2^256-1) := by decide
 have hf := Exp.activeWords_fix2 s 2368 256 2112 256 (by decide) (by decide) (by norm_num) (by norm_num) hact
 simp [hmax,finishProgram,state,entered,frame,saved,memory,StagedOperand.stage,SlimFrames.outer,
  CycleSubmission.Global.Fast.Shift.entrySlots,CycleSubmission.Global.Fast.Shift.aprevSlot,CycleSubmission.Global.Fast.Shift.hdSlot,Exp.outer,runInstructions,Stepper.runInstr,List.exchange,
  State.activeWordsAfterUInt256_2,hf,hd,Word.literal_eq_ofNat,Word.word_toNat_ofNat,
  Word.succ_ofNat_mod,Word.ofNat_add_mod]
 all_goals decide
theorem readWord (mem : ByteArray) (addr : Nat) (hd : addr+32 ≤ 2368 ∨ 2624 ≤ addr) :
 MachineState.readWord (memory mem) addr = MachineState.readWord mem addr :=
 StagedOperand.read_stage_outside mem 2112 8 addr (by simpa using hd)
theorem keep (mem : ByteArray) (ptr n X : Nat) (hd : ptr+32*n ≤ 2368 ∨ 2624 ≤ ptr)
 (hr : Model.FastRepresents mem ptr n X) : Model.FastRepresents (memory mem) ptr n X := by
 refine (Model.fastRepresents_congr (a := mem) ?_ X).1 hr
 intro j hj
 rw [readWord mem (ptr+32*j) (by omega)]
theorem represents (mem : ByteArray) (A : Nat) (ha : Model.FastRepresents mem 2112 8 A) :
 Model.FastRepresents (memory mem) 2368 8 A := CallerMemory.represents_stage mem A ha

theorem guard_bound (mem : ByteArray) (A : Nat)
    (ha : Model.FastRepresents mem 2112 8 A)
    (hg : (guardWord mem).toNat ≠ 0) : A < 2^2048 - 2^1938 := by
  have htop := Model.readWord_of_fastRepresents ha (j := 0) (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at htop
  have hsr := hg
  simp only [guardWord] at hsr
  generalize hw : MachineState.readWord mem 2112 = w at htop hsr
  have hwl : w.toNat < 2^256 := w.val.isLt
  rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by decide : 146 < 256), Nat.shiftRight_eq_div_pow] at hsr
  have hlnot : (UInt256.lnot w).toNat = 2 ^ 256 - 1 - w.toNat := by
    rw [UInt256.lnot, Challenge.EvmProof.Word.word_toNat_ofNat]
    change (2 ^ 256 - 1 - w.toNat) % 2 ^ 256 = _
    exact Nat.mod_eq_of_lt (by omega)
  rw [hlnot] at hsr
  have hw2 : w.toNat < 2^256 - 2^146 := by
    by_contra hc
    apply hsr
    apply Nat.div_eq_of_lt
    omega
  have hA8 : A < Challenge.Modexp.Submission.Proofs.Limbs.radix^8 := ha.1
  have hr7 : Challenge.Modexp.Submission.Proofs.Limbs.radix^7 = 2^1792 := by
    rw [Challenge.Modexp.Submission.Proofs.Limbs.radix, ← Nat.pow_mul]
  have hr8 : Challenge.Modexp.Submission.Proofs.Limbs.radix^8 = 2^1792 * 2^256 := by
    rw [Challenge.Modexp.Submission.Proofs.Limbs.radix, ← Nat.pow_mul, ← Nat.pow_add]
  have hr : Challenge.Modexp.Submission.Proofs.Limbs.radix = 2^256 := rfl
  rw [show 8 - 1 - 0 = 7 from rfl, hr7, hr] at htop
  rw [hr8] at hA8
  have hdiv : A / 2^1792 % 2^256 = A / 2^1792 := by
    apply Nat.mod_eq_of_lt
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    rw [Nat.mul_comm]; exact hA8
  rw [hdiv] at htop
  have hq : A / 2^1792 < 2^256 - 2^146 := by rw [← htop]; exact hw2
  have hlt : A < (2^256 - 2^146) * 2^1792 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)] at hq; exact hq
  have hc : (2^256 - 2^146) * 2^1792 = (2:Nat)^2048 - 2^1938 := by norm_num
  rw [hc] at hlt
  exact hlt


#print axioms run_hit
#print axioms run_miss
#print axioms run_finish
/-- The selected caller restores the conventional return word for every input frame. -/
theorem frame_return (mem : ByteArray) (count width : UInt256) (bsize esize : Nat) :
 (frame mem count width bsize esize).ret = CycleSubmission.Global.Fast.Shift.headWord mem 8 := rfl
#print axioms frame_return
end CycleSubmission.Global.DirectEightRaw
