import Challenge.Modexp.Submission.Proofs.CycleGlobal.SlimFrames
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftStates
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneEntry
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
noncomputable section
set_option linter.unusedVariables false
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.StackPhaseRun
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel
def frame (s : State) (mem : ByteArray) (pc : Nat) (stack : List UInt256) : State :=
  { s with memory := mem, pc := UInt256.ofNat pc, stack := stack }
def exitPC (b : Bool) : Nat := if b then 10933 else 3049
def transferPC (b : Bool) : Nat := if b then 10934 else 3051
def headProgram (b : Bool) : List Instr :=
  if b then [.op .POP] else [.op .JUMPDEST, .op .POP]
def transferProgram : List Instr := [.op (.Swap ⟨12, by decide⟩), .op .JUMP]

def transferSlots (z : UInt256) (mem : ByteArray) (n bsize esize msize : Nat) : List UInt256 :=
  (CycleSubmission.Global.Fast.Shift.entrySlots z mem n bsize esize).tail.take 12 ++
    [CycleSubmission.Global.Fast.Shift.headWord mem n] ++ Exp.outer n bsize esize msize

theorem run_head (b : Bool) (s : State) (mem : ByteArray) (z : UInt256)
    (n bsize esize msize : Nat) :
    runInstructions (headProgram b)
      (frame s mem (exitPC b) (UInt256.ofNat 0 ::
        CycleSubmission.Global.Fast.Shift.entrySlots z mem n bsize esize ++ Exp.outer n bsize esize msize)) =
      some (frame s mem (transferPC b)
        (CycleSubmission.Global.Fast.Shift.entrySlots z mem n bsize esize ++ Exp.outer n bsize esize msize)) := by
  cases b <;> simp [headProgram, runInstructions, frame, exitPC, transferPC, CycleSubmission.Global.Fast.Shift.entrySlots, CycleSubmission.Global.Fast.Shift.aprevSlot, CycleSubmission.Global.Fast.Shift.hdSlot, Exp.outer,
    Challenge.EvmProof.Stepper.runInstr, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_transfer (s : State) (mem : ByteArray) (pc target : Nat) (z : UInt256)
    (n bsize esize msize : Nat)
    (ht : z = UInt256.ofNat target)
    (hlt : target < 2^256) (hd : Decode.isValidJumpDest s.executionEnv.code target = true) :
    runInstructions transferProgram
      (frame s mem pc (CycleSubmission.Global.Fast.Shift.entrySlots z mem n bsize esize ++ Exp.outer n bsize esize msize)) =
      some (frame s mem target (transferSlots z mem n bsize esize msize)) := by
  have hm : target % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = target := Nat.mod_eq_of_lt hlt
  simp [transferProgram, transferSlots, CycleSubmission.Global.Fast.Shift.entrySlots,CycleSubmission.Global.Fast.Shift.aprevSlot,CycleSubmission.Global.Fast.Shift.hdSlot,
    frame, Exp.outer, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, ht, hm, hd, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod]

def phaseSwitchProgram : List Instr :=
  [.op (.Dup ⟨13, by decide⟩), .push 2 2112, .push 2 256, .op .MCOPY,
   .op (.Dup ⟨13, by decide⟩), .push 1 7, .op .SHR, .push 2 2298,
   .op (.Swap ⟨13, by decide⟩), .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .JUMP]
def phaseSwitchMemory (mem : ByteArray) (n : Nat) : ByteArray := Exp.mcopyMem mem 256 2112 (32 * n)

theorem run_phaseSwitch (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : n = 4 ∨ n = 8) (hbs : bsize = 32 * n) (hact : 88 ≤ s.activeWords.toNat)
    (hdest : Decode.isValidJumpDest s.executionEnv.code (CycleSubmission.Global.Fast.Shift.loopPC mem n) = true) :
    runInstructions phaseSwitchProgram
      (frame s mem 3928 (transferSlots (UInt256.ofNat 3927) mem n bsize esize msize)) =
      some (frame s (phaseSwitchMemory mem n) (CycleSubmission.Global.Fast.Shift.loopPC mem n)
        (UInt256.ofNat (n / 4) :: CycleSubmission.Global.Fast.Shift.entrySlots (UInt256.ofNat 2298) mem n bsize esize ++ Exp.outer n bsize esize msize)) := by
  have hn1 : 1 ≤ n := by omega
  have hn8 : n ≤ 8 := by omega
  have hcap2 : (transferSlots (UInt256.ofNat 3927) mem n bsize esize msize).length + 2 < 1024 := by simp [transferSlots, CycleSubmission.Global.Fast.Shift.entrySlots, CycleSubmission.Global.Fast.Shift.aprevSlot, CycleSubmission.Global.Fast.Shift.hdSlot, Exp.outer]
  have hcap3 : (transferSlots (UInt256.ofNat 3927) mem n bsize esize msize).length + 3 < 1024 := by simp [transferSlots, CycleSubmission.Global.Fast.Shift.entrySlots, CycleSubmission.Global.Fast.Shift.aprevSlot, CycleSubmission.Global.Fast.Shift.hdSlot, Exp.outer]
  have hcap4 : (transferSlots (UInt256.ofNat 3927) mem n bsize esize msize).length + 4 < 1024 := by simp [transferSlots, CycleSubmission.Global.Fast.Shift.entrySlots, CycleSubmission.Global.Fast.Shift.aprevSlot, CycleSubmission.Global.Fast.Shift.hdSlot, Exp.outer]
  have hcap5 : (transferSlots (UInt256.ofNat 3927) mem n bsize esize msize).length + 5 < 1024 := by simp [transferSlots, CycleSubmission.Global.Fast.Shift.entrySlots, CycleSubmission.Global.Fast.Shift.aprevSlot, CycleSubmission.Global.Fast.Shift.hdSlot, Exp.outer]
  have hs32 : (UInt256.ofNat (32 * n)).toNat = 32 * n := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hquarter : UInt256.shiftRight (UInt256.ofNat (32*n)) (UInt256.ofNat 7) =
      UInt256.ofNat (n / 4) := by
    rcases hn with rfl | rfl <;> decide
  have ha2 : 32 * n ≠ 0 := by omega
  have ha3 : 256 + 32 * n ≤ 2816 := by omega
  have ha4 : 2112 + 32 * n ≤ 2816 := by omega
  have hactive2 := Exp.activeWords_fix2 s 256 (32 * n) 2112 (32 * n) ha2 ha2 ha3 ha4 hact
  have hhead : CycleSubmission.Global.Fast.Shift.loopPC mem n %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      CycleSubmission.Global.Fast.Shift.loopPC mem n :=
    Nat.mod_eq_of_lt (CycleSubmission.Global.Fast.Shift.loopPC_lt mem n)
  simp [runInstructions, phaseSwitchProgram, phaseSwitchMemory, transferSlots, frame, CycleSubmission.Global.Fast.Shift.headWord, hhead,
    Challenge.EvmProof.Stepper.runInstr, Exp.storeWord, Exp.mcopyMem,
    hbs, CycleSubmission.Global.Fast.Shift.entrySlots, CycleSubmission.Global.Fast.Shift.aprevSlot, CycleSubmission.Global.Fast.Shift.hdSlot, CycleSubmission.Global.Fast.Shift.rideSlots, Exp.outer, List.exchange,
    hcap2, hcap3, hcap4, hcap5, hs32, hquarter, hdest, Exp.push0_word,
    State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2, hactive2,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]
def commonHeadProgram : List Instr := [.op .JUMPDEST]

theorem run_commonHead (s : State) (mem : ByteArray) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions commonHeadProgram (frame s mem 3927 rest) =
      some (frame s mem 3928 rest) := by
  have hcap : rest.length < 1024 := by omega
  simp [runInstructions, commonHeadProgram, frame, Challenge.EvmProof.Stepper.runInstr,
    hcap, Challenge.EvmProof.Word.succ_ofNat_mod]


open Challenge.EvmProof WindowTwentyOneBinding
structure PhaseBlocks (artifact : ProgramArtifact) (fork : Fork) where
  exitHead : (b : Bool) → Block artifact fork (exitPC b) (headProgram b)
  transfer : (b : Bool) → Block artifact fork (transferPC b) transferProgram
  commonHead : Block artifact fork 3927 commonHeadProgram
  switch : Block artifact fork 3928 phaseSwitchProgram
end CycleSubmission.Global.StackPhaseRun
