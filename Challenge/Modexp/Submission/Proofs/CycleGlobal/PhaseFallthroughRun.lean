import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Fast.Exp
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftStates
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneEntry

noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace CycleSubmission.Global.PhaseFallthroughRun
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission.Global.Fast
open CycleSubmission.Global
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel

/-- Generic carrier: memory is arbitrary, including arbitrary bytes outside the copied region. -/
def frame (s : State) (mem : ByteArray) (pc : Nat) (stack : List UInt256) : State :=
  { s with memory := mem, pc := UInt256.ofNat pc, stack := stack }

def phaseGuardProgram : List Instr := [.push 2 1760, .op .MLOAD, .push 2 10971, .op .JUMPI]

theorem run_phaseGuard (s : State) (mem : ByteArray) (pc : Nat) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) (hact : 88 ≤ s.activeWords.toNat)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 10971 = true) :
    runInstructions phaseGuardProgram (frame s mem pc rest) =
      some (frame s mem (if (MachineState.readWord mem 1760).toNat = 0 then pc + 8 else 10971) rest) := by
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have ha : MachineState.activeWordsAfter s.activeWords.toNat 1760 32 = s.activeWords.toNat := by
    unfold MachineState.activeWordsAfter
    simp only [show (32 : Nat) ≠ 0 by decide, if_false]
    exact Nat.max_eq_left (by omega)
  have hactive : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1760 32) = s.activeWords := by
    rw [ha]
    exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  by_cases hv : (MachineState.readWord mem 1760).toNat = 0 <;>
    simp [runInstructions, phaseGuardProgram, frame, Challenge.EvmProof.Stepper.runInstr,
      hcap0, hcap1, hcap2, State.activeWordsAfterUInt256, hactive,
      hv, hdest, UInt256.isTrue, Nat.add_assoc,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_phaseGuardZero (s : State) (mem : ByteArray) (pc : Nat) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) (hact : 88 ≤ s.activeWords.toNat)
    (hflag : MachineState.readWord mem 1760 = UInt256.ofNat 0)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 10971 = true) :
    runInstructions phaseGuardProgram (frame s mem pc rest) =
      some (frame s mem (pc + 8) rest) := by
  simpa [hflag] using run_phaseGuard s mem pc rest hrest hact hdest

theorem run_phaseGuardOne (s : State) (mem : ByteArray) (pc : Nat) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) (hact : 88 ≤ s.activeWords.toNat)
    (hflag : MachineState.readWord mem 1760 = UInt256.ofNat 1)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 10971 = true) :
    runInstructions phaseGuardProgram (frame s mem pc rest) =
      some (frame s mem 10971 rest) := by
  simpa [hflag] using run_phaseGuard s mem pc rest hrest hact hdest



def cleanupProgram : List Instr := List.replicate 16 (.op .POP) ++ [.push 2 2284, .op .ADD, .op .JUMP]

theorem run_pops (s : State) (mem : ByteArray) (pc : Nat)
    (front rest : List UInt256) (hbound : front.length + rest.length < 1024) :
    runInstructions (List.replicate front.length (.op .POP)) (frame s mem pc (front ++ rest)) =
      some (frame s mem (pc + front.length) rest) := by
  induction front generalizing pc with
  | nil => simp [runInstructions, frame]
  | cons x xs ih =>
    have hcap : rest.length + (xs.length + 1) < 1024 := by
      simp only [List.length_cons] at hbound
      omega
    have hb : xs.length + rest.length < 1024 := by omega
    simpa [List.replicate_succ, runInstructions, frame, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hcap]
      using ih (pc + 1) hb

theorem run_cleanup (s : State) (mem : ByteArray) (pc d target : Nat)
    (front rest : List UInt256) (hlen : front.length = 16) (hrest : rest.length ≤ 1000)
    (htarget : 2284 + d = target) (hlt : target < 2^256)
    (hdest : Decode.isValidJumpDest s.executionEnv.code target = true) :
    runInstructions cleanupProgram (frame s mem pc (front ++ UInt256.ofNat d :: rest)) =
      some (frame s mem target rest) := by
  have hp := run_pops s mem pc front (UInt256.ofNat d :: rest) (by simp only [List.length_cons]; omega)
  rw [hlen] at hp
  rw [cleanupProgram, runInstructions_append, hp]
  have hcap : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hadd : UInt256.ofNat 2284 + UInt256.ofNat d = UInt256.ofNat target := by
    rw [Challenge.EvmProof.Word.ofNat_add_mod, htarget]
  have hmod : target % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = target := Nat.mod_eq_of_lt hlt
  simp [runInstructions, frame, Challenge.EvmProof.Stepper.runInstr, hcap, hcap2, hmod,
    hadd, hdest, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hlt,
    Challenge.EvmProof.Word.succ_ofNat_mod]

def phaseSwitchProgram : List Instr :=
  [.op (.Swap ⟨15, by decide⟩), .push 2 1760, .op .MSTORE, .push 1 12, .op (.Swap ⟨15, by decide⟩), .op (.Dup ⟨14, by decide⟩), .push 2 2112, .push 2 256, .op .MCOPY, .op (.Dup ⟨13, by decide⟩), .push 1 2, .op .SHR, .op (.Dup ⟨1, by decide⟩), .op .JUMP]

/-- The flag is cleared before MCOPY reads the retained accumulator at 2112. -/
def phaseSwitchMemory (mem : ByteArray) (n : Nat) : ByteArray :=
  Exp.mcopyMem (Exp.storeWord mem 1760 (UInt256.ofNat 0)) 256 2112 (32 * n)


theorem run_phaseSwitch (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (rest : List UInt256)
    (hn : n = 4 ∨ n = 8) (hbs : bsize = 32 * n)
    (hrest : rest.length ≤ 1000) (hact : 88 ≤ s.activeWords.toNat)
    (hstack : rest =
      Shift.entrySlots (UInt256.ofNat 0) mem n bsize esize ++ Exp.outer n bsize esize msize)
    (hdest : Decode.isValidJumpDest s.executionEnv.code (Shift.headPC n) = true) :
    runInstructions phaseSwitchProgram
      (frame s mem 10972 rest) =
      some (frame s (phaseSwitchMemory mem n) (Shift.headPC n)
        (UInt256.ofNat (n / 4) :: Shift.entrySlots (UInt256.ofNat 12) mem n bsize esize ++
          Exp.outer n bsize esize msize)) := by
  have hn1 : 1 ≤ n := by omega
  have hn8 : n ≤ 8 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hs32 : (UInt256.ofNat (32 * n)).toNat = 32 * n := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hquarter : UInt256.shiftRight (UInt256.ofNat n) (UInt256.ofNat 2) =
      UInt256.ofNat (n / 4) := by
    rcases hn with rfl | rfl <;> decide
  have hactive1 := Exp.activeWords_fix s 1760 32 (by decide) (by decide) hact
  have ha2 : 32 * n ≠ 0 := by omega
  have ha3 : 256 + 32 * n ≤ 2816 := by omega
  have ha4 : 2112 + 32 * n ≤ 2816 := by omega
  have hactive2 := Exp.activeWords_fix2 s 256 (32 * n) 2112 (32 * n) ha2 ha2 ha3 ha4 hact
  have hhead : Shift.headPC n %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      Shift.headPC n :=
    Nat.mod_eq_of_lt (by unfold Shift.headPC; split_ifs <;> norm_num)
  simp [runInstructions, phaseSwitchProgram, phaseSwitchMemory, frame, Shift.headWord, hhead,
    Challenge.EvmProof.Stepper.runInstr, Exp.storeWord, Exp.mcopyMem,
    hstack, hbs, Shift.entrySlots, Shift.rideSlots, Exp.outer, List.exchange,
    hcap2, hcap3, hcap4, hcap5, hs32, hquarter, hdest, Exp.push0_word,
    State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2, hactive1, hactive2,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]


def exitPC (b : Bool) : Nat := if b then 10939 else 3036
def guardPC (b : Bool) : Nat := if b then 10940 else 3038
def cleanupPC (b : Bool) : Nat := if b then 10948 else 3046
def exitHeadProgram (b : Bool) : List Instr := if b then [.op .POP] else [.op .JUMPDEST, .op .POP]
def commonHeadProgram : List Instr := [.op .JUMPDEST]

theorem run_exitHead (b : Bool) (s : State) (mem : ByteArray) (value : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (exitHeadProgram b) (frame s mem (exitPC b) (value :: rest)) =
      some (frame s mem (guardPC b) rest) := by
  have hcap : rest.length + 1 < 1024 := by omega
  cases b <;> simp [runInstructions, exitHeadProgram, exitPC, guardPC, frame,
    Challenge.EvmProof.Stepper.runInstr, hcap, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_commonHead (s : State) (mem : ByteArray) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions commonHeadProgram (frame s mem 10971 rest) =
      some (frame s mem 10972 rest) := by
  have hcap : rest.length < 1024 := by omega
  simp [runInstructions, commonHeadProgram, frame, Challenge.EvmProof.Stepper.runInstr,
    hcap, Challenge.EvmProof.Word.succ_ofNat_mod]

open Challenge.EvmProof WindowTwentyOneBinding
structure PhaseBlocks (artifact : ProgramArtifact) (fork : Fork) where
  exitHead : (b : Bool) → Block artifact fork (exitPC b) (exitHeadProgram b)
  guard : (b : Bool) → Block artifact fork (guardPC b) phaseGuardProgram
  cleanup : (b : Bool) → Block artifact fork (cleanupPC b) cleanupProgram
  commonHead : Block artifact fork 10971 commonHeadProgram
  switch : Block artifact fork 10972 phaseSwitchProgram

end CycleSubmission.Global.PhaseFallthroughRun


