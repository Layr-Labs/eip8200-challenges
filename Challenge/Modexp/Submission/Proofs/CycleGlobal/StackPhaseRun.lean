import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftStates
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneEntry
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
noncomputable section
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
def exitPC (b : Bool) : Nat := if b then 10939 else 3035
def guardPC (b : Bool) : Nat := if b then 10940 else 3037
def cleanupPC (b : Bool) : Nat := if b then 10948 else 3046
def headProgram (b : Bool) : List Instr :=
  if b then [.op (.Swap ⟨15, by decide⟩)] else [.op .JUMPDEST, .op (.Swap ⟨15, by decide⟩)]
def guardWidth (b : Bool) : Fin 33 := if b then 6 else 7
def guardProgram (b : Bool) : List Instr := [.push (guardWidth b) 10971, .op .JUMPI]

theorem run_head (b : Bool) (s : State) (mem : ByteArray) (flag z : UInt256)
    (n bsize esize msize : Nat) :
    runInstructions (headProgram b)
      (frame s mem (exitPC b) (UInt256.ofNat 0 ::
        CycleSubmission.Global.Fast.Shift.entrySlots z mem n bsize esize flag ++ Exp.outer n bsize esize msize)) =
      some (frame s mem (guardPC b) (flag ::
        CycleSubmission.Global.Fast.Shift.entrySlots z mem n bsize esize (UInt256.ofNat 0) ++ Exp.outer n bsize esize msize)) := by
  cases b <;> simp [runInstructions, headProgram, frame, exitPC, guardPC,
    Challenge.EvmProof.Stepper.runInstr, CycleSubmission.Global.Fast.Shift.entrySlots, Exp.outer, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_guard (b : Bool) (s : State) (mem : ByteArray) (flag : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 10971 = true) :
    runInstructions (guardProgram b) (frame s mem (guardPC b) (flag :: rest)) =
      some (frame s mem (if flag.toNat = 0 then cleanupPC b else 10971) rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  cases b <;> by_cases hf : flag.toNat = 0 <;>
    simp [runInstructions, guardProgram, guardWidth, frame, guardPC, cleanupPC,
      Challenge.EvmProof.Stepper.runInstr, hc1, hc2, hf, hdest, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

def packSlots (scratch z flag : UInt256) (mem : ByteArray) (n bsize esize : Nat) : List UInt256 :=
  scratch :: (CycleSubmission.Global.Fast.Shift.entrySlots z mem n bsize esize flag).tail

def packProgram : List Instr := [.op (.Swap ⟨15, by decide⟩), .op .POP, .op (.Dup ⟨15, by decide⟩)]

theorem run_pack (s : State) (mem : ByteArray) (scratch z flag : UInt256)
    (n bsize esize msize : Nat) :
    runInstructions packProgram
      (frame s mem 2642 (flag :: packSlots scratch z (UInt256.ofNat 0) mem n bsize esize ++
        Exp.outer n bsize esize msize)) =
      some (frame s mem 2645 (flag :: packSlots scratch z flag mem n bsize esize ++
        Exp.outer n bsize esize msize)) := by
  simp [runInstructions, packProgram, packSlots, frame, Challenge.EvmProof.Stepper.runInstr,
    CycleSubmission.Global.Fast.Shift.entrySlots, Exp.outer, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod]


def phaseSwitchProgram : List Instr :=
  [.op (.Swap ⟨15, by decide⟩), .op .POP, .push 4 12, .op (.Swap ⟨15, by decide⟩), .op (.Dup ⟨14, by decide⟩), .push 2 2112, .push 2 256, .op .MCOPY, .op (.Dup ⟨13, by decide⟩), .push 1 2, .op .SHR, .op (.Dup ⟨1, by decide⟩), .op .JUMP]

def phaseSwitchMemory (mem : ByteArray) (n : Nat) : ByteArray :=
  Exp.mcopyMem mem 256 2112 (32 * n)

theorem run_phaseSwitch (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (rest : List UInt256)
    (hn : n = 4 ∨ n = 8) (hbs : bsize = 32 * n)
    (hrest : rest.length ≤ 1000) (hact : 88 ≤ s.activeWords.toNat)
    (hstack : rest =
      CycleSubmission.Global.Fast.Shift.entrySlots (UInt256.ofNat 0) mem n bsize esize ++ Exp.outer n bsize esize msize)
    (hdest : Decode.isValidJumpDest s.executionEnv.code (CycleSubmission.Global.Fast.Shift.headPC n) = true) :
    runInstructions phaseSwitchProgram
      (frame s mem 10972 rest) =
      some (frame s (phaseSwitchMemory mem n) (CycleSubmission.Global.Fast.Shift.headPC n)
        (UInt256.ofNat (n / 4) :: CycleSubmission.Global.Fast.Shift.entrySlots (UInt256.ofNat 12) mem n bsize esize ++
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
  have ha2 : 32 * n ≠ 0 := by omega
  have ha3 : 256 + 32 * n ≤ 2816 := by omega
  have ha4 : 2112 + 32 * n ≤ 2816 := by omega
  have hactive2 := Exp.activeWords_fix2 s 256 (32 * n) 2112 (32 * n) ha2 ha2 ha3 ha4 hact
  have hhead : CycleSubmission.Global.Fast.Shift.headPC n %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      CycleSubmission.Global.Fast.Shift.headPC n :=
    Nat.mod_eq_of_lt (by unfold CycleSubmission.Global.Fast.Shift.headPC; split_ifs <;> norm_num)
  simp [runInstructions, phaseSwitchProgram, phaseSwitchMemory, frame, CycleSubmission.Global.Fast.Shift.headWord, hhead,
    Challenge.EvmProof.Stepper.runInstr, Exp.storeWord, Exp.mcopyMem,
    hstack, hbs, CycleSubmission.Global.Fast.Shift.entrySlots, CycleSubmission.Global.Fast.Shift.rideSlots, Exp.outer, List.exchange,
    hcap2, hcap3, hcap4, hcap5, hs32, hquarter, hdest, Exp.push0_word,
    State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2, hactive2,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]




def cleanupProgram : List Instr := List.replicate 6 (.op .POP) ++
  List.replicate 6 (.op (.Dup ⟨15, by decide⟩)) ++ [.push 6 2284, .op .ADD, .op .JUMP]
def cleanupSuffix (d : Nat) (mem : ByteArray) (n bsize esize msize : Nat) : List UInt256 :=
  (CycleSubmission.Global.Fast.Shift.entrySlots (UInt256.ofNat d) mem n bsize esize).drop 6 ++ Exp.outer n bsize esize msize

theorem run_cleanup (s : State) (mem : ByteArray) (pc d target n bsize esize msize : Nat)
    (htarget : 2284 + d = target) (hlt : target < 2^256)
    (hdest : Decode.isValidJumpDest s.executionEnv.code target = true) :
    runInstructions cleanupProgram
      (frame s mem pc (CycleSubmission.Global.Fast.Shift.entrySlots (UInt256.ofNat d) mem n bsize esize ++ Exp.outer n bsize esize msize)) =
      some (frame s mem target (Exp.outer n bsize esize msize ++ cleanupSuffix d mem n bsize esize msize)) := by
  have hadd : UInt256.ofNat 2284 + UInt256.ofNat d = UInt256.ofNat target := by
    rw [Challenge.EvmProof.Word.ofNat_add_mod, htarget]
  have hmod : target % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = target := Nat.mod_eq_of_lt hlt
  simp (config := {maxSteps := 400000}) [cleanupProgram, cleanupSuffix, runInstructions, frame, CycleSubmission.Global.Fast.Shift.entrySlots, Exp.outer,
    Challenge.EvmProof.Stepper.runInstr, hmod, hadd, hdest,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hlt,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem cleanupSuffix_length (d : Nat) (mem : ByteArray) (n bsize esize msize : Nat) :
    (cleanupSuffix d mem n bsize esize msize).length = 16 := by
  simp [cleanupSuffix, CycleSubmission.Global.Fast.Shift.entrySlots, Exp.outer]


def commonHeadProgram : List Instr := [.op .JUMPDEST]

theorem run_commonHead (s : State) (mem : ByteArray) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions commonHeadProgram (frame s mem 10971 rest) =
      some (frame s mem 10972 rest) := by
  have hcap : rest.length < 1024 := by omega
  simp [runInstructions, commonHeadProgram, frame, Challenge.EvmProof.Stepper.runInstr,
    hcap, Challenge.EvmProof.Word.succ_ofNat_mod]


open Challenge.EvmProof WindowTwentyOneBinding
structure PhaseBlocks (artifact : ProgramArtifact) (fork : Fork) where
  exitHead : (b : Bool) → Block artifact fork (exitPC b) (headProgram b)
  guard : (b : Bool) → Block artifact fork (guardPC b) (guardProgram b)
  cleanup : (b : Bool) → Block artifact fork (cleanupPC b) cleanupProgram
  commonHead : Block artifact fork 10971 commonHeadProgram
  switch : Block artifact fork 10972 phaseSwitchProgram

end CycleSubmission.Global.StackPhaseRun
