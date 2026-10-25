import Challenge.Modexp.Submission.Proofs.CycleCaller.Blocks
import Challenge.Modexp.Submission.Proofs.CycleCaller.Memory
import Challenge.Modexp.Submission.Proofs.Cycle.EntryMeaning
import Challenge.Modexp.Submission.Proofs.CRT.CRTControlBase
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace CycleSubmission.CallerPrefix
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open HistoricalSearch.CRTControl
open CycleSubmission.CallerBlocks CycleSubmission.EntryMeaning

def qWord (n : Nat) : UInt256 := UInt256.ofNat 480 - UInt256.ofNat (512+32*n-32)

def frame (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256) : Caller where
  pbi := qWord 8
  hd := UInt256.ofNat 5297
  w3 := MachineState.readWord mem 192
  ent := UInt256.ofNat 3347
  m32 := MachineState.readWord mem 32
  m128 := MachineState.readWord mem 128
  m64 := MachineState.readWord mem 64
  m0 := MachineState.readWord mem 160
  tl := MachineState.readWord mem 224
  m96 := MachineState.readWord mem 96
  inv := MachineState.readWord mem 2720
  tn := UInt256.ofNat 0
  aprev := UInt256.ofNat 2336
  counter := UInt256.ofNat (k-1)
  ret := ret
  tail := tail

def call (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 3181
    memory := mem
    stack := [UInt256.ofNat 3728, UInt256.ofNat 2112, UInt256.ofNat 512,
      UInt256.ofNat (k-1), ret] ++ tail}

def staged (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256) : State :=
  CiosCached.outState s (CallerMemory.memory mem) 512 8 0 (UInt256.ofNat 3728)
    (UInt256.ofNat 3347) (MachineState.readWord mem 32) (MachineState.readWord mem 64)
    (MachineState.readWord mem 160)
    ([MachineState.readWord mem 224, MachineState.readWord mem 96,
      MachineState.readWord mem 2720, UInt256.ofNat 0, UInt256.ofNat 2336,
      UInt256.ofNat (k-1), ret] ++ tail)

def stateAt (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256)
    (pc : Nat) : State :=
  {s with
    pc := UInt256.ofNat pc
    memory := CallerMemory.memory mem
    stack := saved (frame mem k ret tail)}

theorem entry_run (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256)
    (hcap : tail.length ≤ 943) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entryProgram (staged s mem k ret tail) = some (stateAt s mem k ret tail 3743) := by
  have h16 : tail.length + 16 < 1024 := by omega
  have h17 : tail.length + 17 < 1024 := by omega
  have hactM := Csub.activeWords_fix s 192 32 (by decide) (by decide) hact
  simp [entryProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    staged, stateAt, frame, saved, CiosCached.outState, qWord,
    Monpro.ptrAt_zero, h16, h17, hactM, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    CallerMemory.readWord mem 192 (Or.inl (by decide)),
    CallerMemory.readWord mem 128 (Or.inl (by decide)), CiosCached.allOnes]

def tested (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256) : State :=
  {stateAt s mem k ret tail 3750 with
    stack := UInt256.ofNat 3768 :: UInt256.ofNat (2^256-128) :: saved (frame mem k ret tail)}

theorem test_run (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256)
    (hcap : tail.length ≤ 943) :
    runInstructions testProgram (stateAt s mem k ret tail 3743) = some (tested s mem k ret tail) := by
  have h16 : tail.length + 16 < 1024 := by omega
  have h17 : tail.length + 17 < 1024 := by omega
  have h18 : tail.length + 18 < 1024 := by omega
  have hsum : UInt256.ofNat 128 + qWord 8 = UInt256.ofNat (2^256-128) := by decide
  simp [testProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    stateAt, tested, frame, saved, h16, h17, h18, hsum,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable opaque setupTrace (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : tail.length ≤ 943) (hact : 88 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat 256)
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat 224)
    (hw : tail[1]? = some (UInt256.ofNat 256))
    (hn : tail[2]? = some (UInt256.ofNat 8)) :
    GasSteps (call s mem k ret tail) (staged s mem k ret tail) := by
  have hcommon := commonBlock.steps (s := call s mem k ret tail)
    (env.transfer rfl rfl) rfl (jumpDest_run _ (by
      simp only [call, List.length_append, List.length_cons, List.length_nil]; omega))
  have hsetup := setupBlock.steps
    (s := CiosCached.setupState s mem (UInt256.ofNat 3728) 2112 512 (UInt256.ofNat (k-1)) ret tail)
    (env.transfer rfl rfl) rfl
    (TnM128Setup.run_entry_sq s mem (UInt256.ofNat 3728) 2112 512 8
      (UInt256.ofNat (k-1)) ret tail (by omega) hact (by decide) (by decide)
      (Or.inr rfl) (by decide) (by decide) (by decide) hcds hs32 hml hw hn
      (by rw [env.code]; exact valid3728))
  exact hcommon.trans hsetup

noncomputable opaque suffixTrace (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : tail.length ≤ 943) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps (staged s mem k ret tail) (stateAt s mem k ret tail 5964) := by
  have he2 := entryBlock.steps (s := staged s mem k ret tail)
    (env.transfer rfl rfl) rfl (entry_run s mem k ret tail hcap hact)
  have ht := testBlock.steps (s := stateAt s mem k ret tail 3743)
    (env.transfer rfl rfl) rfl (test_run s mem k ret tail hcap)
  have hc : (tested s mem k ret tail).stack.length < 1024 := by
    simp only [tested, stateAt, saved, frame, List.length_cons, List.length_append, List.length_nil]; omega
  have hr := jumpi_run (tested s mem k ret tail) (UInt256.ofNat 3768)
    (UInt256.ofNat (2^256-128)) (saved (frame mem k ret tail)) rfl hc
    (by rw [show (tested s mem k ret tail).executionEnv.code = Artifact.bytecode from env.code]; exact valid3768)
  have hj := branchBlock.steps (s := tested s mem k ret tail) (env.transfer rfl rfl) rfl hr
  have chosen : conditionalModel (tested s mem k ret tail) = stateAt s mem k ret tail 3768 := by
    simp only [conditionalModel, tested, List.drop_succ_cons, List.drop_zero, List.headD_cons]
    rfl
  rw [chosen] at hj
  have hc16 : (saved (frame mem k ret tail)).length < 1024 := by
    simp only [saved, frame, List.length_cons, List.length_append, List.length_nil]; omega
  have hc17 : (saved (frame mem k ret tail)).length + 1 < 1024 := by
    simp only [saved, frame, List.length_cons, List.length_append, List.length_nil]; omega
  let pushed : State := {stateAt s mem k ret tail 3772 with stack := UInt256.ofNat 5964 :: saved (frame mem k ret tail)}
  have htr : runInstructions trampolineProgram (stateAt s mem k ret tail 3768) = some pushed := by
    simp [trampolineProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      stateAt, pushed, hc16, hc17, Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  have hg := trampolineBlock.steps (s := stateAt s mem k ret tail 3768)
    (env.transfer rfl rfl) rfl htr
  have hjr := jump_run pushed (UInt256.ofNat 5964) (saved (frame mem k ret tail)) rfl
    (by simpa only [pushed, List.length_cons] using hc17)
    (by rw [show pushed.executionEnv.code = Artifact.bytecode from env.code]; exact valid5964)
  have hj2 := jumpBlock.steps (s := pushed) (env.transfer rfl rfl) rfl hjr
  change GasSteps pushed (stateAt s mem k ret tail 5964) at hj2
  have tailTrace : GasSteps (stateAt s mem k ret tail 3768) (stateAt s mem k ret tail 5964) := hg.trans hj2
  have branchTrace : GasSteps (tested s mem k ret tail) (stateAt s mem k ret tail 5964) := hj.trans tailTrace
  have testTrace : GasSteps (stateAt s mem k ret tail 3743) (stateAt s mem k ret tail 5964) := ht.trans branchTrace
  have entryTrace : GasSteps (staged s mem k ret tail) (stateAt s mem k ret tail 5964) := he2.trans testTrace
  exact entryTrace

noncomputable def run (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : tail.length ≤ 943) (hact : 88 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat 256)
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat 224)
    (hw : tail[1]? = some (UInt256.ofNat 256))
    (hn : tail[2]? = some (UInt256.ofNat 8)) :
    GasSteps (call s mem k ret tail) (stateAt s mem k ret tail 5964) :=
  (setupTrace s mem k ret tail env hcap hact hcds hs32 hml hw hn).trans
    (suffixTrace s mem k ret tail env hcap hact)

end CycleSubmission.CallerPrefix
