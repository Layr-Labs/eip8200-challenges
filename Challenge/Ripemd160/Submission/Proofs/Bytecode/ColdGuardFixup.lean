import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Sites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32SparseRun
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentStart
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Scratch

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-!
# The cold guard-miss route through the shared 32-byte block

Every length the alignment guard at 449 does not send to the block loop jumps to 143, the
32-byte block. That block sets the continuation slot to the output entry 4748 and writes two
scratch bytes (165 and 188) before its length test at 158. Any other length falls through to the
fixup at 166, which stores a zero word at 157 and so clears both scratch bytes again (that window
is still untouched zero memory), then falls into the sentinel store at 170.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdGuardFixup
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate Shared32Sites

def cstk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256) (rho : List UInt256) :
    List UInt256 :=
  a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: off :: lim :: rho

/-- The two scratch bytes of the shared 32-byte block. -/
def wMemory (m : ByteArray) (b c : UInt8) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes m (ByteArray.mk #[b]) 165)
    (ByteArray.mk #[c]) 188

/-- The fixup word store undoes both scratch bytes on zero, active memory. -/
theorem restore (m : ByteArray) (b c : UInt8) (hsize : 189 ≤ m.size)
    (hzero : ∀ a, 157 ≤ a → a < 189 → m[a]?.getD 0 = 0) :
    MachineState.writeBytes (wMemory m b c) (Data.Bytes.natToBytesPadded 0 32) 157 = m := by
  have e1 : (ByteArray.mk #[c]).size = 1 := rfl
  have eb : (ByteArray.mk #[b]).size = 1 := rfl
  apply ByteArray.ext_getElem
  · simp only [wMemory, MachineState.writeBytes_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size, e1, eb]
    split_ifs <;> omega
  · intro a hA hB
    rw [← Memory.getD0_eq_getElem _ _ hA, ← Memory.getD0_eq_getElem _ _ hB]
    simp only [wMemory, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size, e1, eb]
    by_cases h1 : 157 ≤ a ∧ a < 157 + 32
    · rw [if_pos h1, YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by omega),
        hzero a h1.1 (by omega)]
      simp
    · rw [if_neg h1, if_neg (by omega), if_neg (by omega)]

private theorem add_eq_hAdd (x y : UInt256) : UInt256.add x y = x + y := rfl

private theorem active_byte (c : UInt256) (address : Nat) (hc : 34 ≤ c.toNat)
    (ha : address ≤ 1056) :
    UInt256.ofNat (MachineState.activeWordsAfter c.toNat address 1) = c := by
  have h : MachineState.activeWordsAfter c.toNat address 1 = c.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (1 : Nat) ≠ 0)]
    apply Nat.max_eq_left
    omega
  rw [h]
  exact (Word.word_eq_ofNat_toNat _).symm

theorem run_head (s : State) (pc a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 880) (hrun : s.halt = .Running) :
    runInstrSeq Shared32SparseRun.headTemplate
      {s with pc := pc, stack := cstk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} =
      some {s with
        pc := pcAfter pc Shared32SparseRun.headTemplate
        stack := cstk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 off (UInt256.ofNat 4748) rho} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [Shared32SparseRun.headTemplate, runInstrSeq, DataStepper.runInstr,
    pcAfter, hrun, hcap, Instr.size, UInt256.succ, cstk, Nat.add_assoc,
    List.getElem?_cons_zero, List.exchange]
  rfl

theorem run_sparse (s : State) (pc v x0 x1 x2 x3 x4 : UInt256) (G : List UInt256)
    (hstack : G.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq Shared32SparseRun.template {s with pc := pc, stack := v :: x0 :: x1 :: x2 :: x3 :: x4 :: G} =
      some {s with
        pc := pcAfter pc Shared32SparseRun.template
        stack := x0 :: x1 :: x2 :: x3 :: x4 :: G
        memory := wMemory s.memory (UInt8.ofNat (v.toNat % 256)) (UInt8.ofNat (x4.toNat % 256))} := by
  have hcap (n : Nat) (hn : n ≤ 27) : G.length + n < 1024 := by omega
  have hcap0 : G.length < 1024 := by omega
  have h165 := active_byte s.activeWords 165 hactive (by decide)
  have h188 := active_byte s.activeWords 188 hactive (by decide)
  simp (discharger := omega) [Shared32SparseRun.template, runInstrSeq, DataStepper.runInstr,
    pcAfter, hrun, hcap, hcap0, Instr.size, UInt256.succ, Nat.add_assoc, Word.word_toNat_ofNat,
    List.getElem?_cons_zero, State.activeWordsAfterUInt256, h165, h188, wMemory, add_eq_hAdd]

theorem run_guard_miss (s : State) (stack : List UInt256)
    (hstack : stack.length ≤ 1000) (hsize : s.executionEnv.calldata.size < 2^256)
    (hne : s.executionEnv.calldata.size ≠ 32) (hrun : s.halt = .Running) :
    runInstrSeq guard.template {s with pc := UInt256.ofNat 158, stack := stack} =
      some {s with pc := UInt256.ofNat 166, stack := stack} := by
  have hcap (n : Nat) (hn : n ≤ 3) : stack.length+n < 1024 := by omega
  have hcap0 : stack.length < 1024 := by omega
  have hw : (UInt256.ofNat s.executionEnv.calldata.size).toNat = s.executionEnv.calldata.size := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsize]
  have heq : UInt256.eq (UInt256.ofNat 32) (UInt256.ofNat s.executionEnv.calldata.size) = UInt256.ofNat 0 := by
    unfold UInt256.eq
    rw [hw, if_neg (by simpa using Ne.symm hne)]
  simp [guard.template, runInstrSeq, DataStepper.runInstr, hrun, hcap, hcap0, heq,
    UInt256.isTrue, pcAfter, Nat.add_assoc]
  rfl

namespace fixup
abbrev template : List Instr :=
  [.push ⟨0, by decide⟩ (UInt256.ofNat 0), .push ⟨1, by decide⟩ (UInt256.ofNat 157), .op .MSTORE]
theorem actual_slice : (Artifact.submissionArtifact.instructions.drop 110).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 110 actual_slice
    (by change 110 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 166 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 110) = UInt256.ofNat 166
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem run (s : State) (stack : List UInt256) (hstack : stack.length ≤ 900)
    (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template (atState s 166 stack) =
      some {s with
        pc := UInt256.ofNat 170
        stack := stack
        memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded 0 32) 157} := by
  have hcap (n : Nat) (hn : n ≤ 27) : stack.length + n < 1024 := by omega
  have hc0 : stack.length < 1024 := by omega
  have hc1 : stack.length + 1 < 1024 := by omega
  have hact := Stagger144Active.word_active_preserved_of_small s.activeWords 157 hactive (by decide)
  simp (discharger := omega) [template, atState, runInstrSeq, DataStepper.runInstr, pcAfter,
    hrun, hcap, hc0, hc1, Instr.size, UInt256.succ, Nat.add_assoc, Word.word_toNat_ofNat,
    List.getElem?_cons_zero, List.length_cons, State.activeWordsAfterUInt256, hact]
  exact ⟨rfl, rfl⟩

def gasSteps (s : State) (e : Env s) (stack : List UInt256) (hstack : stack.length ≤ 900)
    (hactive : 34 ≤ s.activeWords.toNat) :
    GasSteps (atState s 166 stack)
      {s with
        pc := UInt256.ofNat 170
        stack := stack
        memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded 0 32) 157} := by
  apply PadLift.gasSteps_of_raw site (atState s 166 stack) _
    e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact run s stack hstack e.run hactive
end fixup

/-- A guard miss at 449 that is not 32 bytes long reaches the sentinel store at 170 with the
same memory it entered with and the output entry 4748 in the continuation slot. -/
def gasSteps_partial (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 860) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hsize : s.executionEnv.calldata.size < 2^256)
    (hne : s.executionEnv.calldata.size ≠ 32)
    (hactive : 34 ≤ s.activeWords.toNat)
    (hmsize : 189 ≤ s.memory.size)
    (hzero : ∀ a, 157 ≤ a → a < 189 → s.memory[a]?.getD 0 = 0) :
    GasSteps {s with pc := UInt256.ofNat 143, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 170, stack := StaggerPersistentFrame.frame h off (UInt256.ofNat 4748) rho} := by
  have e : Env s := ⟨hcode, hfork, hrun, hnp⟩
  let a0 := Paired144WordRound.factorPlusWord
  let a1 := UInt256.ofNat 4294967295
  let a2 := Paired144WordRound.fusedModulusWord 5 7
  let a3 := Paired144WordRound.fusedModulusWord 8 5
  let a4 := Paired144WordRound.fusedCoefficientWord 0 3
  let a5 := Paired144WordRound.fusedCoefficientWord 0 2
  let a6 := Word.ofUInt32 h.h4
  let a7 := Word.ofUInt32 h.h3
  let a8 := Word.ofUInt32 h.h2
  let a9 := Word.ofUInt32 h.h1
  let a10 := Word.ofUInt32 h.h0
  let F := cstk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 off limit rho
  let F0 := cstk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 off (UInt256.ofNat 4748) rho
  have hF : StaggerPersistentFrame.frame h off limit rho = F := rfl
  have hF0 : StaggerPersistentFrame.frame h off (UInt256.ofNat 4748) rho = F0 := rfl
  have hF0len : F0.length ≤ 900 := by simp only [F0, cstk, List.length_cons]; omega
  let v := UInt256.ofNat 128
  let b := UInt8.ofNat (v.toNat % 256)
  let c := UInt8.ofNat (a4.toNat % 256)
  let sW : State := {s with memory := wMemory s.memory b c}
  have eW : Env sW := ⟨hcode, hfork, hrun, hnp⟩
  have g0 : GasSteps (atState s 143 F) (atState s 144 F) := by
    apply special.lift s (atState s 144 F) e F
    simpa only [special.template, atState, show UInt256.ofNat 143 + UInt256.ofNat 1 = UInt256.ofNat 144 by decide] using
      PadJump.run_merge s (UInt256.ofNat 143) F (by simp only [F, cstk, List.length_cons]; omega) hrun
  have g1 : GasSteps (atState s 144 F) (atState s 149 F0) := by
    apply head.lift s (atState s 149 F0) e F
    have hh := run_head s (UInt256.ofNat 144) a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 off limit rho
      (by omega) hrun
    simpa only [head.template, head.end_pc, atState, F, F0] using hh
  have g3 : GasSteps (atState s 149 F0) (atState s 151 (v :: F0)) := by
    apply fold.lift s (atState s 151 (v :: F0)) e F0
    have hh := Shared32SparseRun.run_fold s (UInt256.ofNat 149) F0 hF0len hrun
    simpa only [fold.template, fold.end_pc, atState] using hh
  have g4 : GasSteps (atState s 151 (v :: F0)) (atState sW 158 F0) := by
    apply sparse.lift s (atState sW 158 F0) e (v :: F0)
    have hh := run_sparse s (UInt256.ofNat 151) v a0 a1 a2 a3 a4
      (a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: off :: UInt256.ofNat 4748 :: rho)
      (by simp only [List.length_cons]; omega) hrun hactive
    simpa only [sparse.template, sparse.end_pc, atState, sW, b, c, F0, cstk] using hh
  have g5 : GasSteps (atState sW 158 F0) (atState sW 166 F0) := by
    apply guard.lift sW (atState sW 166 F0) eW F0
    exact run_guard_miss sW F0 (by omega) hsize hne hrun
  have g9 := fixup.gasSteps sW eW F0 (by omega) hactive
  have hrest : MachineState.writeBytes sW.memory (Data.Bytes.natToBytesPadded 0 32) 157 = s.memory :=
    restore s.memory b c hmsize hzero
  have g9' : GasSteps (atState sW 166 F0) {s with pc := UInt256.ofNat 170, stack := F0} := by
    refine g9.cast rfl ?_
    simp only [hrest]
    rfl
  rw [hF, hF0]
  exact g0.trans (g1.trans (g3.trans (g4.trans (g5.trans g9'))))

#print axioms restore
#print axioms gasSteps_partial
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdGuardFixup
