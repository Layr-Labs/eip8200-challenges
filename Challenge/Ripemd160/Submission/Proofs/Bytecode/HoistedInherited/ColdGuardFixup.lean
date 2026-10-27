import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32Codecopy
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32Sites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32SparseRun
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerPersistentStart
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32Scratch

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-!
# The cold guard-miss route through the shared 32-byte block

Every length the alignment guard at 449 does not send to the block loop jumps to 143, the
32-byte block. That block sets the continuation slot to the output entry 9949 and writes two
scratch bytes (165 and 188) before its length test at 158. Any other length falls through to the
sentinel store at 9998 with both scratch bytes still written: no store undoes them. They are not
part of the padded message (which starts at 1056) nor of the zero band the block loop needs, and
the staging store at 0xa2 of the first block overwrites both before any read.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.ColdGuardFixup
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate HoistedInherited.Shared32Sites

def cstk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256) (rho : List UInt256) :
    List UInt256 :=
  a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: off :: lim :: rho

/-- The two scratch bytes of the shared 32-byte block. -/
def wMemory (m : ByteArray) (b c : UInt8) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes m (ByteArray.mk #[b]) 165)
    (ByteArray.mk #[c]) 188

/-- The two scratch byte values the 32-byte block leaves on the generic route: the sentinel `0x80`
at 165 and the low byte of the resident coefficient word at 188. -/
def dirtyB : UInt8 := UInt8.ofNat ((UInt256.ofNat 128).toNat % 256)
def dirtyC : UInt8 := UInt8.ofNat ((Paired144WordRound.fusedCoefficientWord 0 3).toNat % 256)

/-- A zero word store would undo both scratch bytes on zero, active memory. -/
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

/-- Away from the two scratch bytes the 32-byte block's writes are invisible. -/
theorem wMemory_getD (m : ByteArray) (b c : UInt8) (a : Nat) (h165 : a ≠ 165) (h188 : a ≠ 188) :
    (wMemory m b c)[a]?.getD 0 = m[a]?.getD 0 := by
  have e1 : (ByteArray.mk #[c]).size = 1 := rfl
  have eb : (ByteArray.mk #[b]).size = 1 := rfl
  simp only [wMemory, MachineState.writeBytes_getElem?_getD, e1, eb]
  rw [if_neg (by omega), if_neg (by omega)]

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
    runInstrSeq HoistedInherited.Shared32SparseRun.headTemplate
      {s with pc := pc, stack := cstk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} =
      some {s with
        pc := pcAfter pc HoistedInherited.Shared32SparseRun.headTemplate
        stack := UInt256.eq (UInt256.ofNat 32) lim :: cstk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 off (UInt256.ofNat 9949) rho} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [HoistedInherited.Shared32SparseRun.headTemplate, runInstrSeq, DataStepper.runInstr,
    pcAfter, hrun, hcap, Instr.size, UInt256.succ, cstk, Nat.add_assoc,
    List.getElem?_cons_zero, List.exchange]
  rfl

/-- A guard miss at 449 that is not 32 bytes long reaches the sentinel store at 9998 with the two
scratch bytes written and the output entry 9949 in the continuation slot. -/
def gasSteps_partial (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 860) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hsize : s.executionEnv.calldata.size < 2^256)
    (hne : s.executionEnv.calldata.size ≠ 32)
    (hactive : 34 ≤ s.activeWords.toNat)
    (hmemsize : 194 ≤ s.memory.size)
    (hzero : ∀ a, 162 ≤ a → a < 194 → s.memory[a]?.getD 0 = 0)
    (hlim : limit = UInt256.ofNat s.executionEnv.calldata.size) :
    GasSteps {s with pc := UInt256.ofNat 143, stack := StaggerPersistentFrame.frame h off limit rho}
      { s with
        pc := UInt256.ofNat 9998
        stack := StaggerPersistentFrame.frame h off (UInt256.ofNat 9949) rho
        memory := wMemory s.memory dirtyB dirtyC } := by
  have heq : UInt256.eq (UInt256.ofNat 32) limit = UInt256.ofNat 0 := by
    rw [hlim]
    have hw : (UInt256.ofNat s.executionEnv.calldata.size).toNat = s.executionEnv.calldata.size := by
      rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsize]
    unfold UInt256.eq
    rw [hw, if_neg (by simpa using Ne.symm hne)]
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
  let F0 := cstk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 off (UInt256.ofNat 9949) rho
  have hF : StaggerPersistentFrame.frame h off limit rho = F := rfl
  have hF0 : StaggerPersistentFrame.frame h off (UInt256.ofNat 9949) rho = F0 := rfl
  have hF0len : F0.length ≤ 900 := by simp only [F0, cstk, List.length_cons]; omega
  let b := UInt8.ofNat ((UInt256.ofNat 128).toNat % 256)
  let c := UInt8.ofNat (a4.toNat % 256)
  let sW : State := {s with memory := wMemory s.memory b c}
  have eW : Env sW := ⟨hcode, hfork, hrun, hnp⟩
  have g0 : GasSteps (atState s 143 F) (atState s 144 F) := by
    apply special.lift s (atState s 144 F) e F
    simpa only [special.template, atState, show UInt256.ofNat 143 + UInt256.ofNat 1 = UInt256.ofNat 144 by decide] using
      PadJump.run_merge s (UInt256.ofNat 143) F (by simp only [F, cstk, List.length_cons]; omega) hrun
  have g1 : GasSteps (atState s 144 F) (atState s 151 (UInt256.ofNat 0 :: F0)) := by
    apply head.lift s (atState s 151 (UInt256.ofNat 0 :: F0)) e F
    have hh := run_head s (UInt256.ofNat 144) a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 off limit rho
      (by omega) hrun
    simpa only [head.template, head.end_pc, atState, F, F0, heq] using hh
  have g3 : GasSteps (atState s 151 (UInt256.ofNat 0 :: F0)) (atState sW 188 F0) := by
    apply combined.lift s (atState sW 188 F0) e (UInt256.ofNat 0 :: F0)
    have hh := HoistedInherited.Shared32SparseRun.run_combined_miss s F0 hF0len hrun hactive
    have hm : HoistedInherited.Shared32SparseRun.copied s.memory s.executionEnv.code = wMemory s.memory b c := by
      rw [hcode, HoistedInherited.Shared32Codecopy.copied_sparse s.memory hmemsize hzero]
      have hb : b = 128 := by decide
      have hc : c = 1 := by decide
      simp only [HoistedInherited.Shared32Scratch.sparseMemory, wMemory, hb, hc]
    simpa only [combined.template, atState, sW, hm] using hh
  have hvW : Decode.isValidJumpDest sW.executionEnv.code 9997 = true := by
    have h := HoistedInherited.Artifact.submissionArtifact.isValidJumpDest_index 6913 (by rfl)
    have hp : HoistedInherited.Artifact.submissionArtifact.instructionPC 6913 = 9997 := by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
    rw [hp] at h
    rw [eW.code]
    exact h
  have g4 : GasSteps (atState sW 188 F0) (atState sW 9997 F0) := by
    apply missJump.lift sW (atState sW 9997 F0) eW F0
    exact HoistedInherited.Shared32SparseRun.run_missJump sW F0 (by simp only [F0, cstk, List.length_cons]; omega) hrun hvW
  have g6 : GasSteps (atState sW 9997 F0) (atState sW 9998 F0) := by
    apply missTail.lift sW (atState sW 9998 F0) eW F0
    have hc : F0.length < 1024 := by omega
    simp [missTail.template, runInstrSeq, DataStepper.runInstr, atState, eW.run, hc]
    rfl
  rw [hF, hF0]
  exact g0.trans (g1.trans (g3.trans (g4.trans g6)))

#print axioms restore
#print axioms gasSteps_partial
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.ColdGuardFixup
