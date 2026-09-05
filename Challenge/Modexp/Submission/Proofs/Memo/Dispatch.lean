import Challenge.Modexp.Submission.Proofs.Memo.PCs
import Challenge.Modexp.Submission.Proofs.Memo.Logic
import Challenge.Modexp.Submission.Proofs.Memo.Step

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.Dispatch

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Memo

/-- The residue table: byte `r` is the 32-byte entry index of the guard for calldata sizes
congruent to `r` modulo 26; unused residues select the fallback stub at pc 1376. -/
def table : Nat := 19978037702055533804967148740280010722836663273717868341649456475336210066219

def prefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 977 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 978 32 19978037702055533804967148740280010722836663273717868341649456475336210066219,
   Main.pushAt 979 1 26,
   Main.opAt 980 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATASIZE)),
   Main.opAt 981 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.MOD)),
   Main.opAt 982 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.BYTE)),
   Main.pushAt 983 1 5,
   Main.opAt 984 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.SHL))
  ]

def jumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 985 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMP))

def jumpState (input : ByteArray) (dest : Nat) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1356
      stack := [UInt256.ofNat dest] }

theorem run_prefix (input : ByteArray) (r e : Nat) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = r)
    (he : UInt256.byteAt (UInt256.ofNat r) (UInt256.ofNat 19978037702055533804967148740280010722836663273717868341649456475336210066219) = UInt256.ofNat e)
    (he255 : e ≤ 255) :
    Challenge.EvmProof.Stepper.runLocatedBlock prefixPath (Main.trampolineState input 1314) =
      some (jumpState input (32 * e)) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have hmod : UInt256.ofNat input.size % UInt256.ofNat 26 = UInt256.ofNat r := by
    rw [Logic.mod_ofNat hsize (by norm_num) (by norm_num), hr]
  have hshl : UInt256.shiftLeft (UInt256.ofNat e) (UInt256.ofNat 5) = UInt256.ofNat (32 * e) :=
    Logic.shl5_ofNat (lt_of_lt_of_le (by omega : e < 256) (by norm_num))
  simp [prefixPath, jumpState, hmod, he, hshl, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_jump (input : ByteArray) (dest : Nat) (hdest : dest < 8192)
    (hjump : Decode.isValidJumpDest submissionBytecode dest = true) :
    Challenge.EvmProof.Stepper.runLocated jumpLocated (jumpState input dest) =
      some (Main.trampolineState input dest) := by
  have hpc : (jumpState input dest).pc.toNat = Artifact.submissionArtifact.instructionPC 985 := by
    simp [jumpState, initialState, PCs.pc0, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jump jumpLocated rfl (jumpState input dest) dest [] hpc rfl (by simp) rfl
    (lt_of_lt_of_le hdest (by norm_num)) hjump).trans rfl

def stubPrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1005 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 1006 2 1196
  ]

def stubJumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1380
      stack := [UInt256.ofNat 1196] }

def stubJumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1007 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMP))

theorem run_stub_prefix (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock stubPrefixPath (Main.trampolineState input 1376) =
      some (stubJumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [stubPrefixPath, stubJumpState, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_stub_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated stubJumpLocated (stubJumpState input) =
      some (Main.trampolineState input 1196) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 1196 = true :=
    Artifact.isValidJumpDest_index 899 (by rfl)
  have hpc : (stubJumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1007 := by
    simp [stubJumpState, initialState, PCs.pc0, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jump stubJumpLocated rfl (stubJumpState input) 1196 [] hpc rfl (by simp) rfl (by norm_num) hjump).trans rfl

end Challenge.Modexp.Submission.Proofs.Memo.Dispatch
