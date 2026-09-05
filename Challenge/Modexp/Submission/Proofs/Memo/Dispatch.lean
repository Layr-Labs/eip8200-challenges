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

/-- The residue table: byte `r` is the 16-byte entry index of the guard for calldata sizes
congruent to `r` modulo 26; zero entries select the fallback stub at pc 1361. -/
def table : Nat := 452312851962337609803021705617712436052817602537946923124231457836929908736

def base : Nat := 1361

def prefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 977 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 978 32 452312851962337609803021705617712436052817602537946923124231457836929908736,
   Main.pushAt 979 1 26,
   Main.opAt 980 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATASIZE)),
   Main.opAt 981 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.MOD)),
   Main.opAt 982 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.BYTE)),
   Main.pushAt 983 1 4,
   Main.opAt 984 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.SHL)),
   Main.pushAt 985 2 1361
  ]

def addLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 986 (EvmSemantics.Operation.StopArith (EvmSemantics.Operation.StopArithOps.ADD))

def jumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 987 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMP))

def addState (input : ByteArray) (e : Nat) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1359
      stack := [UInt256.ofNat 1361, UInt256.ofNat (16 * e)] }

def jumpState (input : ByteArray) (dest : Nat) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1360
      stack := [UInt256.ofNat dest] }

theorem run_prefix (input : ByteArray) (r e : Nat) (hsize : input.size < 2 ^ 256)
    (hr : input.size % 26 = r)
    (he : UInt256.byteAt (UInt256.ofNat r) (UInt256.ofNat 452312851962337609803021705617712436052817602537946923124231457836929908736) = UInt256.ofNat e)
    (he255 : e ≤ 255) :
    Challenge.EvmProof.Stepper.runLocatedBlock prefixPath (Main.trampolineState input 1314) =
      some (addState input e) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have hmod : UInt256.ofNat input.size % UInt256.ofNat 26 = UInt256.ofNat r := by
    rw [Logic.mod_ofNat hsize (by norm_num) (by norm_num), hr]
  have hshl : UInt256.shiftLeft (UInt256.ofNat e) (UInt256.ofNat 4) = UInt256.ofNat (16 * e) :=
    Logic.shl4_ofNat (lt_of_lt_of_le (by omega : e < 256) (by norm_num))
  simp [prefixPath, addState, hmod, he, hshl, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc0,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_add (input : ByteArray) (e : Nat) (he255 : e ≤ 255) :
    Challenge.EvmProof.Stepper.runLocated addLocated (addState input e) =
      some (jumpState input (1361 + 16 * e)) := by
  have hpc : (addState input e).pc.toNat = Artifact.submissionArtifact.instructionPC 986 := by
    simp [addState, initialState, PCs.pc0, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_add addLocated rfl (addState input e) 1361 (16 * e) 1359 [] hpc rfl (by norm_num) rfl (by decide)
    (lt_of_lt_of_le (by omega : 1361 + 16 * e < 8192) (by norm_num))).trans rfl

theorem run_jump (input : ByteArray) (dest : Nat) (hdest : dest < 8192)
    (hjump : Decode.isValidJumpDest submissionBytecode dest = true) :
    Challenge.EvmProof.Stepper.runLocated jumpLocated (jumpState input dest) =
      some (Main.trampolineState input dest) := by
  have hpc : (jumpState input dest).pc.toNat = Artifact.submissionArtifact.instructionPC 987 := by
    simp [jumpState, initialState, PCs.pc0, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jump jumpLocated rfl (jumpState input dest) dest [] hpc rfl (by simp) rfl
    (lt_of_lt_of_le hdest (by norm_num)) hjump).trans rfl

def stubPrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 988 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 989 2 1196
  ]

def stubJumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1365
      stack := [UInt256.ofNat 1196] }

def stubJumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 990 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMP))

theorem run_stub_prefix (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock stubPrefixPath (Main.trampolineState input 1361) =
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
  have hpc : (stubJumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 990 := by
    simp [stubJumpState, initialState, PCs.pc0, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jump stubJumpLocated rfl (stubJumpState input) 1196 [] hpc rfl (by simp) rfl (by norm_num) hjump).trans rfl

end Challenge.Modexp.Submission.Proofs.Memo.Dispatch
