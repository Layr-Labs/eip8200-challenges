import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newMaskHelperTemplates
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadCallTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskCallTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newMaskProjection
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-! Common metadata and builders for the H30b four-round sites. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskProjection
open Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskCallTrace

abbrev Artifact := Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout.A

abbrev leftWrapperIndex := QuadLayout.leftWrapperIndex
abbrev leftPC := QuadLayout.leftPC
abbrev leftJumpPC := QuadLayout.leftJumpPC
abbrev leftReturnPC := QuadLayout.leftReturnPC
abbrev leftHelperStartIndex := QuadLayout.leftHelperStartIndex
abbrev leftHelperJumpIndex := QuadLayout.leftHelperJumpIndex

abbrev rightWrapperIndex := QuadLayout.rightWrapperIndex
abbrev rightPC := QuadLayout.rightPC
abbrev rightJumpPC := QuadLayout.rightJumpPC
abbrev rightReturnPC := QuadLayout.rightReturnPC
abbrev rightHelperStartIndex := QuadLayout.rightHelperStartIndex
abbrev rightHelperJumpIndex := QuadLayout.rightHelperJumpIndex

abbrev leftStartPC : UInt256 := leftPC 0
abbrev leftEndPC : UInt256 := leftPC 20
abbrev rightStartPC : UInt256 := rightPC 0
abbrev rightEndPC : UInt256 := rightPC 20

abbrev leftHelperPCOfGroup (group : Nat) : UInt256 :=
  UInt256.ofNat (QuadLayout.leftHelperPCNat group)

abbrev rightHelperPCOfGroup (group : Nat) : UInt256 :=
  UInt256.ofNat (QuadLayout.rightHelperPCNat group)

abbrev leftHelperPC (k : Nat) : UInt256 :=
  leftHelperPCOfGroup (k / 4)

abbrev rightHelperPC (k : Nat) : UInt256 :=
  rightHelperPCOfGroup (k / 4)

theorem pc_toNat_instructionPC (index : Nat) :
    (UInt256.ofNat (Artifact.instructionPC index)).toNat =
      Artifact.instructionPC index := by
  exact QuadLayout.pc_toNat_instructionPC index

def leftAddress0 (k : Fin 20) : UInt256 :=
  StackRoundData.leftAddress (4 * k.val)

def leftAddress1 (k : Fin 20) : UInt256 :=
  StackRoundData.leftAddress (4 * k.val + 1)

def leftAddress2 (k : Fin 20) : UInt256 :=
  StackRoundData.leftAddress (4 * k.val + 2)

def leftAddress3 (k : Fin 20) : UInt256 :=
  StackRoundData.leftAddress (4 * k.val + 3)

def rightAddress0 (k : Fin 20) : UInt256 :=
  StackRoundData.rightAddress (4 * k.val)

def rightAddress1 (k : Fin 20) : UInt256 :=
  StackRoundData.rightAddress (4 * k.val + 1)

def rightAddress2 (k : Fin 20) : UInt256 :=
  StackRoundData.rightAddress (4 * k.val + 2)

def rightAddress3 (k : Fin 20) : UInt256 :=
  StackRoundData.rightAddress (4 * k.val + 3)

def leftRotation0 (k : Fin 20) : Nat :=
  StackRoundData.leftRotation (4 * k.val)

def leftRotation1 (k : Fin 20) : Nat :=
  StackRoundData.leftRotation (4 * k.val + 1)

def leftRotation2 (k : Fin 20) : Nat :=
  StackRoundData.leftRotation (4 * k.val + 2)

def leftRotation3 (k : Fin 20) : Nat :=
  StackRoundData.leftRotation (4 * k.val + 3)

def rightRotation0 (k : Fin 20) : Nat :=
  StackRoundData.rightRotation (4 * k.val)

def rightRotation1 (k : Fin 20) : Nat :=
  StackRoundData.rightRotation (4 * k.val + 1)

def rightRotation2 (k : Fin 20) : Nat :=
  StackRoundData.rightRotation (4 * k.val + 2)

def rightRotation3 (k : Fin 20) : Nat :=
  StackRoundData.rightRotation (4 * k.val + 3)

def leftConstant (k : Fin 20) : UInt256 :=
  StackRoundData.leftConstant (16 * (k.val / 4))

def rightConstant (k : Fin 20) : UInt256 :=
  StackRoundData.rightConstant (16 * (k.val / 4))

def shiftedFactor (r : Nat) : UInt256 :=
  UInt256.ofNat ((0x100000001 : Nat) <<< r)

def shiftedFactorWidth (r : Nat) : Fin 32 :=
  ⟨Nat.min 31 (((r + 40) / 8) - 1), by
    exact Nat.lt_succ_of_le (Nat.min_le_left 31 (((r + 40) / 8) - 1))⟩

def maskQuadWrapperTemplate
    (w0 w1 w2 w3 : Fin 32)
    (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (c0 c1 c2 c3 : UInt256) : List Instr :=
  MaskCallTrace.maskQuadCallPushes w0 w1 w2 w3
    returnPC p0 p1 p2 p3 helperPC c0 c1 c2 c3 ++
    [op .JUMP, op .JUMPDEST]

def leftCallTemplate (k : Fin 20) : List Instr :=
  MaskCallTrace.maskQuadCallPushes (shiftedFactorWidth (leftRotation0 k))
    (shiftedFactorWidth (leftRotation1 k))
    (shiftedFactorWidth (leftRotation2 k))
    (shiftedFactorWidth (leftRotation3 k))
    (leftReturnPC k.val)
    (leftAddress0 k) (leftAddress1 k) (leftAddress2 k) (leftAddress3 k)
    (leftHelperPC k.val) (shiftedFactor (leftRotation0 k))
    (shiftedFactor (leftRotation1 k)) (shiftedFactor (leftRotation2 k))
    (shiftedFactor (leftRotation3 k))

def rightCallTemplate (k : Fin 20) : List Instr :=
  MaskCallTrace.maskQuadCallPushes ⟨0, by decide⟩ ⟨0, by decide⟩
    ⟨0, by decide⟩ ⟨0, by decide⟩
    (rightReturnPC k.val)
    (rightAddress0 k) (rightAddress1 k) (rightAddress2 k) (rightAddress3 k)
    (rightHelperPC k.val)
    (UInt256.ofNat (32 - rightRotation0 k))
    (UInt256.ofNat (32 - rightRotation1 k))
    (UInt256.ofNat (32 - rightRotation2 k))
    (UInt256.ofNat (32 - rightRotation3 k))

def leftWrapperTemplate (k : Fin 20) : List Instr :=
  leftCallTemplate k ++ [op .JUMP, op .JUMPDEST]

def rightWrapperTemplate (k : Fin 20) : List Instr :=
  rightCallTemplate k ++ [op .JUMP, op .JUMPDEST]

def leftHelperTemplate (group : Fin 5) : List Instr :=
  MaskHelperTemplates.leftTemplate group
    (StackRoundData.leftConstant (16 * group.val))

def rightHelperTemplate (group : Fin 5) : List Instr :=
  MaskHelperTemplates.rightTemplate group
    (StackRoundData.rightConstant (16 * group.val))

theorem getElem_of_slice {artifact : ProgramArtifact}
    (startIndex : Nat) (template : List Instr)
    (hslice : (artifact.instructions.drop startIndex).take template.length = template)
    (offset : Nat) (hoffset : offset < template.length) :
    artifact.instructions[startIndex + offset]? = some template[offset] := by
  have hs := congrArg (fun xs : List Instr => xs[offset]?) hslice
  rw [List.getElem?_take, if_pos hoffset, List.getElem?_drop] at hs
  simpa [Nat.add_comm] using hs.trans (List.getElem?_eq_getElem hoffset)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites
