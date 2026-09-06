import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-!
# Q4M quad-round site certificate base

Exact Q4M layout metadata (wrapper and helper indices, program counters,
per-site parameters) shared by the left and right certificate modules.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

abbrev Artifact := Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact.submissionArtifact

theorem pc_toNat_instructionPC (index : Nat) :
    (UInt256.ofNat (Artifact.instructionPC index)).toNat =
      Artifact.instructionPC index := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hle :=
    Challenge.EvmProof.ProgramArtifact.instructionPC_le_code_size Artifact index
  have hcode := StackRoundData.artifact_code_bound
  exact Nat.lt_of_le_of_lt hle hcode

/-- Wrapper `k` of the left lane occupies instructions `858 + 12k .. 858 + 12k + 11`
(ten pushes, `JUMP`, and the return `JUMPDEST`). -/
def leftWrapperIndex (k : Nat) : Nat := 858 + 12 * k

def rightWrapperIndex (k : Nat) : Nat := 1108 + 12 * k

def leftPC (k : Nat) : UInt256 :=
  UInt256.ofNat (Artifact.instructionPC (leftWrapperIndex k))

def rightPC (k : Nat) : UInt256 :=
  UInt256.ofNat (Artifact.instructionPC (rightWrapperIndex k))

def leftStartPC : UInt256 := leftPC 0

def leftEndPC : UInt256 := leftPC 20

def rightStartPC : UInt256 := rightPC 0

def rightEndPC : UInt256 := rightPC 20

def leftJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (Artifact.instructionPC (leftWrapperIndex k + 10))

def rightJumpPC (k : Nat) : UInt256 :=
  UInt256.ofNat (Artifact.instructionPC (rightWrapperIndex k + 10))

def leftReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (Artifact.instructionPC (leftWrapperIndex k + 11))

def rightReturnPC (k : Nat) : UInt256 :=
  UInt256.ofNat (Artifact.instructionPC (rightWrapperIndex k + 11))

def leftHelperPCOfGroup : Nat → UInt256
  | 0 => UInt256.ofNat 0xedc
  | 1 => UInt256.ofNat 0x4
  | 2 => UInt256.ofNat 0x236
  | 3 => UInt256.ofNat 0xf7f
  | _ => UInt256.ofNat 0x2f5

/-- Right-lane group 4 (Boolean form 0, constant 0) shares the left-lane group 0 helper. -/
def rightHelperPCOfGroup : Nat → UInt256
  | 0 => UInt256.ofNat 0x1042
  | 1 => UInt256.ofNat 0x1101
  | 2 => UInt256.ofNat 0x11c4
  | 3 => UInt256.ofNat 0x1283
  | _ => UInt256.ofNat 0xedc

def leftHelperPC (k : Nat) : UInt256 := leftHelperPCOfGroup (k / 4)

def rightHelperPC (k : Nat) : UInt256 := rightHelperPCOfGroup (k / 4)

def leftHelperStartIndex : Nat → Nat
  | 0 => 1409
  | 1 => 2
  | 2 => 413
  | 3 => 1512
  | _ => 528

def rightHelperStartIndex : Nat → Nat
  | 0 => 1631
  | 1 => 1746
  | 2 => 1865
  | 3 => 1980
  | _ => 1409

def leftHelperJumpIndex : Nat → Nat
  | 0 => 1511
  | 1 => 120
  | 2 => 527
  | 3 => 1630
  | _ => 642

def rightHelperJumpIndex : Nat → Nat
  | 0 => 1745
  | 1 => 1864
  | 2 => 1979
  | 3 => 2098
  | _ => 1511

def leftAddress0 (k : Fin 20) : UInt256 := StackRoundData.leftAddress (4 * k.val)
def leftAddress1 (k : Fin 20) : UInt256 := StackRoundData.leftAddress (4 * k.val + 1)
def leftAddress2 (k : Fin 20) : UInt256 := StackRoundData.leftAddress (4 * k.val + 2)
def leftAddress3 (k : Fin 20) : UInt256 := StackRoundData.leftAddress (4 * k.val + 3)

def rightAddress0 (k : Fin 20) : UInt256 := StackRoundData.rightAddress (4 * k.val)
def rightAddress1 (k : Fin 20) : UInt256 := StackRoundData.rightAddress (4 * k.val + 1)
def rightAddress2 (k : Fin 20) : UInt256 := StackRoundData.rightAddress (4 * k.val + 2)
def rightAddress3 (k : Fin 20) : UInt256 := StackRoundData.rightAddress (4 * k.val + 3)

def leftRotation0 (k : Fin 20) : Nat := StackRoundData.leftRotation (4 * k.val)
def leftRotation1 (k : Fin 20) : Nat := StackRoundData.leftRotation (4 * k.val + 1)
def leftRotation2 (k : Fin 20) : Nat := StackRoundData.leftRotation (4 * k.val + 2)
def leftRotation3 (k : Fin 20) : Nat := StackRoundData.leftRotation (4 * k.val + 3)

def rightRotation0 (k : Fin 20) : Nat := StackRoundData.rightRotation (4 * k.val)
def rightRotation1 (k : Fin 20) : Nat := StackRoundData.rightRotation (4 * k.val + 1)
def rightRotation2 (k : Fin 20) : Nat := StackRoundData.rightRotation (4 * k.val + 2)
def rightRotation3 (k : Fin 20) : Nat := StackRoundData.rightRotation (4 * k.val + 3)

/-- The multiplier immediate width: `PUSH5` for `r ≤ 7`, otherwise `PUSH6`. -/
def rotWidth (r : Nat) : Fin 33 :=
  if r ≤ 7 then ⟨5, by decide⟩ else ⟨6, by decide⟩

theorem rotWidth_ne_zero (r : Nat) : (rotWidth r).val ≠ 0 := by
  unfold rotWidth
  split <;> decide

def leftM0 (k : Fin 20) : UInt256 := QuadRoundModel.rotM (leftRotation0 k)
def leftM1 (k : Fin 20) : UInt256 := QuadRoundModel.rotM (leftRotation1 k)
def leftM2 (k : Fin 20) : UInt256 := QuadRoundModel.rotM (leftRotation2 k)
def leftM3 (k : Fin 20) : UInt256 := QuadRoundModel.rotM (leftRotation3 k)

def rightM0 (k : Fin 20) : UInt256 := QuadRoundModel.rotM (rightRotation0 k)
def rightM1 (k : Fin 20) : UInt256 := QuadRoundModel.rotM (rightRotation1 k)
def rightM2 (k : Fin 20) : UInt256 := QuadRoundModel.rotM (rightRotation2 k)
def rightM3 (k : Fin 20) : UInt256 := QuadRoundModel.rotM (rightRotation3 k)

def leftW0 (k : Fin 20) : Fin 33 := rotWidth (leftRotation0 k)
def leftW1 (k : Fin 20) : Fin 33 := rotWidth (leftRotation1 k)
def leftW2 (k : Fin 20) : Fin 33 := rotWidth (leftRotation2 k)
def leftW3 (k : Fin 20) : Fin 33 := rotWidth (leftRotation3 k)

def rightW0 (k : Fin 20) : Fin 33 := rotWidth (rightRotation0 k)
def rightW1 (k : Fin 20) : Fin 33 := rotWidth (rightRotation1 k)
def rightW2 (k : Fin 20) : Fin 33 := rotWidth (rightRotation2 k)
def rightW3 (k : Fin 20) : Fin 33 := rotWidth (rightRotation3 k)

def leftConstant (k : Fin 20) : UInt256 :=
  StackRoundData.leftConstant (16 * (k.val / 4))

def rightConstant (k : Fin 20) : UInt256 :=
  StackRoundData.rightConstant (16 * (k.val / 4))

def quadWrapperTemplate (returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 : UInt256)
    (w0 w1 w2 w3 : Fin 33) : List Instr :=
  QuadRoundState.quadCallPushes returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 w0 w1 w2 w3 ++
    [op .JUMP, op .JUMPDEST]

def leftWrapperTemplate (k : Fin 20) : List Instr :=
  quadWrapperTemplate (leftReturnPC k.val) (leftAddress0 k) (leftAddress1 k)
    (leftAddress2 k) (leftAddress3 k) (leftHelperPC k.val)
    (leftM0 k) (leftM1 k) (leftM2 k) (leftM3 k)
    (leftW0 k) (leftW1 k) (leftW2 k) (leftW3 k)

def rightWrapperTemplate (k : Fin 20) : List Instr :=
  quadWrapperTemplate (rightReturnPC k.val) (rightAddress0 k) (rightAddress1 k)
    (rightAddress2 k) (rightAddress3 k) (rightHelperPC k.val)
    (rightM0 k) (rightM1 k) (rightM2 k) (rightM3 k)
    (rightW0 k) (rightW1 k) (rightW2 k) (rightW3 k)

def leftHelperTemplate (group : Fin 5) : List Instr :=
  quadBeforeJumpTemplate group.val
    (StackRoundData.leftConstant (16 * group.val))

def rightHelperTemplate (group : Fin 5) : List Instr :=
  quadBeforeJumpTemplate (4 - group.val)
    (StackRoundData.rightConstant (16 * group.val))

theorem getElem_of_slice {artifact : ProgramArtifact}
    (startIndex : Nat) (template : List Instr)
    (hslice : (artifact.instructions.drop startIndex).take template.length = template)
    (offset : Nat) (hoffset : offset < template.length) :
    artifact.instructions[startIndex + offset]? = some template[offset] := by
  have hs := congrArg (fun xs : List Instr => xs[offset]?) hslice
  rw [List.getElem?_take, if_pos hoffset, List.getElem?_drop] at hs
  simpa [Nat.add_comm] using hs.trans (List.getElem?_eq_getElem hoffset)

def castTemplate {artifact : ProgramArtifact} {fork : Fork}
    {first second : List Instr}
    (site : GenericRoundSite artifact fork first) (h : first = second) :
    GenericRoundSite artifact fork second where
  startPC := site.startPC
  endPC := site.endPC
  sites := site.sites
  head_eq := site.head_eq
  end_eq := site.end_eq
  instruction_eq := site.instruction_eq.trans h
  contiguous := site.contiguous

theorem castTemplate_start {artifact : ProgramArtifact} {fork : Fork}
    {first second : List Instr}
    (site : GenericRoundSite artifact fork first) (h : first = second) :
    (castTemplate site h).startPC = site.startPC := rfl

theorem castTemplate_end {artifact : ProgramArtifact} {fork : Fork}
    {first second : List Instr}
    (site : GenericRoundSite artifact fork first) (h : first = second) :
    (castTemplate site h).endPC = site.endPC := rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites
