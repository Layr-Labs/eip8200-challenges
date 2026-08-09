import Challenge.Sha256.Submission.Proofs.Bytecode.Schedule
import Challenge.Sha256.Submission.Proofs.Bytecode.BigSigma
import Challenge.Sha256.Submission.Proofs.Bytecode.PaddedBlockBridge
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
/-!
# Direct execution of the reference SHA-256 compression routine

This file starts the bytecode-local proof of `compress`.  Its public states
make the internal calling convention explicit, so the eventual round invariant
can be reused by proofs for independently optimized participant bytecode.
-/

namespace Challenge.Sha256.Submission.Proofs.Bytecode.Compression

open EvmSemantics
open EvmSemantics.EVM

@[simp] private theorem wordOfNatZero : UInt256.ofNat 0 = 0 := by decide
@[simp] private theorem wordStructZero : ({ val := 0 } : UInt256) = 0 := by decide

private theorem activeWordsAfter_small (curr offset : Nat)
    (hcurr : 10 ≤ curr) (hoff : offset + 32 ≤ 320) :
    MachineState.activeWordsAfter curr offset 32 = curr := by
  unfold MachineState.activeWordsAfter
  simp only [OfNat.ofNat, Nat.reduceEqDiff, ↓reduceIte]
  apply Nat.max_eq_left
  have hdiv : (offset + 32 - 1) / 32 < 10 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    omega
  exact (Nat.succ_le_iff.mpr hdiv).trans hcurr

private theorem activeWordsAfter_ge_ten (curr offset : Nat)
    (hoff : 288 ≤ offset) :
    10 ≤ MachineState.activeWordsAfter curr offset 32 := by
  unfold MachineState.activeWordsAfter
  simp only [OfNat.ofNat, Nat.reduceEqDiff, ↓reduceIte]
  apply le_trans _ (Nat.le_max_right curr ((offset + 32 - 1) / 32 + 1))
  have hdiv : 9 ≤ (offset + 32 - 1) / 32 := by
    apply (Nat.le_div_iff_mul_le (by decide)).2
    omega
  exact Nat.succ_le_succ hdiv

private theorem activeWordsAfter_lt (curr offset limit : Nat)
    (hcurr : curr < limit) (hoff : offset + 32 < limit) :
    MachineState.activeWordsAfter curr offset 32 < limit := by
  unfold MachineState.activeWordsAfter
  simp only [OfNat.ofNat, Nat.reduceEqDiff, ↓reduceIte]
  rw [max_lt_iff]
  constructor
  · exact hcurr
  · have hdiv := Nat.div_le_self (offset + 32 - 1) 32
    calc
      (offset + 32 - 1) / 32 + 1 ≤ (offset + 32 - 1) + 1 :=
        Nat.add_le_add_right hdiv 1
      _ = offset + 32 := by omega
      _ < limit := hoff

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private theorem word_land_comm (a b : UInt256) : a.land b = b.land a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_land, Nat.land_comm]

def entryPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨506, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨507, .push ⟨2, by decide⟩ (UInt256.ofNat 621), by rfl, by decide⟩,
   ⟨508, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨509, .push ⟨2, by decide⟩ (UInt256.ofNat 446), by rfl, by decide⟩,
   ⟨510, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def copyAndLoopStartPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨511, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨512, .push ⟨2, by decide⟩ (UInt256.ofNat 256), by rfl, by decide⟩,
   ⟨513, .push ⟨2, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨514, .push ⟨2, by decide⟩ (UInt256.ofNat 544), by rfl, by decide⟩,
   ⟨515, .op .MCOPY, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨516, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩]

def conditionPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨517, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨518, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨519, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨520, .op .EQ, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨521, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨522, .push ⟨2, by decide⟩ (UInt256.ofNat 935), by rfl, by decide⟩,
   ⟨523, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def setupWPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨524, .push ⟨2, by decide⟩ (UInt256.ofNat 416), by rfl, by decide⟩,
   ⟨525, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨526, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨527, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨528, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨529, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨530, .push ⟨2, by decide⟩ (UInt256.ofNat 800), by rfl, by decide⟩,
   ⟨531, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨532, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩]

def setupKPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨533, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨534, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨535, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨536, .push ⟨1, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨537, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨538, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨539, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨540, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩]

/- Superseded standalone helper setup paths. -/
/-
def setupH6Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨537, .push ⟨3, by decide⟩ (UInt256.ofNat 703), by rfl, by decide⟩,
   ⟨538, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨539, .push ⟨2, by decide⟩ (UInt256.ofNat 480), by rfl, by decide⟩,
   ⟨540, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨541, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨542, .push ⟨3, by decide⟩ 0, by rfl, by decide⟩,
   ⟨543, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩]

def setupH5Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨544, .push ⟨3, by decide⟩ (UInt256.ofNat 448), by rfl, by decide⟩,
   ⟨545, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨546, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨547, .push ⟨3, by decide⟩ 0, by rfl, by decide⟩,
   ⟨548, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩]

def setupChPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨549, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨550, .op (.Dup ⟨7, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨551, .push ⟨2, by decide⟩ (UInt256.ofNat 212), by rfl, by decide⟩,
   ⟨552, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setupBigSigma1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨553, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨554, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨555, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨556, .push ⟨2, by decide⟩ (UInt256.ofNat 163), by rfl, by decide⟩,
   ⟨557, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def finishT1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨560, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩]

def setupT2H2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨561, .push ⟨2, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨562, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨563, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨564, .push ⟨2, by decide⟩ (UInt256.ofNat 770), by rfl, by decide⟩,
   ⟨565, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨566, .push ⟨2, by decide⟩ (UInt256.ofNat 352), by rfl, by decide⟩,
   ⟨567, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩]

def setupT2H1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨568, .push ⟨2, by decide⟩ (UInt256.ofNat 320), by rfl, by decide⟩,
   ⟨569, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩]

def setupMajPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨570, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨571, .push ⟨2, by decide⟩ (UInt256.ofNat 233), by rfl, by decide⟩,
   ⟨572, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def setupBigSigma0Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨590, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨591, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨592, .push ⟨2, by decide⟩ (UInt256.ofNat 114), by rfl, by decide⟩,
   ⟨593, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def finishT2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨595, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨596, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨597, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩]
-/

/-- Load H6/H5 and enter the integrated Ch+BSIG1+T1 helper. -/
def setupT1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨541, .push ⟨12, by decide⟩ (UInt256.ofNat 480), by rfl, by decide⟩,
   ⟨542, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨543, .push ⟨11, by decide⟩ (UInt256.ofNat 448), by rfl, by decide⟩,
   ⟨544, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨545, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨546, .push ⟨2, by decide⟩ (UInt256.ofNat 163), by rfl, by decide⟩,
   ⟨547, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Load H0/H2/H1 and enter the integrated Maj+BSIG0+T2 helper. -/
def setupT2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨574, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨575, .push ⟨2, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨576, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨577, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨578, .push ⟨12, by decide⟩ (UInt256.ofNat 352), by rfl, by decide⟩,
   ⟨579, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨580, .push ⟨10, by decide⟩ (UInt256.ofNat 320), by rfl, by decide⟩,
   ⟨581, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨582, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨583, .push ⟨2, by decide⟩ (UInt256.ofNat 114), by rfl, by decide⟩,
   ⟨584, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def shift76Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨598, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨599, .push ⟨10, by decide⟩ (UInt256.ofNat 480), by rfl, by decide⟩,
   ⟨600, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨601, .push ⟨5, by decide⟩ (UInt256.ofNat 512), by rfl, by decide⟩,
   ⟨602, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩]

def store7Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  []

def shift65Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨603, .push ⟨12, by decide⟩ (UInt256.ofNat 448), by rfl, by decide⟩,
   ⟨604, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨605, .push ⟨5, by decide⟩ (UInt256.ofNat 480), by rfl, by decide⟩,
   ⟨606, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩]

def store6Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  []

def storeEPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨607, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨608, .push ⟨3, by decide⟩ (UInt256.ofNat 448), by rfl, by decide⟩,
   ⟨609, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩]

def setupH3ForH4Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨610, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨611, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨612, .push ⟨11, by decide⟩ (UInt256.ofNat 384), by rfl, by decide⟩,
   ⟨613, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨614, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨615, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨616, .push ⟨5, by decide⟩ (UInt256.ofNat 416), by rfl, by decide⟩,
   ⟨617, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩]

def storeH4Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  []

def shift32Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨618, .push ⟨12, by decide⟩ (UInt256.ofNat 352), by rfl, by decide⟩,
   ⟨619, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨620, .push ⟨5, by decide⟩ (UInt256.ofNat 384), by rfl, by decide⟩,
   ⟨621, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩]

def store3Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  []

def shift21Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨622, .push ⟨12, by decide⟩ (UInt256.ofNat 320), by rfl, by decide⟩,
   ⟨623, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨624, .push ⟨5, by decide⟩ (UInt256.ofNat 352), by rfl, by decide⟩,
   ⟨625, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩]

def store2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  []

def finishRoundPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨626, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨627, .push ⟨3, by decide⟩ (UInt256.ofNat 320), by rfl, by decide⟩,
   ⟨628, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨629, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨630, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨631, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨632, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨633, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨634, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨635, .push ⟨2, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨636, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨637, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨638, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨639, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨640, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨641, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨642, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨643, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨644, .push ⟨5, by decide⟩ (UInt256.ofNat 633), by rfl, by decide⟩,
   ⟨645, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def roundsExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  conditionPath ++
  [⟨646, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨647, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨648, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩]

def foldConditionPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨649, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨650, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨651, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨652, .op .EQ, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨653, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨654, .push ⟨2, by decide⟩ (UInt256.ofNat 993), by rfl, by decide⟩,
   ⟨655, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def foldSetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨656, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨657, .push ⟨3, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨658, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨659, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨660, .push ⟨3, by decide⟩ (UInt256.ofNat 544), by rfl, by decide⟩,
   ⟨661, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨662, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨663, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨664, .push ⟨3, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨665, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨666, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨667, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨668, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨669, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨670, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨671, .push ⟨2, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨672, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨673, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩]

def foldIncrementPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨674, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨675, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨676, .push ⟨7, by decide⟩ (UInt256.ofNat 938), by rfl, by decide⟩,
   ⟨677, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def foldExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  foldConditionPath ++
  [⟨678, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨679, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨680, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨681, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def compressEntry (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 612
    stack := [msgOff, returnDest] ++ rest }

def callSchedule (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  Schedule.scheduleEntry s msgOff (UInt256.ofNat 621)
    (msgOff :: returnDest :: rest)

def afterSchedule (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  Schedule.scheduleResult s msgOff (UInt256.ofNat 621)
    (msgOff :: returnDest :: rest)

def copyHashState (s : State) : State :=
  { s with
    memory := MachineState.writeBytes s.memory
      (MachineState.readPadded s.memory 288 256) 544
    activeWords := s.activeWordsAfterUInt256_2 544 256 288 256 }

def roundAt (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { s with
    pc := UInt256.ofNat 633
    stack := [UInt256.ofNat j, msgOff, returnDest] ++ rest }

def afterCondition (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { s with
    pc := UInt256.ofNat 643
    stack := [UInt256.ofNat j, msgOff, returnDest] ++ rest }

def hValue (s : State) (i : Nat) : UInt256 :=
  MachineState.readWord s.memory
    (Accessors.slotOffset 288 (UInt256.ofNat i))

def wValue (s : State) (j : Nat) : UInt256 :=
  MachineState.readWord s.memory
    (Accessors.slotOffset 800 (UInt256.ofNat j))

def kValue (s : State) (j : Nat) : UInt256 :=
  let offset := (UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 2) +
    UInt256.ofNat 32).toNat
  UInt256.shiftRight (MachineState.readWord s.memory offset)
    (UInt256.ofNat 224)

def loadedE (s : State) : State :=
  { s with activeWords := s.activeWordsAfterUInt256 416 32 }

def callW (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadEntry (loadedE s) 279 (UInt256.ofNat j) 0
    (UInt256.ofNat 661)
    ([UInt256.ofNat 0xffffffff, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def gotW (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadReturned (loadedE s) 800 (UInt256.ofNat j)
    (UInt256.ofNat 661)
    ([UInt256.ofNat 0xffffffff, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def callK (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadEntry (gotW s msgOff returnDest rest j) 257
    (UInt256.ofNat j) 0 (UInt256.ofNat 671)
    ([wValue s j, UInt256.ofNat 0xffffffff, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)

def gotK (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.kAtReturned (gotW s msgOff returnDest rest j)
    (UInt256.ofNat j) (UInt256.ofNat 671)
    ([wValue s j, UInt256.ofNat 0xffffffff, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)

def callH6 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadEntry (gotK s msgOff returnDest rest j) 318
    (UInt256.ofNat 6) 0 (UInt256.ofNat 686)
    ([0, UInt256.ofNat 703, kValue s j, wValue s j,
      UInt256.ofNat 0xffffffff, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def gotH6 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadReturned (gotK s msgOff returnDest rest j) 288
    (UInt256.ofNat 6) (UInt256.ofNat 686)
    ([0, UInt256.ofNat 703, kValue s j, wValue s j,
      UInt256.ofNat 0xffffffff, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def callH5 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadEntry (gotH6 s msgOff returnDest rest j) 318
    (UInt256.ofNat 5) 0 (UInt256.ofNat 697)
    ([hValue s 6, 0, UInt256.ofNat 703, kValue s j, wValue s j,
      UInt256.ofNat 0xffffffff, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def gotH5 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadReturned (gotH6 s msgOff returnDest rest j) 288
    (UInt256.ofNat 5) (UInt256.ofNat 697)
    ([hValue s 6, 0, UInt256.ofNat 703, kValue s j, wValue s j,
      UInt256.ofNat 0xffffffff, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def callCh (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Functions.ternaryEntry (gotH5 s msgOff returnDest rest j) 212
    (hValue s 4) (hValue s 5) (hValue s 6) 0 (UInt256.ofNat 703)
    ([kValue s j, wValue s j, UInt256.ofNat 0xffffffff, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)

def gotCh (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Functions.unaryReturned (gotH5 s msgOff returnDest rest j)
    (Word.evmCh (hValue s 4) (hValue s 5) (hValue s 6))
    (UInt256.ofNat 703)
    ([kValue s j, wValue s j, UInt256.ofNat 0xffffffff, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)

def chPlusK (s : State) (j : Nat) : UInt256 :=
  Word.evmCh (hValue s 4) (hValue s 5) (hValue s 6) + kValue s j

def callBigSigma1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  BigSigma.t1Entry (gotCh s msgOff returnDest rest j)
    (hValue s 4) (hValue s 5) (hValue s 6) (kValue s j) (wValue s j)
    ([hValue s 4, UInt256.ofNat j, msgOff, returnDest] ++ rest)

def gotFusedT1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  BigSigma.t1Returned (gotCh s msgOff returnDest rest j)
    (hValue s 4) (hValue s 5) (hValue s 6) (kValue s j) (wValue s j)
    ([hValue s 4, UInt256.ofNat j, msgOff, returnDest] ++ rest)

def gotBigSigma1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Functions.unaryReturned (gotCh s msgOff returnDest rest j)
    (Word.evmBigSigma1 (hValue s 4)) (UInt256.ofNat 714)
    ([chPlusK s j, wValue s j, UInt256.ofNat 0xffffffff, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)

def callH7 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadEntry (gotBigSigma1 s msgOff returnDest rest j) 318
    (UInt256.ofNat 7) 0 (UInt256.ofNat 725)
    ([Word.evmBigSigma1 (hValue s 4), chPlusK s j, wValue s j,
      UInt256.ofNat 0xffffffff, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def gotH7 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadReturned (gotBigSigma1 s msgOff returnDest rest j) 288
    (UInt256.ofNat 7) (UInt256.ofNat 725)
    ([Word.evmBigSigma1 (hValue s 4), chPlusK s j, wValue s j,
      UInt256.ofNat 0xffffffff, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def t1 (s : State) (j : Nat) : UInt256 :=
  Challenge.EvmProof.Word.mask32
    (hValue s 7 +
      (((Word.evmBigSigma1 (hValue s 4) +
        Word.evmCh (hValue s 4) (hValue s 5) (hValue s 6)) +
        kValue s j) + wValue s j))

def loadedT1Inputs (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q0 := gotK s msgOff returnDest rest j
  let q1 := { q0 with activeWords := q0.activeWordsAfterUInt256 480 32 }
  { q1 with activeWords := q1.activeWordsAfterUInt256 448 32 }

def callIntegratedT1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  BigSigma.t1Entry (loadedT1Inputs s msgOff returnDest rest j)
    (hValue s 4) (hValue s 5) (hValue s 6) (kValue s j) (wValue s j)
    ([hValue s 4, UInt256.ofNat j, msgOff, returnDest] ++ rest)

def gotIntegratedT1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  BigSigma.t1Returned (loadedT1Inputs s msgOff returnDest rest j)
    (hValue s 4) (hValue s 5) (hValue s 6) (kValue s j) (wValue s j)
    ([hValue s 4, UInt256.ofNat j, msgOff, returnDest] ++ rest)

def afterT1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  gotIntegratedT1 s msgOff returnDest rest j

def loadedA (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { afterT1 s msgOff returnDest rest j with
    activeWords := (afterT1 s msgOff returnDest rest j).activeWordsAfterUInt256
      288 32 }

def callT2H2 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadEntry (loadedA s msgOff returnDest rest j) 318
    (UInt256.ofNat 2) 0 (UInt256.ofNat 753)
    ([0, UInt256.ofNat 770, UInt256.ofNat 0xffffffff, hValue s 0,
      t1 s j, hValue s 4, UInt256.ofNat j, msgOff, returnDest] ++ rest)

def gotT2H2 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadReturned (loadedA s msgOff returnDest rest j) 288
    (UInt256.ofNat 2) (UInt256.ofNat 732)
    ([0, UInt256.ofNat 770, UInt256.ofNat 0xffffffff, hValue s 0,
      t1 s j, hValue s 4, UInt256.ofNat j, msgOff, returnDest] ++ rest)

def callT2H1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadEntry (gotT2H2 s msgOff returnDest rest j) 318
    (UInt256.ofNat 1) 0 (UInt256.ofNat 764)
    ([hValue s 2, 0, UInt256.ofNat 770, UInt256.ofNat 0xffffffff,
      hValue s 0, t1 s j, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def gotT2H1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.loadReturned (gotT2H2 s msgOff returnDest rest j) 288
    (UInt256.ofNat 1) (UInt256.ofNat 736)
    ([hValue s 2, 0, UInt256.ofNat 770, UInt256.ofNat 0xffffffff,
      hValue s 0, t1 s j, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def callMaj (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Functions.ternaryEntry (gotT2H1 s msgOff returnDest rest j) 233
    (hValue s 0) (hValue s 1) (hValue s 2) 0 (UInt256.ofNat 770)
    ([UInt256.ofNat 0xffffffff, hValue s 0, t1 s j, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)

def gotMaj (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Functions.unaryReturned (gotT2H1 s msgOff returnDest rest j)
    (Word.evmMaj (hValue s 0) (hValue s 1) (hValue s 2))
    (UInt256.ofNat 770)
    ([UInt256.ofNat 0xffffffff, hValue s 0, t1 s j, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)

def callBigSigma0 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  BigSigma.t2Entry (gotMaj s msgOff returnDest rest j)
    (hValue s 0) (hValue s 1) (hValue s 2)
    ([hValue s 0, t1 s j, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)

def gotBigSigma0 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Functions.unaryReturned (gotMaj s msgOff returnDest rest j)
    (Word.evmBigSigma0 (hValue s 0)) (UInt256.ofNat 780)
    ([Word.evmMaj (hValue s 0) (hValue s 1) (hValue s 2),
      UInt256.ofNat 0xffffffff, hValue s 0, t1 s j, hValue s 4,
      UInt256.ofNat j, msgOff, returnDest] ++ rest)

def t2 (s : State) : UInt256 :=
  Challenge.EvmProof.Word.mask32
    (Word.evmBigSigma0 (hValue s 0) +
      Word.evmMaj (hValue s 0) (hValue s 1) (hValue s 2))

def loadedT2Inputs (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q0 := afterT1 s msgOff returnDest rest j
  let q1 := { q0 with activeWords := q0.activeWordsAfterUInt256 288 32 }
  let q2 := { q1 with activeWords := q1.activeWordsAfterUInt256 352 32 }
  { q2 with activeWords := q2.activeWordsAfterUInt256 320 32 }

def callIntegratedT2 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  BigSigma.t2Entry (loadedT2Inputs s msgOff returnDest rest j)
    (hValue s 0) (hValue s 1) (hValue s 2)
    ([hValue s 0, t1 s j, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def afterT2 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  BigSigma.t2Returned (loadedT2Inputs s msgOff returnDest rest j)
    (hValue s 0) (hValue s 1) (hValue s 2)
    ([hValue s 0, t1 s j, hValue s 4, UInt256.ofNat j,
      msgOff, returnDest] ++ rest)

def roundContext (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : List UInt256 :=
  [t2 s, hValue s 0, t1 s j, hValue s 4,
    UInt256.ofNat j, msgOff, returnDest] ++ rest

def shiftLoadEntry (q : State) (src loadReturn storeReturn : Nat)
    (context : List UInt256) : State :=
  Accessors.loadEntry q 318 (UInt256.ofNat src) 0
    (UInt256.ofNat loadReturn) (UInt256.ofNat storeReturn :: context)

def shiftLoaded (q : State) (src loadReturn storeReturn : Nat)
    (context : List UInt256) : State :=
  Accessors.loadReturned q 288 (UInt256.ofNat src)
    (UInt256.ofNat loadReturn) (UInt256.ofNat storeReturn :: context)

def shiftStoreEntry (q : State) (src dest loadReturn storeReturn : Nat)
    (context : List UInt256) : State :=
  Accessors.storeEntry (shiftLoaded q src loadReturn storeReturn context) 338
    (UInt256.ofNat dest) (hValue q src) (UInt256.ofNat storeReturn) context

def shiftReturned (q : State) (src dest loadReturn storeReturn : Nat)
    (context : List UInt256) : State :=
  Accessors.storeReturned (shiftLoaded q src loadReturn storeReturn context)
    288 (UInt256.ofNat dest) (hValue q src) (UInt256.ofNat storeReturn) context

def afterShift7 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  shiftReturned (afterT2 s msgOff returnDest rest j) 6 7 796 803
    (roundContext s msgOff returnDest rest j)

def afterShift6 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  shiftReturned (afterShift7 s msgOff returnDest rest j) 5 6 817 824
    (roundContext s msgOff returnDest rest j)

def directStored (q : State) (offset : Nat) (value : UInt256)
    (nextPC : Nat) (context : List UInt256) : State :=
  { q with
    pc := UInt256.ofNat nextPC
    stack := context
    memory := MachineState.writeBytes q.memory
      (Data.Bytes.natToBytesPadded value.toNat 32) offset
    activeWords := q.activeWordsAfterUInt256 offset 32 }

def afterStoreE (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  directStored (afterShift6 s msgOff returnDest rest j) 448 (hValue s 4) 830
    (roundContext s msgOff returnDest rest j)

def h4LoadEntry (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q := afterStoreE s msgOff returnDest rest j
  Accessors.loadEntry q 318 (UInt256.ofNat 3) 0 (UInt256.ofNat 849)
    ([t1 s j, UInt256.ofNat 0xffffffff, UInt256.ofNat 858] ++
      roundContext s msgOff returnDest rest j)

def h4Loaded (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q := afterStoreE s msgOff returnDest rest j
  Accessors.loadReturned q 288 (UInt256.ofNat 3) (UInt256.ofNat 849)
    ([t1 s j, UInt256.ofNat 0xffffffff, UInt256.ofNat 858] ++
      roundContext s msgOff returnDest rest j)

def newH4 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : UInt256 :=
  let q := afterStoreE s msgOff returnDest rest j
  Challenge.EvmProof.Word.mask32 (hValue q 3 + t1 s j)

def h4StoreEntry (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.storeEntry (h4Loaded s msgOff returnDest rest j) 338
    (UInt256.ofNat 4) (newH4 s msgOff returnDest rest j)
    (UInt256.ofNat 858) (roundContext s msgOff returnDest rest j)

def afterStoreH4 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  Accessors.storeReturned (h4Loaded s msgOff returnDest rest j) 288
    (UInt256.ofNat 4) (newH4 s msgOff returnDest rest j)
    (UInt256.ofNat 858) (roundContext s msgOff returnDest rest j)

def afterShift3 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  shiftReturned (afterStoreH4 s msgOff returnDest rest j) 2 3 872 879
    (roundContext s msgOff returnDest rest j)

def afterShift2 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  shiftReturned (afterShift3 s msgOff returnDest rest j) 1 2 893 900
    (roundContext s msgOff returnDest rest j)

def afterStoreH1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q := afterShift2 s msgOff returnDest rest j
  directStored q 320 (hValue s 0) 906 (roundContext s msgOff returnDest rest j)

def afterSecondIteration (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let q := afterStoreH1 s msgOff returnDest rest j
  { q with
    pc := UInt256.ofNat 633
    stack := [UInt256.ofNat (j + 1), msgOff, returnDest] ++ rest
    memory := MachineState.writeBytes q.memory
      (Data.Bytes.natToBytesPadded
        (Challenge.EvmProof.Word.mask32 (t1 s j + t2 s)).toNat 32) 288
    activeWords := q.activeWordsAfterUInt256 288 32 }

def foldAt (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 938
    stack := [UInt256.ofNat i, msgOff, returnDest] ++ rest }

def afterFoldCondition (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 948
    stack := [UInt256.ofNat i, msgOff, returnDest] ++ rest }

def savedOffset (i : Nat) : Nat :=
  (UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) +
    UInt256.ofNat 544).toNat

def savedValue (s : State) (i : Nat) : UInt256 :=
  MachineState.readWord s.memory (savedOffset i)

def loadedSaved (s : State) (i : Nat) : State :=
  { s with activeWords := s.activeWordsAfterUInt256 (savedOffset i) 32 }

def foldCallH (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  Accessors.loadEntry (loadedSaved s i) 318 (UInt256.ofNat i) 0
    (UInt256.ofNat 974)
    ([savedValue s i, UInt256.ofNat 0xffffffff, UInt256.ofNat 982,
      UInt256.ofNat i, msgOff, returnDest] ++ rest)

def foldGotH (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  Accessors.loadReturned (loadedSaved s i) 288 (UInt256.ofNat i)
    (UInt256.ofNat 974)
    ([savedValue s i, UInt256.ofNat 0xffffffff, UInt256.ofNat 982,
      UInt256.ofNat i, msgOff, returnDest] ++ rest)

def foldedValue (s : State) (_msgOff _returnDest : UInt256)
    (_rest : List UInt256) (i : Nat) : UInt256 :=
  let q := loadedSaved s i
  Challenge.EvmProof.Word.mask32
    (hValue q i + savedValue s i)

def foldCallSet (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  Accessors.storeEntry (foldGotH s msgOff returnDest rest i) 338
    (UInt256.ofNat i) (foldedValue s msgOff returnDest rest i)
    (UInt256.ofNat 982) ([UInt256.ofNat i, msgOff, returnDest] ++ rest)

def foldGotSet (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  Accessors.storeReturned (foldGotH s msgOff returnDest rest i) 288
    (UInt256.ofNat i) (foldedValue s msgOff returnDest rest i)
    (UInt256.ofNat 981) ([UInt256.ofNat i, msgOff, returnDest] ++ rest)

def afterFoldIteration (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { foldGotSet s msgOff returnDest rest i with
    pc := UInt256.ofNat 938
    stack := [UInt256.ofNat (i + 1), msgOff, returnDest] ++ rest }

def compressReturned (s : State) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := returnDest, stack := rest }

@[simp] private theorem entryPC (i : Nat) (hlo : 506 ≤ i) (hhi : i ≤ 523) :
    Artifact.referenceArtifact.instructionPC i =
      [612, 613, 616, 617, 620, 621, 622, 625, 628, 631, 632, 633,
       634, 635, 637, 638, 639, 642][i - 506]! := by
  interval_cases i <;> decide

@[simp] private theorem t1PC (i : Nat) (hlo : 524 ≤ i) (hhi : i ≤ 547) :
    Artifact.referenceArtifact.instructionPC i =
      [643, 646, 647, 652, 653, 655, 656, 659, 660, 661,
       662, 664, 665, 667, 668, 669, 670, 671, 684, 685,
       697, 698, 699, 702][i - 524]! := by
  interval_cases i <;> decide

@[simp] private theorem t2PC (i : Nat) (hlo : 574 ≤ i) (hhi : i ≤ 584) :
    Artifact.referenceArtifact.instructionPC i =
      [729, 730, 733, 734, 739, 752, 753, 764, 765, 766,
       769][i - 574]! := by
  interval_cases i <;> decide

@[simp] private theorem updatePC (i : Nat) (hlo : 598 ≤ i) (hhi : i ≤ 645) :
    Artifact.referenceArtifact.instructionPC i =
      [783, 784, 795, 796, 802, 803, 816, 817, 823, 824,
       825, 829, 830, 835, 836, 848, 849, 850, 851, 857,
       858, 871, 872, 878, 879, 892, 893, 899, 900, 901,
       905, 906, 911, 912, 913, 914, 915, 916, 919, 920,
       921, 922, 923, 924, 925, 927, 928, 934][i - 598]! := by
  interval_cases i <;> decide

@[simp] private theorem foldPC (i : Nat) (hlo : 646 ≤ i) (hhi : i ≤ 681) :
    Artifact.referenceArtifact.instructionPC i =
      [935, 936, 937, 938, 939, 940, 942, 943, 944, 947,
       948, 949, 953, 954, 955, 959, 960, 961, 962, 966,
       967, 968, 969, 974, 975, 976, 979, 980, 981, 983,
       984, 992, 993, 994, 995, 996][i - 646]! := by
  interval_cases i <;> decide

set_option linter.unusedSimpArgs false in
theorem run_entry (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1019)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock entryPath
      (compressEntry s msgOff returnDest rest) =
        some (callSchedule s msgOff returnDest rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hdest : Decode.isValidJumpDest submissionBytecode 446 = true := by decide
  simp [entryPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    compressEntry, callSchedule, Schedule.scheduleEntry, List.exchange,
    hc2, hc3, hc4, hc5, hcode, hrun, hdest]

set_option linter.unusedSimpArgs false in
theorem run_copyAndLoopStart (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1019)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock copyAndLoopStartPath
      { s with pc := UInt256.ofNat 621
               stack := [msgOff, returnDest] ++ rest } =
        some (roundAt (copyHashState s) msgOff returnDest rest 0) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [copyAndLoopStartPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    copyHashState, roundAt, hc2, hc3, hc4, hc5, hrun,
    State.activeWordsAfterUInt256_2]

set_option linter.unusedSimpArgs false in
theorem run_condition (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 64)
    (hcap : rest.length < 1019) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock conditionPath
      (roundAt s msgOff returnDest rest j) =
        some (afterCondition s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hjWord : (UInt256.ofNat j).toNat = j := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have heq : UInt256.eq (UInt256.ofNat 64) (UInt256.ofNat j) = 0 := by
    simp [UInt256.eq, hjWord, Challenge.EvmProof.Word.word_toNat_ofNat]
    omega
  have htrue : UInt256.isTrue (0 : UInt256) = false := by decide
  simp [conditionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    roundAt, afterCondition, hc3, hc4, hc5, hrun, heq, htrue]

set_option linter.unusedSimpArgs false in
theorem run_setupW (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1015)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupWPath
      (afterCondition s msgOff returnDest rest j) =
        some (gotW s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hoff4 :
      ((UInt256.ofNat 4).shiftLeft (UInt256.ofNat 5) +
        UInt256.ofNat 288).toNat = 416 := by decide
  have haddr :
      UInt256.ofNat 800 +
        (UInt256.ofNat j).shiftLeft (UInt256.ofNat 5) =
      (UInt256.ofNat j).shiftLeft (UInt256.ofNat 5) +
        UInt256.ofNat 800 :=
    Challenge.EvmProof.Word.word_add_comm _ _
  simp [setupWPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterCondition, gotW, loadedE, hValue, Accessors.slotOffset,
    Accessors.loadReturned, List.exchange, hc3, hc4, hc5, hc6, hc7, hc8,
    hc9, hoff4, haddr, hrun, State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_setupK (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 64)
    (hcap : rest.length < 1014)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupKPath
      (gotW s msgOff returnDest rest j) =
        some (gotK s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hshift :
      (UInt256.ofNat j).shiftLeft (UInt256.ofNat 2) =
        UInt256.ofNat (j * 4) := by
    simpa using Challenge.EvmProof.Word.shiftLeft_ofNat
      (value := j) (shift := 2) (by omega) (by decide) (by omega)
  have hdirect :
      (UInt256.ofNat 4 + (UInt256.ofNat j).shiftLeft
        (UInt256.ofNat 2)).toNat = 4 + j * 4 := by
    rw [hshift, Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hkoff :
      ((UInt256.ofNat j).shiftLeft (UInt256.ofNat 2) +
        UInt256.ofNat 32).toNat = 32 + j * 4 := by
    rw [hshift, Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hmask :
      Challenge.EvmProof.Word.mask32
          (MachineState.readWord s.memory (4 + j * 4)) = kValue s j := by
    unfold kValue
    rw [hkoff, PaddedBlockBridge.shiftRight_readWord_224,
      PaddedBlockBridge.mask32_readWord_last4]
    have hoff : 4 + j * 4 + 28 = 32 + j * 4 := by omega
    rw [hoff]
  have hand (a b : UInt256) : a &&& b = b &&& a := by
    apply Challenge.EvmProof.Word.word_ext
    change (a.val &&& b.val).val = (b.val &&& a.val).val
    rw [Fin.and_val, Fin.and_val, Nat.and_comm]
  have hmask' :
      UInt256.ofNat 0xffffffff &&&
          MachineState.readWord s.memory (4 + j * 4) = kValue s j := by
    rw [hand]
    simpa [Challenge.EvmProof.Word.mask32] using hmask
  have hslotW :
      Accessors.slotOffset 800 (UInt256.ofNat j) = 800 + j * 32 := by
    unfold Accessors.slotOffset
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat
        (value := j) (shift := 5) (by omega) (by decide) (by omega)]
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hcurr : (loadedE s).activeWords.toNat < 2 ^ 256 := by
    change (loadedE s).activeWords.val.val < UInt256.size
    exact (loadedE s).activeWords.val.isLt
  have hnext : MachineState.activeWordsAfter
      (loadedE s).activeWords.toNat (800 + j * 32) 32 < 2 ^ 256 := by
    apply activeWordsAfter_lt
    · exact hcurr
    · omega
  have hgotW : 10 ≤ (gotW s msgOff returnDest rest j).activeWords.toNat := by
    simp only [gotW, Accessors.loadReturned]
    rw [State.activeWordsAfterUInt256, hslotW,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hnext]
    apply activeWordsAfter_ge_ten
    omega
  have hactiveD : MachineState.activeWordsAfter
      (gotW s msgOff returnDest rest j).activeWords.toNat
      (4 + j * 4) 32 = (gotW s msgOff returnDest rest j).activeWords.toNat :=
    activeWordsAfter_small _ _ hgotW (by omega)
  have hactiveK : MachineState.activeWordsAfter
      (gotW s msgOff returnDest rest j).activeWords.toNat
      (32 + j * 4) 32 = (gotW s msgOff returnDest rest j).activeWords.toNat :=
    activeWordsAfter_small _ _ hgotW (by omega)
  have hactiveEq :
      (gotW s msgOff returnDest rest j).activeWordsAfterUInt256
          (4 + j * 4) 32 =
        (gotW s msgOff returnDest rest j).activeWordsAfterUInt256
          (32 + j * 4) 32 := by
    unfold State.activeWordsAfterUInt256
    rw [hactiveD, hactiveK]
  simp_all [setupKPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotW, gotK, wValue, hValue, kValue, loadedE,
    Accessors.loadReturned, Accessors.kAtReturned, Accessors.slotOffset,
    Challenge.EvmProof.Word.mask32, List.exchange, hc3, hc4, hc5, hc6,
    hc7, hc8, hc9, hc10, hshift, hdirect, hkoff, hmask', hrun,
    hactiveD, hactiveK, hactiveEq]
  constructor
  · exact hactiveEq
  · exact (hand _ _).trans hmask

/- Superseded execution lemmas for the standalone Ch/Maj pipeline. -/
/-
set_option linter.unusedSimpArgs false in
theorem run_setupH6 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1010)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupH6Path
      (gotK s msgOff returnDest rest j) =
        some (gotH6 s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hslot :
      ((UInt256.ofNat 6).shiftLeft (UInt256.ofNat 5) +
        UInt256.ofNat 288).toNat = 480 := by decide
  simp [setupH6Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotK, gotH6, gotW, loadedE, kValue, wValue, hValue,
    Accessors.kAtReturned, Accessors.loadReturned, Accessors.loadEntry,
    Accessors.slotOffset, List.exchange, hc3, hc4, hc5, hc6, hc7, hc8,
    hc9, hc10, hc11, hc12, hc13, hslot, hrun,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_setupH5 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1009)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupH5Path
      (gotH6 s msgOff returnDest rest j) =
        some (gotH5 s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hslot :
      ((UInt256.ofNat 5).shiftLeft (UInt256.ofNat 5) +
        UInt256.ofNat 288).toNat = 448 := by decide
  simp [setupH5Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotH6, gotH5, gotK, gotW, loadedE, kValue, wValue, hValue,
    Accessors.loadReturned, Accessors.kAtReturned, Accessors.loadEntry,
    Accessors.slotOffset, List.exchange, hc3, hc4, hc5, hc6, hc7, hc8,
    hc9, hc10, hc11, hc12, hc13, hc14, hslot, hrun,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_setupCh (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1008)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupChPath
      (gotH5 s msgOff returnDest rest j) =
        some (callCh s msgOff returnDest rest j) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hdest : Decode.isValidJumpDest submissionBytecode 212 = true := by decide
  simp [setupChPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotH5, callCh, gotH6, gotK, gotW, loadedE, kValue, wValue, hValue,
    Functions.ternaryEntry, Accessors.loadReturned, Accessors.kAtReturned,
    Accessors.slotOffset, List.exchange, hc10, hc11, hc12, hc13, hc14,
    hc15, hcode, hrun, hdest]

set_option linter.unusedSimpArgs false in
theorem run_setupBigSigma1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1009)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupBigSigma1Path
      (gotCh s msgOff returnDest rest j) =
        some (callBigSigma1 s msgOff returnDest rest j) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hdest : Decode.isValidJumpDest submissionBytecode 163 = true := by decide
  simp [setupBigSigma1Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotCh, callBigSigma1, gotH5, gotH6, gotK, gotW, loadedE,
    chPlusK, kValue, wValue, hValue, Functions.unaryReturned,
    BigSigma.t1Entry, Accessors.loadReturned, Accessors.kAtReturned,
    Accessors.slotOffset, List.exchange, hc7, hc8, hc9, hc10, hc11, hc12,
    hc13, hc14, hcode, hrun, hdest]

set_option linter.unusedSimpArgs false in
theorem run_finishT1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1011)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock finishT1Path
      (gotFusedT1 s msgOff returnDest rest j) =
        some (afterT1 s msgOff returnDest rest j) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hslot :
      ((UInt256.ofNat 7).shiftLeft (UInt256.ofNat 5) +
        UInt256.ofNat 288).toNat = 512 := by decide
  simp [finishT1Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotFusedT1, gotH7, afterT1, gotBigSigma1, gotCh, gotH5, gotH6, gotK, gotW,
    loadedE, t1, chPlusK, kValue, wValue, hValue,
    BigSigma.t1Returned, Challenge.EvmProof.Word.mask32, Functions.unaryReturned,
    Accessors.loadReturned, Accessors.kAtReturned, Accessors.slotOffset,
    List.exchange, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hslot, hrun,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_setupT2H2 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1007)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupT2H2Path
      (afterT1 s msgOff returnDest rest j) =
        some (gotT2H2 s msgOff returnDest rest j) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hoff0 : Accessors.slotOffset 288 (UInt256.ofNat 0) = 288 := by decide
  have haddr0 :
      (UInt256.shiftLeft 0 (UInt256.ofNat 5) + UInt256.ofNat 288).toNat =
        288 := by decide
  have haddr2 :
      ((UInt256.ofNat 2).shiftLeft (UInt256.ofNat 5) +
        UInt256.ofNat 288).toNat = 352 := by decide
  simp [setupT2H2Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterT1, loadedA, gotT2H2, gotH7, gotBigSigma1, gotCh, gotH5,
    gotH6, gotK, gotW, loadedE, hValue, Accessors.slotOffset,
    Functions.unaryReturned, Accessors.loadReturned, Accessors.kAtReturned,
    List.exchange, hc5, hc6, hc7, hc8, hc9, hc10, hc11,
    hc12, hc13, hc14, hc15, hc16, hoff0, haddr0, haddr2, hrun,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_setupT2H1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1007)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupT2H1Path
      (gotT2H2 s msgOff returnDest rest j) =
        some (gotT2H1 s msgOff returnDest rest j) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have haddr1 :
      ((UInt256.ofNat 1).shiftLeft (UInt256.ofNat 5) +
        UInt256.ofNat 288).toNat = 320 := by decide
  simp [setupT2H1Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotT2H2, gotT2H1, loadedA, afterT1, gotH7, gotBigSigma1, gotCh,
    gotH5, gotH6, gotK, gotW, loadedE, hValue, Functions.unaryReturned,
    Accessors.loadReturned, Accessors.kAtReturned,
    Accessors.slotOffset, List.exchange, hc10, hc11, hc12, hc13, hc14,
    hc15, hc16, haddr1, hrun, State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_setupMaj (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1006)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupMajPath
      (gotT2H1 s msgOff returnDest rest j) =
        some (callMaj s msgOff returnDest rest j) := by
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hdest : Decode.isValidJumpDest submissionBytecode 233 = true := by decide
  simp [setupMajPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotT2H1, callMaj, gotT2H2, loadedA, afterT1, gotH7,
    gotBigSigma1, gotCh, gotH5, gotH6, gotK, gotW, loadedE, hValue,
    Functions.ternaryEntry, Functions.unaryReturned, Accessors.loadReturned,
    Accessors.kAtReturned, Accessors.slotOffset, List.exchange, hc11, hc12, hc13,
    hc14, hc15, hc16, hc17, hcode, hrun, hdest]

set_option linter.unusedSimpArgs false in
theorem run_setupBigSigma0 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1008)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupBigSigma0Path
      (gotMaj s msgOff returnDest rest j) =
        some (callBigSigma0 s msgOff returnDest rest j) := by
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hdest : Decode.isValidJumpDest submissionBytecode 114 = true := by decide
  simp [setupBigSigma0Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotMaj, callBigSigma0, gotT2H1, gotT2H2, loadedA, afterT1, gotH7,
    gotBigSigma1, gotCh, gotH5, gotH6, gotK, gotW, loadedE, hValue,
    Functions.ternaryEntry, BigSigma.t2Entry, Functions.unaryReturned,
    Accessors.loadReturned, Accessors.kAtReturned, Accessors.slotOffset,
    List.exchange, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hcode, hrun, hdest]

set_option linter.unusedSimpArgs false in
theorem run_finishT2 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1010)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock finishT2Path
      (gotBigSigma0 s msgOff returnDest rest j) =
        some (afterT2 s msgOff returnDest rest j) := by
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  simp [finishT2Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    gotBigSigma0, afterT2, gotMaj, gotT2H1, gotT2H2, loadedA, afterT1,
    gotH7, gotBigSigma1, gotCh, gotH5, gotH6, gotK, gotW, loadedE,
    t2, hValue, Challenge.EvmProof.Word.mask32, Functions.unaryReturned,
    Accessors.loadReturned, Accessors.kAtReturned, Accessors.slotOffset,
    List.exchange, hc8, hc9, hc10, hc11, hc12, hc13, hrun]
  rfl
-/

set_option linter.unusedSimpArgs false in
theorem run_setupT1 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1013)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupT1Path
      (gotK s msgOff returnDest rest j) =
        some (callIntegratedT1 s msgOff returnDest rest j) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hdest : Decode.isValidJumpDest submissionBytecode 163 = true := by decide
  have haddr5 :
      ((UInt256.ofNat 5).shiftLeft (UInt256.ofNat 5) +
        UInt256.ofNat 288).toNat = 448 := by decide
  have haddr6 :
      ((UInt256.ofNat 6).shiftLeft (UInt256.ofNat 5) +
        UInt256.ofNat 288).toNat = 480 := by decide
  simp [setupT1Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    callIntegratedT1, loadedT1Inputs, gotK, gotW, loadedE, hValue, kValue,
    wValue, BigSigma.t1Entry, Accessors.loadReturned, Accessors.kAtReturned,
    Accessors.slotOffset, List.exchange, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
    hc8, hc9, hc10, hc11, hcode, hrun, hdest, haddr5, haddr6,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_setupT2 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1013)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupT2Path
      (afterT1 s msgOff returnDest rest j) =
        some (callIntegratedT2 s msgOff returnDest rest j) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hdest : Decode.isValidJumpDest submissionBytecode 114 = true := by decide
  have haddr0 :
      (UInt256.shiftLeft 0 (UInt256.ofNat 5) +
        UInt256.ofNat 288).toNat = 288 := by decide
  have haddr1 :
      ((UInt256.ofNat 1).shiftLeft (UInt256.ofNat 5) +
        UInt256.ofNat 288).toNat = 320 := by decide
  have haddr2 :
      ((UInt256.ofNat 2).shiftLeft (UInt256.ofNat 5) +
        UInt256.ofNat 288).toNat = 352 := by decide
  have haddr7 :
      ((UInt256.ofNat 7).shiftLeft (UInt256.ofNat 5) +
        UInt256.ofNat 288).toNat = 512 := by decide
  simp [setupT2Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    callIntegratedT2, loadedT2Inputs, afterT1, gotIntegratedT1,
    loadedT1Inputs, gotK, gotW, loadedE, t1, t2, hValue, kValue, wValue,
    BigSigma.t1Returned, BigSigma.t2Entry, Accessors.loadReturned,
    Accessors.kAtReturned, Accessors.slotOffset, List.exchange, hc1, hc2, hc3,
    hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hcode, hrun, hdest,
    haddr0, haddr1, haddr2, haddr7,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_shiftDirect (path : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    (q : State) (src dest loadReturn storeReturn startPC : Nat)
    (context : List UInt256)
    (hmatch :
      (path = shift76Path ∧ src = 6 ∧ dest = 7 ∧ loadReturn = 796 ∧
        storeReturn = 803 ∧ startPC = 783) ∨
      (path = shift65Path ∧ src = 5 ∧ dest = 6 ∧ loadReturn = 817 ∧
        storeReturn = 824 ∧ startPC = 803) ∨
      (path = shift32Path ∧ src = 2 ∧ dest = 3 ∧ loadReturn = 872 ∧
        storeReturn = 879 ∧ startPC = 858) ∨
      (path = shift21Path ∧ src = 1 ∧ dest = 2 ∧ loadReturn = 893 ∧
        storeReturn = 900 ∧ startPC = 879))
    (hpc : q.pc = UInt256.ofNat startPC) (hstack : q.stack = context)
    (hcap : context.length < 1016)
    (hrun : q.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path q =
      some (shiftReturned q src dest loadReturn storeReturn context) := by
  have hc0 : context.length < 1024 := by omega
  have hc1 : context.length + 1 < 1024 := by omega
  have hc2 : context.length + 2 < 1024 := by omega
  have haddr6 :
      ((UInt256.ofNat 6).shiftLeft (UInt256.ofNat 5) +
        UInt256.ofNat 288).toNat = 480 := by decide
  have haddr5 :
      ((UInt256.ofNat 5).shiftLeft (UInt256.ofNat 5) +
        UInt256.ofNat 288).toNat = 448 := by decide
  have haddr2 :
      ((UInt256.ofNat 2).shiftLeft (UInt256.ofNat 5) +
        UInt256.ofNat 288).toNat = 352 := by decide
  have haddr1 :
      ((UInt256.ofNat 1).shiftLeft (UInt256.ofNat 5) +
        UInt256.ofNat 288).toNat = 320 := by decide
  have haddr7 :
      ((UInt256.ofNat 7).shiftLeft (UInt256.ofNat 5) +
        UInt256.ofNat 288).toNat = 512 := by decide
  have haddr3 :
      ((UInt256.ofNat 3).shiftLeft (UInt256.ofNat 5) +
        UInt256.ofNat 288).toNat = 384 := by decide
  rcases hmatch with h | h | h | h <;>
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals simp [shift76Path, shift65Path, shift32Path, shift21Path,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    shiftReturned, shiftLoaded, hValue, Accessors.storeReturned,
    Accessors.loadReturned, Accessors.slotOffset,
    hpc, hstack, List.exchange, hc0,
    hc1, hc2, haddr7, haddr6, haddr5, haddr3, haddr2, haddr1, hrun,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_storeE (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1013)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock storeEPath
      (afterShift6 s msgOff returnDest rest j) =
        some (afterStoreE s msgOff returnDest rest j) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have qT1run : (afterT1 s msgOff returnDest rest j).halt = .Running := by
    simpa [afterT1, gotIntegratedT1, BigSigma.t1Returned, loadedT1Inputs,
      gotK, gotW, loadedE, Accessors.loadReturned, Accessors.kAtReturned]
      using hrun
  simp [storeEPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterShift6, afterShift7, shiftReturned, shiftLoaded, afterT2,
    loadedT2Inputs, BigSigma.t2Returned, roundContext, afterStoreE,
    directStored, List.exchange,
    Accessors.storeReturned, Accessors.loadReturned,
    hc7, hc8, hc9, hc10, hrun, qT1run, State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_updateH4 (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hcap : rest.length < 1009)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupH3ForH4Path
      (afterStoreE s msgOff returnDest rest j) =
        some (afterStoreH4 s msgOff returnDest rest j) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have qrun : (afterShift6 s msgOff returnDest rest j).halt = .Running := by
    change s.halt = .Running
    exact hrun
  have haddr3 :
      ((UInt256.ofNat 3).shiftLeft (UInt256.ofNat 5) +
        UInt256.ofNat 288).toNat = 384 := by decide
  have haddr4 :
      ((UInt256.ofNat 4).shiftLeft (UInt256.ofNat 5) +
        UInt256.ofNat 288).toNat = 416 := by decide
  simp [setupH3ForH4Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterStoreH4, h4Loaded, newH4, hValue, afterStoreE, directStored,
    roundContext, Challenge.EvmProof.Word.mask32, Accessors.storeReturned,
    Accessors.loadReturned, Accessors.slotOffset,
    List.exchange, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14,
    haddr3, haddr4, hrun, qrun, State.activeWordsAfterUInt256]
  rfl

set_option linter.unusedSimpArgs false in
theorem run_finishRound (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 64)
    (hcap : rest.length < 1012)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock finishRoundPath
      (afterShift2 s msgOff returnDest rest j) =
        some (afterSecondIteration s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hadd : UInt256.ofNat 1 + UInt256.ofNat j =
      UInt256.ofNat (j + 1) := by
    rw [add_comm]
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hdest : Decode.isValidJumpDest submissionBytecode 633 = true := by decide
  have qrun : (afterStoreE s msgOff returnDest rest j).halt = .Running := by
    change s.halt = .Running
    exact hrun
  have qcode :
      (afterStoreE s msgOff returnDest rest j).executionEnv.code =
        submissionBytecode := by
    change s.executionEnv.code = submissionBytecode
    exact hcode
  simp [finishRoundPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterShift2, afterShift3, shiftReturned, shiftLoaded, afterStoreH4,
    h4Loaded, afterStoreH1, directStored, afterSecondIteration, roundContext,
    Challenge.EvmProof.Word.mask32, Accessors.storeReturned,
    Accessors.loadReturned, List.exchange, hc3, hc4, hc5, hc6, hc7,
    hc8, hc9, hc10, hc11, hcode, hrun, qrun, qcode, hadd, hdest,
    State.activeWordsAfterUInt256]
  rfl

set_option linter.unusedSimpArgs false in
theorem run_roundsExit (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1019)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock roundsExitPath
      (roundAt s msgOff returnDest rest 64) =
        some (foldAt s msgOff returnDest rest 0) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have heq : UInt256.eq (UInt256.ofNat 64) (UInt256.ofNat 64) =
      UInt256.ofNat 1 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat 1) = true := by decide
  have hdest935 : Decode.isValidJumpDest submissionBytecode 935 = true := by decide
  simp [roundsExitPath, conditionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    roundAt, foldAt, List.exchange, hc2, hc3, hc4, hc5, hcode, hrun,
    heq, htrue, hdest935]

set_option linter.unusedSimpArgs false in
theorem run_foldCondition (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 8)
    (hcap : rest.length < 1019) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock foldConditionPath
      (foldAt s msgOff returnDest rest i) =
        some (afterFoldCondition s msgOff returnDest rest i) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hiWord : (UInt256.ofNat i).toNat = i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have heq : UInt256.eq (UInt256.ofNat 8) (UInt256.ofNat i) = 0 := by
    simp [UInt256.eq, hiWord, Challenge.EvmProof.Word.word_toNat_ofNat]
    omega
  have htrue : UInt256.isTrue (0 : UInt256) = false := by decide
  simp [foldConditionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    foldAt, afterFoldCondition, hc3, hc4, hc5, hrun, heq, htrue]

set_option linter.unusedSimpArgs false in
theorem run_foldSetup (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hcap : rest.length < 1011)
    (_hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock foldSetupPath
      (afterFoldCondition s msgOff returnDest rest i) =
        some (foldGotSet s msgOff returnDest rest i) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hoff544 : UInt256.ofNat 544 +
        UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) =
      UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) +
        UInt256.ofNat 544 := Challenge.EvmProof.Word.word_add_comm _ _
  have hoff288 : UInt256.ofNat 288 +
        UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) =
      UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) +
        UInt256.ofNat 288 := Challenge.EvmProof.Word.word_add_comm _ _
  simp [foldSetupPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterFoldCondition, foldGotSet, foldGotH, foldedValue, hValue,
    loadedSaved, savedValue, savedOffset, Accessors.loadReturned,
    Accessors.storeReturned, Accessors.slotOffset, List.exchange,
    hc3, hc4, hc5, hc6, hc7, hoff544, hoff288, hrun,
    Challenge.EvmProof.Word.mask32,
    State.activeWordsAfterUInt256]
  rw [word_land_comm (UInt256.ofNat 0xffffffff)]
  rfl

set_option linter.unusedSimpArgs false in
theorem run_foldIncrement (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 8)
    (hcap : rest.length < 1019)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock foldIncrementPath
      (foldGotSet s msgOff returnDest rest i) =
        some (afterFoldIteration s msgOff returnDest rest i) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hadd : UInt256.ofNat 1 + UInt256.ofNat i =
      UInt256.ofNat (i + 1) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hdest : Decode.isValidJumpDest submissionBytecode 938 = true := by decide
  simp [foldIncrementPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    foldGotSet, afterFoldIteration, foldGotH, loadedSaved,
    Accessors.storeReturned, Accessors.loadReturned,
    hc3, hc4, hc5, hcode, hrun, hadd, hdest]

set_option linter.unusedSimpArgs false in
theorem run_foldExit (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1019)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hreturn : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock foldExitPath
      (foldAt s msgOff returnDest rest 8) =
        some (compressReturned s returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have heq : UInt256.eq (UInt256.ofNat 8) (UInt256.ofNat 8) =
      UInt256.ofNat 1 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat 1) = true := by decide
  have hdest993 : Decode.isValidJumpDest submissionBytecode 993 = true := by decide
  simp [foldExitPath, foldConditionPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    foldAt, compressReturned, List.exchange, hc1, hc2, hc3, hc4, hc5,
    hcode, hrun, heq, htrue, hdest993, hreturn]

end Challenge.Sha256.Submission.Proofs.Bytecode.Compression
