import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskParams

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SingleCachedMaskInlineParams

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open CavityQuadGroup CachedMaskQuadGroup

def rightParams (group : Fin 5) (k : Fin 4) : Params where
  function := ⟨4 - group.val, by omega⟩
  address i := StackRoundData.rightAddress (16 * group.val + 4 * k.val + i.val)
  rotation i := StackRoundData.rightRotation (16 * group.val + 4 * k.val + i.val)
  constant := StackRoundData.rightConstant (16 * group.val)
  rotations_bounded i := StackRoundData.rightRotation_le_32
    ⟨16 * group.val + 4 * k.val + i.val, by omega⟩
  constant_zero h := by
    change 4 - group.val = 0 at h
    have hlt := group.isLt
    have heq : group = 4 := Fin.ext (by omega)
    subst group
    rfl

theorem right0_fits (s : State) (hactive : 25 ≤ s.activeWords.toNat) :
    (rightParams 0 0).Fits s := by
  intro i
  have hend : ((rightParams 0 0).address i).toNat + 32 ≤ 25 * 32 := by
    fin_cases i <;> decide
  omega

theorem right1_fits (s : State) (hactive : 25 ≤ s.activeWords.toNat) :
    (rightParams 0 1).Fits s := by
  intro i
  have hend : ((rightParams 0 1).address i).toNat + 32 ≤ 25 * 32 := by
    fin_cases i <;> decide
  omega

theorem right2_fits (s : State) (hactive : 25 ≤ s.activeWords.toNat) :
    (rightParams 0 2).Fits s := by
  intro i
  have hend : ((rightParams 0 2).address i).toNat + 32 ≤ 25 * 32 := by
    fin_cases i <;> decide
  omega

theorem right3_fits (s : State) (hactive : 25 ≤ s.activeWords.toNat) :
    (rightParams 0 3).Fits s := by
  intro i
  have hend : ((rightParams 0 3).address i).toNat + 32 ≤ 25 * 32 := by
    fin_cases i <;> decide
  omega

theorem right4_fits (s : State) (hactive : 25 ≤ s.activeWords.toNat) :
    (rightParams 1 0).Fits s := by
  intro i
  have hend : ((rightParams 1 0).address i).toNat + 32 ≤ 25 * 32 := by
    fin_cases i <;> decide
  omega

def nativeRight0Quad0 : List Instr :=
[  .push 2 212,
  Artifact.op 0x51,
  Artifact.op 0x84,
  Artifact.op 0x19,
  Artifact.op 0x84,
  Artifact.op 0x17,
  Artifact.op 0x83,
  Artifact.op 0x18,
  Artifact.op 0x01,
  Artifact.op 0x01,
  .push 4 1352829926,
  Artifact.op 0x01,
  Artifact.op 0x8b,
  Artifact.op 0x16,
  Artifact.op 0x85,
  Artifact.op 0x02,
  .push 1 24,
  Artifact.op 0x1c,
  Artifact.op 0x84,
  Artifact.op 0x01,
  Artifact.op 0x8b,
  Artifact.op 0x16,
  Artifact.op 0x91,
  Artifact.op 0x85,
  Artifact.op 0x02,
  .push 1 22,
  Artifact.op 0x1c,
  Artifact.op 0x93,
  .push 2 248,
  Artifact.op 0x51,
  Artifact.op 0x85,
  Artifact.op 0x19,
  Artifact.op 0x83,
  Artifact.op 0x17,
  Artifact.op 0x84,
  Artifact.op 0x18,
  Artifact.op 0x01,
  Artifact.op 0x01,
  .push 4 1352829926,
  Artifact.op 0x01,
  Artifact.op 0x8b,
  Artifact.op 0x16,
  Artifact.op 0x85,
  Artifact.op 0x02,
  .push 1 23,
  Artifact.op 0x1c,
  Artifact.op 0x83,
  Artifact.op 0x01,
  Artifact.op 0x8b,
  Artifact.op 0x16,
  Artifact.op 0x90,
  Artifact.op 0x85,
  Artifact.op 0x02,
  .push 1 22,
  Artifact.op 0x1c,
  Artifact.op 0x92,
  .push 2 220,
  Artifact.op 0x51,
  Artifact.op 0x84,
  Artifact.op 0x19,
  Artifact.op 0x84,
  Artifact.op 0x17,
  Artifact.op 0x83,
  Artifact.op 0x18,
  Artifact.op 0x01,
  Artifact.op 0x01,
  .push 4 1352829926,
  Artifact.op 0x01,
  Artifact.op 0x8b,
  Artifact.op 0x16,
  Artifact.op 0x85,
  Artifact.op 0x02,
  .push 1 23,
  Artifact.op 0x1c,
  Artifact.op 0x84,
  Artifact.op 0x01,
  Artifact.op 0x8b,
  Artifact.op 0x16,
  Artifact.op 0x91,
  Artifact.op 0x85,
  Artifact.op 0x02,
  .push 1 22,
  Artifact.op 0x1c,
  Artifact.op 0x93,
  .push 2 192,
  Artifact.op 0x51,
  Artifact.op 0x85,
  Artifact.op 0x19,
  Artifact.op 0x83,
  Artifact.op 0x17,
  Artifact.op 0x84,
  Artifact.op 0x18,
  Artifact.op 0x01,
  Artifact.op 0x01,
  .push 4 1352829926,
  Artifact.op 0x01,
  Artifact.op 0x8b,
  Artifact.op 0x16,
  Artifact.op 0x85,
  Artifact.op 0x02,
  .push 1 21,
  Artifact.op 0x1c,
  Artifact.op 0x83,
  Artifact.op 0x01,
  Artifact.op 0x8b,
  Artifact.op 0x16,
  Artifact.op 0x90,
  Artifact.op 0x85,
  Artifact.op 0x02,
  .push 1 22,
  Artifact.op 0x1c,
  Artifact.op 0x92
]

theorem nativeRight0Quad0_eq : nativeRight0Quad0 = code (rightParams 0 0) 5 := by
  rfl

#print axioms right0_fits
#print axioms nativeRight0Quad0_eq

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SingleCachedMaskInlineParams
