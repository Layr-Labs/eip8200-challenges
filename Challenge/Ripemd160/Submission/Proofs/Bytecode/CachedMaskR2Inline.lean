import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskQuadGroup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSemantic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskR2Inline

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundState QuadRoundTemplate
open CavityQuadGroup CachedMaskQuadGroup QuadSemantic StackCompression

/-- R2 constant from the work assignment: `KP[2]`. -/
def K2 : UInt256 := UInt256.ofNat 0x6d703ef3

/-- Current dense-memory addresses for right rounds 32–47. -/
def r2addrList : List (List Nat) :=
  [[252, 212, 196, 204],
   [220, 248, 216, 228],
   [236, 224, 240, 200],
   [232, 192, 208, 244]]

def r2address (k : Fin 4) (i : Fin 4) : UInt256 :=
  UInt256.ofNat ((r2addrList[k.val]!)[i.val]!)

/-- R2 rotation table: `[9,7,15,11]`, `[8,6,6,14]`, `[12,13,5,14]`,
    `[13,13,7,5]`. -/
def r2rotList : List (List Nat) :=
  [[9, 7, 15, 11],
   [8, 6, 6, 14],
   [12, 13, 5, 14],
   [13, 13, 7, 5]]

def r2rotation (k : Fin 4) (i : Fin 4) : Nat :=
  (r2rotList[k.val]!)[i.val]!

/-- All sixteen table addresses match the current base message map. -/
theorem r2address_eq (k : Fin 4) (i : Fin 4) :
    r2address k i = StackRoundData.rightAddress (32 + 4 * k.val + i.val) := by
  fin_cases k <;> fin_cases i <;> decide

/-- All sixteen table rotations match the current base rotation map. -/
theorem r2rotation_eq (k : Fin 4) (i : Fin 4) :
    r2rotation k i = StackRoundData.rightRotation (32 + 4 * k.val + i.val) := by
  fin_cases k <;> fin_cases i <;> decide

/-- The R2 constant matches the current base constant for rounds 32-47. -/
theorem r2const_eq :
    K2 = StackRoundData.rightConstant 32 := by
  decide

/-- Table addresses equal the shared right-quad address accessor. -/
theorem r2address_quad (k : Fin 4) (i : Fin 4) :
    r2address k i = quadRightAddress ⟨8 + k.val, by omega⟩ i := by
  fin_cases k <;> fin_cases i <;> decide

/-- Table rotations equal the shared right-quad rotation accessor. -/
theorem r2rotation_quad (k : Fin 4) (i : Fin 4) :
    r2rotation k i = quadRightRotation ⟨8 + k.val, by omega⟩ i := by
  fin_cases k <;> fin_cases i <;> decide

/-- The R2 constant equals the shared right-quad constant for quads 8-11. -/
theorem r2const_quad (k : Fin 4) :
    K2 = quadRightConstant ⟨8 + k.val, by omega⟩ := by
  fin_cases k <;> decide

/-- R2 control parameters: function 2 at shift 5 over the table above. -/
def r2 (k : Fin 4) : Params where
  function := ⟨2, by decide⟩
  address := r2address k
  rotation := r2rotation k
  constant := K2
  rotations_bounded := fun i => by
    rw [r2rotation_eq k i]
    exact StackRoundData.rightRotation_le_32
      ⟨32 + 4 * k.val + i.val, by have := k.isLt; have := i.isLt; omega⟩
  constant_zero h := absurd h (by decide)

/-- The four inline quads concatenated: the C replacement code. -/
def r2Code : List Instr := fourCode r2 5

/-- The composed R2 working state after all four inline quads. -/
def r2Result (s : State) (w : Compression.EvmWorking) :
    Compression.EvmWorking :=
  fourResult r2 s w

/-- Running the four inline quads threads the endpoint through each quad. -/
theorem run_r2 (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (a b c d e : UInt256) (rho : List UInt256)
    (hfit : ∀ k, (r2 k).Fits s) (hstack : rho.length < 1001)
    (hrun : s.halt = .Running) :
    runInstrSeq r2Code (stateAt s pc w (a :: b :: c :: d :: e :: mask :: rho)) =
      some (stateAt s (pcAfter pc r2Code) (r2Result s w)
        (a :: b :: c :: d :: e :: mask :: rho)) :=
  run_right_four r2 s pc w a b c d e rho hfit hstack hrun

/-- Every R2 inline instruction advances the straight-line trace. -/
theorem r2_advances :
    ∀ instruction ∈ r2Code, PairMultiplyLift.Advances instruction :=
  four_advances r2 5

/-- Each R2 quad fits the active memory window. -/
theorem r2_fits (s : State) (hactive : 25 ≤ s.activeWords.toNat) :
    ∀ k, (r2 k).Fits s := by
  intro k i
  have h := quadRightAddress_end_le s ⟨8 + k.val, by omega⟩ i hactive
  rwa [← r2address_quad k i] at h

/-- One R2 quad computes four `rightStep` rounds. -/
def rightQuad32 (word : Nat → UInt32) (k : Fin 4)
    (w : Compression.EvmWorking) : Compression.EvmWorking :=
  rightStep word (quadIndex ⟨8 + k.val, by omega⟩ 3)
    (rightStep word (quadIndex ⟨8 + k.val, by omega⟩ 2)
      (rightStep word (quadIndex ⟨8 + k.val, by omega⟩ 1)
        (rightStep word (quadIndex ⟨8 + k.val, by omega⟩ 0) w)))

theorem r2_apply (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (k : Fin 4)
    (hwords : DenseWordsAt s word) :
    (r2 k).apply s w = rightQuad32 word k w := by
  have hk := k.isLt
  have h := quadWorking_right s word w ⟨8 + k.val, by omega⟩ hwords
  have hfun : 4 - (8 + k.val) / 4 = 2 := by omega
  have hval : (⟨8 + k.val, by omega⟩ : Fin 20).val = 8 + k.val := rfl
  rw [hval, hfun] at h
  rw [← r2address_quad k 0, ← r2address_quad k 1,
    ← r2address_quad k 2, ← r2address_quad k 3,
    ← r2rotation_quad k 0, ← r2rotation_quad k 1,
    ← r2rotation_quad k 2, ← r2rotation_quad k 3,
    ← r2const_quad k] at h
  have hgoal : (r2 k).apply s w =
      QuadRoundState.quadWorking s w 2 (r2address k 0) (r2address k 1)
        (r2address k 2) (r2address k 3) (r2rotation k 0) (r2rotation k 1)
        (r2rotation k 2) (r2rotation k 3) K2 := rfl
  rw [hgoal, rightQuad32]
  exact h

/-- Applied after round 32, the four inline quads complete round 48. -/
theorem r2_result_after32 (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (hwords : DenseWordsAt s word) :
    r2Result s (rightRounds word 32 w) = rightRounds word 48 w := by
  rw [r2Result, fourResult, r2_apply s word _ _ hwords,
    r2_apply s word _ _ hwords, r2_apply s word _ _ hwords,
    r2_apply s word _ _ hwords]
  rw [rightRounds_quad word 11, rightRounds_quad word 10,
    rightRounds_quad word 9, rightRounds_quad word 8]
  rfl

/-- A location certificate for the whole inline region preserves all five
saved left words and the complete suffix. Its end PC is not an old helper PC. -/
theorem runLocated_r2 {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork r2Code)
    (s : State) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hactive : 25 ≤ s.activeWords.toNat) (hstack : rho.length < 1001)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock site.path
      (stateAt s site.startPC w (a :: b :: c :: d :: e :: mask :: rho)) =
      some (stateAt s site.endPC (r2Result s w)
        (a :: b :: c :: d :: e :: mask :: rho)) := by
  have hend : site.endPC = pcAfter site.startPC r2Code := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [PairMultiplyLift.runLocatedBlock_eq_raw site r2_advances _ rfl]
  rw [run_r2 s site.startPC w a b c d e rho (r2_fits s hactive) hstack hrun, ← hend]

/-- The C integration endpoint: right rounds 32 through 47, with the
original arbitrary left-word/suffix contract and the certified new PCs. -/
def gasSteps_r2_after32 {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork r2Code)
    (s : State) (word : Nat → UInt32) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hwords : DenseWordsAt s word)
    (hactive : 25 ≤ s.activeWords.toNat) (hstack : rho.length < 1001)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (stateAt s site.startPC (rightRounds word 32 w)
        (a :: b :: c :: d :: e :: mask :: rho))
      (stateAt s site.endPC (rightRounds word 48 w)
        (a :: b :: c :: d :: e :: mask :: rho)) := by
  have h := runLocated_r2 site s (rightRounds word 32 w)
    a b c d e rho hactive hstack hrun
  rw [r2_result_after32 s word w hwords] at h
  exact Stepper.runLocatedBlock_sound artifact fork site.path hcode hfork h hrun hnp

/-- Four 140-byte quads replace the 329-byte call group. -/
theorem r2_quad_bytes (k : Fin 4) :
    ((CachedMaskQuadGroup.code (r2 k) 5).map Instr.size).sum = 140 := by
  fin_cases k <;> decide

theorem r2Code_bytes :
    (r2Code.map Instr.size).sum = 560 := by
  decide

theorem r2Code_length : r2Code.length = 448 := by decide

#print axioms r2address_eq
#print axioms r2rotation_eq
#print axioms r2const_eq
#print axioms run_r2
#print axioms r2_advances
#print axioms r2_fits
#print axioms r2_apply
#print axioms r2_result_after32
#print axioms runLocated_r2
#print axioms gasSteps_r2_after32

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskR2Inline
