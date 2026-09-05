import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateLaneStep
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSites

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateLaneTrace

open EvmSemantics EvmSemantics.EVM
open ImmediateWrapper ImmediateIteration
open CompressionTrace

def leftAt (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  wrapperEntryAt (leftSite i) (leftStates s messageOffset returnDest rest i)
    messageOffset returnDest rest

def gasSteps_left80 (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256)
    (certs : ∀ i : Fin 80, ImmediateSites.ImmediateSiteCertificate
      (ImmediateSites.leftData i))
    (nextPC : ∀ i : Fin 80, (leftSite i).ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (leftSite (i.val + 1)).startIndex))
    (hactive : 67 ≤ s.activeWords.toNat)
    (tables : InitializationCorrect.TablesCorrect s.memory)
    (constants : ∀ j, j < 5 → InitializationCorrect.slotWord s.memory 0x620 j =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.K[j]!))
    (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (leftAt s messageOffset returnDest rest 0)
      (leftAt s messageOffset returnDest rest 80) := by
  apply Challenge.EvmProof.GasSteps.iterateBounded (count := 80)
  intro i hi
  let q := leftStates s messageOffset returnDest rest i
  have hqcode : q.executionEnv.code = submissionBytecode := by
    rw [leftStates_executionEnv]
    exact hcode
  have hqfork : q.fork = .Osaka := by
    rw [State.fork, leftStates_executionEnv]
    exact hfork
  have hqrun : q.halt = .Running := by rw [leftStates_halt]; exact hrun
  have hqnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig
      q.executionEnv.fork q.executionEnv.codeAddr = false := by
    rw [leftStates_executionEnv]
    exact hnp
  have hqactive : 67 ≤ q.activeWords.toNat := by
    rw [ImmediateStateFacts.leftStates_activeWords s messageOffset returnDest rest
      tables hactive i (by omega)]
    exact hactive
  have hqtables := ImmediateStateFacts.leftStates_tables_preserved
    s messageOffset returnDest rest i tables
  have hqconstants : ∀ j, j < 5 →
      InitializationCorrect.slotWord q.memory 0x620 j =
        Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.K[j]!) := by
    intro j hj
    rw [ImmediateStateFacts.leftStates_slotWord s messageOffset returnDest rest
      i 0x620 j (by omega)]
    exact constants j hj
  have hj : (leftSite i).j.toNat < 5 := by
    change (UInt256.ofNat (i / 16)).toNat < 5
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have g := ImmediateSites.gasStepsImmediateSiteToNext (certs ⟨i, hi⟩)
    (leftSite (i + 1)) (nextPC ⟨i, hi⟩) q messageOffset returnDest rest
    hj hstack hqcode hqfork hqrun hqnp
  have hrr := ImmediateLaneModel.leftSite_roundReturned q messageOffset returnDest rest
    i hi hqactive hqtables hqconstants
  have hend :
      wrapperEntryAt (leftSite (i + 1))
        (ImmediateSites.immediateRoundReturned (ImmediateSites.leftData i)
          q messageOffset returnDest rest) messageOffset returnDest rest =
        leftAt s messageOffset returnDest rest (i + 1) := by
    change wrapperEntryAt (leftSite (i + 1))
      (RoundTrace.roundReturned q (leftSite i).base (leftSite i).j.toNat
        (leftSite i).wordIndex (leftSite i).rotation (leftSite i).k (leftSite i).ret
        ([messageOffset, returnDest] ++ rest)) messageOffset returnDest rest = _
    rw [hrr]
    simp only [wrapperEntryAt, leftAt, leftStates_succ, q]
  exact g.cast rfl hend

/-- Index 79 is the PUSH0 before the final wrapper, not the wrapper itself. -/
def rightRegularSite (i : Nat) : WrapperSite :=
  {rightSite i with startIndex := 1717 + 9 * i}

theorem rightRegularSite_eq (i : Nat) (hi : i < 79) :
    rightRegularSite i = rightSite i := by
  simp only [rightRegularSite, rightSite, if_neg (by omega : i ≠ 79), mkImmediateSite]

def rightAt (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  wrapperEntryAt (rightRegularSite i)
    (CompressionRightTrace.rightStates s messageOffset returnDest rest i)
    messageOffset returnDest rest

def gasSteps_right79 (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256)
    (certs : ∀ i : Fin 79, ImmediateSites.ImmediateSiteCertificate
      (ImmediateSites.rightData i))
    (nextPC : ∀ i : Fin 79, (rightSite i).ret.succ =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC
        (rightRegularSite (i.val + 1)).startIndex))
    (hactive : 67 ≤ s.activeWords.toNat)
    (tables : InitializationCorrect.TablesCorrect s.memory)
    (constants : ∀ j, j < 5 → InitializationCorrect.slotWord s.memory 0x6c0 j =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[j]!))
    (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (rightAt s messageOffset returnDest rest 0)
      (rightAt s messageOffset returnDest rest 79) := by
  apply Challenge.EvmProof.GasSteps.iterateBounded (count := 79)
  intro i hi
  let q := CompressionRightTrace.rightStates s messageOffset returnDest rest i
  have hqcode : q.executionEnv.code = submissionBytecode := by
    rw [CompressionRightTrace.rightStates_executionEnv]
    exact hcode
  have hqfork : q.fork = .Osaka := by
    rw [State.fork, CompressionRightTrace.rightStates_executionEnv]
    exact hfork
  have hqrun : q.halt = .Running := by
    rw [CompressionRightTrace.rightStates_halt]
    exact hrun
  have hqnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig
      q.executionEnv.fork q.executionEnv.codeAddr = false := by
    rw [CompressionRightTrace.rightStates_executionEnv]
    exact hnp
  have hqactive : 67 ≤ q.activeWords.toNat := by
    rw [ImmediateStateFacts.rightStates_activeWords s messageOffset returnDest rest
      tables hactive i (by omega)]
    exact hactive
  have hqtables := ImmediateStateFacts.rightStates_tables_preserved
    s messageOffset returnDest rest i tables
  have hqconstants : ∀ j, j < 5 →
      InitializationCorrect.slotWord q.memory 0x6c0 j =
        Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[j]!) := by
    intro j hj
    rw [ImmediateStateFacts.rightStates_slotWord s messageOffset returnDest rest
      i 0x6c0 j (by omega)]
    exact constants j hj
  have hj : (rightSite i).j.toNat < 5 := by
    change (UInt256.ofNat (4 - i / 16)).toNat < 5
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have g := ImmediateSites.gasStepsImmediateSiteToNext (certs ⟨i, hi⟩)
    (rightRegularSite (i + 1)) (nextPC ⟨i, hi⟩) q messageOffset returnDest rest
    hj hstack hqcode hqfork hqrun hqnp
  have hrr := ImmediateLaneModel.rightSite_roundReturned q messageOffset returnDest rest
    i (by omega) hqactive hqtables hqconstants
  have hend :
      wrapperEntryAt (rightRegularSite (i + 1))
        (ImmediateSites.immediateRoundReturned (ImmediateSites.rightData i)
          q messageOffset returnDest rest) messageOffset returnDest rest =
        rightAt s messageOffset returnDest rest (i + 1) := by
    change wrapperEntryAt (rightRegularSite (i + 1))
      (RoundTrace.roundReturned q (rightSite i).base (rightSite i).j.toNat
        (rightSite i).wordIndex (rightSite i).rotation (rightSite i).k (rightSite i).ret
        ([messageOffset, returnDest] ++ rest)) messageOffset returnDest rest = _
    rw [hrr]
    simp only [wrapperEntryAt, rightAt, CompressionRightTrace.rightStates_succ, q]
  have hstart :
      wrapperEntryAt (ImmediateSites.rightData i).site q messageOffset returnDest rest =
        rightAt s messageOffset returnDest rest i := by
    unfold rightAt
    rw [rightRegularSite_eq i hi]
    rfl
  exact g.cast hstart hend

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateLaneTrace
