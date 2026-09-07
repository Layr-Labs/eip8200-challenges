import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityQuadGroup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityParams

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open StackRoundTrace CavityQuadGroup

/-- The first four left-lane quads are all in RIPEMD round function zero. -/
def left (k : Fin 4) : Params where
  function := ⟨0, by decide⟩
  address i := StackRoundData.leftAddress (4 * k.val + i.val)
  rotation i := StackRoundData.leftRotation (4 * k.val + i.val)
  constant := 0
  rotations_bounded i :=
    StackRoundData.leftRotation_le_32 ⟨4 * k.val + i.val, by omega⟩
  constant_zero _ := rfl

/-- The final four right-lane quads are also in RIPEMD round function zero. -/
def right (k : Fin 4) : Params where
  function := ⟨0, by decide⟩
  address i := StackRoundData.rightAddress (64 + 4 * k.val + i.val)
  rotation i := StackRoundData.rightRotation (64 + 4 * k.val + i.val)
  constant := 0
  rotations_bounded i :=
    StackRoundData.rightRotation_le_32 ⟨64 + 4 * k.val + i.val, by omega⟩
  constant_zero _ := rfl

def leftCode : List YulEvmCompiler.Instr :=
  (left 0).template ++ (left 1).template ++
    (left 2).template ++ (left 3).template

def rightCode : List YulEvmCompiler.Instr :=
  (right 0).template ++ (right 1).template ++
    (right 2).template ++ (right 3).template

def leftResult (s : State) (w : Compression.EvmWorking) :
    Compression.EvmWorking :=
  (left 3).apply s ((left 2).apply s ((left 1).apply s ((left 0).apply s w)))

def rightResult (s : State) (w : Compression.EvmWorking) :
    Compression.EvmWorking :=
  (right 3).apply s ((right 2).apply s ((right 1).apply s ((right 0).apply s w)))

theorem run_leftCode (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (rho : List UInt256)
    (hfit : ∀ k, (left k).Fits s) (hstack : rho.length < 1007)
    (hrun : s.halt = .Running) :
    runInstrSeq leftCode (stateAt s pc w rho) =
      some (stateAt s (pcAfter pc leftCode) (leftResult s w) rho) := by
  have hrunAt (nextPC : UInt256) (next : Compression.EvmWorking) :
      (stateAt s nextPC next rho).halt = .Running := by
    simpa [stateAt, StackRoundTrace.roundEntry] using hrun
  have h0 := runInstrSeq_quad (left 0) s pc w rho (hfit 0) hstack hrun
  have h1 := runInstrSeq_quad (left 1) s
    (pcAfter pc (left 0).template) ((left 0).apply s w) rho
    (hfit 1) hstack hrun
  have h2 := runInstrSeq_quad (left 2) s
    (pcAfter (pcAfter pc (left 0).template) (left 1).template)
    ((left 1).apply s ((left 0).apply s w)) rho (hfit 2) hstack hrun
  have h3 := runInstrSeq_quad (left 3) s
    (pcAfter
      (pcAfter (pcAfter pc (left 0).template) (left 1).template)
      (left 2).template)
    ((left 2).apply s ((left 1).apply s ((left 0).apply s w))) rho
    (hfit 3) hstack hrun
  have hall := QuadRoundState.runInstrSeq_append h0 (hrunAt _ _) <|
    QuadRoundState.runInstrSeq_append h1 (hrunAt _ _) <|
      QuadRoundState.runInstrSeq_append h2 (hrunAt _ _) h3
  simpa only [leftCode, leftResult, QuadRoundState.pcAfter_append,
    List.append_assoc] using hall

theorem run_rightCode (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (rho : List UInt256)
    (hfit : ∀ k, (right k).Fits s) (hstack : rho.length < 1007)
    (hrun : s.halt = .Running) :
    runInstrSeq rightCode (stateAt s pc w rho) =
      some (stateAt s (pcAfter pc rightCode) (rightResult s w) rho) := by
  have hrunAt (nextPC : UInt256) (next : Compression.EvmWorking) :
      (stateAt s nextPC next rho).halt = .Running := by
    simpa [stateAt, StackRoundTrace.roundEntry] using hrun
  have h0 := runInstrSeq_quad (right 0) s pc w rho (hfit 0) hstack hrun
  have h1 := runInstrSeq_quad (right 1) s
    (pcAfter pc (right 0).template) ((right 0).apply s w) rho
    (hfit 1) hstack hrun
  have h2 := runInstrSeq_quad (right 2) s
    (pcAfter (pcAfter pc (right 0).template) (right 1).template)
    ((right 1).apply s ((right 0).apply s w)) rho (hfit 2) hstack hrun
  have h3 := runInstrSeq_quad (right 3) s
    (pcAfter
      (pcAfter (pcAfter pc (right 0).template) (right 1).template)
      (right 2).template)
    ((right 2).apply s ((right 1).apply s ((right 0).apply s w))) rho
    (hfit 3) hstack hrun
  have hall := QuadRoundState.runInstrSeq_append h0 (hrunAt _ _) <|
    QuadRoundState.runInstrSeq_append h1 (hrunAt _ _) <|
      QuadRoundState.runInstrSeq_append h2 (hrunAt _ _) h3
  simpa only [rightCode, rightResult, QuadRoundState.pcAfter_append,
    List.append_assoc] using hall

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityParams
