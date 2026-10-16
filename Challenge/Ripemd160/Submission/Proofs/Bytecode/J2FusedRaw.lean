import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSelectorRaw

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2FusedRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace J2Raw J2Moves

/-- One-word memory makes `CALLDATASIZE MSIZE AND` distinguish the only
non-final-boundary lengths: 256 has bit 5 clear; 376 and 1000 have it set. -/
def branchTemplate : List Instr := [ .op .JUMPDEST, .op .CALLDATASIZE, .op .MSIZE,
  .op .AND, .push ⟨2, by decide⟩ (UInt256.ofNat non256PC), .op .JUMPI ]

def projectionTemplate : List Instr := [ .op .JUMPDEST,
  .push ⟨1, by decide⟩ (UInt256.ofNat 40), .op .SHR, .op .OR ]

def predicateTemplate : List Instr := [
  .push ⟨5, by decide⟩ J2FusedAccumulator.correction, .op .XOR, .op .OR,
  .push ⟨2, by decide⟩ (UInt256.ofNat 4565), .op .JUMPI ]

/-- The two instructions after MSIZE, matching the existing early serializer. -/
def returnTemplate : List Instr := [ .push ⟨0, by decide⟩ 0, .op .RETURN ]

theorem run_branch (s : State) (pc : UInt256) (stack : List UInt256)
    (hs : stack.length ≤ 1018) (hrun : s.halt = .Running)
    (hactive : s.activeWords = UInt256.ofNat 1)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code non256PC = true) :
    runInstrSeq branchTemplate {s with pc := pc, stack := stack} =
      some {s with pc := if UInt256.land (UInt256.ofNat s.executionEnv.calldata.size) 32 = 0
        then pcAfter pc branchTemplate else UInt256.ofNat non256PC, stack := stack} := by
  have hbase : stack.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 5) : stack.length + n < 1024 := by omega
  have hz : ∀ x : UInt256, x.toNat = 0 ↔ x = 0 := by
    intro x; constructor
    · intro h; apply Word.word_ext; exact h
    · rintro rfl; rfl
  have hmod : non256PC % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = non256PC := by decide
  by_cases hc : UInt256.land (UInt256.ofNat s.executionEnv.calldata.size) (UInt256.ofNat 32) = UInt256.ofNat 0
  all_goals simp (discharger := omega) [branchTemplate, runInstrSeq, DataStepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, Nat.add_assoc, hrun, hactive,
    MachineState.msize, hbase, hcap, hvalid, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    RawExpressionAC.land_comm, hz, UInt256.isTrue, hc, hmod]
  all_goals rfl

theorem run_projection (s : State) (pc : UInt256) (f : J2Raw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hshift : UInt256.shiftLeft (UInt256.sub f.off f.full) (UInt256.ofNat 3) = UInt256.ofNat 40) :
    runInstrSeq projectionTemplate {s with pc := pc, stack := pending s f rho} =
      some {s with pc := pcAfter pc projectionTemplate, stack := frame (tailResult s f) rho} := by
  exact run_boundaryProjection s pc f rho hs hrun hshift

theorem run_predicate (s : State) (pc : UInt256) (f : J2Raw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 4565 = true) :
    runInstrSeq predicateTemplate {s with pc := pc, stack := pending s f rho} =
      some {s with pc := if (fusedAcc s f).toNat = 0 then pcAfter pc predicateTemplate
        else UInt256.ofNat 4565, stack := finishRest f rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  by_cases hc : (fusedAcc s f).toNat = 0
  all_goals simp only [fusedAcc, RawExpressionAC.xor_comm, RawExpressionAC.lor_comm] at hc
  all_goals simp (discharger := omega) [predicateTemplate, pending, frame, finishRest, fusedAcc,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    Nat.add_assoc, hrun, hbase, hcap, hvalid, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    RawExpressionAC.xor_comm, RawExpressionAC.lor_comm, UInt256.isTrue, hc]
  all_goals rfl

theorem run_return (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq returnTemplate {s with pc := pc, stack := 32 :: rho} =
      some (RecognitionSelectorRaw.returned s pc rho) := by
  exact RecognitionSelectorRaw.run_finish s pc rho (by omega) hrun

/-- The direct return, including MSIZE, leaves the residual frame untouched. -/
def fullReturnTemplate : List Instr := [.op .MSIZE, .push ⟨0, by decide⟩ 0, .op .RETURN]

theorem run_fullReturn (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hactive : s.activeWords = UInt256.ofNat 1) :
    runInstrSeq fullReturnTemplate {s with pc := pc, stack := rho} =
      some (RecognitionSelectorRaw.returned s (pc + UInt256.ofNat 1) rho) := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  have htwo : rho.length + 1 + 1 < 1024 := by omega
  simp (discharger := omega) [fullReturnTemplate, RecognitionSelectorRaw.returned,
    runInstrSeq, DataStepper.runInstr, MachineState.msize, hactive, hrun, hbase, hcap,
    UInt256.succ, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    State.activeWordsAfterUInt256, htwo, show ({val := 0} : UInt256).toNat = 0 from rfl]
  all_goals rfl

#print axioms run_branch
#print axioms run_predicate
#print axioms run_return
#print axioms run_fullReturn
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2FusedRaw
