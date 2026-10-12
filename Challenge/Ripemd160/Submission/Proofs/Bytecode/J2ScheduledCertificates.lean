import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2ScheduledTransition
import Challenge.EvmProof.Meter

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

/-!
# Independent certificates for the installed 34-instruction boundary schedule

These declarations freeze the predecessor for an independent comparison with
the installed 41-byte block. They certify its non-memory static charge and
exact result at the boundary PC. The local artifact has been regenerated and
its suffix instruction indices repaired separately; the full canonical gate,
not these comparison certificates alone, establishes whole-program correctness.
-/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace RecognitionRecurrence

/-- Frozen baseline, retained so the comparison certificate remains independent
of subsequent changes to the installed transition template. -/
def baselineTransitionTemplate : List Instr := [
  .op .JUMPDEST, .op (.Swap ⟨1, by decide⟩),
  .op (.Dup ⟨5, by decide⟩), .push ⟨3, by decide⟩ (UInt256.ofNat 2), .op .SHL,
  .push ⟨1, by decide⟩ (UInt256.ofNat 9), .op (.Dup ⟨1, by decide⟩), .op .SDIV,
  .op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .OR,
  .op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD,
  .op .XOR, .op .XOR, .op (.Swap ⟨1, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 251),
  .op (.Dup ⟨7, by decide⟩),
  .op .ADD,
  .op (.Dup ⟨0, by decide⟩),
  .op .CALLDATASIZE,
  .op .SUB,
  .op (.Dup ⟨0, by decide⟩),
  .op .CALLDATASIZE,
  .op .SAR,
  .op .AND,
  .op .ADD,
  .push ⟨1, by decide⟩ (UInt256.ofNat 32),
  .op (.Dup ⟨1, by decide⟩),
  .op .SUB,
  .op (.Swap ⟨4, by decide⟩),
  .op .POP,
  .op (.Swap ⟨6, by decide⟩),
  .op (.Swap ⟨1, by decide⟩)
]

private theorem baseline_hadd_eq (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem baseline_hmul_eq (a b : UInt256) : a * b = UInt256.mul a b := rfl
private theorem baseline_hsub_eq (a b : UInt256) : a - b = UInt256.sub a b := rfl

theorem run_baseline_transition (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) :
    runInstrSeq baselineTransitionTemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := pcAfter pc baselineTransitionTemplate, stack := f.off :: frame (transitionResult f) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [baselineTransitionTemplate, transitionResult, frame, c114,
      tw, emin, clamp, aligned, advance, runInstrSeq, DataStepper.runInstr,
      pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
      Nat.add_assoc, hrun, hbase, hcap, signed_sentinel_div9, add_negative_eq_sub, ← hlen,
      Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [signed_sentinel_div9, add_negative_eq_sub, baseline_hsub_eq, baseline_hadd_eq, baseline_hmul_eq,
    RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm,
    RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm,
    RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm,
    RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

#print axioms signed_sentinel_div9
#print axioms complement_sentinel_div9


/-- Exact proposed block, including the gas-neutral four-byte shift literal. -/
theorem scheduled_transition_bytes :
    PcEncoding.assembleBytes scheduledTransitionTemplate =
      [0x5b, 0x91, 0x85, 0x63, 0x00, 0x00, 0x00, 0x02,
       0x1b, 0x80, 0x82, 0x17, 0x60, 0x09, 0x81, 0x92,
       0x05, 0x01, 0x18, 0x18, 0x91, 0x60, 0xfb, 0x87,
       0x01, 0x80, 0x36, 0x03, 0x80, 0x36, 0x1d, 0x16,
       0x01, 0x60, 0x20, 0x81, 0x03, 0x94, 0x50, 0x96, 0x91] := by
  decide

/-- The transition has no memory expansion or state-dependent instruction charge. -/
theorem scheduled_transition_copyFree :
    ∀ instruction ∈ scheduledTransitionTemplate, Meter.CopyFree instruction = true := by
  decide

theorem scheduled_transition_static_cost :
    (scheduledTransitionTemplate.map (Meter.instrStaticCost .Osaka)).sum = 99 := by
  decide

theorem baseline_transition_static_cost :
    (baselineTransitionTemplate.map (Meter.instrStaticCost .Osaka)).sum = 102 := by
  decide

/-- The exact gas difference per boundary is three, not merely an instruction-count estimate. -/
theorem scheduled_transition_saves_three :
    (scheduledTransitionTemplate.map (Meter.instrStaticCost .Osaka)).sum + 3 =
      (baselineTransitionTemplate.map (Meter.instrStaticCost .Osaka)).sum := by
  rw [scheduled_transition_static_cost, baseline_transition_static_cost]

/-- The tested unsigned selection has the same four-byte footprint as the
signed selection, but costs two more gas. Operand setup and MUL must both be
included; counting just CALLDATASIZE versus DUP gives the wrong prediction. -/
def signedSelection : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op .CALLDATASIZE, .op .SAR, .op .AND]

def unsignedSelection : List Instr :=
  [.op .CALLDATASIZE, .op (.Dup ⟨2, by decide⟩), .op .GT, .op .MUL]

theorem signedSelection_bytes : PcEncoding.assembleBytes signedSelection =
    [0x80, 0x36, 0x1d, 0x16] := by decide

theorem unsignedSelection_bytes : PcEncoding.assembleBytes unsignedSelection =
    [0x36, 0x82, 0x11, 0x02] := by decide

theorem selection_same_byte_length :
    (signedSelection.map Instr.size).sum = (unsignedSelection.map Instr.size).sum := by decide

theorem signedSelection_cost :
    (signedSelection.map (Meter.instrStaticCost .Osaka)).sum = 11 := by decide

theorem unsignedSelection_cost :
    (unsignedSelection.map (Meter.instrStaticCost .Osaka)).sum = 13 := by decide

theorem unsignedSelection_costs_two_more :
    (signedSelection.map (Meter.instrStaticCost .Osaka)).sum + 2 =
      (unsignedSelection.map (Meter.instrStaticCost .Osaka)).sum := by decide

theorem scheduled_transition_pc :
    pcAfter (UInt256.ofNat 4638) scheduledTransitionTemplate = UInt256.ofNat 4679 := by
  decide

/-- Both arbitrary-frame traces return the exact same state at the real boundary.
No matching-pattern, input-content, or segment-reachability assumption is needed. -/
theorem scheduled_transition_same_state (s : State) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) :
    runInstrSeq scheduledTransitionTemplate {s with pc := UInt256.ofNat 4638, stack := frame f rho} =
      runInstrSeq baselineTransitionTemplate {s with pc := UInt256.ofNat 4638, stack := frame f rho} := by
  rw [run_scheduled_transition s (UInt256.ofNat 4638) f rho hstack hrun hlen,
    run_baseline_transition s (UInt256.ofNat 4638) f rho hstack hrun hlen,
    scheduled_transition_pc]
  have old_pc : pcAfter (UInt256.ofNat 4638) baselineTransitionTemplate = UInt256.ofNat 4679 := by decide
  rw [old_pc]

#print axioms scheduled_transition_bytes
#print axioms scheduled_transition_saves_three
#print axioms scheduled_transition_same_state
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
