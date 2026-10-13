import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLengthLookup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
import Challenge.EvmProof.Meter

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.TwoLengthGateCertificates
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace

def baseline : List Instr :=
  [.push 2 376, .push 4 24641792, .op .CALLDATASIZE, .push 1 16,
   .op .AND, .op .SHR, .op .AND, .op .EQ]

def replacement : List Instr :=
  [.push 2 256, .op .EQ, .push 7 376, .op .CALLDATASIZE, .op .EQ, .op .OR]

def condition (n : UInt256) : UInt256 :=
  UInt256.lor (UInt256.eq 376 n) (UInt256.eq 256 n)

theorem baseline_bytes : PcEncoding.assembleBytes baseline =
    [0x61,0x01,0x78,0x63,0x01,0x78,0x01,0x00,0x36,0x60,0x10,0x16,0x1c,0x16,0x14] := by decide

theorem replacement_bytes : PcEncoding.assembleBytes replacement =
    [0x61,0x01,0x00,0x14,0x66,0x00,0x00,0x00,0x00,0x00,0x01,0x78,0x36,0x14,0x17] := by decide

theorem same_span : (baseline.map Instr.size).sum = (replacement.map Instr.size).sum := by decide

theorem baseline_cost : (baseline.map (Meter.instrStaticCost .Osaka)).sum = 23 := by decide

theorem replacement_cost : (replacement.map (Meter.instrStaticCost .Osaka)).sum = 17 := by decide

theorem saving : (replacement.map (Meter.instrStaticCost .Osaka)).sum + 6 =
    (baseline.map (Meter.instrStaticCost .Osaka)).sum := by decide

theorem installed : (Artifact.submissionArtifact.instructions.drop 3503).take 6 = replacement := by rfl

theorem lookup_same (n : UInt256) : UInt256.eq n (PackedLengthLookup.lookup n) = condition n :=
  PackedLengthLookup.flag n

private theorem wordEq_comm (a b : UInt256) : UInt256.eq a b = UInt256.eq b a := by
  simp [UInt256.eq, eq_comm]

theorem run_replacement (s : State) (pc : UInt256) (rho : List UInt256)
    (hrun : s.halt = .Running) (hstack : rho.length ≤ 1019) :
    runInstrSeq replacement
      {s with pc := pc, stack := UInt256.ofNat s.executionEnv.calldata.size :: rho} =
      some {s with pc := pcAfter pc replacement, stack := condition (UInt256.ofNat s.executionEnv.calldata.size) :: rho} := by
  have hadd (a b : UInt256) : UInt256.add a b = a + b := rfl
  have hcap (n : Nat) (hn : n ≤ 4) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [replacement, condition, runInstrSeq, DataStepper.runInstr,
    pcAfter, Instr.size, UInt256.succ, hrun, hcap, Nat.add_assoc,
    Word.literal_eq_ofNat, wordEq_comm, hadd]

#print axioms installed
#print axioms saving
#print axioms lookup_same
#print axioms run_replacement
end Challenge.Ripemd160.Submission.Proofs.Bytecode.TwoLengthGateCertificates
