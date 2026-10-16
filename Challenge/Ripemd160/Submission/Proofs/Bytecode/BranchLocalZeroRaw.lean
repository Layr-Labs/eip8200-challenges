import Challenge.Ripemd160.Submission.Proofs.Bytecode.UnrolledRepeatRaw

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! Generic raw tail proofs, not an exact located-bytecode certificate. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.BranchLocalZeroRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace

def branch : List Instr :=
  [.push ⟨3, by decide⟩ (UInt256.ofNat 4706), .op .JUMPI]

def miss : List Instr :=
  [.push ⟨0, by decide⟩ (UInt256.ofNat 0),
   .push ⟨1, by decide⟩ (UInt256.ofNat 245), .op .JUMP]

theorem run_hit (s : State) (a r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (ha : UInt256.isTrue a)
    (hv : Decode.isValidJumpDest s.executionEnv.code 4706 = true) :
    runInstrSeq branch
      {s with pc := UInt256.ofNat 9633, stack := [a,r] ++ rho} =
      some {s with pc := UInt256.ofNat 4706, stack := r :: rho} := by
  have hcap2 : rho.length + 1 + 1 < 1024 := by omega
  have hcap3 : rho.length + 1 + 1 + 1 < 1024 := by omega
  simp (discharger := omega) [branch, runInstrSeq, DataStepper.runInstr,
    hrun, ha, hv, UInt256.succ, Instr.size, hcap2, hcap3, Word.literal_eq_ofNat, Word.word_toNat_ofNat]
  repeat first | apply And.intro | rfl

theorem run_miss (s : State) (a r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (ha : ¬ UInt256.isTrue a) :
    runInstrSeq branch
      {s with pc := UInt256.ofNat 9633, stack := [a,r] ++ rho} =
      some {s with pc := UInt256.ofNat 9638, stack := r :: rho} := by
  have hcap2 : rho.length + 1 + 1 < 1024 := by omega
  have hcap3 : rho.length + 1 + 1 + 1 < 1024 := by omega
  simp (discharger := omega) [branch, runInstrSeq, DataStepper.runInstr,
    hrun, ha, UInt256.succ, Instr.size, hcap2, hcap3, Word.literal_eq_ofNat, Word.word_toNat_ofNat]
  repeat first | apply And.intro | rfl

theorem restore_miss (s : State) (r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hv : Decode.isValidJumpDest s.executionEnv.code 245 = true) :
    runInstrSeq miss
      {s with pc := UInt256.ofNat 9638, stack := r :: rho} =
      some {s with pc := UInt256.ofNat 245, stack := [0,r] ++ rho} := by
  have hcap1 : rho.length + 1 < 1024 := by omega
  have hcap2 : rho.length + 1 + 1 < 1024 := by omega
  have hcap3 : rho.length + 1 + 1 + 1 < 1024 := by omega
  simp (discharger := omega) [miss, runInstrSeq, DataStepper.runInstr,
    hrun, hv, UInt256.succ, Instr.size, hcap1, hcap2, hcap3, Word.literal_eq_ofNat, Word.word_toNat_ofNat]
  repeat first | apply And.intro | rfl

#print axioms run_hit
#print axioms run_miss
#print axioms restore_miss
end Challenge.Ripemd160.Submission.Proofs.Bytecode.BranchLocalZeroRaw
