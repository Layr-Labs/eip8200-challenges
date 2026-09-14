import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Scratch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13NormalTrace

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Lower
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedScheduleMemory Pair13Endian

def lowerTemplate : List Instr :=
  ((loadTemplate 1120 ++ (stage8 false ++ stage16)) ++ lowStore) ++
    [.op (.Dup ⟨1, by decide⟩)]

theorem run_lower (s : State) (pc ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 lim : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 880) (hrun : s.halt = .Running)
    (hactive : s.activeWords = UInt256.ofNat 36) :
    runInstrSeq lowerTemplate
      {s with pc := pc, stack := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 0) lim rho} =
      some {s with
        pc := pcAfter pc lowerTemplate
        stack := mw :: stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 0) lim rho
        memory := writeWord s.memory 28
          (PairedScheduleData.reversedWord (MachineState.readWord s.memory 1120))} := by
  let F := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 0) lim rho
  let low := PairedScheduleData.reversedWord (MachineState.readWord s.memory 1120)
  have hF : F.length < 1022 := by simp only [F, stk, List.length_cons]; omega
  have ha : 35 ≤ s.activeWords.toNat := by rw [hactive]; decide
  have hloadActive : activeAfterWord s.activeWords (UInt256.ofNat 1120) = s.activeWords := by
    rw [hactive]
    rfl
  have h1 := run_load s pc ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 0) lim rho
    1120 1120 (by omega) hrun (by decide) (by decide)
  rw [hloadActive] at h1
  let pc1 := pcAfter pc (loadTemplate 1120)
  have h2 := run_reverse s pc1 (MachineState.readWord s.memory 1120)
    ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 0) lim rho false (by omega) hrun
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  let pc2 := pcAfter (pcAfter pc1 (stage8 false)) stage16
  have h3 := run_lowStore s pc2 low F hF hrun
  rw [Stagger144Active.word_active_preserved _ _ ha (by decide)] at h3
  have h123 := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  let s1 : State := {s with memory := writeWord s.memory 28 low}
  have h4 : runInstrSeq [.op (.Dup ⟨1, by decide⟩)]
      {s1 with pc := pcAfter pc2 lowStore, stack := F} =
      some {s1 with
        pc := pcAfter (pcAfter pc2 lowStore) [.op (.Dup ⟨1, by decide⟩)]
        stack := mw :: F} := by
    have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
    simp (discharger := omega) [F, stk, runInstrSeq, DataStepper.runInstr, pcAfter,
      hrun, hcap, Instr.size, UInt256.succ, s1, Nat.add_assoc, List.getElem?_cons_zero]
    rfl
  have h := DenseScheduleTrace.runInstrSeq_append_running h123 (by exact hrun) h4
  simpa only [lowerTemplate, DenseScheduleTrace.pcAfter_append, pc1, pc2, s1, low] using h

theorem lower_bytes : assembleBytes lowerTemplate =
    [97, 4, 96, 140, 1, 81, 128, 96, 8, 28, 129, 24, 143, 22,
     97, 1, 1, 2, 24, 143, 129, 128, 96, 16, 28, 24, 22, 98, 1, 0, 1, 2, 24,
     96, 28, 82, 129] := by decide

#print axioms run_lower
#print axioms lower_bytes
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Lower
