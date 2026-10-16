import Challenge.Ripemd160.Submission.Proofs.Bytecode.UnrolledRepeatRaw
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CounterFreeSeedRaw.Warm
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace StackRoundTemplate

def template : List Instr :=
  [.push ⟨0, by decide⟩ 0, .op .MLOAD, .op .CALLDATALOAD]

theorem empty_read : MachineState.readWord ByteArray.empty 0 = UInt256.ofNat 0 := by
  unfold MachineState.readWord
  rw [← Bytes.bytesNat_toList, Bytes.readPadded_toList,
    YulEvmCompiler.ByteArray.toList_eq_data]
  decide

theorem run (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hm : s.memory = ByteArray.empty) (ha : s.activeWords = 0) :
    runInstrSeq template {s with pc := pc, stack := rho} =
      some {s with
        pc := pcAfter pc template
        stack := MachineState.readWord s.executionEnv.calldata 0 :: rho
        activeWords := UInt256.ofNat 1} := by
  have hcap0 : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [template, runInstrSeq, DataStepper.runInstr,
    pcAfter, hrun, hm, ha, hcap0, hcap, empty_read, UInt256.succ, Instr.size,
    Nat.add_assoc, Word.literal_eq_ofNat, Word.word_toNat_ofNat,
    MachineState.activeWordsAfter, State.activeWordsAfterUInt256]
  repeat first | apply And.intro | rfl
  change MachineState.readWord s.executionEnv.calldata
    (MachineState.readWord ByteArray.empty 0).toNat = _
  rw [empty_read]
  rfl


end Challenge.Ripemd160.Submission.Proofs.Bytecode.CounterFreeSeedRaw.Warm

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CounterFreeSeedRaw.Seed
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace

def template : List Instr :=
  [.push ⟨2, by decide⟩ (UInt256.ofNat 968), .op .CALLDATALOAD,
   .op (.Dup ⟨1, by decide⟩), .op .EQ]

theorem run_template (s : State) (pc r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := pc, stack := r :: rho} =
      some {s with
        pc := pcAfter pc template
        stack := UInt256.eq r (MachineState.readWord s.executionEnv.calldata 968) :: r :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [template, runInstrSeq, DataStepper.runInstr,
    pcAfter, hrun, hcap, UInt256.succ, Instr.size, Nat.add_assoc,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat, DirectGuard.equality_comm,
    List.getElem?_cons_zero, List.getElem?_cons_succ]
  repeat first | apply And.intro | rfl


end Challenge.Ripemd160.Submission.Proofs.Bytecode.CounterFreeSeedRaw.Seed

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CounterFreeSeedRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace (pcAfter_append runInstrSeq_append_running)

def jumpTemplate : List Instr := [.push ⟨2, by decide⟩ (UInt256.ofNat 9429), .op .JUMP]
def template : List Instr := (Warm.template ++ Seed.template) ++ jumpTemplate

theorem run_jump (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 9429 = true) :
    runInstrSeq jumpTemplate {s with pc := pc, stack := rho} =
      some {s with pc := UInt256.ofNat 9429, stack := rho} := by
  have hc0 : rho.length < 1024 := by omega
  have hc1 : rho.length + 1 < 1024 := by omega
  simp [jumpTemplate, runInstrSeq, DataStepper.runInstr, hrun, hc0, hc1,
    Word.word_toNat_ofNat, hdest]

theorem run (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hm : s.memory = ByteArray.empty) (ha : s.activeWords = 0)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 9429 = true) :
    runInstrSeq template {s with pc := pc, stack := rho} =
      some {s with
        pc := UInt256.ofNat 9429
        activeWords := UInt256.ofNat 1
        stack := [DirectGuard.equalityAcc s.executionEnv.calldata 0,
          KnownInputCompactState.referenceWord s.executionEnv.calldata] ++ rho} := by
  let w : State := {s with activeWords := UInt256.ofNat 1}
  have hw := Warm.run s pc rho (by omega) hrun hm ha
  have ht := Seed.run_template w (pcAfter pc Warm.template)
    (MachineState.readWord s.executionEnv.calldata 0) rho (by omega) hrun
  have hw' : runInstrSeq Warm.template {s with pc := pc, stack := rho} =
      some {w with
        pc := pcAfter pc Warm.template
        stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} := by
    exact hw
  have hb := runInstrSeq_append_running hw' hrun ht
  have hj := run_jump w (pcAfter (pcAfter pc Warm.template) Seed.template)
    ([DirectGuard.equalityAcc s.executionEnv.calldata 0,
      KnownInputCompactState.referenceWord s.executionEnv.calldata] ++ rho)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hrun hdest
  have hh := runInstrSeq_append_running hb hrun hj
  simpa only [template, w, DirectGuard.equalityAcc,
    KnownInputCompactState.referenceWord] using hh

#print axioms run
end Challenge.Ripemd160.Submission.Proofs.Bytecode.CounterFreeSeedRaw
