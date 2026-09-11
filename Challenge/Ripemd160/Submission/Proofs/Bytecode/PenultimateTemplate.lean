import Challenge.Ripemd160.Submission.Proofs.Bytecode.PenultimateFinish

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 50000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PenultimateTemplate
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace
open PairedHelperBooleanTrace (scaledRotation inlineSum inlineProduct rawC10 inline4Boolean)
open PenultimateRound PenultimateFinish

def code : List Instr :=
  PairedAllInlineCoreTrace.inline78Template.take 35 ++
    (PairedAllInlineCoreTrace.inline78Template.drop 37).take 5

theorem length_code : code.length = 40 := by decide

theorem pc_code : pcAfter (UInt256.ofNat 4519) code = UInt256.ofNat 4565 := by decide

theorem run_code (s : State) (pc : UInt256) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq code {s with pc := pc, stack := PairedAllInlineCoreTrace.inline78Entry q rho} =
      some {s with
        pc := pcAfter pc code
        stack := PairedAllInlineCoreTrace.inline79Entry (dirty78Frame s.memory q) rho} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 704) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := PairedHelperBooleanTrace.active_schedule_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [code, PairedAllInlineCoreTrace.inline78Template,
    PairedAllInlineCoreTrace.inline78Entry, PairedAllInlineCoreTrace.inline79Entry,
    dirty78Frame, rawT78, TerminalRound.modifiedC10,
    scaledRotation, inlineSum, PairedAllInlineCoreTrace.inline78Frame,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    State.activeWordsAfterUInt256, hactiveAt]
  constructor
  · rfl
  constructor
  · rfl
  · change UInt256.add q.e (scaledRotation (PairedAllInlineCoreTrace.inline78Frame s.memory q)
      q.upper (UInt256.ofNat 63) (UInt256.ofNat 27) (PairedSynthCoreTrace.fourRaw q)) =
        UInt256.add q.e (scaledRotation (PairedAllInlineCoreTrace.inline78Frame s.memory q)
          q.upper (UInt256.ofNat 63) (UInt256.ofNat 27) (inline4Boolean q))
    rw [PairedSynthCoreTrace.fourRaw_eq_inline4Boolean]

#print axioms run_code
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PenultimateTemplate
