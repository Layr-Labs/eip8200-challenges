import Challenge.Ripemd160.Submission.Local20261028.PadValues
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadSetup
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof StackRoundTrace

def template : List Instr := [ .op .JUMPDEST,
    .op .CALLDATASIZE,
    .push ⟨19, by decide⟩ (UInt256.ofNat 178405961588244985132285746181186892047843336),
    .op .MUL,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op .MSTORE ]

def prepared (s : State) (len : UInt256) : State :=
  {s with memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded (PadValues.load len 162).toNat 32) 0}

theorem read (s : State) (len : UInt256) :
    MachineState.readWord (prepared s len).memory 0 = PadValues.load len 162 :=
  Memory.readWord_writeWord _ _ _

theorem run (s : State) (len : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 1000) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len) :
    runInstrSeq template {s with pc := UInt256.ofNat 64, stack := rho} =
      some {prepared s len with pc := UInt256.ofNat 89, stack := rho} := by
  have hcap (k : Nat) (hk : k ≤ 20) : rho.length+k < 1024 := by omega
  have hactive : s.activeWordsAfterUInt256 0 32 = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords 0 ha (by decide)
  have hbase : rho.length < 1024 := by omega
  simp (discharger := omega) [template,prepared,PadValues.load,runInstrSeq,
    DataStepper.runInstr,pcAfter,UInt256.succ,Instr.size,hr,hcap,hcal,hactive,State.activeWordsAfterUInt256,
    Word.word_toNat_ofNat,Word.literal_eq_ofNat,
    List.length_cons, hbase, hcap 1 (by decide), hcap 2 (by decide),
    if_pos, if_neg, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceMod, Nat.add_assoc]
  all_goals repeat first | apply And.intro | exact hactive | rfl

#print axioms read
#print axioms run
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadSetup
