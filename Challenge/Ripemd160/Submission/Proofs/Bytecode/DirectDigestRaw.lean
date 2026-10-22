import Challenge.Ripemd160.Submission.Proofs.Bytecode.CombinedSelectorRaw
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectDigestRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof StackRoundTrace
def selectorConst : Nat := 1805781487605728127014015497632372731422648

def shortSelected (size : Nat) : UInt256 :=
  UInt256.land (UInt256.shiftRight (UInt256.ofNat selectorConst) (UInt256.ofNat size)) (UInt256.ofNat 8191)

def selected (_codesize : UInt256) (size : Nat) : UInt256 :=
  if size = 256 then UInt256.ofNat 7805
  else if size = 376 then UInt256.ofNat 5666
  else shortSelected size

def storeTemplate (word : UInt256) : List Instr := [
 .op .JUMPDEST, .push ⟨20, by decide⟩ word,
 .push ⟨0, by decide⟩ (UInt256.ofNat 0), .op .MSTORE]

def stored (s : State) (pc word : UInt256) (rho : List UInt256) : State :=
 {s with
  pc := pcAfter pc (storeTemplate word)
  stack := rho
  memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded word.toNat 32) 0
  activeWords := s.activeWordsAfterUInt256 0 32}

theorem run_store (s : State) (pc word : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq (storeTemplate word) {s with pc := pc,stack := rho} =
      some (stored s pc word rho) := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length+n<1024 := by omega
  simp (discharger := omega) [storeTemplate, stored, runInstrSeq,DataStepper.runInstr,pcAfter,hrun,
    UInt256.succ,Instr.size,Nat.add_assoc,Word.literal_eq_ofNat,show rho.length<1024 by omega,hcap]
  repeat first | apply And.intro | rfl

theorem store_pc (pc word : UInt256) :
    pcAfter pc (storeTemplate word) = UInt256.add (UInt256.ofNat 24) pc := by
  have hadd (a b : UInt256) : a+b = UInt256.add a b := rfl
  simp [pcAfter,storeTemplate,Instr.size,UInt256.succ]
  simp only [hadd,RawExpressionAC.add_assoc]
  rw [RawExpressionAC.add_comm pc]
  rfl

#print axioms run_store
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectDigestRaw
