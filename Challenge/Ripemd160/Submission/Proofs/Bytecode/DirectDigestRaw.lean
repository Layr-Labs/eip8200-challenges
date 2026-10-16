import Challenge.Ripemd160.Submission.Proofs.Bytecode.CombinedSelectorRaw
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectDigestRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof StackRoundTrace
def selected (_codesize : UInt256) (size : Nat) : UInt256 :=
  UInt256.land (UInt256.div (UInt256.ofNat 34711266746334640) (UInt256.ofNat size)) (UInt256.ofNat 8191)

def prefixTemplate : List Instr := [
 .push ⟨2, by decide⟩ (UInt256.ofNat 8191), .op .CALLDATASIZE,
 .push ⟨7, by decide⟩ (UInt256.ofNat 34711266746334640), .op .DIV, .op .AND, .op .JUMP]

def storeTemplate (word : UInt256) : List Instr := [
 .op .JUMPDEST, .push ⟨20, by decide⟩ word,
 .push ⟨0, by decide⟩ (UInt256.ofNat 0), .op .MSTORE]

def stored (s : State) (pc word : UInt256) (rho : List UInt256) : State :=
 {s with
  pc := pcAfter pc (storeTemplate word)
  stack := rho
  memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded word.toNat 32) 0
  activeWords := s.activeWordsAfterUInt256 0 32}

private theorem hdiv_eq (a b : UInt256) : a/b = UInt256.div a b := rfl

theorem run_prefix (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hv : Decode.isValidJumpDest s.executionEnv.code
      (selected (UInt256.ofNat s.executionEnv.code.size) s.executionEnv.calldata.size).toNat = true) :
    runInstrSeq prefixTemplate {s with pc := pc,stack := rho} =
    some {s with pc := selected (UInt256.ofNat s.executionEnv.code.size) s.executionEnv.calldata.size,stack := rho} := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length+n<1024 := by omega
  simp (discharger := omega) [prefixTemplate, selected,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    Nat.add_assoc, hrun, show rho.length<1024 by omega,hcap,
    Word.word_toNat_ofNat,Word.literal_eq_ofNat,hdiv_eq] at hv ⊢
  rw [if_pos hv]

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

#print axioms run_prefix
#print axioms run_store
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectDigestRaw
