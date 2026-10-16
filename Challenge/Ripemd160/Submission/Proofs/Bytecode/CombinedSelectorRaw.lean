import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionAbsoluteSelectorRaw
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CombinedSelectorRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof StackRoundTrace

def selected (_codesize : UInt256) (size : Nat) : UInt256 :=
  UInt256.land (UInt256.div (UInt256.ofNat 4126384768455473537) (UInt256.ofNat size)) (UInt256.ofNat 8191)

def prefixTemplate : List Instr := [
 .push ⟨2, by decide⟩ (UInt256.ofNat 8191), .op .CALLDATASIZE,
 .push ⟨8, by decide⟩ (UInt256.ofNat 4126384768455473537), .op .DIV, .op .AND,
 .push ⟨1, by decide⟩ (UInt256.ofNat 32), .op (.Dup ⟨1, by decide⟩),
 .push ⟨0, by decide⟩ (UInt256.ofNat 0)]

def jumpTemplate : List Instr := [.push ⟨1, by decide⟩ (UInt256.ofNat 32), .op .ADD, .op .JUMP]

private theorem hadd_eq (a b : UInt256) : a+b = UInt256.add a b := rfl
private theorem hdiv_eq (a b : UInt256) : a/b = UInt256.div a b := rfl

theorem run_prefix (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq prefixTemplate {s with pc := pc,stack := rho} =
    some {s with
      pc := pcAfter pc prefixTemplate
      stack := 0 :: selected (UInt256.ofNat s.executionEnv.code.size) s.executionEnv.calldata.size :: 32 ::
        selected (UInt256.ofNat s.executionEnv.code.size) s.executionEnv.calldata.size :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length+n<1024 := by omega
  simp (discharger := omega) [prefixTemplate, selected, runInstrSeq, DataStepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, show rho.length<1024 by omega,hcap,
    Word.word_toNat_ofNat,Word.literal_eq_ofNat,hdiv_eq]
  repeat first | apply And.intro | rfl

theorem run_jump (s : State) (pc src : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hv : Decode.isValidJumpDest s.executionEnv.code (UInt256.add (UInt256.ofNat 32) src).toNat = true) :
    runInstrSeq jumpTemplate {s with pc := pc,stack := src::rho} =
      some {s with pc := UInt256.add (UInt256.ofNat 32) src,stack := rho} := by
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length+n<1024 := by omega
  simp (discharger := omega) [jumpTemplate, runInstrSeq,DataStepper.runInstr,pcAfter,hrun,
    UInt256.succ,Instr.size,Nat.add_assoc,Word.literal_eq_ofNat,hcap,hadd_eq,hv]

#print axioms run_prefix
#print axioms run_jump
end Challenge.Ripemd160.Submission.Proofs.Bytecode.CombinedSelectorRaw
