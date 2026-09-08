import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidWords

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000


namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidProduct

open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCached CiosCachedMidDefs
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

def loadMuProgram : List Instr :=
  [.push 2 9440, .op .MLOAD, .op .MLOAD, .push 2 9376, .op .MLOAD, .op .MUL]

def loadM0Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 2 9408, .op .MLOAD, .op .MLOAD]

theorem program_eq : productProgram =
    (loadMuProgram ++ loadM0Program) ++ CiosCachedMidWords.program := rfl

theorem run_loadMu (s : State) (n : Nat) (bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32)
    (htl : MachineState.readWord s.memory 9440 = UInt256.ofNat (8224+32*n)) :
    runInstructions loadMuProgram
      (framed s (UInt256.ofNat 4619) (baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4629)
      ([rowMu s.memory n] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) := by
  have hc8 : rest.length+9 < 1024 := by omega
  have hc9 : rest.length+10 < 1024 := by omega
  have hc10 : rest.length+11 < 1024 := by omega
  have h9376 : (9376 : UInt256).toNat = 9376 := by decide
  have h9440 : (9440 : UInt256).toNat = 9440 := by decide
  have hTLN : (8224+32*n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8224+32*n := Nat.mod_eq_of_lt (by omega)
  have hactTL : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9440 32) =
      s.activeWords := activeWords_fix s 9440 32 (by decide) (by omega) hact
  have hactT0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (8224+32*n) 32) =
      s.activeWords := activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactMI : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9376 32) =
      s.activeWords := activeWords_fix s 9376 32 (by decide) (by omega) hact
  simp [loadMuProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    baseStack, framed, rowMu, hc8, hc9, hc10, h9376, h9440, hTLN, htl,
    hactTL, hactT0, hactMI, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_loadM0 (s : State) (n : Nat) (mu bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32)
    (hml : MachineState.readWord s.memory 9408 = UInt256.ofNat (32*n-32)) :
    runInstructions loadM0Program
      (framed s (UInt256.ofNat 4629) ([mu] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4635)
      ([MachineState.readWord s.memory (32*n-32), mu, mu] ++
        baseStack bi pbi paEnd pbEnd flag dst ret rest)) := by
  have hc9 : rest.length+10 < 1024 := by omega
  have hc10 : rest.length+11 < 1024 := by omega
  have hc11 : rest.length+12 < 1024 := by omega
  have h9408 : (9408 : UInt256).toNat = 9408 := by decide
  have hMLN : (32*n-32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32*n-32 := Nat.mod_eq_of_lt (by omega)
  have hactML : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9408 32) =
      s.activeWords := activeWords_fix s 9408 32 (by decide) (by omega) hact
  have hactM0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat (32*n-32) 32) =
      s.activeWords := activeWords_fix s _ 32 (by decide) (by omega) hact
  simp [loadM0Program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    baseStack, framed, hc9, hc10, hc11, h9408, hMLN, hml, hactML, hactM0,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_product (s : State) (n : Nat) (bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat)
    (_hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hml : MachineState.readWord s.memory 9408 = UInt256.ofNat (32*n-32))
    (htl : MachineState.readWord s.memory 9440 = UInt256.ofNat (8224+32*n)) :
    runInstructions productProgram
      (framed s (UInt256.ofNat 4619) (baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (product s n bi pbi paEnd pbEnd flag dst ret rest) := by
  rw [program_eq]
  exact runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _
      (run_loadMu s n bi pbi paEnd pbEnd flag dst ret rest hcap hact hn32 htl)
      (run_loadM0 s n (rowMu s.memory n) bi pbi paEnd pbEnd flag dst ret rest hcap hact hn32 hml))
    (CiosCachedMidWords.run_words s (MachineState.readWord s.memory (32*n-32)) (rowMu s.memory n)
      bi pbi paEnd pbEnd flag dst ret rest hcap)

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidProduct
