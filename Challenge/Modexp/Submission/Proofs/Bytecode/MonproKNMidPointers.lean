import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMidDefs

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMidPointers

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel MonproKNCache MonproKNRowPrograms MonproKNMidDefs
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem run_words (s : State) (ml tl c0 mu bi pbi paEnd pbEnd dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1007) (hact : 296 ≤ s.activeWords.toNat)
    (hml : MachineState.readWord s.memory 9408 = ml)
    (htl : MachineState.readWord s.memory 9440 = tl) :
    runInstructions pointersProgram
      (framed s (UInt256.ofNat 2061) ([c0, mu] ++ baseStack bi pbi paEnd pbEnd dst ret rest)) =
    some (framed s (UInt256.ofNat 2077)
      ([ml-UInt256.ofNat 32, tl-UInt256.ofNat 32, c0, mu] ++
        baseStack bi pbi paEnd pbEnd dst ret rest)) := by
  have hc10 : rest.length+10 < 1024 := by omega
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  have hc13 : rest.length+13 < 1024 := by omega
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h9408 : (9408 : UInt256).toNat = 9408 := by decide
  have h9440 : (9440 : UInt256).toNat = 9440 := by decide
  have hactML : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9408 32) =
      s.activeWords := activeWords_fix s 9408 32 (by decide) (by omega) hact
  have hactTL : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9440 32) =
      s.activeWords := activeWords_fix s 9440 32 (by decide) (by omega) hact
  simp [pointersProgram, midProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    baseStack, framed, hc10, hc11, hc12, hc13, h32, h9408, h9440, hml, htl,
    hactML, hactTL, List.exchange, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_pointers (s : State) (n : Nat) (bi pbi paEnd pbEnd dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1007) (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hml : MachineState.readWord s.memory 9408 = UInt256.ofNat (32*n-32))
    (htl : MachineState.readWord s.memory 9440 = UInt256.ofNat (8224+32*n)) :
    runInstructions pointersProgram (product s n bi pbi paEnd pbEnd dst ret rest) =
      some (result s n bi pbi paEnd pbEnd dst ret rest) := by
  have hsubTL : UInt256.ofNat (8224+32*n) - UInt256.ofNat 32 = UInt256.ofNat (8192+32*n) := by
    rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)]
    exact congrArg UInt256.ofNat (by omega)
  have hsubML : UInt256.ofNat (32*n-32) - UInt256.ofNat 32 = UInt256.ofNat (32*n-64) := by
    rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)]
    exact congrArg UInt256.ofNat (by omega)
  simpa only [product, result, hsubTL, hsubML] using
    run_words s (UInt256.ofNat (32*n-32)) (UInt256.ofNat (8224+32*n))
      (rowC0 s.memory n) (rowMu s.memory n) bi pbi paEnd pbEnd dst ret rest hcap hact hml htl

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMidPointers
