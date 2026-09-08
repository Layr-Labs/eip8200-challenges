import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMidDefs

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMidStore

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel MonproKNCache MonproKNRowPrograms MonproKNMidDefs
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem run_store (s : State) (paj ptj c bi pbi paEnd pbEnd dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1007) (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions storeProgram (input s paj ptj c bi pbi paEnd pbEnd dst ret rest) =
      some (stored s c bi pbi paEnd pbEnd dst ret rest) := by
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have h8192 : (8192 : UInt256).toNat = 8192 := by decide
  have hactN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 8224 32) =
      s.activeWords := activeWords_fix s 8224 32 (by decide) (by omega) hact
  have hactP : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 8192 32) =
      s.activeWords := activeWords_fix s 8192 32 (by decide) (by omega) hact
  simp [storeProgram, midProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    input, stored, baseStack, framed, midMem, midMem1,
    hc9, hc10, hc11, hc12, h8224, h8192, hactN, hactP,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMidStore
