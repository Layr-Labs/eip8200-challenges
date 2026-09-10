import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart02

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

theorem run_entryPrelude (s : State) (pa pb dst ret : UInt256) (n : Nat)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n ≤ 32)
    (hact : 296 ≤ s.activeWords.toNat)
    (hml : MachineState.readWord s.memory 9408 = UInt256.ofNat (32*n-32)) :
    runInstructions entryPrelude
      (framed s (UInt256.ofNat 4164) ([pa,pb,dst,ret] ++ rest)) =
    some (framed s (UInt256.ofNat 4195)
      ([pa,pb,MachineState.readWord s.memory 9376,MachineState.readWord s.memory (32*n-32),
        MachineState.readWord s.memory 9440,MachineState.readWord s.memory 96,
        MachineState.readWord s.memory 64,MachineState.readWord s.memory 32,
        pa + UInt256.ofNat (32*n-32),dst,ret] ++ rest)) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hp96 : (96 : UInt256).toNat = 96 := by decide
  have hp9440 : (9440 : UInt256).toNat = 9440 := by decide
  have hp9376 : (9376 : UInt256).toNat = 9376 := by decide
  have hp9408 : (9408 : UInt256).toNat = 9408 := by decide
  have hp64 : (64 : UInt256).toNat = 64 := by decide
  have hp32 : (32 : UInt256).toNat = 32 := by decide
  have hmod : (32*n-32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32*n-32 := Nat.mod_eq_of_lt (by omega)
  have hA := activeWords_fix s 9440 32 (by decide) (by omega) hact
  have hB := activeWords_fix s 9376 32 (by decide) (by omega) hact
  have hC := activeWords_fix s 9408 32 (by decide) (by omega) hact
  have hD := activeWords_fix s (32*n-32) 32 (by decide) (by omega) hact
  have hE := activeWords_fix s 64 32 (by decide) (by omega) hact
  have hF := activeWords_fix s 32 32 (by decide) (by omega) hact
  have hH := activeWords_fix s 96 32 (by decide) (by omega) hact
  simp [entryPrelude, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hp96, hp9440, hp9376, hp9408, hp64, hp32, hml,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat,
    hmod, hA, hB, hC, hD, hE, hF, hH, List.exchange]

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
