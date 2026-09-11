import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart08

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

theorem run_cachedLoadLow (s : State) (bi pbi pa pb flag target2 inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n ≤ 32)
    (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions cachedLoadLow
      (framed s (UInt256.ofNat 4562)
        (cacheStack bi pbi pa pb flag target2 (UInt256.ofNat (8224+32*n)) inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 4564)
      ([MachineState.readWord s.memory (8224+32*n)] ++
        cacheStack bi pbi pa pb flag target2 (UInt256.ofNat (8224+32*n)) inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hmod : (8224+32*n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8224+32*n := Nat.mod_eq_of_lt (by omega)
  have hactQ := activeWords_fix s (8224+32*n) 32 (by decide) (by omega) hact
  simp [cachedLoadLow, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, cacheStack, baseStack, Nat.add_assoc, hc17, hc18, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hmod, hactQ]

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
