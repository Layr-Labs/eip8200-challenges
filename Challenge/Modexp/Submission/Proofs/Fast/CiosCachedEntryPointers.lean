import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedEntryPointerWords

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 200000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCached

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem run_pointers (s : State) (mem : ByteArray) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (_hpa : 32 ≤ pa) (_hpaFit : pa+32*n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472) :
    runInstructions pointersProgram (clearedState s mem pa pb n dst ret rest) =
      some (outState s (mpZeroed s mem n) pa pb n 0 dst ret rest) := by
  have hsub1 : UInt256.ofNat (pb+32*n) - UInt256.ofNat 32 = UInt256.ofNat (pb+32*n-32) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)
  have hsub2 : UInt256.ofNat pb - UInt256.ofNat 32 = UInt256.ofNat (pb-32) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)
  have hp0 : ptrAt (pb+32*n-32) 0 = pb+32*n-32 := by simp [ptrAt]
  have h := CiosCachedEntryPointerWords.run_words { s with memory := mpZeroed s mem n } (UInt256.ofNat (32*n))
    (UInt256.ofNat pa) (UInt256.ofNat pb) (l1Target n) (l2Target n) dst (ret :: rest) (by simp only [List.length_cons]; omega)
  simpa only [List.cons_append, List.nil_append, clearedState, outState, CiosCachedMacCore.framed, hp0, Challenge.EvmProof.Word.ofNat_add_mod,
    hsub1, hsub2] using h

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
