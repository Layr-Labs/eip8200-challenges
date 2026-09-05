import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreFinish
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWrapperValue
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreGas

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreBridge

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof

private theorem step_returnParams (s : State) (a b modulus : UInt256) (n i : Nat)
    (np ret : UInt256) (rest : List UInt256) :
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.step s a b modulus n i np ret rest =
      Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.step s a b modulus n i np 0 [] := rfl

theorem progress_returnParams (s : State) (a b modulus : UInt256) (n : Nat)
    (np ret : UInt256) (rest : List UInt256) (i : Nat) :
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s a b modulus n np ret rest i =
      Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s a b modulus n np 0 [] i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      change Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.step (Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s a b modulus n np ret rest i)
          a b modulus n i np ret rest =
        Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.step (Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s a b modulus n np 0 [] i)
          a b modulus n i np 0 []
      rw [ih]
      exact step_returnParams _ a b modulus n i np ret rest

theorem finish_returnParams (s : State) (out modulus : UInt256) (n : Nat)
    (reduceRet : UInt256) (reduceRest : List UInt256)
    (copyRet : UInt256) (copyRest : List UInt256) :
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.finishLeaf s out modulus n reduceRet reduceRest copyRet copyRest =
      Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.finishLeaf s out modulus n 0 [] 0 [] := rfl

theorem coreLeaf_returned (s : State) (aPtr bPtr out n : Nat) (np ret : UInt256)
    (rest : List UInt256) (reduceRet : UInt256) (reduceRest : List UInt256)
    (copyRet : UInt256) (copyRest : List UInt256) :
    { Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.finishLeaf
        (Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s (UInt256.ofNat aPtr) (UInt256.ofNat bPtr) 0 n np ret rest n)
        (UInt256.ofNat out) 0 n reduceRet reduceRest copyRet copyRest with
        pc := ret, stack := rest } =
      { Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWrapperValue.coreLeaf s aPtr bPtr out n np with pc := ret, stack := rest } := by
  rw [progress_returnParams, finish_returnParams]
  rfl

private theorem smallWord (n : Nat) (h : n ≤ 8192) : (UInt256.ofNat n).toNat = n := by
  change n % (2^256) = n
  exact Nat.mod_eq_of_lt (by omega)

/-- The real public core execution certificate, matched to the frozen flat leaf. -/
def gasSteps_coreLeaf (s : State) (aPtr bPtr out n : Nat) (np ret : UInt256)
    (rest : List UInt256) (hN : n ≤ 32) (haPtr : aPtr ≤ 8192) (hbPtr : bPtr ≤ 8192)
    (hcap : rest.length + 8 < 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hret : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true) :
    GasSteps (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock.coreEntry s (UInt256.ofNat aPtr) (UInt256.ofNat bPtr)
        (UInt256.ofNat out) 0 n np ret rest)
      { Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWrapperValue.coreLeaf s aPtr bPtr out n np with pc := ret, stack := rest } := by
  have hnWord := smallWord n (by omega)
  have haWord := smallWord aPtr haPtr
  have hbWord := smallWord bPtr hbPtr
  have cert := Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreGas.gasSteps_core s (UInt256.ofNat aPtr) (UInt256.ofNat bPtr)
    (UInt256.ofNat out) 0 (UInt256.ofNat n) np ret rest
    (by rw [hnWord]; exact hN) hcap
    (by rw [haWord, hnWord]; change aPtr + 32*n < 2^256; omega)
    (by rw [hbWord, hnWord]; change bPtr + 32*n < 2^256; omega)
    (by rw [hnWord]; change 0 + 32*n < 2^256; omega)
    hcode hfork hrun hnp hret
  simp only [Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreFinish.finishReturned, hnWord] at cert
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreBridge.coreLeaf_returned] at cert
  simpa only [Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock.coreEntry, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver.entry, Challenge.EvmProof.Word.literal_eq_ofNat] using cert

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreBridge
