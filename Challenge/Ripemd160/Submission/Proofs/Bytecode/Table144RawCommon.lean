import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144Raw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
structure Input where
  v0 : UInt256
  v1 : UInt256
  v2 : UInt256
  v3 : UInt256
  v4 : UInt256
  v5 : UInt256
  v6 : UInt256
  v7 : UInt256
  v8 : UInt256
  v9 : UInt256

def cache : List UInt256 := [28, 20282409598929303941081901039615, 127, 20282409608374036906834076368900, 15, 20282409608374036906851256238088]
def inputStack (x : Input) (rho : List UInt256) : List UInt256 :=
  [x.v0, x.v1, x.v2, x.v3, x.v4, x.v5, x.v6, x.v7, x.v8, x.v9] ++ (cache ++ rho)
@[simp] theorem cache_length : cache.length = 6 := rfl
theorem active_preserved (current : UInt256) (address : Nat)
    (hcurrent : 53 ≤ current.toNat) (haddress : address ≤ 1664) :
    UInt256.ofNat (MachineState.activeWordsAfter current.toNat address 32) = current := by
  have hwords : (address + 32 - 1) / 32 + 1 ≤ current.toNat := by omega
  simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
  change UInt256.ofNat (max current.toNat ((address + 32 - 1) / 32 + 1)) = current
  rw [Nat.max_eq_left hwords]
  exact (Word.word_eq_ofNat_toNat current).symm
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144Raw
