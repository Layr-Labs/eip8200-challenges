import Challenge.Ripemd160.Submission.H39Memo.DispatchState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputData

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.H39Memo.A1000
open EvmSemantics EvmSemantics.EVM DispatchState

abbrev cacheWord := Proofs.Bytecode.KnownInputData.fullWord
abbrev tailWord := Proofs.Bytecode.KnownInputData.finalWord

def entry (s : State) : State := atPC s 3115 [1000]
def cached (s : State) : State := atPC s 3157 [cacheWord, 1000]
def loop (s : State) (n : Nat) : State :=
  atPC s 3161 [UInt256.ofNat (32 * (n + 1)), cacheWord]
def checked (s : State) (n : Nat) : State :=
  atPC s 3170 [UInt256.ofNat (32 * (n + 1)), cacheWord]
def tailEntry (s : State) : State := atPC s 3183 [992, cacheWord]
def answerEntry (s : State) : State := atPC s 3224 []
def failEntry (s : State) (offset : UInt256) : State :=
  atPC s 3251 [offset, cacheWord]
def notAEntry (s : State) : State := atPC s 3258 [cacheWord, 1000]
def fallback (s : State) : State := atPC s 1006 []
def pattern (s : State) : State := atPC s 1696 [1000]

end Challenge.Ripemd160.Submission.H39Memo.A1000

