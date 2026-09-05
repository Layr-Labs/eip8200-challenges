import Challenge.Ripemd160.Submission.H39Memo.A1000PCs
import Challenge.Ripemd160.Submission.H39Memo.A1000Paths

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.A1000
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState

theorem run_firstPrefix (s : State) (input : ByteArray)
    (hinput : s.executionEnv.calldata = input) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock firstPrefix (entry s) =
      some (atPC s 3156 [3258,
        UInt256.xor cacheWord (MachineState.readWord input 0), cacheWord, 1000]) := by
  simp [firstPrefix, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, entry, atPC, hinput, hrun,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  rfl

theorem run_cache (s : State) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock cachePath (cached s) = some (loop s 0) := by
  simp [cachePath, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, cached, loop, atPC, hrun, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_loopPrefix (s : State) (input : ByteArray) (n : Nat) (hn : n < 30)
    (hinput : s.executionEnv.calldata = input) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock loopPrefix (loop s n) =
      some (atPC s 3169 [3251,
        UInt256.xor cacheWord (MachineState.readWord input (32 * (n + 1))),
        UInt256.ofNat (32 * (n + 1)), cacheWord]) := by
  have hoff : 32 * (n + 1) < 2 ^ 256 := by omega
  have hmod := Nat.mod_eq_of_lt hoff
  simp [loopPrefix, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, loop, atPC, hinput, hrun, hmod,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  exact congrArg (fun k => UInt256.xor cacheWord (MachineState.readWord input k)) hmod

end Challenge.Ripemd160.Submission.H39Memo.A1000
