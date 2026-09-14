import Challenge.Modexp.Submission.Proofs.Fast.TnCacheSetupEntry

set_option warningAsError true
set_option maxHeartbeats 1000000

/-!
# The kernel setup entry (60 instructions)

`load` (24) · `shuffle` (11) · `low` (3) · `zero` (13: `MCOPY` staging + `CALLDATACOPY`
zeroing) · `pointersJump` (9, ending `DUP2; JUMP` to the row head `hd`).
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.StagedOperand
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached

def fullEntryProgram : List Instr := TnCacheSetup.fullEntryProgram

theorem fullEntryProgram_length : fullEntryProgram.length = 59 := rfl

/-- The whole `setup`: from `setupState` (pc 4116, `[hd, pa, pb, dst, ret] ++ rest`) to the
row-0 head at `hd` with the staged, zeroed memory and `ent = l1Target n`. -/
theorem run_entry (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hpaFit : pa+32*n ≤ 2816)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 2816)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32*n-32))
    (htarget : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    runInstructions fullEntryProgram (setupState s mem hd pa pb dst ret rest) =
    some (outState s (mpZeroed s (stage mem pa n) n) pb n 0 hd (l1Target n)
      (MachineState.readWord mem 2720) (MachineState.readWord mem (32*n-32))
      (MachineState.readWord mem 2784 :: MachineState.readWord mem 96 ::
        MachineState.readWord mem 64 :: MachineState.readWord mem 32 ::
        UInt256.ofNat (pa+32*n-32) :: dst :: ret :: rest)) := by
  have g := TnCacheSetup.run_entry s mem hd pa pb n dst ret rest hcap hact hn hn32
    hpaFit hpb hpbFit hcds hs32 hml htarget
  simpa only [fullEntryProgram, setupState, outState, l1Target, l2Target,
    TnCacheSetup.setupState, TnCacheSetup.outState, TnCacheSetup.l1Target,
    TnCacheSetup.l2Target, TnCacheSetup.zeroTn] using g

end Challenge.Modexp.Submission.Proofs.Fast.StagedOperand
