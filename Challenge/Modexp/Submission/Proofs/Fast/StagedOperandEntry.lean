import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandEntryPrefix
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandEntryZero

set_option warningAsError true
set_option maxHeartbeats 1000000

/-!
# The kernel `setup` (pc 3948 = 0x0f6c, instructions 2978..3039, 62 instructions)

`load` (24) · `shuffle` (11) · `low` (3) · `zero` (13: `MCOPY` staging + `CALLDATACOPY`
zeroing) · `pointersJump` (11, ending `DUP2; JUMP` to the row head `hd`).
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.StagedOperand
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached

def fullEntryProgram : List Instr :=
  ((EntryPrefix.loadProgram ++ EntryPrefix.shuffleProgram) ++ EntryPrefix.lowProgram) ++
    (zeroProgram ++ pointersJumpProgram)

theorem fullEntryProgram_length : fullEntryProgram.length = 62 := rfl

/-- The whole `setup`: from `setupState` (pc 3948, `[hd, pa, pb, dst, ret] ++ rest`) to the
row-0 head at `hd` with the staged, zeroed memory and `ent = l1Target n`. -/
theorem run_entry (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hpaFit : pa+32*n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32*n-32))
    (htarget : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    runInstructions fullEntryProgram (setupState s mem hd pa pb dst ret rest) =
    some (outState s (mpZeroed s (stage mem pa n) n) pb n 0 hd (l1Target n)
      (MachineState.readWord mem 9376) (MachineState.readWord mem (32*n-32))
      (MachineState.readWord mem 9440 :: MachineState.readWord mem 96 ::
        MachineState.readWord mem 64 :: MachineState.readWord mem 32 ::
        UInt256.ofNat (pa+32*n-32) :: dst :: ret :: rest)) := by
  let tl := MachineState.readWord mem 9440
  let inv := MachineState.readWord mem 9376
  let m0 := MachineState.readWord mem (32*n-32)
  let aEnd := UInt256.ofNat (pa+32*n-32)
  let m96 := MachineState.readWord mem 96
  let m64 := MachineState.readWord mem 64
  let m32 := MachineState.readWord mem 32
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  have hreads := EntryPrefix.run_load { s with memory := mem } hd
    (UInt256.ofNat pa) (UInt256.ofNat pb) dst ret rest (32*n-32)
    hcap hact (by omega) hml
  have hAend : UInt256.ofNat pa + UInt256.ofNat (32*n-32) = aEnd := by
    dsimp [aEnd]
    rw [Challenge.EvmProof.Word.ofNat_add_mod]
    congr 1
    omega
  rw [hAend] at hreads
  have hshuffle := EntryPrefix.run_shuffle { s with memory := mem } hd
    (UInt256.ofNat pa) (UInt256.ofNat pb) dst ret m0 inv aEnd tl m96 m32
    (EntryPrefix.displacement mem) rest hcap
  have hlow := EntryPrefix.run_low { s with memory := mem } hd
    (UInt256.ofNat pa) (UInt256.ofNat pb)
    (UInt256.ofNat 4068 + EntryPrefix.displacement mem)
    (UInt256.ofNat 4367 + EntryPrefix.displacement mem)
    dst ret m0 inv aEnd tl m96 m32 rest hcap hact
  have hprefix := runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _ hreads hshuffle) hlow
  have hmasked :
      runInstructions ((EntryPrefix.loadProgram ++ EntryPrefix.shuffleProgram) ++
          EntryPrefix.lowProgram)
        (setupState s mem hd pa pb dst ret rest) =
      some (cachedSetupState s mem hd pa pb n inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
    simpa only [setupState, cachedSetupState, EntryPrefix.displacement,
      hs32, l1Target, l2Target, isFour, tl, inv, m0, aEnd, m96, m64, m32,
      List.cons_append, List.nil_append] using hprefix
  have hzero := run_zero s mem hd pa pb n inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    hcap' hact (by omega) hn32 hpaFit hcds hs32
  have hpointers := run_pointersJump s (stage mem pa n) hd pb n inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    hcap' hpb hpbFit htarget
  have hbody := runInstructions_append_some _ _ _ _ _ hzero hpointers
  exact runInstructions_append_some _ _ _ _ _ hmasked hbody

end Challenge.Modexp.Submission.Proofs.Fast.StagedOperand
