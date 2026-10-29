import Challenge.Modexp.Submission.Proofs.CycleGlobal.TnShiftPrefix
import Challenge.Modexp.Submission.Proofs.CycleGlobal.TnShiftZero

set_option warningAsError true
set_option maxHeartbeats 1000000

/-!
# The kernel setup entry (54 instructions)

`load` (20) · `shuffle` (8) · `low` (3) · `zero` (13: `MCOPY` staging + scratch-word `MSTORE`
zeroing) · `pointersJump` (10, ending `DUP2; JUMP` to the row head `hd`).
-/

namespace CycleSubmission.Global.TnShift
open Challenge.Modexp.Submission.Proofs Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached StagedOperand

def fullEntryProgram : List Instr :=
  ((EntryPrefix.loadProgram ++ EntryPrefix.shuffleProgram) ++ EntryPrefix.lowProgram) ++
    (zeroProgram ++ pointersJumpProgram)

theorem fullEntryProgram_length : fullEntryProgram.length = 54 := rfl

theorem run_entry (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hn4 : n = 4 ∨ n = 8)
    (hpaFit : pa+32*n ≤ 2816)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 2816)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32*n-32))
    (hw : rest[1]? = some (UInt256.ofNat (32*n)))
    (_hslot : rest[2]? = some (MachineState.readWord mem 2688))
    (htarget : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    runInstructions fullEntryProgram (setupState s mem hd pa pb dst ret rest) =
    some (outState s (SquarePartialClear.memory (stageW mem pa n)) pb n 0 hd (l1Target n)
      (MachineState.readWord mem 32) (MachineState.readWord mem 64) (MachineState.readWord mem (16*n+32))
      (MachineState.readWord mem 224 :: MachineState.readWord mem 96 ::
        MachineState.readWord mem 2720 :: zeroTn ::
        UInt256.ofNat (pa+32*n-32) :: dst :: ret :: rest)) := by
  let tl := MachineState.readWord mem 224
  let inv := MachineState.readWord mem 2720
  let m0 := MachineState.readWord mem (16*n+32)
  let aEnd := UInt256.ofNat (pa+32*n-32)
  let m96 := MachineState.readWord mem 96
  let m64 := MachineState.readWord mem 64
  let m32 := MachineState.readWord mem 32
  have hcap' : (tl :: m96 :: inv :: zeroTn :: aEnd :: dst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  have hreads := EntryPrefix.run_load { s with memory := mem } hd
    (UInt256.ofNat pa) (UInt256.ofNat pb) dst ret rest (32*n-32) n
    hcap hact (by omega) hn4 hml hw
  have hAend : UInt256.ofNat pa + UInt256.ofNat (32*n-32) = aEnd := by
    dsimp [aEnd]
    rw [Challenge.EvmProof.Word.ofNat_add_mod]
    congr 1
    omega
  rw [hAend] at hreads
  have hshuffle := EntryPrefix.run_shuffle { s with memory := mem } hd
    (UInt256.ofNat pa) (UInt256.ofNat pb) dst ret m0 m64 aEnd tl m96 zeroTn m32
    (UInt256.ofNat 3347) rest hcap hact
  have hlow := EntryPrefix.run_low { s with memory := mem } hd
    (UInt256.ofNat pa) (UInt256.ofNat pb)
    (UInt256.ofNat 3347)
    (MachineState.readWord mem 128)
    dst ret m0 m64 aEnd tl m96 zeroTn m32 rest hcap hact
  have hprefix := runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _ hreads hshuffle) hlow
  have hdisp1 : UInt256.ofNat 3347 = l1Target n := rfl
  have hmasked :
      runInstructions ((EntryPrefix.loadProgram ++ EntryPrefix.shuffleProgram) ++
          EntryPrefix.lowProgram)
        (setupState s mem hd pa pb dst ret rest) =
      some (cachedSetupState s mem hd pa pb n m32 m64 m0
        (tl :: m96 :: inv :: zeroTn :: aEnd :: dst :: ret :: rest)) := by
    simpa only [setupState, cachedSetupState, hdisp1,
      hs32, tl, inv, m0, aEnd, m96, m64, m32,
      List.cons_append, List.nil_append] using hprefix
  have hzero := run_zero s mem hd pa pb n m32 m64 m0
    (tl :: m96 :: inv :: zeroTn :: aEnd :: dst :: ret :: rest)
    hcap' hact (by omega) hn32 hpaFit hcds hs32
  have hpointers := run_pointersJump s (stageW mem pa n) hd pb n m32 m64 m0
    (tl :: m96 :: inv :: zeroTn :: aEnd :: dst :: ret :: rest)
    hcap' hpb hpbFit hn32 htarget
  have hbody := runInstructions_append_some _ _ _ _ _ hzero hpointers
  exact runInstructions_append_some _ _ _ _ _ hmasked hbody

theorem run_entry_sq (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hn4 : n = 4 ∨ n = 8)
    (hpaFit : pa+32*n ≤ 2816)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 2816)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32*n-32))
    (hw : rest[1]? = some (UInt256.ofNat (32*n)))
    (_hslot : rest[2]? = some (UInt256.ofNat n))
    (htarget : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    runInstructions fullEntryProgram (setupState s mem hd pa pb dst ret rest) =
    some (outState s (SquarePartialClear.memory (stageW mem pa n)) pb n 0 hd (UInt256.ofNat 3347)
      (MachineState.readWord mem 32) (MachineState.readWord mem 64) (MachineState.readWord mem (16*n+32))
      (MachineState.readWord mem 224 :: MachineState.readWord mem 96 ::
        MachineState.readWord mem 2720 :: zeroTn ::
        UInt256.ofNat (pa+32*n-32) :: dst :: ret :: rest)) := by
  let tl := MachineState.readWord mem 224
  let inv := MachineState.readWord mem 2720
  let m0 := MachineState.readWord mem (16*n+32)
  let aEnd := UInt256.ofNat (pa+32*n-32)
  let m96 := MachineState.readWord mem 96
  let m64 := MachineState.readWord mem 64
  let m32 := MachineState.readWord mem 32
  have hcap' : (tl :: m96 :: inv :: zeroTn :: aEnd :: dst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  have hreads := EntryPrefix.run_load { s with memory := mem } hd
    (UInt256.ofNat pa) (UInt256.ofNat pb) dst ret rest (32*n-32) n
    hcap hact (by omega) hn4 hml hw
  have hAend : UInt256.ofNat pa + UInt256.ofNat (32*n-32) = aEnd := by
    dsimp [aEnd]
    rw [Challenge.EvmProof.Word.ofNat_add_mod]
    congr 1
    omega
  rw [hAend] at hreads
  have hshuffle := EntryPrefix.run_shuffle { s with memory := mem } hd
    (UInt256.ofNat pa) (UInt256.ofNat pb) dst ret m0 m64 aEnd tl m96 zeroTn m32
    (UInt256.ofNat 3347) rest hcap hact
  have hlow := EntryPrefix.run_low { s with memory := mem } hd
    (UInt256.ofNat pa) (UInt256.ofNat pb)
    (UInt256.ofNat 3347)
    (MachineState.readWord mem 128)
    dst ret m0 m64 aEnd tl m96 zeroTn m32 rest hcap hact
  have hprefix := runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _ hreads hshuffle) hlow
  have hmasked :
      runInstructions ((EntryPrefix.loadProgram ++ EntryPrefix.shuffleProgram) ++
          EntryPrefix.lowProgram)
        (setupState s mem hd pa pb dst ret rest) =
      some (cachedSetupStateSq s mem hd pa pb n m32 m64 m0
        (tl :: m96 :: inv :: zeroTn :: aEnd :: dst :: ret :: rest)) := by
    simpa only [setupState, cachedSetupStateSq,
      hs32, tl, inv, m0, aEnd, m96, m64, m32,
      List.cons_append, List.nil_append] using hprefix
  have hzero := run_zero_sq s mem hd pa pb n m32 m64 m0
    (tl :: m96 :: inv :: zeroTn :: aEnd :: dst :: ret :: rest)
    hcap' hact (by omega) hn32 hpaFit hcds hs32
  have hpointers := run_pointersJump_sq s (stageW mem pa n) hd pb n m32 m64 m0
    (tl :: m96 :: inv :: zeroTn :: aEnd :: dst :: ret :: rest)
    hcap' hpb hpbFit hn32 htarget
  have hbody := runInstructions_append_some _ _ _ _ _ hzero hpointers
  exact runInstructions_append_some _ _ _ _ _ hmasked hbody

end CycleSubmission.Global.TnShift
