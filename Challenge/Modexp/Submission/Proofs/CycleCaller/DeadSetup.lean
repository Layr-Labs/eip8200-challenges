import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.Prepared.SetupPrefix
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SetupEntry

open CycleSubmission.SharedStackArgs

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

/-!
# The kernel setup entry with the unread frame words zeroed

`Fast.TnM128Setup.oldFullEntryProgram` loads seven words into the caller frame that no square or
product kernel of this artifact ever reads (`m96`, `tl`, `m0`, `m64`, the row-end pointer
`aprev`, `m32`, and the `DUP9`-addressed `m0` limb): they ride below the working stack until
`RETURN`.  This variant pushes `0` for each of them instead (`PUSH0`, padded with `JUMPDEST`s so
every instruction keeps its index; the freed bytes widen the `3347` literal to `PUSH10`).  All twelve padding `JUMPDEST`s are now gone: the seven zero
pushes come first and the `3347` literal is a `PUSH22`; the twelve instructions this removes are
given back by re-splitting the unreachable fillers at pc 3437 (`PUSH9 0` into ten `PUSH0`s) and
pc 3482 (`PUSH6` into `PUSH3` and three `MLOAD`s), so every instruction index from 2712
(pc 3493) on is unchanged.  The
`shuffle`, `low`, `zero` and `pointersJump` parts are the inherited ones.
-/

namespace CycleSubmission.DeadSetup
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached StagedOperand
open Challenge.Modexp.Submission.Proofs.Fast.TnM128Setup

def loadProgram : List Instr :=
  [.push 0 0, .push 0 0, .push 0 0, .push 0 0, .push 0 0, .push 0 0, .push 0 0,
   .push 22 3347]

def oldFullEntryProgram : List Instr :=
  ((loadProgram ++ EntryPrefix.shuffleProgram) ++ EntryPrefix.lowProgram) ++
    (zeroProgram ++ pointersJumpProgram)

theorem oldFullEntryProgram_length : oldFullEntryProgram.length = 39 := rfl

theorem run_load (s : State) (hd pa pb dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) :
    runInstructions loadProgram
      {s with pc := UInt256.ofNat 3182, stack := [hd, pa, pb, dst, ret] ++ rest} =
    some {s with
        pc := UInt256.ofNat 3212
        stack := [UInt256.ofNat 3347, UInt256.ofNat 0, zeroTn, UInt256.ofNat 0, UInt256.ofNat 0,
          UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, hd, pa, pb, dst, ret] ++ rest} := by
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  simp [loadProgram, zeroTn, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    capacity, Nat.add_assoc, hz,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, ← word_add_assoc]
  try exact ⟨rfl, rfl⟩

theorem old_run_entry_sq (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hpaFit : pa+32*n ≤ 2816)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 2816)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n))
    (htarget : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    runInstructions oldFullEntryProgram (TnM128Setup.setupState s mem hd pa pb dst ret rest) =
    some (TnM128Setup.outState s (SquarePartialClear.memory (stageW mem pa n)) pb n 0 hd (UInt256.ofNat 3347)
      (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0)
      (UInt256.ofNat 0 :: UInt256.ofNat 0 ::
        MachineState.readWord mem 2720 :: zeroTn ::
        UInt256.ofNat 0 :: dst :: ret :: rest)) := by
  let z : UInt256 := UInt256.ofNat 0
  let inv := MachineState.readWord mem 2720
  have hcap' : (z :: z :: inv :: zeroTn :: z :: dst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  have hreads := run_load { s with memory := mem } hd
    (UInt256.ofNat pa) (UInt256.ofNat pb) dst ret rest hcap
  have hshuffle := EntryPrefix.run_shuffle { s with memory := mem } hd
    (UInt256.ofNat pa) (UInt256.ofNat pb) dst ret z z z z z zeroTn z
    (UInt256.ofNat 3347) rest hcap hact
  have hlow := EntryPrefix.run_low { s with memory := mem } hd
    (UInt256.ofNat pa) (UInt256.ofNat pb)
    (UInt256.ofNat 3347)
    (MachineState.readWord mem 128)
    dst ret z z z z z zeroTn z rest hcap hact
  have hprefix := runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _ hreads hshuffle) hlow
  have hmasked :
      runInstructions ((loadProgram ++ EntryPrefix.shuffleProgram) ++
          EntryPrefix.lowProgram)
        (TnM128Setup.setupState s mem hd pa pb dst ret rest) =
      some (cachedSetupStateSq s mem hd pa pb n z z z
        (z :: z :: inv :: zeroTn :: z :: dst :: ret :: rest)) := by
    simpa only [TnM128Setup.setupState, cachedSetupStateSq, inv, z,
      List.cons_append, List.nil_append] using hprefix
  have hzero := run_zero_sq s mem hd pa pb n z z z
    (z :: z :: inv :: zeroTn :: z :: dst :: ret :: rest)
    hcap' hact (by omega) hn32 hpaFit hcds hs32
  have hpointers := run_pointersJump_sq s (stageW mem pa n) hd pb n z z z
    (z :: z :: inv :: zeroTn :: z :: dst :: ret :: rest)
    hcap' hpb hpbFit hn32 htarget
  have hbody := runInstructions_append_some _ _ _ _ _ hzero hpointers
  exact runInstructions_append_some _ _ _ _ _ hmasked hbody

def newTailProgram : List Instr :=
  [.op (.Dup dA1),
   .op (.Dup dA0),
   .op .ADD,
   .push 2 1856,
   .op .ADD,
   .op .MCOPY,
   .op (.Swap sA1),
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD,
   .op (.Swap sA1),
   .op (.Swap sA0),
   .op (.Dup dA2),
   .op .ADD,
   .op (.Dup dA1),
   .op .JUMP]

def fullEntryProgram : List Instr :=
  Prepared.SetupPrefix.newProgram ++ newTailProgram

theorem fullEntryProgram_length : fullEntryProgram.length = 33 := rfl

private theorem run_tail_eq (s : State) (hd pa pb dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) :
    runInstructions newTailProgram (Prepared.SetupPrefix.newModel s hd pa pb dst ret rest) =
    runInstructions (oldFullEntryProgram.drop 23) (Prepared.SetupPrefix.oldModel s hd pa pb dst ret rest) := by
  have capacity (j : Nat) (hj : j ≤ 25) : rest.length + j < 1024 := by omega
  have hn32 : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 = UInt256.lnot (UInt256.ofNat 31) := by decide
  have hn32Cast : (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) = UInt256.lnot (31 : UInt256) := by decide
  simp [newTailProgram, oldFullEntryProgram, loadProgram,
    EntryPrefix.shuffleProgram, EntryPrefix.lowProgram, zeroProgram, stageProgram, clearProgram,
    pointersJumpProgram, Prepared.SetupPrefix.newModel, Prepared.SetupPrefix.oldModel,
    runInstructions, Challenge.EvmProof.Stepper.runInstr, capacity, Nat.add_assoc, List.exchange, hn32, hn32Cast, State.activeWordsAfterUInt256_2]

theorem full_run_eq (s : State) (hd pa pb dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hw : rest[1]? = some (MachineState.readWord s.memory 2688)) :
    runInstructions fullEntryProgram {s with pc := UInt256.ofNat 3203, stack := hd :: pa :: pb :: dst :: ret :: rest} =
    runInstructions oldFullEntryProgram {s with pc := UInt256.ofNat 3182, stack := hd :: pa :: pb :: dst :: ret :: rest} := by
  change runInstructions (Prepared.SetupPrefix.newProgram ++ newTailProgram) _ =
    runInstructions (Prepared.SetupPrefix.oldProgram ++ oldFullEntryProgram.drop 23) _
  simp only [runInstructions_append, Prepared.SetupPrefix.new_run s hd pa pb dst ret rest hcap hact hw,
    Prepared.SetupPrefix.old_run s hd pa pb dst ret rest hcap hact, Option.bind_some]
  exact run_tail_eq s hd pa pb dst ret rest hcap

theorem run_entry_sq (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hpaFit : pa+32*n ≤ 2816)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 2816)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n))
    (hw : rest[1]? = some (UInt256.ofNat (32*n)))
    (htarget : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    runInstructions fullEntryProgram ({ TnM128Setup.setupState s mem hd pa pb dst ret rest with pc := UInt256.ofNat 3203 }) =
    some (TnM128Setup.outState s (SquarePartialClear.memory (stageW mem pa n)) pb n 0 hd (UInt256.ofNat 3347)
      (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0)
      (UInt256.ofNat 0 :: UInt256.ofNat 0 ::
        MachineState.readWord mem 2720 :: zeroTn ::
        UInt256.ofNat 0 :: dst :: ret :: rest)) := by
  have h := full_run_eq {s with memory := mem} hd (UInt256.ofNat pa) (UInt256.ofNat pb) dst ret rest hcap hact
    (by rw [hw]; exact congrArg some hs32.symm)
  change runInstructions fullEntryProgram _ = runInstructions oldFullEntryProgram _ at h
  rw [show runInstructions fullEntryProgram ({ TnM128Setup.setupState s mem hd pa pb dst ret rest with pc := UInt256.ofNat 3203 }) =
    runInstructions oldFullEntryProgram (TnM128Setup.setupState s mem hd pa pb dst ret rest) from h]
  exact old_run_entry_sq s mem hd pa pb n dst ret rest hcap hact hn hn32 hpaFit hpb hpbFit hcds hs32 htarget

#print axioms run_entry_sq
end CycleSubmission.DeadSetup
