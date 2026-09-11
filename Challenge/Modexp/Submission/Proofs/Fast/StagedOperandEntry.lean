import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandEntryPrefix
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandEntryZero

set_option warningAsError true
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.StagedOperand
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached

def fullEntryProgram : List Instr :=
  (EntryPrefix.loadProgram ++ EntryPrefix.shuffleProgram) ++ (zeroProgram ++ pointersProgram)

theorem run_entry (s : State) (mem : ByteArray) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (_hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32*n-32)) :
    runInstructions fullEntryProgram (entryState s mem pa pb dst ret rest) =
    some {outState s (mpZeroed s (stage mem pa n) n) pa pb n 0
      (MachineState.readWord mem 9376) (MachineState.readWord mem (32*n-32))
      (MachineState.readWord mem 9440 :: MachineState.readWord mem 96 :: MachineState.readWord mem 64 :: MachineState.readWord mem 32 :: MachineState.readWord mem (pa+32*n-32) :: dst :: ret :: rest) with pc := UInt256.ofNat 4160} := by
  let tl := MachineState.readWord mem 9440
  let inv := MachineState.readWord mem 9376
  let m0 := MachineState.readWord mem (32*n-32)
  let aEnd := MachineState.readWord mem (pa+32*n-32)
  let m96 := MachineState.readWord mem 96
  let m64 := MachineState.readWord mem 64
  let m32 := MachineState.readWord mem 32
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest).length ≤ 1005 := by simp only [List.length_cons]; omega
  have hAddr : (UInt256.ofNat pa + UInt256.ofNat (32*n-32)).toNat = pa+32*n-32 := by
    rw [Challenge.EvmProof.Word.word_toNat_add,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (show pa < 2^256 by omega),
      Nat.mod_eq_of_lt (show 32*n-32 < 2^256 by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have hreads := EntryPrefix.run_load { s with memory := mem }
    (UInt256.ofNat pa) (UInt256.ofNat pb) dst ret rest (32*n-32)
    hcap hact (by omega) hml (by rw [hAddr]; omega)
  simp only [hAddr] at hreads
  have hshuffle := EntryPrefix.run_shuffle { s with memory := mem }
    (UInt256.ofNat pa) (UInt256.ofNat pb) dst ret m0 inv aEnd tl m96 m64 m32
    (EntryPrefix.displacement mem) rest hcap
  have hprefix := runInstructions_append_some _ _ _ _ _ hreads hshuffle
  have hmasked :
      runInstructions (EntryPrefix.loadProgram ++ EntryPrefix.shuffleProgram)
        (entryState s mem pa pb dst ret rest) =
      some {cachedEntryState s mem pa pb n inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest) with pc := UInt256.ofNat 4130} := by
    simpa only [entryState, cachedEntryState, EntryPrefix.displacement,
      hs32, l1Target, l2Target, isFour, tl, inv, m0, aEnd, m96, m64, m32,
      List.cons_append, List.nil_append] using hprefix
  have hzero := run_zero s mem pa pb n inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    hcap' hact (by omega) hn32 hpaFit hcds hs32
  have hpointers := CiosCached.run_pointers s (stage mem pa n) pa pb n inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    hcap' hpa hpaFit hpb hpbFit
  have hbody := runInstructions_append_some _ _ _ _ _ hzero hpointers
  exact runInstructions_append_some _ _ _ _ _ hmasked hbody

end Challenge.Modexp.Submission.Proofs.Fast.StagedOperand
