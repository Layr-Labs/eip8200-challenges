import Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
import Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Entry

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# CIOS2 specialized prologue

The specialized entry is MONPRO prologue with one cached decrement constant.
The constant is inserted below pa/pb and removed at the final CSUB jump.  This certificate connects the width dispatcher to the row loop.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Entry

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Entry

def outState (s : State) (mem : ByteArray) (pa pb n i : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4150
           stack := [UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32),
                     (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256), pdst, ret] ++ rest
           memory := mem }

set_option linter.unusedSimpArgs false in
theorem run_entry (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n)) :
    Challenge.EvmProof.Stepper.runLocatedBlock cios2Entry
      (specializedEntryState s mem pa pb pdst ret rest) =
      some (outState s (mpZeroed s mem n) pa pb n 0 pdst ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hK : (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) = UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 := by decide
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h64 : (64 : UInt256) = UInt256.ofNat 64 := by decide
  have h8192 : (8192 : UInt256).toNat = 8192 := by decide
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  have hsizeN : (64 + 32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      64 + 32 * n := Nat.mod_eq_of_lt (by omega)
  have hcdsN : s.executionEnv.calldata.size %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      s.executionEnv.calldata.size := Nat.mod_eq_of_lt (by omega)
  have hsub1 : UInt256.ofNat (pb + 32 * n) - UInt256.ofNat 32 =
      UInt256.ofNat (pb + 32 * n - 32) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)
  have hsub2 : UInt256.ofNat pb - UInt256.ofNat 32 = UInt256.ofNat (pb - 32) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)
  have hsub3 : UInt256.ofNat pa - UInt256.ofNat 32 = UInt256.ofNat (pa - 32) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)
  have hactS : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9344 32) = s.activeWords :=
    activeWords_fix s 9344 32 (by decide) (by omega) hact
  have hactC : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 8192 (64 + 32 * n)) =
      s.activeWords := activeWords_fix s 8192 (64 + 32 * n) (by omega) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [cios2Entry, Cios2Paths.Entry.entryPC, Cios2Paths.Entry.startIndex,
      Cios2Paths.Entry.opAt, Cios2Paths.Entry.pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      specializedEntryState, outState, mpZeroed, fastPC10,
      hc4, hc5, hc6, hc7, hc8, hc9, hrun, hK, h32, h64, h8192, h9344, hs32,
      hsizeN, hcdsN, hsub1, hsub2, hsub3, hactS, hactC,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

def gasSteps_entry (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n)) :
    Challenge.EvmProof.GasSteps
      (specializedEntryState s mem pa pb pdst ret rest)
      (outState s (mpZeroed s mem n) pa pb n 0 pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka cios2Entry hcode hfork
    (run_entry s mem pa pb n pdst ret rest hcap hrun hact hn hn32 hpa hpaFit
      hpb hpbFit hcds hs32) hrun hnp

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Entry
