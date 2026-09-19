import Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SetupZero
import Challenge.Modexp.Submission.Proofs.Fast.GenericReturnAdapter

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128PreclearEntry

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open WindowTwentyOneBinding WindowNibbleKernel

def bodyProgram : List Instr :=
  [.push 2 2688, .op .MLOAD, .push 1 64, .op .ADD,
   .op .CALLDATASIZE, .push 2 2048, .op .CALLDATACOPY,
   .push 2 3390, .op .JUMP]

def program : List Instr := GenericReturnAdapter.genericEntryPrefix ++ bodyProgram

def input (s : State) (mem : ByteArray) (pa pb _n : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with
      pc := UInt256.ofNat 5454
      stack := [UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
      memory := mem }

def bodyInput (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with
      pc := UInt256.ofNat 5461
      stack := [UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
      memory := mem }

def legacyState (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with
      pc := UInt256.ofNat 3390
      stack := [UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
      memory := mem }

theorem jumpDest :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5454 = true := by
  exact Artifact.isValidJumpDest_index 4378 (by rfl)

theorem run_body (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hact : 88 ≤ s.activeWords.toNat)
    (n : Nat) (hn4 : n = 4 ∨ n = 8) (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n))
    (htarget : Decode.isValidJumpDest s.executionEnv.code 3390 = true) :
    runInstructions bodyProgram (bodyInput s mem pa pb pdst ret rest) =
      some (legacyState s (mpZeroed s mem n) pa pb pdst ret rest) := by
  have hn8 : n ≤ 8 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hsizeN : (64 + 32*n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      64 + 32*n := Nat.mod_eq_of_lt (by omega)
  have hcdsN : s.executionEnv.calldata.size %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      s.executionEnv.calldata.size := Nat.mod_eq_of_lt hcds
  have hactS := activeWords_fix s 2688 32 (by decide) (by omega) hact
  have hactC := activeWords_fix s 2048 (64 + 32*n) (by omega) (by omega) hact
  have h64 : (64 : UInt256) = UInt256.ofNat 64 := by decide
  simp (config := { maxSteps := 200000 })
    [bodyProgram, bodyInput, legacyState, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      mpZeroed, hs32, State.activeWordsAfterUInt256, hactS, hactC,
      h64, hsizeN, hcdsN, hc4, hc5, hc6, hc7,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, htarget]

theorem run_entry (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 991) (hact : 88 ≤ s.activeWords.toNat)
    (hn4 : n = 4 ∨ n = 8)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n))
    (htarget : Decode.isValidJumpDest s.executionEnv.code 3390 = true) :
    runInstructions program (input s mem pa pb n pdst ret rest) =
      some (legacyState s (mpZeroed s mem n) pa pb
        pdst (UInt256.ofNat GenericReturnAdapter.genericShimPC) (ret :: rest)) := by
  have hprefix := GenericReturnAdapter.run_genericEntryPrefix s mem
    (UInt256.ofNat pa) (UInt256.ofNat pb) pdst ret rest (by omega)
  have hbodycap : (ret :: rest).length ≤ 1008 := by simp; omega
  have hbody := run_body s mem pa pb pdst
    (UInt256.ofNat GenericReturnAdapter.genericShimPC) (ret :: rest)
    hbodycap hact n hn4 hcds hs32 htarget
  let middle := GenericReturnAdapter.entryPrefixOutput s mem
    (UInt256.ofNat pa) (UInt256.ofNat pb) pdst ret rest
  have hprefix' : runInstructions GenericReturnAdapter.genericEntryPrefix
      (input s mem pa pb n pdst ret rest) = some middle := by
    simpa [input, GenericReturnAdapter.adapterInput, GenericReturnAdapter.atState,
      GenericReturnAdapter.genericEntryPC] using hprefix
  have hbody' : runInstructions bodyProgram middle =
      some (legacyState s (mpZeroed s mem n) pa pb
      pdst (UInt256.ofNat GenericReturnAdapter.genericShimPC) (ret :: rest)) := by
    simpa [middle, GenericReturnAdapter.entryPrefixOutput,
      GenericReturnAdapter.adapterOutput, GenericReturnAdapter.atState,
      GenericReturnAdapter.genericEntryPC, bodyInput, legacyState] using hbody
  simpa [program] using
    (runInstructions_append_some GenericReturnAdapter.genericEntryPrefix bodyProgram
      (input s mem pa pb n pdst ret rest) middle
      (legacyState s (mpZeroed s mem n) pa pb
        pdst (UInt256.ofNat GenericReturnAdapter.genericShimPC) (ret :: rest))
      hprefix' hbody')

def block : Block Artifact.submissionArtifact .Osaka 5454 program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4378 14 5454 program
    (by decide) (by rfl) (by rfl) (by decide)

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by
    change Challenge.Modexp.submissionBytecode.size < 2^256
    rw [Challenge.Modexp.submissionBytecode_size]
    decide,
    hcode, hfork, hrun, hnp⟩

def gasSteps_entry (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 991) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn4 : n = 4 ∨ n = 8)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n)) :
    Challenge.EvmProof.GasSteps
      (input s mem pa pb n pdst ret rest)
      (legacyState s (mpZeroed s mem n) pa pb
        pdst (UInt256.ofNat GenericReturnAdapter.genericShimPC) (ret :: rest)) :=
  have htarget : Decode.isValidJumpDest s.executionEnv.code 3390 = true := by
    rw [hcode]
    exact Artifact.isValidJumpDest_index 2713 (by rfl)
  block.steps (environment _ hcode hfork hrun hnp) rfl
    (run_entry s mem pa pb n pdst ret rest hcap hact hn4 hcds hs32 htarget)

end Challenge.Modexp.Submission.Proofs.Fast.TnM128PreclearEntry
