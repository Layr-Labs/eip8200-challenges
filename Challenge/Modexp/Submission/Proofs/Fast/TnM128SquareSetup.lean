import Challenge.Modexp.Submission.Proofs.Fast.TnM128SetupEntry
import Challenge.Modexp.Submission.Proofs.Fast.SquarePartialClear
import Challenge.Modexp.Submission.Proofs.Fast.SquareRow

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareSetup
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached StagedOperand
open TnM128Setup

/-- Shared partial-clear setup. The ordinary entry performs its full clear first. -/
def stageProgram : List Instr :=
  [.push 2 2688, .op .MLOAD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨2, by decide⟩),
   .push 2 2368, .op .MCOPY]

def clearProgram : List Instr := [.push 0 0, .push 2 2048, .op .MSTORE]

def bodyProgram : List Instr :=
  ((EntryPrefix.loadProgram ++ EntryPrefix.shuffleProgram) ++ EntryPrefix.lowProgram) ++
    ((stageProgram ++ clearProgram) ++ pointersJumpProgram)

def program : List Instr := [.op .JUMPDEST] ++ bodyProgram

def input (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (dst ret : UInt256) (rest : List UInt256) : State :=
  { s with
      pc := UInt256.ofNat 3394
      memory := mem
      stack := [hd, UInt256.ofNat pa, UInt256.ofNat pb, dst, ret] ++ rest }

def cached (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (inv m0 : UInt256) (rest : List UInt256) : State :=
  { cachedSetupState s mem hd pa pb n inv m0 rest with pc := UInt256.ofNat 3451 }

def staged (s : State) (mem : ByteArray) (hd : UInt256) (pb n : Nat)
    (inv m0 : UInt256) (rest : List UInt256) : State :=
  { s with
      pc := UInt256.ofNat 3461
      memory := mem
      stack := [hd, UInt256.ofNat (32*n), UInt256.ofNat pb,
        TnM128Setup.l1Target n, zeroTn, allOnes, MachineState.readWord mem 128, inv, m0] ++ rest }

def cleared (s : State) (mem : ByteArray) (hd : UInt256) (pb n : Nat)
    (inv m0 : UInt256) (rest : List UInt256) : State :=
  { staged s (SquarePartialClear.memory mem) hd pb n inv m0 rest with
    pc := UInt256.ofNat 3466 }

theorem run_stage (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (inv m0 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hact : 88 ≤ s.activeWords.toNat) (hnpos : 0 < n) (hn : n ≤ 8) (hpa : pa+32*n ≤ 2816)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n)) :
    runInstructions stageProgram (cached s mem hd pa pb n inv m0 rest) =
      some (staged s (stage mem pa n) hd pb n inv m0 rest) := by
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  have hpaN : pa % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa := Nat.mod_eq_of_lt (by omega)
  have hszN : (32*n) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 32*n := Nat.mod_eq_of_lt (by omega)
  have hactS := activeWords_fix s 2688 32 (by decide) (by omega) hact
  have hactD := activeWordsAfter_fix s.activeWords.toNat 2368 (32*n) (by omega) (by omega) hact
  have hactA := activeWordsAfter_fix s.activeWords.toNat pa (32*n) (by omega) (by omega) hact
  have hactN : s.activeWords.toNat % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = s.activeWords.toNat :=
    Nat.mod_eq_of_lt s.activeWords.val.isLt
  have h2688 : (2688 : UInt256).toNat = 2688 := by decide
  have h2368 : (2368 : UInt256).toNat = 2368 := by decide
  simp only [cached, cachedSetupState, staged,
    read_stage_outside mem pa n 128 (Or.inl (by decide))]
  simp [stageProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    stage, hs32, State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
    hactS, hactD, hactA, hactN, h2688, h2368,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hpaN, hszN,
    hc9, hc10, hc11, hc12, List.exchange]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat s.activeWords).symm

theorem run_clear (s : State) (mem : ByteArray) (hd : UInt256) (pb n : Nat)
    (inv m0 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions clearProgram (staged s mem hd pb n inv m0 rest) =
      some (cleared s mem hd pb n inv m0 rest) := by
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  have hc11 : rest.length+11 < 1024 := by omega
  have ha := activeWords_fix s 2048 32 (by decide) (by decide) hact
  have h2048 : (2048 : UInt256).toNat = 2048 := by decide
  simp [clearProgram, staged, cleared, SquarePartialClear.readWord_outside _ 128
    (Or.inl (by decide)), SquarePartialClear.memory, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, State.activeWordsAfterUInt256, ha, h2048,
    hc9, hc10, hc11, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]
  refine ⟨by rfl, ?_⟩
  exact (SquarePartialClear.readWord_outside mem 128 (Or.inl (by decide))).symm

theorem run_pointers (s : State) (mem : ByteArray) (hd : UInt256) (pb n : Nat)
    (inv m0 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 2816) (hn : n ≤ 8)
    (htarget : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    runInstructions pointersJumpProgram (cleared s mem hd pb n inv m0 rest) =
      some (TnM128Setup.outState s (SquarePartialClear.memory mem) pb n 0 hd (TnM128Setup.l1Target n) inv m0 rest) := by
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  have hlow : negative32 + UInt256.ofNat pb = UInt256.ofNat (pb-32) :=
    negative32_add_ofNat pb hpb (by omega)
  have hsum : UInt256.ofNat (pb-32) + UInt256.ofNat (32*n) =
      UInt256.ofNat (pb+32*n-32) := by
    rw [Challenge.EvmProof.Word.ofNat_add_mod]
    congr 1
    omega
  simp [pointersJumpProgram, cleared, staged, TnM128Setup.outState, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, ← negative32_not, hc9, hc10, hc11, hc12,
    htarget, hlow, hsum, ptrAt_zero, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod]
  simp only [show UInt256.lnot (31 : UInt256) = negative32 by decide,
    hlow, hsum, and_self]

theorem run_entry (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hn4 : n = 4 ∨ n = 8) (hpaFit : pa+32*n ≤ 2816)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 2816)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32*n-32))
    (htarget : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    runInstructions program (input s mem hd pa pb dst ret rest) =
      some (TnM128Setup.outState s (SquarePartialClear.memory (stage mem pa n)) pb n 0 hd (TnM128Setup.l1Target n)
        (MachineState.readWord mem 2720) (MachineState.readWord mem (32*n-32))
        (MachineState.readWord mem 2784 :: MachineState.readWord mem 96 ::
          MachineState.readWord mem 64 :: MachineState.readWord mem 32 ::
          UInt256.ofNat (pa+32*n-32) :: dst :: ret :: rest)) := by
  have hn : n ≤ 8 := by omega
  let inv := MachineState.readWord mem 2720
  let m0 := MachineState.readWord mem (32*n-32)
  let tail := MachineState.readWord mem 2784 :: MachineState.readWord mem 96 ::
    MachineState.readWord mem 64 :: MachineState.readWord mem 32 ::
    UInt256.ofNat (pa+32*n-32) :: dst :: ret :: rest
  have htail : tail.length ≤ 1005 := by
    simp only [tail, List.length_cons]; omega
  have h0 : runInstructions [.op .JUMPDEST] (input s mem hd pa pb dst ret rest) =
      some { input s mem hd pa pb dst ret rest with pc := UInt256.ofNat 3395 } := by
    simp [input, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      show rest.length+5 < 1024 by omega, Challenge.EvmProof.Word.succ_ofNat_mod]
  have hl := EntryPrefix.run_load {s with memory := mem} hd
    (UInt256.ofNat pa) (UInt256.ofNat pb) dst ret rest (32*n-32)
    hcap hact (by omega) hml 3395
  have hend : UInt256.ofNat pa + UInt256.ofNat (32*n-32) = UInt256.ofNat (pa+32*n-32) := by
    rw [Challenge.EvmProof.Word.ofNat_add_mod]; congr 1; omega
  rw [hend] at hl
  have hsh := EntryPrefix.run_shuffle {s with memory := mem} hd
    (UInt256.ofNat pa) (UInt256.ofNat pb) dst ret m0 inv (UInt256.ofNat (pa+32*n-32))
    (MachineState.readWord mem 2784) (MachineState.readWord mem 96)
    (MachineState.readWord mem 32) (EntryPrefix.displacement mem) rest hcap hact 3434
  have hlo := EntryPrefix.run_low {s with memory := mem} hd
    (UInt256.ofNat pa) (UInt256.ofNat pb)
    (UInt256.ofNat 3572 + EntryPrefix.displacement mem) (MachineState.readWord mem 128)
    dst ret m0 inv (UInt256.ofNat (pa+32*n-32)) (MachineState.readWord mem 2784)
    (MachineState.readWord mem 96) (MachineState.readWord mem 32) rest hcap hact 3447
  have hprefix := runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _ hl hsh) hlo
  have hdisp : UInt256.ofNat 3572 + EntryPrefix.displacement mem = TnM128Setup.l1Target n := by
    rcases hn4 with rfl | rfl <;> rw [EntryPrefix.displacement, hs32] <;> decide
  have hprefix' : runInstructions
      ((EntryPrefix.loadProgram ++ EntryPrefix.shuffleProgram) ++ EntryPrefix.lowProgram)
      { input s mem hd pa pb dst ret rest with pc := UInt256.ofNat 3395 } =
      some (cached s mem hd pa pb n inv m0 tail) := by
    simpa only [input, cached, cachedSetupState, inv, m0, tail, hdisp,
      List.cons_append, List.nil_append] using hprefix
  have hstage := run_stage s mem hd pa pb n inv m0 tail htail hact (by omega) hn hpaFit hs32
  have hclear := run_clear s (stage mem pa n) hd pb n inv m0 tail htail hact
  have hptr := run_pointers s (stage mem pa n) hd pb n inv m0 tail htail hpb hpbFit hn htarget
  have hbody := runInstructions_append_some _ _ _ _ _ hprefix'
    (runInstructions_append_some _ _ _ _ _
      (runInstructions_append_some _ _ _ _ _ hstage hclear) hptr)
  exact runInstructions_append_some _ _ _ _ _ h0 hbody

#print axioms run_entry

def block : Block Artifact.submissionArtifact .Osaka 3394 program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2713 57 3394 program
    (by decide) (by rfl) (by rfl) (by decide)

def gasSteps_entry (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn4 : n = 4 ∨ n = 8)
    (hpaFit : pa+32*n ≤ 2816) (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 2816)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32*n-32))
    (htarget : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode hd.toNat = true) :
    Challenge.EvmProof.GasSteps (input s mem hd pa pb dst ret rest)
      (TnM128Setup.outState s (SquarePartialClear.memory (stage mem pa n)) pb n 0 hd (TnM128Setup.l1Target n)
        (MachineState.readWord mem 2720) (MachineState.readWord mem (32*n-32))
        (MachineState.readWord mem 2784 :: MachineState.readWord mem 96 ::
          MachineState.readWord mem 64 :: MachineState.readWord mem 32 ::
          UInt256.ofNat (pa+32*n-32) :: dst :: ret :: rest)) :=
  block.steps (SquareRow.environment _ hcode hfork hrun hnp) rfl
    (run_entry s mem hd pa pb n dst ret rest hcap hact hn4 hpaFit hpb hpbFit hs32 hml
      (by rw [hcode]; exact htarget))

#print axioms gasSteps_entry
end Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareSetup
