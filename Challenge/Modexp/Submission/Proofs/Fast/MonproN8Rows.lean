import Challenge.Modexp.Submission.Proofs.Fast.MonproN8Mac
import Challenge.Modexp.Submission.Proofs.Fast.MonproN8Paths

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.MonproN8
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

/-- The specialized outer head retains the incumbent five-word frame. -/
def rowState (s : State) (mem : ByteArray) (pa pb i : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  atState s mem 5407
    ([UInt256.ofNat (ptrAt (pb + 256 - 32) i), UInt256.ofNat (pa - 32),
      UInt256.ofNat (pb - 32), pdst, ret] ++ rest)

def rowHead : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3124 .JUMPDEST, pushAt 3125 0 0, opAt 3126 .NOT,
   opAt 3127 (.Dup ⟨2, by decide⟩), opAt 3128 (.Dup ⟨2, by decide⟩),
   opAt 3129 .MLOAD, pushAt 3130 0 0]

def rowBranch : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3705 (.Dup ⟨2, by decide⟩), opAt 3706 (.Dup ⟨1, by decide⟩),
   opAt 3707 .GT, pushAt 3708 2 5407, opAt 3709 .JUMPI]

def rowExit : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3710 .POP, opAt 3711 .POP, opAt 3712 .POP,
   pushAt 3713 2 2637, opAt 3714 .JUMP]

/-- Loading the multiplier reads the same word as rowBi, including aliasing. -/
theorem run_rowHead (s : State) (mem : ByteArray) (pa pb i : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) (hi : i < 8)
    (hpb : 32 ≤ pb) (hpbFit : pb + 256 ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock rowHead
      (rowState s mem pa pb i pdst ret rest) =
      some (atState s mem 5414
        ([UInt256.ofNat 0, rowBi mem pb 8 i, UInt256.ofNat (pa - 32), maxWord,
          UInt256.ofNat (ptrAt (pb + 256 - 32) i), UInt256.ofNat (pa - 32),
          UInt256.ofNat (pb - 32), pdst, ret] ++ rest)) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hpbi : ptrAt (pb + 256 - 32) i %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pb + 32 * (7 - i) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hactB : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pb + 32 * (7 - i)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [rowHead, rowState, atState, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      rowBi, maxWord, hrun, hc5, hc6, hc7, hc8, hc9, hpbi, hactB,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, List.exchange]

/-- Row arithmetic plus its real load prologue, with the full memory contract. -/
def gasSteps_rowToBranch (s : State) (mem : ByteArray) (pa pb i : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hi : i < 8)
    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 256 ≤ 9472) :
    Challenge.EvmProof.GasSteps (rowState s mem pa pb i pdst ret rest)
      (atState s (rowMem mem pa pb 8 i) 6083
        ([UInt256.ofNat (ptrAt (pb + 256 - 32) (i + 1)), UInt256.ofNat (pa - 32),
          UInt256.ofNat (pb - 32), pdst, ret] ++ rest)) := by
  have hh := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := rowState s mem pa pb i pdst ret rest)
    Artifact.submissionArtifact .Osaka rowHead hcode hfork
    (run_rowHead s mem pa pb i pdst ret rest hcap hrun hact hi hpb hpbFit) hrun hnp
  have ha := gasSteps_rowArithmetic s mem pa pb i
    (UInt256.ofNat (ptrAt (pb + 256 - 32) i))
    ([UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32), pdst, ret] ++ rest)
    (by simp; omega) hrun hcode hfork hnp hact hpa hpaFit
  simpa only [Challenge.EvmProof.Word.ofNat_add_mod, ptrAt_succ,
    List.append_assoc, List.cons_append, List.nil_append]
    using hh.trans ha

/-- Taken and terminal branches are separate paths, never a linear path through JUMPI. -/
theorem run_rowBranchNext (s : State) (mem : ByteArray) (pa pb i : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hi : i + 1 < 8) (hpb : 32 ≤ pb) (hpbFit : pb + 256 ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock rowBranch
      (atState s mem 6083
        ([UInt256.ofNat (ptrAt (pb + 256 - 32) (i + 1)), UInt256.ofNat (pa - 32),
          UInt256.ofNat (pb - 32), pdst, ret] ++ rest)) =
      some (rowState s mem pa pb (i + 1) pdst ret rest) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hnextB : ptrAt (pb + 256 - 32) (i + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pb + 32 * (6 - i) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hpbm : (pb - 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pb - 32 := Nat.mod_eq_of_lt (by omega)
  have hgt : pb - 32 < pb + 32 * (6 - i) := by omega
  simp (config := { maxSteps := 800000 })
    [rowBranch, rowState, atState, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      hrun, hcode, hc5, hc6, hc7, hnextB, hpbm, hgt, jump_row8,
      UInt256.gt, UInt256.isTrue, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, List.exchange]


theorem run_rowBranchLast (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hpb : 32 ≤ pb) (hpbFit : pb + 256 ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock (rowBranch ++ rowExit)
      (atState s mem 6083
        ([UInt256.ofNat (ptrAt (pb + 256 - 32) 8), UInt256.ofNat (pa - 32),
          UInt256.ofNat (pb - 32), pdst, ret] ++ rest)) =
      some (mpCsubState s mem pdst ret rest) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hnextB : ptrAt (pb + 256 - 32) 8 %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pb - 32 := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hpbm : (pb - 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pb - 32 := Nat.mod_eq_of_lt (by omega)
  simp (config := { maxSteps := 800000 })
    [rowBranch, rowExit, mpCsubState, atState, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      hrun, hcode, jumpDest2642, hc5, hc6, hc7, hnextB, hpbm,
      UInt256.gt, UInt256.isTrue, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, List.exchange]

def gasSteps_rowNext (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 256 ≤ 9472) (i : Nat) (hi : i + 1 < 8) :
    Challenge.EvmProof.GasSteps (rowState s mem pa pb i pdst ret rest)
      (rowState s (rowMem mem pa pb 8 i) pa pb (i + 1) pdst ret rest) :=
  (gasSteps_rowToBranch s mem pa pb i pdst ret rest hcap hrun hcode hfork hnp
    hact (by omega) hpa hpaFit hpb hpbFit).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      (s := atState s (rowMem mem pa pb 8 i) 6083
        ([UInt256.ofNat (ptrAt (pb + 256 - 32) (i + 1)), UInt256.ofNat (pa - 32),
          UInt256.ofNat (pb - 32), pdst, ret] ++ rest))
      Artifact.submissionArtifact .Osaka rowBranch hcode hfork
      (run_rowBranchNext s (rowMem mem pa pb 8 i) pa pb i pdst ret rest
        hcap hrun hcode hi hpb hpbFit) hrun hnp)

def gasSteps_rowsToCsub (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 256 ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 256 ≤ 9472) :
    Challenge.EvmProof.GasSteps (rowState s mem pa pb 0 pdst ret rest)
      (mpCsubState s (rowsMem mem pa pb 8 8) pdst ret rest) := by
  have hrows := Challenge.EvmProof.GasSteps.iterateBounded
    (I := fun i => rowState s (rowsMem mem pa pb 8 i) pa pb i pdst ret rest) 7
    (fun i hi => gasSteps_rowNext s (rowsMem mem pa pb 8 i) pa pb pdst ret rest
      hcap hrun hcode hfork hnp hact hpa hpaFit hpb hpbFit i (by omega))
  have hlast := gasSteps_rowToBranch s (rowsMem mem pa pb 8 7) pa pb 7 pdst ret rest
    hcap hrun hcode hfork hnp hact (by decide) hpa hpaFit hpb hpbFit
  have hexit := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    (s := atState s (rowsMem mem pa pb 8 8) 6083
      ([UInt256.ofNat (ptrAt (pb + 256 - 32) 8), UInt256.ofNat (pa - 32),
        UInt256.ofNat (pb - 32), pdst, ret] ++ rest))
    Artifact.submissionArtifact .Osaka (rowBranch ++ rowExit) hcode hfork
    (run_rowBranchLast s (rowsMem mem pa pb 8 8) pa pb pdst ret rest
      hcap hrun hcode hpb hpbFit) hrun hnp
  exact hrows.trans (hlast.trans hexit)

end Challenge.Modexp.Submission.Proofs.Fast.MonproN8
