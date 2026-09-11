import Challenge.Modexp.Submission.Proofs.Fast.SquareFourInitCore

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareInit
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.EvmProof.Word

def prefixProgram : List Instr :=
  [.op .JUMPDEST, .push 0 0, .op (.Dup ⟨4, by decide⟩), .push 2 256,
   .op .AND, .push 2 5115, .op .JUMPI]
def joinProgram : List Instr := [.op .JUMPDEST]

def prefixBlock : Block Artifact.submissionArtifact .Osaka 5040 prefixProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3836 7 5040 prefixProgram
    (by decide) (by rfl) (by rfl) (by decide)
def firstBlock : Block Artifact.submissionArtifact .Osaka 5051 (fromProgram 0 4) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3843 44 5051 (fromProgram 0 4)
    (by decide) (by rfl) (by rfl) (by decide)
def joinBlock : Block Artifact.submissionArtifact .Osaka 5115 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3887 1 5115 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)
def lastBlock : Block Artifact.submissionArtifact .Osaka 5116 (fromProgram 4 4) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3888 44 5116 (fromProgram 4 4)
    (by decide) (by rfl) (by rfl) (by decide)
def finishBlock : Block Artifact.submissionArtifact .Osaka 5180 finishProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3932 5 5180 finishProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jump_join : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5115 = true :=
  Artifact.isValidJumpDest_index 3887 (by rfl)

theorem run_prefix (s : State) (mem : ByteArray) (rest : List UInt256)
    (tag : UInt256) (htag : rest[3]? = some tag) (hcap : rest.length ≤ 1018)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions prefixProgram (stateAt s mem 5040 rest) =
      some (stateAt s mem (if UInt256.isTrue (UInt256.land 256 tag) then 5115 else 5051)
        (UInt256.ofNat 0 :: rest)) := by
  rcases rest with _ | ⟨a, rest⟩ <;> try simp only [List.getElem?_nil, reduceCtorEq] at htag
  rcases rest with _ | ⟨b, rest⟩ <;> try simp only [List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at htag
  rcases rest with _ | ⟨c, rest⟩ <;> try simp only [List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at htag
  rcases rest with _ | ⟨d, rest⟩ <;> try simp only [List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at htag
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at htag
  subst d
  simp only [List.length_cons] at hcap
  have hc4 : rest.length+4 < 1024 := by omega
  have hc5 : rest.length+5 < 1024 := by omega
  have hc6 : rest.length+6 < 1024 := by omega
  have hc7 : rest.length+7 < 1024 := by omega
  have hp : (5115 : UInt256).toNat = 5115 := by decide
  have hep : (5115 : UInt256) = UInt256.ofNat 5115 := by decide
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := by decide
  by_cases hb : UInt256.isTrue (UInt256.land 256 tag) <;>
    simp [prefixProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      stateAt, hc4, hc5, hc6, hc7, hp, hep, hz, hcode, jump_join, hb,
      succ_ofNat_mod, ofNat_add_mod]

def gasSteps_last (s : State) (d : Doubling) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) (hact : 296 ≤ s.activeWords.toNat)
    (env : Environment Artifact.submissionArtifact .Osaka s) :
    Challenge.EvmProof.GasSteps (stateAt s d.memory 5115 (d.carry :: rest))
      (stateAt s (finishMemory (doubleFrom d 4 4)) 5191 rest) := by
  have hj : runInstructions joinProgram (stateAt s d.memory 5115 (d.carry :: rest)) =
      some (stateAt s d.memory 5116 (d.carry :: rest)) := by
    have hlen : rest.length < 1023 := by omega
    simp [joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, stateAt,
      succ_ofNat_mod, hlen]
  have a := joinBlock.steps
    (EarlyCsub.environment (stateAt s d.memory 5115 (d.carry :: rest)) env.code env.forkEq env.running env.noPrecompile) rfl hj
  have b := lastBlock.steps
    (EarlyCsub.environment (stateAt s d.memory 5116 (d.carry :: rest)) env.code env.forkEq env.running env.noPrecompile) rfl
    (run_from s d 4 5116 rest hcap hact 4 (by decide))
  have c := finishBlock.steps
    (EarlyCsub.environment (stateAt s (doubleFrom d 4 4).memory 5180 ((doubleFrom d 4 4).carry :: rest)) env.code env.forkEq env.running env.noPrecompile) rfl
    (run_finish s (doubleFrom d 4 4) 5180 rest hcap hact)
  exact a.trans (b.trans c)

def gasSteps_init (s : State) (mem : ByteArray) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) (hact : 296 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (htag : rest[3]? = some (UInt256.ofNat 4204)) :
    Challenge.EvmProof.GasSteps (stateAt s mem 5040 rest)
      (stateAt s (initMemory mem) 5191 rest) := by
  have env := EarlyCsub.environment s hcode hfork hrun hnp
  have a := prefixBlock.steps (EarlyCsub.environment (stateAt s mem 5040 rest) hcode hfork hrun hnp) rfl
    (run_prefix s mem rest (UInt256.ofNat 4204) htag hcap hcode)
  have ht : UInt256.isTrue (UInt256.land 256 (UInt256.ofNat 4204)) = false := by decide
  simp only [ht, Bool.false_eq_true, ↓reduceIte] at a
  have b := firstBlock.steps (EarlyCsub.environment (stateAt s mem 5051 (UInt256.ofNat 0 :: rest)) hcode hfork hrun hnp) rfl
    (run_from s (doubleWords mem 0) 0 5051 rest hcap hact 4 (by decide))
  have c := gasSteps_last s (doubleWords mem 4) rest hcap hact env
  simp only [doubleFrom_words, Nat.zero_add] at b
  simpa only [doubleFrom_words, initMemory, finishMemory] using a.trans (b.trans c)

def gasSteps_init4 (s : State) (mem : ByteArray) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) (hact : 296 ≤ s.activeWords.toNat)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (htag : rest[3]? = some (UInt256.ofNat 4356)) :
    Challenge.EvmProof.GasSteps (stateAt s mem 5040 rest)
      (stateAt s (SquareFourInit.initMemory mem) 5191 rest) := by
  have a := prefixBlock.steps
    (EarlyCsub.environment (stateAt s mem 5040 rest) env.code env.forkEq env.running env.noPrecompile) rfl
    (run_prefix s mem rest (UInt256.ofNat 4356) htag hcap env.code)
  have ht : UInt256.isTrue (UInt256.land 256 (UInt256.ofNat 4356)) = true := by decide
  simp only [ht, ↓reduceIte] at a
  have c := gasSteps_last s ⟨mem, UInt256.ofNat 0⟩ rest hcap hact env
  simpa only [SquareFourInit.from_words, SquareFourInit.initMemory, finishMemory] using a.trans c

#print axioms gasSteps_init
#print axioms gasSteps_init4
end Challenge.Modexp.Submission.Proofs.Fast.SquareInit
