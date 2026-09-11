import Challenge.Modexp.Submission.Proofs.Fast.SquareReduce
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowPrograms

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 100000

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareTop
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open SquareInit Monpro

def value (mem : ByteArray) (c extra : UInt256) : UInt256 :=
  MachineState.readWord mem 8224 + (c+extra)
def flag (mem : ByteArray) (c extra : UInt256) : UInt256 :=
  UInt256.lt (value mem c extra) (c+extra) + UInt256.gt c (c+extra)
def memory (mem : ByteArray) (c extra : UInt256) : ByteArray :=
  storeWord mem 8224 (value mem c extra)

theorem word_add_comm (a b : UInt256) : a+b = b+a := by
  change UInt256.mk (a.val+b.val) = UInt256.mk (b.val+a.val)
  rw [add_comm]

theorem flag_toNat (mem : ByteArray) (c extra : UInt256) :
    (flag mem c extra).toNat =
      (UInt256.lt (value mem c extra) (c+extra)).toNat +
        (UInt256.lt (c+extra) c).toNat := by
  have h1 : (UInt256.lt (value mem c extra) (c+extra)).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]; split <;> omega
  have h2 : (UInt256.lt (c+extra) c).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]; split <;> omega
  change (UInt256.lt (value mem c extra) (c+extra) + UInt256.lt (c+extra) c).toNat = _
  rw [Challenge.EvmProof.Word.word_toNat_add, Nat.mod_eq_of_lt (by omega)]

theorem flag_le_two (mem : ByteArray) (c extra : UInt256) :
    (flag mem c extra).toNat ≤ 2 := by
  rw [flag_toNat, Challenge.EvmProof.Word.word_toNat_lt, Challenge.EvmProof.Word.word_toNat_lt]
  split <;> split <;> omega

/-- The two overflow bits account for all three added words. -/
theorem top_spec (mem : ByteArray) (c extra : UInt256) :
    (flag mem c extra).toNat*Limbs.radix + (value mem c extra).toNat =
      (MachineState.readWord mem 8224).toNat+c.toNat+extra.toNat := by
  have h1 := add_carry_split extra c
  rw [word_add_comm extra c] at h1
  have h2 := add_carry_split (MachineState.readWord mem 8224) (c+extra)
  rw [flag_toNat, value, radix_eq]
  calc
    _ = (UInt256.lt (c+extra) c).toNat*2^256 +
        ((UInt256.lt (MachineState.readWord mem 8224+(c+extra)) (c+extra)).toNat*2^256 +
          (MachineState.readWord mem 8224+(c+extra)).toNat) := by ring
    _ = (UInt256.lt (c+extra) c).toNat*2^256 +
        ((MachineState.readWord mem 8224).toNat+(c+extra).toNat) := by rw [h2]
    _ = (MachineState.readWord mem 8224).toNat +
        ((UInt256.lt (c+extra) c).toNat*2^256+(c+extra).toNat) := by ring
    _ = (MachineState.readWord mem 8224).toNat + (extra.toNat+c.toNat) := by rw [h1]
    _ = _ := by ring

theorem add_zero (x : UInt256) : x+UInt256.ofNat 0 = x := by
  change UInt256.mk (x.val+0) = x
  simp only [_root_.add_zero]

theorem zero_add (x : UInt256) : UInt256.ofNat 0+x = x := by
  rw [word_add_comm, add_zero]

theorem mul_zero (x : UInt256) : x*UInt256.ofNat 0 = UInt256.ofNat 0 := by
  apply Challenge.EvmProof.Word.word_ext
  rw [word_toNat_mul, Challenge.EvmProof.Word.word_toNat_ofNat]
  simp only [Nat.zero_mod, Nat.mul_zero]

theorem gt_self (x : UInt256) : UInt256.gt x x = UInt256.ofNat 0 := by
  simp [UInt256.gt, UInt256.lt]

theorem memory_zero (mem : ByteArray) (c : UInt256) :
    memory mem c (UInt256.ofNat 0) = midMem1 mem c := by
  simp only [memory, value, add_zero, storeWord, midMem1]

theorem flag_zero (mem : ByteArray) (c : UInt256) :
    flag mem c (UInt256.ofNat 0) = UInt256.lt (MachineState.readWord mem 8224+c) c := by
  simp only [flag, value, add_zero, gt_self]

/-- The exact shared TOP block, including its common MU cleanup. -/
def topBlock : Block Artifact.submissionArtifact .Osaka 4461 CarryRowPrograms.middleStore :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3401 24 4461 CarryRowPrograms.middleStore
    (by decide) (by rfl) (by rfl) (by decide)

def firstProgram : List Instr := CarryRowPrograms.middleStore.take 12
def secondProgram : List Instr := CarryRowPrograms.middleStore.drop 12

theorem run_first (s : State) (mem : ByteArray) (c bi : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1016) (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions firstProgram (stateAt s mem 4461 (c :: bi :: rest)) =
      some (stateAt s mem 4475
        ((c+bi*MachineState.readWord mem 8928) ::
         UInt256.gt c (c+bi*MachineState.readWord mem 8928) :: bi :: rest)) := by
  have hc2 : rest.length+2 < 1024 := by omega
  have hc3 : rest.length+3 < 1024 := by omega
  have hc4 : rest.length+4 < 1024 := by omega
  have hc5 : rest.length+5 < 1024 := by omega
  have hc6 : rest.length+6 < 1024 := by omega
  have haD := EarlyCsub.activeWords_fix s 8928 32 (by decide) (by decide) hact
  have hd : (8928 : UInt256).toNat = 8928 := by decide
  simp [firstProgram, CarryRowPrograms.middleStore, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, stateAt, hc2, hc3, hc4, hc5, hc6, haD, hd,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, List.exchange, Nat.add_assoc]

theorem run_second (s : State) (mem : ByteArray) (v f bi : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1016) (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions secondProgram (stateAt s mem 4475 (v :: f :: bi :: rest)) =
      some (stateAt s (storeWord mem 8224 (MachineState.readWord mem 8224+v)) 4491
        ((UInt256.lt (MachineState.readWord mem 8224+v) v+f) :: rest)) := by
  have hc2 : rest.length+2 < 1024 := by omega
  have hc3 : rest.length+3 < 1024 := by omega
  have hc4 : rest.length+4 < 1024 := by omega
  have hc5 : rest.length+5 < 1024 := by omega
  have hc6 : rest.length+6 < 1024 := by omega
  have haN := EarlyCsub.activeWords_fix s 8224 32 (by decide) (by decide) hact
  have hn : (8224 : UInt256).toNat = 8224 := by decide
  simp [secondProgram, CarryRowPrograms.middleStore, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, stateAt, storeWord, hc2, hc3, hc4, hc5, hc6, haN, hn,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, List.exchange, Nat.add_assoc]

theorem run_top (s : State) (mem : ByteArray) (c bi : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1016) (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.middleStore (stateAt s mem 4461 (c :: bi :: rest)) =
      some (stateAt s (memory mem c (bi*MachineState.readWord mem 8928)) 4491
        (flag mem c (bi*MachineState.readWord mem 8928) :: rest)) := by
  exact runInstructions_append_some firstProgram secondProgram _ _ _
    (run_first s mem c bi rest hcap hact)
    (run_second s mem (c+bi*MachineState.readWord mem 8928)
      (UInt256.gt c (c+bi*MachineState.readWord mem 8928)) bi rest hcap hact)

def gasSteps_top (s : State) (mem : ByteArray) (c bi : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1016) (hact : 296 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (stateAt s mem 4461 (c :: bi :: rest))
      (stateAt s (memory mem c (bi*MachineState.readWord mem 8928)) 4491
        (flag mem c (bi*MachineState.readWord mem 8928) :: rest)) :=
  topBlock.steps (EarlyCsub.environment (stateAt s mem 4461 (c :: bi :: rest)) hcode hfork hrun hnp) rfl
    (run_top s mem c bi rest hcap hact)

end Challenge.Modexp.Submission.Proofs.Fast.SquareTop
