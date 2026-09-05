import Challenge.Ripemd160.Submission.H39Memo.TerminalPathsSites
import Challenge.Ripemd160.Submission.H39Memo.PatternFactsArtifact
import Challenge.Ripemd160.Submission.H39Memo.Logic
import Challenge.Ripemd160.Submission.H39Memo.RefMetadata

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTerminal

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

abbrev Located := Stepper.Located Artifact.h39Artifact .Osaka

structure HeadCertificate (pc : Nat) where
  dest : Located
  pop : Located
  destInstruction : dest.instruction = .op .JUMPDEST
  popInstruction : pop.instruction = .op .POP
  destPC : Artifact.h39Artifact.instructionPC dest.index = pc
  popPC : Artifact.h39Artifact.instructionPC pop.index = pc + 1
  pcBound : pc + 2 < 2 ^ 256

def headPath {pc : Nat} (c : HeadCertificate pc) : List Located := [c.dest, c.pop]

set_option linter.unusedSimpArgs false in
theorem run_head {pc : Nat} (c : HeadCertificate pc) (s : State) (sizeWord : UInt256)
    (hpc : s.pc = UInt256.ofNat pc) (hstack : s.stack = [sizeWord])
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock (headPath c) s =
      some (DispatchState.atPC s (pc + 2) []) := by
  have h0 : pc < 2 ^ 256 := by have := c.pcBound; omega
  have h1 : pc + 1 < 2 ^ 256 := by have := c.pcBound; omega
  norm_num at h0 h1
  simp [headPath, Stepper.runLocatedBlock, Stepper.runLocated,
    c.destInstruction, c.popInstruction, c.destPC, c.popPC,
    Stepper.runInstr, hpc, hstack, hrun, DispatchState.atPC,
    Word.succ_ofNat_mod, Word.word_toNat_ofNat, Nat.add_assoc, h0, h1]

structure TailCertificate (pc : Nat) (width : Fin 33) (offset : Nat) (value : UInt256) where
  pushOffset : Located
  load : Located
  pushValue : Located
  xor : Located
  pushFallback : Located
  jump : Located
  offsetInstruction : pushOffset.instruction = .push width (UInt256.ofNat offset)
  loadInstruction : load.instruction = .op .CALLDATALOAD
  valueInstruction : pushValue.instruction = .push 32 value
  xorInstruction : xor.instruction = .op .XOR
  fallbackInstruction : pushFallback.instruction = .push 2 1006
  jumpInstruction : jump.instruction = .op .JUMPI
  offsetPC : Artifact.h39Artifact.instructionPC pushOffset.index = pc
  loadPC : Artifact.h39Artifact.instructionPC load.index = pc + width.val + 1
  valuePC : Artifact.h39Artifact.instructionPC pushValue.index = pc + width.val + 2
  xorPC : Artifact.h39Artifact.instructionPC xor.index = pc + width.val + 35
  fallbackPC : Artifact.h39Artifact.instructionPC pushFallback.index = pc + width.val + 36
  jumpPC : Artifact.h39Artifact.instructionPC jump.index = pc + width.val + 39
  zeroOffset : width.val = 0 → offset = 0
  offsetBound : offset < 2 ^ 256
  pcBound : pc + width.val + 40 < 2 ^ 256

def tailPath {pc offset : Nat} {width : Fin 33} {value : UInt256}
    (c : TailCertificate pc width offset value) : List Located :=
  [c.pushOffset, c.load, c.pushValue, c.xor, c.pushFallback, c.jump]

private theorem isTrue_iff_ne_zero (w : UInt256) : UInt256.isTrue w ↔ w ≠ 0 := by
  constructor
  · intro ht he
    apply ht
    rw [he]
    rfl
  · intro hn ht
    apply hn
    apply Word.word_ext
    exact ht

private theorem xor_true_iff (a b : UInt256) :
    UInt256.isTrue (UInt256.xor a b) ↔ a ≠ b := by
  simp only [isTrue_iff_ne_zero, ne_eq, Logic.wordXor_eq_zero_iff]

set_option linter.unusedSimpArgs false in
theorem run_tail {pc offset : Nat} {width : Fin 33} {value : UInt256}
    (c : TailCertificate pc width offset value) (s : State)
    (hpc : s.pc = UInt256.ofNat pc) (hstack : s.stack = [])
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode) :
    Stepper.runLocatedBlock (tailPath c) s =
      some (DispatchState.atPC s
        (if MachineState.readWord s.executionEnv.calldata offset = value
          then pc + width.val + 40 else 1006) []) := by
  have h0 : pc < 2 ^ 256 := by have := c.pcBound; omega
  have h1 : pc + width.val + 1 < 2 ^ 256 := by have := c.pcBound; omega
  have h2 : pc + width.val + 2 < 2 ^ 256 := by have := c.pcBound; omega
  have h35 : pc + width.val + 35 < 2 ^ 256 := by have := c.pcBound; omega
  have h36 : pc + width.val + 36 < 2 ^ 256 := by have := c.pcBound; omega
  have h39 : pc + width.val + 39 < 2 ^ 256 := by have := c.pcBound; omega
  have hoff := c.offsetBound
  have hz : (⟨0⟩ : UInt256).toNat = 0 := rfl
  norm_num at h0 h1 h2 h35 h36 h39 hoff
  by_cases hw : width.val = 0
  · have ho := c.zeroOffset hw
    subst offset
    simp only [hw, Nat.add_zero] at h1 h2 h35 h36 h39
    simp [tailPath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
      c.offsetInstruction, c.loadInstruction, c.valueInstruction, c.xorInstruction,
      c.fallbackInstruction, c.jumpInstruction, c.offsetPC, c.loadPC,
      c.valuePC, c.xorPC, c.fallbackPC, c.jumpPC, hpc, hstack, hrun, hcode,
      DispatchState.atPC, hw, Word.literal_eq_ofNat, Word.succ_ofNat_mod,
      Word.ofNat_add_mod, Word.word_toNat_ofNat, Nat.add_assoc, h0, h1, h2,
      h35, h36, h39, hz, xor_true_iff, ne_comm, Artifact.validJumpDest_3ee]
    split_ifs <;> simp_all
  · simp only [Nat.add_assoc] at h1 h2 h35 h36 h39
    simp [tailPath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
      c.offsetInstruction, c.loadInstruction, c.valueInstruction, c.xorInstruction,
      c.fallbackInstruction, c.jumpInstruction, c.offsetPC, c.loadPC,
      c.valuePC, c.xorPC, c.fallbackPC, c.jumpPC, hpc, hstack, hrun, hcode,
      DispatchState.atPC, hw, Word.literal_eq_ofNat, Word.succ_ofNat_mod,
      Word.ofNat_add_mod, Word.word_toNat_ofNat, Nat.add_assoc, h0, h1, h2,
      h35, h36, h39, Nat.mod_eq_of_lt hoff, hz, xor_true_iff, ne_comm, Artifact.validJumpDest_3ee]
    split_ifs <;> simp_all

def gasSteps_of_run (path : List Located) {s t : State}
    (hresult : Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) : GasSteps s t :=
  Stepper.runLocatedBlock_sound Artifact.h39Artifact .Osaka path
    hcode hfork hresult hrun hnp

end Challenge.Ripemd160.Submission.H39Memo.PatternTerminal
