import Challenge.Ripemd160.Submission.H39Memo.Artifact
import Challenge.Ripemd160.Submission.H39Memo.DispatchState
import Challenge.Ripemd160.Submission.H39Memo.DispatchTable
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Word
import YulEvmCompiler.BytesLemmas

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.H39Memo.TerminalPaths

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

abbrev Located := Stepper.Located Artifact.h39Artifact .Osaka

/-- The PC is the first PUSH20, after all routing and stack cleanup. -/
structure Certificate (pc : Nat) (digest : UInt256) where
  pushDigest : Located
  pushOffset : Located
  store : Located
  pushSize : Located
  pushReturnOffset : Located
  ret : Located
  digestInstruction : pushDigest.instruction = .push 20 digest
  offsetInstruction : pushOffset.instruction = .push 0 0
  storeInstruction : store.instruction = .op .MSTORE
  sizeInstruction : pushSize.instruction = .push 1 32
  returnOffsetInstruction : pushReturnOffset.instruction = .push 0 0
  returnInstruction : ret.instruction = .op .RETURN
  digestPC : Artifact.h39Artifact.instructionPC pushDigest.index = pc
  offsetPC : Artifact.h39Artifact.instructionPC pushOffset.index = pc + 21
  storePC : Artifact.h39Artifact.instructionPC store.index = pc + 22
  sizePC : Artifact.h39Artifact.instructionPC pushSize.index = pc + 23
  returnOffsetPC : Artifact.h39Artifact.instructionPC pushReturnOffset.index = pc + 25
  returnPC : Artifact.h39Artifact.instructionPC ret.index = pc + 26
  pcBound : pc + 26 < 2 ^ 256

def path {pc : Nat} {digest : UInt256} (c : Certificate pc digest) : List Located :=
  [c.pushDigest, c.pushOffset, c.store, c.pushSize, c.pushReturnOffset, c.ret]

set_option linter.unusedSimpArgs false in
theorem run_output {pc : Nat} {digest : UInt256} (c : Certificate pc digest)
    (s : State) (hpc : s.pc = UInt256.ofNat pc) (hstack : s.stack = [])
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock (path c) s =
      some (DispatchState.returned s (pc + 26) digest) := by
  have h0 : pc < 2 ^ 256 := by have := c.pcBound; omega
  have h21 : pc + 21 < 2 ^ 256 := by have := c.pcBound; omega
  have h22 : pc + 22 < 2 ^ 256 := by have := c.pcBound; omega
  have h23 : pc + 23 < 2 ^ 256 := by have := c.pcBound; omega
  have h25 : pc + 25 < 2 ^ 256 := by have := c.pcBound; omega
  have h26 := c.pcBound
  have hzero : (⟨0⟩ : UInt256).toNat = 0 := rfl
  norm_num at h0 h21 h22 h23 h25 h26
  simp [path, Stepper.runLocatedBlock, Stepper.runLocated,
    c.digestPC, c.offsetPC, c.storePC, c.sizePC, c.returnOffsetPC, c.returnPC,
    c.digestInstruction, c.offsetInstruction, c.storeInstruction,
    c.sizeInstruction, c.returnOffsetInstruction, c.returnInstruction,
    Stepper.runInstr, hpc, hstack, hrun, DispatchState.returned,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat, Nat.add_assoc, Nat.mod_eq_of_lt h0,
    Nat.mod_eq_of_lt h21, Nat.mod_eq_of_lt h22, Nat.mod_eq_of_lt h23,
    Nat.mod_eq_of_lt h25, Nat.mod_eq_of_lt c.pcBound,
    h0, h21, h22, h23, h25, h26, hzero, State.activeWordsAfterUInt256]

def gasSteps_output {pc : Nat} {digest : UInt256} (c : Certificate pc digest)
    (s : State) (hpc : s.pc = UInt256.ofNat pc) (hstack : s.stack = [])
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.h39Artifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps s (DispatchState.returned s (pc + 26) digest) :=
  Stepper.runLocatedBlock_sound Artifact.h39Artifact .Osaka (path c)
    hcode hfork (run_output c s hpc hstack hrun) hrun hnp

theorem returned_hReturn (s : State) (returnPC : Nat) (digest : UInt256) :
    (DispatchState.returned s returnPC digest).hReturn =
      Data.Bytes.natToBytesPadded digest.toNat 32 := by
  change MachineState.readPadded
    (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded digest.toNat 32) 0)
    0 32 = _
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using
    Memory.readPadded_writeBytes_same s.memory
    (Data.Bytes.natToBytesPadded digest.toNat 32) 0

theorem returned_pc (s : State) (returnPC : Nat) (digest : UInt256) :
    (DispatchState.returned s returnPC digest).pc = UInt256.ofNat returnPC := rfl

theorem returned_memory (s : State) (returnPC : Nat) (digest : UInt256) :
    (DispatchState.returned s returnPC digest).memory =
      MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded digest.toNat 32) 0 := rfl

theorem returned_activeWords (s : State) (returnPC : Nat) (digest : UInt256) :
    (DispatchState.returned s returnPC digest).activeWords =
      UInt256.ofNat (MachineState.activeWordsAfter
        (s.activeWordsAfterUInt256 0 32).toNat 0 32) := rfl

end Challenge.Ripemd160.Submission.H39Memo.TerminalPaths
