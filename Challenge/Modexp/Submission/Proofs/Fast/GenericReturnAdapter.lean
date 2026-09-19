import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Challenge.Modexp.Submission.Proofs.Fast.CsubReturnState
import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateArtifact

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.GenericReturnAdapter

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof Challenge.EvmProof.Stepper
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

def genericEntryPC : Nat := 5454
def genericShimPC : Nat := 5477
def terminalReturnPC : Nat := 5495
def sharedCleanupPC : Nat := 4152
def sharedCleanupNextPC : Nat := 4166
def terminalDestination : Nat := 256

def adapterProgram (shim : Nat) : List Instr :=
  [.push 2 (UInt256.ofNat shim),
   .op (.Swap ⟨2, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨0, by decide⟩)]

def genericEntryPrefix : List Instr :=
  [.op .JUMPDEST] ++ adapterProgram genericShimPC

def terminalReturnProgram : List Instr :=
  [.op .JUMPDEST, .push 1 64, .op .CALLDATALOAD,
   .push 2 256, .op .RETURN]

def genericReturnProgram : List Instr :=
  [.op .JUMPDEST, .op .POP, .op .POP, .op .POP, .op .POP,
   .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP,
   .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP,
   .op .JUMP]

def genericReturnBlock :
    Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding.Block
      TnM128CandidateArtifact.submissionArtifact .Osaka genericShimPC genericReturnProgram :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed
    4392 18 genericShimPC genericReturnProgram
    (by decide) (by rfl) (by rfl) (by decide)

def retainFrame2DUP16Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩), .op (.Dup ⟨15, by decide⟩),
   .push 10 0, .op .POP]

def frame16 (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) :
    List UInt256 :=
  [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15]

def atState (s : State) (pc : Nat) (memory : ByteArray) (stack : List UInt256) : State :=
  {s with pc := UInt256.ofNat pc, memory := memory, stack := stack}

def adapterInput (s : State) (memory : ByteArray) (pa pb dst ret : UInt256)
    (rest : List UInt256) : State :=
  atState s genericEntryPC memory ([pa, pb, dst, ret] ++ rest)

def adapterOutput (s : State) (memory : ByteArray) (shim : Nat)
    (pa pb dst ret : UInt256) (rest : List UInt256) : State :=
  atState s (genericEntryPC + 1 + 6) memory
    ([pa, pb, dst, UInt256.ofNat shim, ret] ++ rest)

def entryPrefixOutput (s : State) (memory : ByteArray) (pa pb dst ret : UInt256)
    (rest : List UInt256) : State :=
  adapterOutput s memory genericShimPC pa pb dst ret rest

def retainInput (s : State) (memory : ByteArray)
    (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256)
    (rest : List UInt256) : State :=
  atState s sharedCleanupPC memory
    (frame16 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 ++ rest)

def retainOutput (s : State) (memory : ByteArray)
    (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256)
    (rest : List UInt256) : State :=
  atState s sharedCleanupNextPC memory
    ([f14, f15] ++ frame16 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 ++ rest)

def returnInput (s : State) (memory : ByteArray)
    (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 ret : UInt256)
    (rest : List UInt256) : State :=
  atState s genericShimPC memory
    (frame16 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 ++ ret :: rest)

def returnOutput (s : State) (memory : ByteArray) (ret : UInt256)
    (rest : List UInt256) : State :=
  atState s ret.toNat memory rest

def terminalInput (s : State) (memory : ByteArray) (rest : List UInt256) : State :=
  atState s terminalReturnPC memory rest

def terminalOutput (s : State) (memory : ByteArray) (rest : List UInt256) : State :=
  {atState s (terminalReturnPC + 7) memory rest with
    halt := .Returned
    hReturn := MachineState.readPadded memory terminalDestination
      (MachineState.readWord s.executionEnv.calldata 64).toNat
    activeWords := s.activeWordsAfterUInt256 terminalDestination
      (MachineState.readWord s.executionEnv.calldata 64).toNat}

private def genericReturnEnvironment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding.Environment
      TnM128CandidateArtifact.submissionArtifact .Osaka s :=
  { sizeBound := by
      change TnM128Candidate.bytecode.size < 2 ^ 256
      rw [TnM128Candidate.bytecode_size]
      decide
    code := by
      change s.executionEnv.code = TnM128Candidate.bytecode
      exact hcode
    forkEq := hfork
    running := hrun
    noPrecompile := hnp }

def bytesOf (program : List Instr) : List UInt8 :=
  program.flatMap Instr.bytes

theorem genericShimPC_bound : genericShimPC ≤ 65535 := by decide

theorem adapterProgram_bytes :
    bytesOf (adapterProgram genericShimPC) = [0x61, 0x15, 0x65, 0x92, 0x91, 0x90] := by
  decide

theorem genericEntryPrefix_bytes :
    bytesOf genericEntryPrefix = [0x5b, 0x61, 0x15, 0x65, 0x92, 0x91, 0x90] := by
  decide

theorem terminalReturnProgram_bytes :
    bytesOf terminalReturnProgram = [0x5b, 0x60, 0x40, 0x35, 0x61, 0x01, 0x00, 0xf3] := by
  decide

theorem genericReturnProgram_bytes :
    bytesOf genericReturnProgram =
      [0x5b, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50,
       0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x56] := by
  decide

theorem retainFrame2DUP16Program_bytes :
    bytesOf retainFrame2DUP16Program =
      [0x8f, 0x8f, 0x69, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x50] := by
  decide

theorem run_adapter (s : State) (memory : ByteArray) (shim : Nat)
    (pa pb dst ret : UInt256) (rest : List UInt256)
    (_hshim : shim ≤ 65535) (hcap : rest.length ≤ 1018) :
    runInstructions (adapterProgram shim) (atState s (genericEntryPC + 1) memory
      ([pa, pb, dst, ret] ++ rest)) =
      some (adapterOutput s memory shim pa pb dst ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [adapterProgram, adapterOutput, atState, runInstructions,
    genericEntryPC, Challenge.EvmProof.Stepper.runInstr, List.exchange, hc4, hc5,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_genericEntryPrefix (s : State) (memory : ByteArray)
    (pa pb dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1018) :
    runInstructions genericEntryPrefix (adapterInput s memory pa pb dst ret rest) =
      some (entryPrefixOutput s memory pa pb dst ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  let middle := atState s (genericEntryPC + 1) memory ([pa, pb, dst, ret] ++ rest)
  have hdest : runInstructions [.op .JUMPDEST]
      (adapterInput s memory pa pb dst ret rest) = some middle := by
    simp [adapterInput, middle, atState, runInstructions,
      genericEntryPC, Challenge.EvmProof.Stepper.runInstr, hc4,
      Challenge.EvmProof.Word.succ_ofNat_mod]
  have hrun := run_adapter s memory genericShimPC pa pb dst ret rest (by decide) hcap
  have hrun' : runInstructions (adapterProgram genericShimPC) middle =
      some (adapterOutput s memory genericShimPC pa pb dst ret rest) := by
    simpa [middle] using hrun
  simpa [genericEntryPrefix, entryPrefixOutput] using
    (runInstructions_append_some [.op .JUMPDEST] (adapterProgram genericShimPC)
      (adapterInput s memory pa pb dst ret rest) middle
      (adapterOutput s memory genericShimPC pa pb dst ret rest) hdest hrun')

theorem run_retainFrame2DUP16 (s : State) (memory : ByteArray)
    (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1004) :
    runInstructions retainFrame2DUP16Program
      (retainInput s memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest) =
      some (retainOutput s memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest) := by
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  simp [retainFrame2DUP16Program, retainInput, retainOutput, frame16, atState,
    sharedCleanupPC, sharedCleanupNextPC, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    hc16, hc17, hc18, hc19,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_genericReturn (s : State) (memory : ByteArray)
    (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hjump : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    runInstructions genericReturnProgram
      (returnInput s memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 ret rest) =
      some (returnOutput s memory ret rest) := by
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hret : UInt256.ofNat ret.toNat = ret :=
    (Challenge.EvmProof.Word.word_eq_ofNat_toNat ret).symm
  simp [genericReturnProgram, returnInput, returnOutput, frame16, atState,
    runInstructions, Challenge.EvmProof.Stepper.runInstr,
    hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13,
    hc14, hc15, hc16, hc17, hret, hjump,
    Challenge.EvmProof.Word.succ_ofNat_mod]

opaque gasSteps_genericReturn (s : State) (memory : ByteArray)
    (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hjump : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    Challenge.EvmProof.GasSteps
      (returnInput s memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 ret rest)
      (returnOutput s memory ret rest) := by
  let input := returnInput s memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 ret rest
  let output := returnOutput s memory ret rest
  let env := genericReturnEnvironment s hcode hfork hrun hnp
  have hraw : runInstructions genericReturnProgram input = some output := by
    simpa [input, output] using
      (run_genericReturn s memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        ret rest hcap hjump)
  have hpath : Challenge.EvmProof.Stepper.runLocatedBlock genericReturnBlock.path input =
      some output := by
    apply WindowTwentyOneLocated.run_linear genericReturnBlock.path _ input output
      env.sizeBound genericReturnBlock.layout rfl env.running
    rw [genericReturnBlock.instructions_eq]
    exact hraw
  exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
    TnM128CandidateArtifact.submissionArtifact .Osaka genericReturnBlock.path
    env.code env.forkEq hpath env.running env.noPrecompile

theorem run_terminalReturn (s : State) (memory : ByteArray)
    (rest : List UInt256) (hcap : rest.length ≤ 1021) :
    runInstructions terminalReturnProgram (terminalInput s memory rest) =
      some (terminalOutput s memory rest) := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  simp [terminalReturnProgram, terminalInput, terminalOutput, atState,
    terminalReturnPC, terminalDestination,
    runInstructions, Challenge.EvmProof.Stepper.runInstr, hc0, hc1, hc2,
    State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem csub_generic_return_shape (s : State) (memory : ByteArray) (n : Nat)
    (dst shim : UInt256) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 ret : UInt256)
    (rest : List UInt256) :
    Challenge.Modexp.Submission.Proofs.Fast.Csub.csReturnedState s memory n n dst shim
        (frame16 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 ++ ret :: rest) =
      {s with
        pc := shim
        stack := frame16 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 ++ ret :: rest
        memory := Challenge.Modexp.Submission.Proofs.Fast.Csub.csResultMemory memory n dst.toNat} := by
  rw [Challenge.Modexp.Submission.Proofs.Fast.Csub.csReturnedState_eq_result]

theorem pc_adapter_fallthrough : genericEntryPC + 1 + 6 = 5461 := by decide
theorem pc_terminal_return_after_return : terminalReturnPC + 7 = 5502 := by decide
theorem pc_retain_frame_fallthrough : sharedCleanupPC + 14 = sharedCleanupNextPC := by decide

end Challenge.Modexp.Submission.Proofs.Fast.GenericReturnAdapter
