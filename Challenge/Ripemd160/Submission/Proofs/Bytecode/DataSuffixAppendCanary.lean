import Challenge.Ripemd160.Submission.Proofs.Bytecode.DataStepper

set_option warningAsError true
set_option maxRecDepth 30000

/-!
# A raw decoder/stepper canary after an immutable data suffix

`DataProgramArtifact` intentionally indexes only its executable prefix.  The
candidate under test has a 4951-byte executable prefix, 280 bytes of
immutable data, and then an appended executable segment.  This file keeps
that layout explicit: the data suffix is a list of bytes, never an
instruction, while the two appended operations are decoded directly from
the raw byte stream at PCs 5231 and 5232.

The final theorem is conditional on the two raw evaluator results, so it is a
small interface canary rather than a claim about the complete RIPEMD proof.
It nevertheless exercises serialization, exact PCs, decoder facts, and the
existing `DataStepper.runInstr_sound` composition.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DataSuffixAppendCanary

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.DataStepper

def jumpdestOp : Operation := .JUMPDEST

def swap1Op : Operation := .Swap ⟨0, by decide⟩

def jumpdestInstr : Instr := .op jumpdestOp

def swap1Instr : Instr := .op swap1Op

def codeWithDataAndAppend
    (execPrefix dataSuffix tail : List UInt8) : ByteArray :=
  mkCode (execPrefix ++ dataSuffix ++ jumpdestInstr.bytes ++
    swap1Instr.bytes ++ tail)

theorem append_opcode_bytes :
    jumpdestInstr.bytes ++ swap1Instr.bytes = [0x5b, 0x90] := by
  decide

theorem append_pc_5231
    (execPrefix dataSuffix : List UInt8)
    (hprefix : execPrefix.length = 4951)
    (hdata : dataSuffix.length = 280) :
    execPrefix.length + dataSuffix.length = 5231 := by
  omega

theorem append_pc_5232
    (execPrefix dataSuffix : List UInt8)
    (hprefix : execPrefix.length = 4951)
    (hdata : dataSuffix.length = 280) :
    execPrefix.length + dataSuffix.length + 1 = 5232 := by
  omega

theorem decode_append_jumpdest
    (execPrefix dataSuffix tail : List UInt8)
    (hprefix : execPrefix.length = 4951)
    (hdata : dataSuffix.length = 280) :
    Decode.decodeAt (codeWithDataAndAppend execPrefix dataSuffix tail) 5231 =
      some (.JUMPDEST, none) := by
  have hpc := append_pc_5231 execPrefix dataSuffix hprefix hdata
  rw [← hpc]
  simpa [codeWithDataAndAppend, jumpdestInstr, swap1Instr, jumpdestOp, swap1Op, List.append_assoc] using
    YulEvmCompiler.decodeAt_op
      (execPrefix ++ dataSuffix)
      (swap1Instr.bytes ++ tail)
      .JUMPDEST (by decide) trivial

theorem decode_append_swap1
    (execPrefix dataSuffix tail : List UInt8)
    (hprefix : execPrefix.length = 4951)
    (hdata : dataSuffix.length = 280) :
    Decode.decodeAt (codeWithDataAndAppend execPrefix dataSuffix tail) 5232 =
      some (.Swap ⟨0, by decide⟩, none) := by
  have hpc := append_pc_5232 execPrefix dataSuffix hprefix hdata
  rw [← hpc]
  simpa [codeWithDataAndAppend, jumpdestInstr, swap1Instr, jumpdestOp, swap1Op,
    List.append_assoc, Nat.add_assoc] using
    YulEvmCompiler.decodeAt_op
      ((execPrefix ++ dataSuffix) ++ jumpdestInstr.bytes)
      tail
      swap1Op (by decide) trivial

theorem state_decodedOp_of_append_jumpdest
    {execPrefix dataSuffix tail : List UInt8} {s : State}
    (hprefix : execPrefix.length = 4951)
    (hdata : dataSuffix.length = 280)
    (hcode : s.executionEnv.code =
      codeWithDataAndAppend execPrefix dataSuffix tail)
    (hpc : s.pc.toNat = 5231)
    (havailable : jumpdestOp.availableInFork s.fork = true) :
    s.decodedOp = some jumpdestOp := by
  have hdecode := decode_append_jumpdest execPrefix dataSuffix tail hprefix hdata
  unfold State.decodedOp
  unfold State.decoded
  rw [hcode, hpc, hdecode]
  simp only [jumpdestOp] at havailable ⊢
  simp [havailable]

theorem state_decodedOp_of_append_swap1
    {execPrefix dataSuffix tail : List UInt8} {s : State}
    (hprefix : execPrefix.length = 4951)
    (hdata : dataSuffix.length = 280)
    (hcode : s.executionEnv.code =
      codeWithDataAndAppend execPrefix dataSuffix tail)
    (hpc : s.pc.toNat = 5232)
    (havailable : swap1Op.availableInFork s.fork = true) :
    s.decodedOp = some swap1Op := by
  have hdecode := decode_append_swap1 execPrefix dataSuffix tail hprefix hdata
  unfold State.decodedOp
  unfold State.decoded
  rw [hcode, hpc, hdecode]
  change ((if swap1Op.availableInFork s.fork then
    some (swap1Op, (none : Option (UInt256 × Nat))) else none).map (·.1)) = some swap1Op
  rw [havailable]
  rfl

def two_append_steps_sound
    {execPrefix dataSuffix tail : List UInt8}
    {s s1 s2 : State}
    (hprefix : execPrefix.length = 4951)
    (hdata : dataSuffix.length = 280)
    (hcode : s.executionEnv.code =
      codeWithDataAndAppend execPrefix dataSuffix tail)
    (hpc1 : s.pc.toNat = 5231)
    (hpc2 : s1.pc.toNat = 5232)
    (havailable1 : jumpdestOp.availableInFork s.fork = true)
    (havailable2 : swap1Op.availableInFork s1.fork = true)
    (hresult1 : runInstr jumpdestInstr s = some s1)
    (hresult2 : runInstr swap1Instr s1 = some s2)
    (hrun1 : s.halt = .Running)
    (hrun2 : s1.halt = .Running)
    (hnp1 : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hnp2 : Precompile.isPrecompileWithConfig s1.executionEnv.precompileConfig
      s1.executionEnv.fork s1.executionEnv.codeAddr = false) :
    GasSteps s s2 := by
  have hdecode1 : Decodes s jumpdestInstr := by
    simpa [jumpdestInstr, jumpdestOp, Decodes] using
      state_decodedOp_of_append_jumpdest hprefix hdata hcode hpc1 havailable1
  have hstep1 := runInstr_sound hdecode1 hresult1 hrun1 hnp1
  have henv : s1.executionEnv = s.executionEnv :=
    runInstr_executionEnv hresult1
  have hcode1 : s1.executionEnv.code =
      codeWithDataAndAppend execPrefix dataSuffix tail := by
    rw [henv, hcode]
  have hdecode2 : Decodes s1 swap1Instr := by
    simpa [swap1Instr, swap1Op, Decodes] using
      state_decodedOp_of_append_swap1 hprefix hdata hcode1 hpc2 havailable2
  exact hstep1.trans (runInstr_sound hdecode2 hresult2 hrun2 hnp2)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DataSuffixAppendCanary
