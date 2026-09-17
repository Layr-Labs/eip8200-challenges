import Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectDispatchTrace

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Located traces for the fixed-exponent addition chains

The one call block ends at the kernel entry `Exp.sqCall` (the `common` block at
pc 3327, `hd = sq_row`).  The loop head additionally stores the square count in
memory word `0x2440 = 2624`, where the kernel's in-kernel square loop reads it.

**S1b.** There is no second call block: this artifact has no multiply entry and
no caller-side count-down loop, so the return address the square call pushes is
the bail trampoline at pc 800 (`PUSH2 0x0320`, instruction index 2043).  The
widths the kernel accelerates never use it — the kernel keeps its frame and
returns to pc 782 — and the widths it does not accelerate leave the fast path
through it, into `modexpBig` at pc 238.  See `run_bailFromSquare`.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectChainTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
open Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

set_option linter.unusedSimpArgs false in
theorem run_start (s : State) (memory : ByteArray)
    (n bsize esize msize count : Nat) (_hn : 2 ≤ n) (_hn32 : n ≤ 8)
    (_hactive : 89 ≤ s.activeWords.toNat)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedDirectPaths.start
      (FixedDirectStates.special s memory n bsize esize msize count) =
      some (FixedDirectStates.square s memory
        n bsize esize msize count) := by
  simp (config := { maxSteps := 300000 })
    [FixedDirectPaths.start, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      FixedDirectStates.special, FixedDirectStates.square, Exp.outer, hrun,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- Program counters for the loop head `FixedDirectPaths.squareCall`
(instruction indices 2039..2049).

`FixedDirectPaths.directPC0` stops at index 2038, the last instruction of the
recogniser; the companion `directPC1` that used to cover the chain was dropped
with the blocks it also served (`squareReturn`, `product`, `fallback`), which no
longer exist.  `squareCall` does still exist, so its eleven counters are restated
here — the only module that locates that block.  Transcribed from the artifact:
`JUMPDEST; DUP1; PUSH2 0x0a40; MSTORE; PUSH2 0x0320; PUSH2 0x0200; DUP1; DUP1;
PUSH2 0x1180; PUSH2 0x0cff; JUMP` at pc 2453..2473. -/
@[simp] theorem directPC1 (i : Nat) (hi : 2039 ≤ i) (hii : i ≤ 2049) :
    Artifact.submissionArtifact.instructionPC i =
      ([2453,2454,2455,2458,2459,2462,2465,2466,2467,2470,2473] : List Nat)[i - 2039]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

/-- The kernel's shared `common` block at pc 3327 (`0x0cff`), the target of the
`JUMP` that ends `squareCall`.  Instruction index 2696 is `JUMPDEST` at pc 3327;
`squareCall`'s own last two pushes are `PUSH2 0x1180` (4480 = `sq_row`) and
`PUSH2 0x0cff` (3327), so this is the block the square call enters.

It lives here rather than in `FixedDirectPaths` so that adding it does not
invalidate the four sibling trace modules that already import `Paths`. -/
theorem jumpDestSqCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3327 = true :=
  Artifact.isValidJumpDest_index 2692 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_squareCall (s : State) (memory : ByteArray)
    (n bsize esize msize count : Nat)
    (hactive : 89 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedDirectPaths.squareCall
      (FixedDirectStates.square s memory n bsize esize msize count) =
      some (Exp.sqCall s (Exp.storeWord memory 2624 (UInt256.ofNat count))
        (UInt256.ofNat 800)
        (UInt256.ofNat count :: Exp.outer n bsize esize msize)) := by
  have haddr : (UInt256.ofNat 2624).toNat = 2624 := by decide
  have hfix : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 2624 32) = s.activeWords :=
    Exp.activeWords_fix s 2624 32 (by omega) (by omega) hactive
  simp (config := { maxSteps := 600000 })
    [FixedDirectPaths.squareCall, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      FixedDirectStates.square, Exp.sqCall, Exp.storeWord, Exp.outer,
      hcode, hrun, haddr, hfix,
      jumpDestSqCommon,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- **S1b.** The square call's own return address is the bail trampoline.

`run_squareReturn_loop`, `run_squareReturn_exit` and `run_product` used to sit
here.  They are DELETED, not renumbered: the caller's count-down loop
(`FixedDirectPaths.squareReturn`), the final mixed-domain product block
(`FixedDirectPaths.product`) and the generic rejoin (`FixedDirectPaths.fallback`)
are all absent from this 5,428-byte artifact.  Measured by exact byte search over
the whole image with the moved `PUSH2` immediates wildcarded: the shapes
`PUSH0; NOT; ADD; DUP1; PUSH2 _; JUMPI`, `POP; PUSH2 _; PUSH2 0x0100; DUP1;
PUSH2 0x0200; PUSH2 _; JUMP` and `JUMPDEST; DUP1; PUSH2 0x0400; PUSH2 0x0100;
MCOPY; PUSH0; PUSH2 _; JUMP` each occur exactly once in the parent image
(pc 2261 / 2269 / 2284) and ZERO times here.  `Exp.mpCall`, which `run_product`
named, was deleted from `Fast.Exp` for the same reason.

What the artifact does instead is transcribed from `squareCall` itself: the
return address it pushes is `PUSH2 0x0320` at instruction index 2043, i.e. 800 --
the six-word trampoline `JUMPDEST; PUSH1 0xee; JUMP` at pc 800/801/803 that lands
on `modexpBig` at pc 238.  So for the widths the kernel does not accelerate the
chain leaves the fast path after the first square, exactly as the three
recogniser misses do.  This is the same located `FixedDirectPaths.bail` block
`FixedDirectFallbackTrace.run_bail` uses, run over the six-word stack the square
call leaves behind (the pushed count is still under the outer frame). -/
theorem run_bailFromSquare (s : State) (memory : ByteArray)
    (n bsize esize msize count : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedDirectPaths.bail
      (Exp.retTo s memory (UInt256.ofNat 800)
        (UInt256.ofNat count :: Exp.outer n bsize esize msize)) =
      some (Exp.retTo s memory (UInt256.ofNat 238)
        (UInt256.ofNat count :: Exp.outer n bsize esize msize)) := by
  simp (config := { maxSteps := 400000 })
    [FixedDirectPaths.bail, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Exp.retTo, Exp.outer, hcode, hrun,
      FixedDirectPaths.jumpDestBigC,
      FixedDirectPaths.pcTramp578, FixedDirectPaths.pcTramp579,
      FixedDirectPaths.pcTramp580,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

private def sound {s t : State}
    (path : List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka))
    (h : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

def gasSteps_start (s : State) (memory : ByteArray)
    (n bsize esize msize count : Nat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hactive : 89 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FixedDirectStates.special s memory n bsize esize msize count)
      (FixedDirectStates.square s memory
        n bsize esize msize count) :=
  sound FixedDirectPaths.start
    (run_start s memory n bsize esize msize count hn hn32 hactive hrun)
    hcode hfork hrun hnp

def gasSteps_squareCall (s : State) (memory : ByteArray)
    (n bsize esize msize count : Nat)
    (hactive : 89 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FixedDirectStates.square s memory n bsize esize msize count)
      (Exp.sqCall s (Exp.storeWord memory 2624 (UInt256.ofNat count))
        (UInt256.ofNat 800)
        (UInt256.ofNat count :: Exp.outer n bsize esize msize)) :=
  sound FixedDirectPaths.squareCall
    (run_squareCall s memory n bsize esize msize count hactive hcode hrun)
    hcode hfork hrun hnp

def gasSteps_bailFromSquare (s : State) (memory : ByteArray)
    (n bsize esize msize count : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (Exp.retTo s memory (UInt256.ofNat 800)
        (UInt256.ofNat count :: Exp.outer n bsize esize msize))
      (Exp.retTo s memory (UInt256.ofNat 238)
        (UInt256.ofNat count :: Exp.outer n bsize esize msize)) :=
  sound FixedDirectPaths.bail
    (run_bailFromSquare s memory n bsize esize msize count hcode hrun)
    hcode hfork hrun hnp

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectChainTrace

#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectChainTrace.run_squareCall
#print axioms Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectChainTrace.run_bailFromSquare
