import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixBranch
import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Word

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000

/-!
# `CALLDATALOAD` as `MachineState.readWord`, for the H1 recognition branch

`PrefixBranch.Recognised` is stated over `MachineState.readWord input`, and the
branch decides it with two `CALLDATALOAD`s.  The step between the two is
*definitional*, not a lemma that was missing:

* `Challenge.EvmProof.Stepper.runInstr` pushes
  `MachineState.readWord s.executionEnv.calldata offset.toNat`
  (`Challenge/EvmProof/Stepper.lean`, the `.op .CALLDATALOAD` arm);
* the relational rule it is proved sound against,
  `EvmSemantics.EVM.StepRunning.calldataload`, pushes the same term
  (`EvmSemantics/EVM/Step.lean`);
* `EvmSemantics.MachineState.readWord bs off` is *by definition*
  `UInt256.ofNat (Data.Bytes.bytesToBigEndianNat (readPadded bs off 32))`,
  which is exactly what the executable semantics `EvmSemantics.EVM.StepF`
  computes for `CALLDATALOAD`.

So no fact about calldata zero-padding, `readPadded` or `bytesToBigEndianNat`
has to be derived here, and none is missing from the tree.

Two packaged forms already exist and must not be duplicated:
`DirectGuard.stepG_calldataload` and `PatternedScan.stepS_calldataload`.  Both
pin the machine to `initialState submissionBytecode input 0` (via `stG` / `stS`),
whose memory is the initial empty memory.  The H1 branch is entered mid-run,
after the driver has already written memory, so neither is usable there.  What
follows is the same fact with memory, active words and gas left free, together
with the two offsets the branch actually pushes and the decision the two
comparisons make.

The `hcalldata` hypothesis below is not an assumption about the machine: the
calldata of a state reached by execution is the calldata it started with, by
`Challenge.EvmProof.Stepper.runInstr_executionEnv` and
`Challenge.EvmProof.Stepper.runLocated_executionEnv`, both already proved.
`Challenge.Ripemd160.initialState_calldata` supplies the base case by `rfl`.

The instruction shapes below were checked against this tree's own
`Artifact.lean`: indices `4575..4611`, program counters `5363..5503`, with
`PUSH32` immediates `expectedWordAt 0 = 0x72c5...5d82` at index `4583` and
`expectedWordAt 1 = 0xa7cc...fd22` at index `4587`, the five `PUSH4` stores
carrying `PatternedDigest.H1` into `352..480`, and `466`, `477`, `5363`, `5499`
all landing on `JUMPDEST`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixCalldata

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof

/-- `CALLDATALOAD` over an arbitrary machine: only the stack and the calldata
are constrained.  Memory, active words, gas and the program counter are left
free, which is what a branch entered mid-run needs. -/
theorem runInstr_calldataload (s : State) (off : UInt256) (rest : List UInt256)
    (hlen : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runInstr (.op .CALLDATALOAD)
        { s with stack := off :: rest } =
      some { s with
        stack := MachineState.readWord s.executionEnv.calldata off.toNat :: rest
        pc := s.pc.succ } := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by exact hlen)]
  try rfl

/-- `PUSH0`, as the branch emits it, pushes the zero word. -/
theorem runInstr_push0 (s : State) (hlen : s.stack.length < 1024) :
    Challenge.EvmProof.Stepper.runInstr PrefixBranch.push0 s =
      some { s with stack := (⟨0⟩ : UInt256) :: s.stack, pc := s.pc.succ } := by
  unfold Challenge.EvmProof.Stepper.runInstr PrefixBranch.push0
  rw [if_pos hlen]
  try rfl

/-- `PUSH1 v` pushes `v` and advances two bytes. -/
theorem runInstr_push1 (s : State) (v : UInt256) (hlen : s.stack.length < 1024) :
    Challenge.EvmProof.Stepper.runInstr (DenseScheduleTemplate.push1 v) s =
      some { s with stack := v :: s.stack, pc := s.pc + UInt256.ofNat 2 } := by
  unfold Challenge.EvmProof.Stepper.runInstr DenseScheduleTemplate.push1
  rw [if_pos hlen]
  try rfl

/-- The word `PUSH0` leaves on the stack reads calldata at offset `0`. -/
theorem toNat_zeroWord : ((⟨0⟩ : UInt256)).toNat = 0 := rfl

/-- The word `PUSH1 32` leaves on the stack reads calldata at offset `32`. -/
theorem toNat_ofNat_32 : (UInt256.ofNat 32).toNat = 32 := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt (by norm_num)

/-- The branch's first load: `PUSH0 ; CALLDATALOAD` puts
`MachineState.readWord input 0` on the stack, for any machine whose calldata is
`input`. -/
theorem calldataload_at_zero (s : State) (input : ByteArray) (rest : List UInt256)
    (hcalldata : s.executionEnv.calldata = input)
    (hlen : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runInstr (.op .CALLDATALOAD)
        { s with stack := (⟨0⟩ : UInt256) :: rest } =
      some { s with
        stack := MachineState.readWord input 0 :: rest
        pc := s.pc.succ } := by
  rw [runInstr_calldataload s ⟨0⟩ rest hlen]
  simp only [hcalldata, toNat_zeroWord]

/-- The branch's second load: `PUSH1 32 ; CALLDATALOAD` puts
`MachineState.readWord input 32` on the stack. -/
theorem calldataload_at_32 (s : State) (input : ByteArray) (rest : List UInt256)
    (hcalldata : s.executionEnv.calldata = input)
    (hlen : rest.length + 1 < 1024) :
    Challenge.EvmProof.Stepper.runInstr (.op .CALLDATALOAD)
        { s with stack := UInt256.ofNat 32 :: rest } =
      some { s with
        stack := MachineState.readWord input 32 :: rest
        pc := s.pc.succ } := by
  rw [runInstr_calldataload s (UInt256.ofNat 32) rest hlen]
  simp only [hcalldata, toNat_ofNat_32]

/-- The condition the branch's `JUMPI` tests, written in the stack order the
bytecode produces: the second `XOR` is on top, so the `OR` sees
`xor e1 w32` first and `xor e0 w0` second. -/
def branchCondition (w0 w32 : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.xor (PatternedWordData.expectedWordAt 1) w32)
    (UInt256.xor (PatternedWordData.expectedWordAt 0) w0)

/-- **The branch's test is exactly `Recognised`.**  The `JUMPI` at the end of
`PrefixBranch.compareTemplate` falls through precisely when the two loaded
calldata words are the expected ones, which is the hypothesis
`PrefixStateData.h8_firstBlock` consumes. -/
theorem branchCondition_eq_zero_iff (input : ByteArray) :
    branchCondition (MachineState.readWord input 0)
        (MachineState.readWord input 32) = 0 ↔
      PrefixBranch.Recognised input := by
  unfold branchCondition PrefixBranch.Recognised
  rw [KnownInputLogic.wordOr_eq_zero_iff,
    KnownInputLogic.wordXor_eq_zero_iff,
    KnownInputLogic.wordXor_eq_zero_iff]
  constructor
  · rintro ⟨h1, h0⟩
    exact ⟨h0.symm, h1.symm⟩
  · rintro ⟨h0, h1⟩
    exact ⟨h1.symm, h0.symm⟩

#print axioms runInstr_calldataload
#print axioms calldataload_at_zero
#print axioms calldataload_at_32
#print axioms branchCondition_eq_zero_iff

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixCalldata
