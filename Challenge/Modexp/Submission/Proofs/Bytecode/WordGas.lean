import Challenge.Modexp.Submission.Proofs.Bytecode.WordCorrect
import Challenge.Modexp.Submission.Proofs.Bytecode.WordGasSteps
import Challenge.EvmProof.Meter
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-!
# Exact gas use of the one-word MODEXP path

The path is value-independent. Its only input-dependent loop counts are the
declared base and exponent byte lengths; the final memory expansion for the
single output word at offset zero is included in the constant term.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordGas

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Word
open WordLoops
open WordExit
open WordCorrect

private theorem blockCost_of_static
    {artifact : Challenge.EvmProof.ProgramArtifact} {fork : Fork}
    (path : List (Challenge.EvmProof.Stepper.Located artifact fork)) {s t : State}
    (work : Nat)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = fork)
    (hfree : ∀ located ∈ path,
      Challenge.EvmProof.Meter.CopyFree located.instruction)
    (hcost : Challenge.EvmProof.Meter.runLocatedBlockStaticCost path = work)
    (hactive : s.activeWords = t.activeWords) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost path s = work := by
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    path work hresult hfork hfree hcost
  rw [hactive] at hmeter
  omega

private theorem iterateBounded_cost_le {I : Nat → State} (count bound : Nat)
    (body : ∀ i, i < count → Challenge.EvmProof.GasSteps (I i) (I (i + 1)))
    (hcost : ∀ i (hi : i < count), (body i hi).cost ≤ bound) :
    (Challenge.EvmProof.GasSteps.iterateBounded count body).cost ≤ count * bound := by
  induction count with
  | zero =>
      rw [Challenge.EvmProof.GasSteps.iterateBounded_zero_cost]
      simp
  | succ count ih =>
      rw [Challenge.EvmProof.GasSteps.iterateBounded_succ_cost]
      have hprefix := ih
        (body := fun i hi => body i (Nat.lt_succ_of_lt hi))
        (hcost := fun i hi => hcost i (Nat.lt_succ_of_lt hi))
      have hlast := hcost count (Nat.lt_succ_self count)
      rw [Nat.succ_mul]
      exact Nat.add_le_add hprefix hlast

theorem gasSteps_start_cost (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodpos : 0 < modulusValue input) :
    (gasSteps_start input hvalid hmsize hword hmodpos).cost = 41 := by
  have hmodlt : modulusValue input < 2 ^ 256 :=
    (Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input
      (modulusOffset input) (modulusSize input)).trans_le (by
        have hp := pow_le_pow_right₀ (by omega : 1 ≤ (256 : Nat)) hword
        exact hp.trans (by norm_num))
  have hload := blockCost_of_static startLoadPath 31
    (run_startLoad input hvalid hmsize hword) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hjump := blockCost_of_static startJumpPath 10
    (run_startJump_nonzero input hmodpos hmodlt) (by rfl)
    (by decide) (by rfl) (by rfl)
  unfold gasSteps_start
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

@[simp] theorem gasSteps_baseSetup_cost (input : ByteArray) :
    (gasSteps_baseSetup input).cost = 5 := by
  have hmeter := blockCost_of_static baseSetupPath 5
    (run_baseSetup input) (by rfl)
    (by decide) (by rfl) (by rfl)
  unfold gasSteps_baseSetup
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  exact hmeter

theorem gasSteps_baseIteration_cost (input : ByteArray) (i : Nat)
    (base : UInt256) (hvalid : ValidInput input) (hi : i < baseSize input) :
    (gasSteps_baseIteration input i base hvalid hi).cost = 132 := by
  have hguard := blockCost_of_static baseGuardPath 26
    (run_baseGuard input i base hvalid hi) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hcall := blockCost_of_static baseCallPath 28
    (run_baseCall input i base hvalid hi) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hcap : (baseRest input i base).length < 1017 := by
    simp [baseRest, callerRest]
  have hhelper := blockCost_of_static Accessors.calldataBytePath 30
    (Accessors.run_calldataByte (baseLoopState input i base)
      (UInt256.ofNat (96 + i)) 0 562 (baseRest input i base) hcap rfl rfl
      (by decide)) (by rfl)
    (by decide) (by rfl) (by rfl)
  have htail := blockCost_of_static baseTailPath 48
    (run_baseTail input i base hvalid hi) (by rfl)
    (by decide) (by rfl) (by rfl)
  have htail' : Challenge.EvmProof.Stepper.runLocatedBlockCost baseTailPath
      (Accessors.calldataByteReturned (baseLoopState input i base)
        (UInt256.ofNat (96 + i)) 562 (baseRest input i base)) = 48 := by
    simpa [baseReturnedState, Accessors.calldataByteReturned] using htail
  unfold gasSteps_baseIteration
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost,
    Accessors.gasSteps_calldataByte]
  omega

theorem gasSteps_baseLoop_cost (input : ByteArray) (hvalid : ValidInput input) :
    (gasSteps_baseLoop input hvalid).cost = 132 * baseSize input := by
  unfold gasSteps_baseLoop
  have h := Challenge.EvmProof.GasSteps.iterateBounded_cost_of_const
    (count := baseSize input) (cost := 132) (body := fun i hi =>
      gasSteps_baseIteration input i (baseAfter input i) hvalid hi) (by
        intro i hi
        exact gasSteps_baseIteration_cost input i (baseAfter input i) hvalid hi)
  simpa [Nat.mul_comm] using h

theorem gasSteps_baseFinish_cost (input : ByteArray) (base : UInt256)
    (hvalid : ValidInput input) (hword : modulusSize input ≤ 32) :
    (gasSteps_baseFinish input base hvalid hword).cost = 42 := by
  have hguard := blockCost_of_static baseGuardPath 26
    (run_baseFinishGuard input base hvalid) (by rfl)
    (by decide) (by rfl) (by rfl)
  have htail := blockCost_of_static baseFinishTailPath 16
    (run_baseFinishTail input base hvalid hword) (by rfl)
    (by decide) (by rfl) (by rfl)
  unfold gasSteps_baseFinish
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

theorem gasSteps_expEnter_cost (input : ByteArray) (i : Nat)
    (acc base : UInt256) (hvalid : ValidInput input)
    (hi : i < exponentSize input) :
    (gasSteps_expEnter input i acc base hvalid hi).cost = 46 := by
  have hguard := blockCost_of_static expGuardPath 24
    (run_expGuard input i acc base hvalid hi) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hload := blockCost_of_static expLoadPath 22
    (run_expLoad input i acc base hvalid hi) (by rfl)
    (by decide) (by rfl) (by rfl)
  unfold gasSteps_expEnter
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

theorem gasSteps_bitIteration_cost (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) (hj : j < 8) :
    (gasSteps_bitIteration input outer j byte offset acc base hj).cost ≤ 128 := by
  have hguard := blockCost_of_static bitGuardPath 24
    (run_bitGuard input outer j byte offset acc base hj) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hdecode := blockCost_of_static bitDecodePath 21
    (run_bitDecode input outer j byte offset acc base hj) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hsquare := blockCost_of_static bitSquarePath 17
    (run_bitSquare input outer j byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  by_cases hzero : exponentBit byte j = UInt256.ofNat 0
  · have hdispatch := blockCost_of_static bitDispatchPath 19
      (run_bitDispatch_zero input outer j byte offset acc base hzero) (by rfl)
      (by decide) (by rfl) (by rfl)
    have hjoin := blockCost_of_static bitJoinPath 6
      (run_bitJoin_zero input outer j byte offset acc base hzero) (by rfl)
      (by decide) (by rfl) (by rfl)
    have hadvance := blockCost_of_static bitAdvancePath 17
      (run_bitAdvance input outer j byte offset acc base hj) (by rfl)
      (by decide) (by rfl) (by rfl)
    unfold gasSteps_bitIteration
    simp only [dif_pos hzero, Challenge.EvmProof.GasSteps.trans_cost,
      Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
    omega
  · have hone : exponentBit byte j = UInt256.ofNat 1 := by
      rcases exponentBit_zero_or_one byte j with h | h
      · exact False.elim (hzero h)
      · exact h
    have hdispatch := blockCost_of_static bitDispatchPath 19
      (run_bitDispatch_one input outer j byte offset acc base hone) (by rfl)
      (by decide) (by rfl) (by rfl)
    have hproduct := blockCost_of_static bitProductPath 22
      (run_bitProduct input outer j byte offset acc base) (by rfl)
      (by decide) (by rfl) (by rfl)
    have hjoin := blockCost_of_static bitJoinPath 6
      (run_bitJoin_one input outer j byte offset acc base hone) (by rfl)
      (by decide) (by rfl) (by rfl)
    have hadvance := blockCost_of_static bitAdvancePath 17
      (run_bitAdvance input outer j byte offset acc base hj) (by rfl)
      (by decide) (by rfl) (by rfl)
    unfold gasSteps_bitIteration
    simp only [dif_neg hzero, Challenge.EvmProof.GasSteps.trans_cost,
      Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
    omega

theorem gasSteps_bitLoop_cost (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    (gasSteps_bitLoop input outer byte offset acc base).cost ≤ 1024 := by
  unfold gasSteps_bitLoop
  have h := iterateBounded_cost_le
    (I := fun j =>
      bitLoopState input outer j byte offset (bitAfter input byte base j acc) base)
    (count := 8) (bound := 128)
    (body := fun j hj => gasSteps_bitIteration input outer j byte offset
      (bitAfter input byte base j acc) base hj)
    (hcost := by
      intro j hj
      exact gasSteps_bitIteration_cost input outer j byte offset
        (bitAfter input byte base j acc) base hj)
  exact h.trans (by norm_num)

theorem gasSteps_bitFinish_cost (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) (hvalid : ValidInput input)
    (houter : outer < exponentSize input) :
    (gasSteps_bitFinish input outer byte offset acc base hvalid houter).cost = 48 := by
  have hguard := blockCost_of_static bitGuardPath 24
    (run_bitFinishGuard input outer byte offset acc base) (by rfl)
    (by decide) (by rfl) (by rfl)
  have htail := blockCost_of_static bitFinishTailPath 24
    (run_bitFinishTail input outer byte offset acc base hvalid houter) (by rfl)
    (by decide) (by rfl) (by rfl)
  unfold gasSteps_bitFinish
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

theorem gasSteps_expIteration_cost (input : ByteArray) (i : Nat)
    (acc base : UInt256) (hvalid : ValidInput input)
    (hi : i < exponentSize input) :
    (gasSteps_expIteration input i acc base hvalid hi).cost ≤ 1118 := by
  have hbitLoop := gasSteps_bitLoop_cost input i
    (byteWord input (expOffset input + i))
    (UInt256.ofNat (expOffset input + i)) acc base
  have hbitFinish := gasSteps_bitFinish_cost input i
    (byteWord input (expOffset input + i))
    (UInt256.ofNat (expOffset input + i))
    (bitAfter input (byteWord input (expOffset input + i)) base 8 acc)
    base hvalid hi
  simp only [gasSteps_expIteration, Challenge.EvmProof.GasSteps.trans_cost]
  rw [gasSteps_expEnter_cost input i acc base hvalid hi, hbitFinish]
  omega

theorem gasSteps_expLoop_cost (input : ByteArray) (acc base : UInt256)
    (hvalid : ValidInput input) :
    (gasSteps_expLoop input acc base hvalid).cost ≤ 1118 * exponentSize input := by
  unfold gasSteps_expLoop
  have h := iterateBounded_cost_le
    (I := fun i => expLoopState input i (expAfter input base i acc) base)
    (count := exponentSize input) (bound := 1118)
    (body := fun i hi => gasSteps_expIteration input i
      (expAfter input base i acc) base hvalid hi)
    (hcost := by
      intro i hi
      exact gasSteps_expIteration_cost input i (expAfter input base i acc)
        base hvalid hi)
  simpa [Nat.mul_comm] using h

theorem gasSteps_expFinish_cost (input : ByteArray) (acc base : UInt256)
    (hvalid : ValidInput input) (hword : modulusSize input ≤ 32) :
    (gasSteps_expFinish input acc base hvalid hword).cost = 62 := by
  have hguard := blockCost_of_static expGuardPath 24
    (run_expFinishGuard input acc base hvalid) (by rfl)
    (by decide) (by rfl) (by rfl)
  have htail := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    expFinishTailPath 35
    (run_expFinishTail input acc base hvalid hword) (by rfl)
    (by decide) (by rfl)
  have hreturned : MachineState.activeWordsAfter 1 0
      (modulusSize input) = 1 := by
    unfold MachineState.activeWordsAfter
    split
    · rfl
    · have hdiv : (modulusSize input - 1) / 32 = 0 := by omega
      dsimp
      rw [show 0 + modulusSize input - 1 = modulusSize input - 1 by omega,
        hdiv]
      decide
  have hstored : MachineState.activeWordsAfter 0 0 32 = 1 := by decide
  have hfinal : (wordFinalState input acc base).activeWords.toNat = 1 := by
    change (UInt256.ofNat (MachineState.activeWordsAfter
      (MachineState.activeWordsAfter 0 0 32) 0
        (modulusSize input))).toNat = 1
    rw [hstored, hreturned]
    decide
  rw [show (expFinishDispatchState input acc base).activeWords.toNat = 0 by rfl,
    hfinal] at htail
  norm_num [MachineState.memCost] at htail
  unfold gasSteps_expFinish
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

theorem gasSteps_zeroModulus_cost (input : ByteArray)
    (hvalid : ValidInput input) (hmsize : 0 < modulusSize input)
    (hword : modulusSize input ≤ 32) (hmodulus : modulusValue input = 0) :
    (gasSteps_zeroModulus input hvalid hmsize hword hmodulus).cost = 50 := by
  have hload := blockCost_of_static startLoadPath 31
    (run_startLoad input hvalid hmsize hword) (by rfl)
    (by decide) (by rfl) (by rfl)
  have hjump := blockCost_of_static startJumpPath 10
    (run_startJump_zero input hmodulus) (by rfl)
    (by decide) (by rfl) (by rfl)
  have htail := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    zeroTailPath 6 (run_zeroTail input hvalid hmodulus) (by rfl)
      (by decide) (by decide)
  have hfinal : (zeroModulusFinalState input).activeWords.toNat = 1 := by
    change (UInt256.ofNat
      (MachineState.activeWordsAfter 0 0 (modulusSize input))).toNat = 1
    have hactive : MachineState.activeWordsAfter 0 0
        (modulusSize input) = 1 := by
      unfold MachineState.activeWordsAfter
      split
      · next hzero => omega
      · next hnonzero =>
        have hdiv : (modulusSize input - 1) / 32 = 0 := by omega
        dsimp
        rw [show 0 + modulusSize input - 1 =
          modulusSize input - 1 by omega, hdiv]
        decide
    rw [hactive]
    decide
  rw [show (zeroDispatchState input).activeWords.toNat = 0 by rfl,
    hfinal] at htail
  norm_num [MachineState.memCost] at htail
  unfold gasSteps_zeroModulus
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  rw [hload, hjump]
  omega

def wordGas (input : ByteArray) : Nat :=
  929 + 132 * baseSize input + 1136 * exponentSize input

end Challenge.Modexp.Submission.Proofs.Bytecode.WordGas
