import Challenge.Modexp.Submission.Proofs.Fast.TnM128R8FirstRow
import Challenge.Modexp.Submission.Proofs.Fast.TnM128R8SuffixSteps
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareTailSteps

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareFirstSteps
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareModel SquareResult CiosCachedMidMemory
open CiosCachedMacCore CiosCached TnCacheMemory TnCacheRowModel TnCacheSquareModel TnCacheRowPreserves
open TnM128SquareFirstModel R8ZeroFirstRow

private theorem mul_comm' (a b : UInt256) : a * b = b * a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val*b.val).val = (b.val*a.val).val
  rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]

theorem mu_eq (Q : ByteArray) (inv : UInt256) (hinv : inv = MachineState.readWord Q 2720) :
    MachineState.readWord Q 2336 * inv = rowMu Q 8 := by
  rw [hinv, mul_comm']
  rfl

theorem c0_eq (Q : ByteArray) (m0 : UInt256) (hm0 : m0 = MachineState.readWord Q 224)
    (hinvQ : inverseInvariant Q 8)
    (hguard : MachineState.readWord Q 2720 ≠ UInt256.ofNat 1) :
    UInt256.addMod (MachineState.readWord Q 2336)
      (UInt256.mulMod m0 (rowMu Q 8) maxWord) maxWord = rowC0 Q 8 := by
  rw [N0Carry.addMod_comm, hm0]
  exact N0Carry.addMod_row_carry _ _ _ hinvQ hguard

def input (s : State) (mem : ByteArray) (aprev tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (ent : UInt256 := UInt256.ofNat 3562) : State :=
  {TnM128SquareSteps.outState (UInt256.ofNat 0) (MachineState.readWord mem 128) s mem 2368 8 0
      (UInt256.ofNat 4258) ent inv m0
      (tl :: m96 :: m64 :: m32 :: aprev :: dst :: ret :: rest) with pc := UInt256.ofNat 5062}

/-- The specialized first product and its reduction enter the general square
loop with the exact cached memory model and the correct previous operand. -/
noncomputable def steps (s : State)
    (env : Environment TnM128CandidateArtifact.submissionArtifact .Osaka s)
    (mem : ByteArray) (aprev tl inv m0 m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hc : Cached mem 2368 8 tl inv m0 m96 m64 m32)
    (ent : UInt256 := UInt256.ofNat 3562) :
    GasSteps (input s mem aprev tl inv m0 m96 m64 m32 dst ret rest ent)
      (TnM128SquareTailSteps.state s (first mem) 8 1 tl inv m0 m96 m64 m32 dst ret rest) := by
  let q := firstProduct mem
  let st : State := {s with memory := mem}
  have hL2 : Decode.isValidJumpDest st.executionEnv.code (UInt256.ofNat 3841).toNat = true := by
    rw [show st.executionEnv.code = TnM128CandidateArtifact.submissionArtifact.code from env.code]
    exact TnM128CandidateArtifact.isValidJumpDest_index 3087 (by rfl)
  have hhead : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 4258).toNat = true := by
    rw [env.code]; exact TnM128L1Jumps.square_jump
  have hp := TnM128R8FirstRow.run_program st (UInt256.ofNat 5062) (UInt256.ofNat 4258)
    ent (UInt256.ofNat 3599) (UInt256.ofNat 0) (MachineState.readWord mem 128)
    (UInt256.ofNat 3841) inv m0 m96 m64 m32 aprev (dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact hL2
  have g0 := TnM128R8FirstRow.block.steps
    (s := initial st (UInt256.ofNat 5062) (UInt256.ofNat 4258) ent
      (UInt256.ofNat 0) (MachineState.readWord mem 128) inv m0 m96 m64 m32 aprev (dst :: ret :: rest))
    (env.transfer rfl rfl) rfl hp
  have hq := product_cached s hc
  have hm : MachineState.readWord mem 128 = MachineState.readWord q.memory 128 :=
    (product_read s mem 128 (Or.inl (by decide))).symm
  have hmu := mu_eq q.memory inv hq.readonly.inverse
  have hc0 := c0_eq q.memory m0 hq.readonly.modulusLow hq.inverse
    (by rw [← hq.readonly.inverse]; exact hq.readonly.inverseGuard)
  have hz : UInt256.ofNat 0 + q.carry = q.carry := R8ZeroFirstRow.zero_add_word _
  have hf : UInt256.lt q.carry q.carry = UInt256.ofNat 0 := by
    unfold UInt256.lt
    simp
  have g1 := TnM128R8SuffixSteps.suffix_steps s env q (UInt256.ofNat 0)
    (UInt256.ofNat 2592) (UInt256.ofNat 4258) (UInt256.ofNat 2336) (UInt256.ofNat 3599)
    (MachineState.readWord mem 128) tl inv m0 (MachineState.readWord mem 2592) m96 m64 m32 dst ret
    rest hcap hact hq.extra hm hhead
  rw [hz, hf] at g1
  have hjoin : TnM128R8FirstRow.result st (UInt256.ofNat 4258) (UInt256.ofNat 3599)
      (MachineState.readWord mem 128) (UInt256.ofNat 3841) inv m0 m96 m64 m32 (dst :: ret :: rest) =
      TnCacheL2Trace.state {s with memory := q.memory} (UInt256.ofNat 3841)
        q.memory (UInt256.ofNat 0) (rowMu q.memory 8) (rowC0 q.memory 8) 8 0
        (UInt256.ofNat 2592) (UInt256.ofNat 4258) (UInt256.ofNat 2336) (UInt256.ofNat 3599)
        q.carry (MachineState.readWord mem 128) inv
        (m0 :: tl :: m96 :: m64 :: m32 :: MachineState.readWord mem 2592 :: dst :: ret :: rest) := by
    simp only [TnM128R8FirstRow.result, st, ← show q = firstProduct mem from rfl,
      hmu, hc0, endFrame, TnCacheL2Trace.state, l2Step, hc.readonly.lowAddress, framed]
    rfl
  have both := (g0.cast rfl hjoin).trans g1
  have hcond : UInt256.isTrue (UInt256.gt (negative32+UInt256.ofNat 2592) (UInt256.ofNat 2336)) := by decide
  have hptr : negative32+UInt256.ofNat 2592 = UInt256.ofNat 2560 := by decide
  have h128 := first_read s mem 128 (Or.inl (by decide))
  have ha0 := first_read s mem 2592 (Or.inr (by decide))
  simp only [hcond, if_true, hptr] at both
  have hstart : initial st (UInt256.ofNat 5062) (UInt256.ofNat 4258) ent
      (UInt256.ofNat 0) (MachineState.readWord mem 128) inv m0 m96 m64 m32 aprev (dst :: ret :: rest) =
      input s mem aprev tl inv m0 m96 m64 m32 dst ret rest ent := by
    simp only [input, TnM128SquareSteps.outState, initial, st, hc.readonly.lowAddress,
      ptrAt_zero, TnCacheFrameOps.frame, framed]
    rfl
  apply both.cast hstart
  simp only [TnM128SquareTailSteps.state, TnM128SquareRowSteps.rowState,
    TnM128SquareTailSteps.previous, sqX, aAddr, Nat.reduceSub, Nat.reduceAdd,
    Nat.reduceMul, h128, ha0, Nat.reduceLT, if_true]
  rfl

#print axioms steps
end Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareFirstSteps
