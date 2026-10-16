import Challenge.Modexp.Submission.Proofs.Fast.SquareRoundC
import Challenge.Modexp.Submission.Proofs.Fast.TnM128GlobalBinding

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 3000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CRTExitTail
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open TnM128SquareExit

/-- The old exit either copies the ordinary low words or subtracts the modulus
when the new kernel reports a nonzero overflow. Its scratch memory is explicit. -/
def memory (mem : ByteArray) (tn : UInt256) : ByteArray :=
  if tn = UInt256.ofNat 0 then SquareRoundC.copy8 mem
  else SquareRoundC.sub8 (TnCacheMemory.lift mem (UInt256.ofNat 5297))

theorem readWord (mem : ByteArray) (tn : UInt256) (addr : Nat)
    (hd : addr + 32 ≤ 1792 ∨ 2624 ≤ addr) :
    MachineState.readWord (memory mem tn) addr = MachineState.readWord mem addr := by
  unfold memory
  split_ifs
  · exact SquareRoundC.copy8_readWord mem addr (by omega)
  · rw [SquareRoundC.sub8_readWord _ addr hd,
      TnCacheMemory.read_lift_outside _ _ addr (by omega)]

theorem represents (mem : ByteArray) (tn : UInt256) (ptr n v : Nat)
    (hd : ptr + 32*n ≤ 1792 ∨ 2624 ≤ ptr)
    (h : Model.FastRepresents mem ptr n v) :
    Model.FastRepresents (memory mem tn) ptr n v := by
  refine (Model.fastRepresents_congr (a := mem) ?_ v).1 h
  intro j hj
  rw [readWord mem tn (ptr + 32*j) (by omega)]

theorem flagWord (mem : ByteArray) :
    (MachineState.readWord (TnCacheMemory.lift mem (UInt256.ofNat 5297)) 2080).toNat ≠ 0 := by
  rw [TnCacheMemory.read_lift]
  decide

theorem isTrue_of_ne_zero (tn : UInt256) (h : tn ≠ UInt256.ofNat 0) :
    UInt256.isTrue tn := by
  show tn.toNat ≠ 0
  intro hz
  exact h (Challenge.EvmProof.Word.word_ext (by rw [hz]; decide))


/-- Any nonfinal exit, independent of how its operand and overflow were computed. -/
def gasSteps_more (s : State) (mem : ByteArray) (tn : UInt256) (c : Nat)
    (w3 ent tl inv m0 m96 m64 m32 aprev ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat 256) (hc : c + 1 ≤ 15) :
    Challenge.EvmProof.GasSteps
      (frameAt tn (MachineState.readWord mem 128) 3942 s mem 8 (UInt256.ofNat 0)
        w3 ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat (c+1)) ret rest)
      (frameAt (UInt256.ofNat 0) (MachineState.readWord (memory mem tn) 128) 4816 s
        (memory mem tn) 8 (UInt256.ofNat (2^256-256)) w3 ent tl inv m0 m96 m64 m32
        aprev (UInt256.ofNat c) ret rest) := by
  have hcode' := hcode.trans TnM128GlobalBinding.bytecode_eq
  by_cases h0 : tn = UInt256.ofNat 0
  · subst tn
    have g1 := gasSteps_n8aZero (MachineState.readWord mem 128) s mem 8 w3 ent tl inv m0
      m96 m64 m32 aprev (UInt256.ofNat (c+1)) ret rest (by omega) hrun hcode' hfork hnp
    have g2 := gasSteps_n8bMore (MachineState.readWord mem 128) s mem 8 c w3 ent tl inv m0
      m96 m64 m32 aprev ret rest (by omega) hact hrun hcode' hfork hnp hc
    rw [readWord mem (UInt256.ofNat 0) 128 (Or.inl (by decide))]
    exact (g1.trans g2).cast rfl rfl
  · have g1 := gasSteps_n8aRare tn (MachineState.readWord mem 128) s mem 8 w3 ent tl inv m0
      m96 m64 m32 aprev (UInt256.ofNat (c+1)) ret rest (by omega) hrun hcode' hfork hnp
      (isTrue_of_ne_zero tn h0)
    have g2 := gasSteps_rareMore (MachineState.readWord mem 128) s mem 8 c w3 ent tl inv m0
      m96 m64 m32 aprev ret rest (by omega) hact hrun hcode' hfork hnp hc
    let X := TnCacheMemory.lift mem (UInt256.ofNat 5297)
    let stack := frameStack (UInt256.ofNat 0) (MachineState.readWord mem 128) 8
      (UInt256.ofNat (2^256-256)) w3 ent tl inv m0 m96 m64 m32 aprev
      (UInt256.ofNat c) ret rest
    have hs : MachineState.readWord (Csub.csStep X 8 8).memory 2688 = UInt256.ofNat (32*8) := by
      rw [Csub.csStep_readWord_disjoint X 8 2688 (by decide) (Or.inr (by decide)) 8 le_rfl]
      exact (TnCacheMemory.read_lift_outside mem _ 2688 (Or.inr (by decide))).trans hs32
    have hf : (MachineState.readWord (Csub.csStep X 8 8).memory 2080).toNat ≠ 0 := by
      rw [Csub.csStep_readWord_disjoint X 8 2080 (by decide) (Or.inr (by decide)) 8 le_rfl]
      exact flagWord mem
    have hj : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
        (UInt256.ofNat 4816).toNat = true := by
      exact Eq.mpr (congrArg
        (fun code => Decode.isValidJumpDest code (UInt256.ofNat 4816).toNat = true)
        TnM128GlobalBinding.bytecode_eq) jumpDestH2
    have g3 := Csub.gasSteps_csFixedFrom8Flag s X (UInt256.ofNat 2368) (UInt256.ofNat 4816)
      stack (by simp only [stack, frameStack, List.length_append, List.length_cons,
        List.length_nil]; omega) hrun hcode hact hfork hnp hj hs (by decide) hf
    have hstart : s8At s X (UInt256.ofNat 4816) stack =
        Csub.csFixedState s X 8 0 4037 (UInt256.ofNat 2368) (UInt256.ofNat 4816) stack := rfl
    have hend : Csub.subFlagReturnedState s X 8 (UInt256.ofNat 2368) (UInt256.ofNat 4816) stack =
        frameAt (UInt256.ofNat 0) (MachineState.readWord (memory mem tn) 128) 4816 s
          (memory mem tn) 8 (UInt256.ofNat (2^256-256)) w3 ent tl inv m0 m96 m64 m32
          aprev (UInt256.ofNat c) ret rest := by
      simp only [memory, if_neg h0,
        SquareRoundC.sub8_readWord _ 128 (Or.inl (by decide)),
        TnCacheMemory.read_lift_outside _ _ 128 (Or.inl (by decide))]
      rfl
    exact (g1.trans g2).trans (g3.cast hstart.symm hend)

/-- The final exit reaches the unchanged fused product entry. -/
def gasSteps_last (s : State) (mem : ByteArray) (tn : UInt256)
    (w3 ent tl inv m0 m96 m64 m32 aprev ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat 256) :
    Challenge.EvmProof.GasSteps
      (frameAt tn (MachineState.readWord mem 128) 3942 s mem 8 (UInt256.ofNat 0)
        w3 ent tl inv m0 m96 m64 m32 aprev (UInt256.ofNat 0) ret rest)
      (frameAt (UInt256.ofNat 0) (MachineState.readWord (memory mem tn) 128) 3256 s
        (memory mem tn) 8 (UInt256.ofNat (2^256-256)) w3 ent tl inv m0 m96 m64 m32
        aprev CiosCached.allOnes ret rest) := by
  have hcode' := hcode.trans TnM128GlobalBinding.bytecode_eq
  by_cases h0 : tn = UInt256.ofNat 0
  · subst tn
    have g1 := gasSteps_n8aZero (MachineState.readWord mem 128) s mem 8 w3 ent tl inv m0
      m96 m64 m32 aprev (UInt256.ofNat 0) ret rest (by omega) hrun hcode' hfork hnp
    have g2 := gasSteps_n8bLast (MachineState.readWord mem 128) s mem 8 w3 ent tl inv m0
      m96 m64 m32 aprev ret rest (by omega) hact hrun hcode' hfork hnp
    rw [readWord mem (UInt256.ofNat 0) 128 (Or.inl (by decide))]
    exact (g1.trans g2).cast rfl rfl
  · have g1 := gasSteps_n8aRare tn (MachineState.readWord mem 128) s mem 8 w3 ent tl inv m0
      m96 m64 m32 aprev (UInt256.ofNat 0) ret rest (by omega) hrun hcode' hfork hnp
      (isTrue_of_ne_zero tn h0)
    have g2 := gasSteps_rareLast (MachineState.readWord mem 128) s mem 8 w3 ent tl inv m0
      m96 m64 m32 aprev ret rest (by omega) hact hrun hcode' hfork hnp
    let X := TnCacheMemory.lift mem (UInt256.ofNat 5297)
    let stack := frameStack (UInt256.ofNat 0) (MachineState.readWord mem 128) 8
      (UInt256.ofNat (2^256-256)) w3 ent tl inv m0 m96 m64 m32 aprev
      CiosCached.allOnes ret rest
    have hs : MachineState.readWord X 2688 = UInt256.ofNat (32*8) :=
      (TnCacheMemory.read_lift_outside mem _ 2688 (Or.inr (by decide))).trans hs32
    have hj : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
        (UInt256.ofNat 3256).toNat = true := by
      exact Eq.mpr (congrArg
        (fun code => Decode.isValidJumpDest code (UInt256.ofNat 3256).toNat = true)
        TnM128GlobalBinding.bytecode_eq) jumpDestSetup
    have g3 := SquareRoundC.gasSteps_lazyFlag8 s X (UInt256.ofNat 3256) stack
      (by simp only [stack, frameStack, List.length_append, List.length_cons,
        List.length_nil]; omega) hrun hcode hfork hnp hact hj hs (flagWord mem)
    have hend : { s with pc := UInt256.ofNat 3256, stack := stack, memory := SquareRoundC.sub8 X } =
        frameAt (UInt256.ofNat 0) (MachineState.readWord (memory mem tn) 128) 3256 s
          (memory mem tn) 8 (UInt256.ofNat (2^256-256)) w3 ent tl inv m0 m96 m64 m32
          aprev CiosCached.allOnes ret rest := by
      simp only [memory, if_neg h0,
        SquareRoundC.sub8_readWord _ 128 (Or.inl (by decide)),
        TnCacheMemory.read_lift_outside _ _ 128 (Or.inl (by decide))]
      rfl
    exact (g1.trans g2).trans (g3.cast rfl hend)

#print axioms gasSteps_more
#print axioms gasSteps_last
end Challenge.Modexp.Submission.Proofs.Fast.CRTExitTail
