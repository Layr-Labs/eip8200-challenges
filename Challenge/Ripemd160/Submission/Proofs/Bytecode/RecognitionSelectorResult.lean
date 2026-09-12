import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSelectorRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Codecopy
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSelectorResult
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open RecognitionSelectorRaw RecognitionAccumulator RecognitionDigest

def copied (s : State) (src : UInt256) (rho : List UInt256) : State :=
  {s with
    stack := rho
    pc := s.pc.succ
    activeWords := UInt256.ofNat 1
    memory := MachineState.writeBytes ByteArray.empty
      (MachineState.readPadded s.executionEnv.code src.toNat 20) 12}

def sized (s : State) (src : UInt256) (rho : List UInt256) : State :=
  {copied s src rho with pc := s.pc.succ.succ, stack := 32 :: rho}

def gasSteps_copy_size (s : State) (src : UInt256) (rho : List UInt256)
    (hstack : s.stack = 12 :: src :: 20 :: rho) (hcap : rho.length ≤ 990)
    (hmem : s.memory = ByteArray.empty) (hactive : s.activeWords = 0)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hcopy : s.decodedOp = some .CODECOPY)
    (hsize : (copied s src rho).decodedOp = some .MSIZE) :
    GasSteps s (sized s src rho) := by
  have hac : s.activeWordsAfterUInt256 12 20 = UInt256.ofNat 1 := by
    simp [State.activeWordsAfterUInt256, hactive, Word.word_toNat_ofNat]
    rfl
  have gcopy : GasSteps s (copied s src rho) := by
    have g := Codecopy.step 12 src 20 rho hcopy hstack (by change s.stack.length + 0 ≤ 1024 + 3; rw [hstack]; simp; omega) hrun hnp
    simpa only [copied, hmem, hac, show (12 : UInt256).toNat = 12 by rfl,
      show (20 : UInt256).toNat = 20 by rfl] using g
  have gs := Msize.step hsize (by simpa [copied] using (show rho.length < 1024 by omega))
    (by simpa [copied] using hrun) (by simpa [copied] using hnp)
  exact gcopy.trans (by simpa [sized, copied, Word.word_toNat_ofNat, Word.literal_eq_ofNat] using gs)

theorem selected_nat (n : Nat) (hn : Allowed n) :
    (selected (UInt256.ofNat 4866) n).toNat = 4866 + 21*((203142/n)%14) := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem digest_size (n : Nat) (hn : Allowed n) : (paddedDigest n).size = 32 := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

theorem copied_memory (s : State) (src : UInt256) (rho : List UInt256) (n : Nat)
    (hn : Allowed n)
    (hread : MachineState.readPadded s.executionEnv.code src.toNat 20 =
      MachineState.readPadded payload (21*((203142/n)%14)) 20) :
    (copied s src rho).memory = paddedDigest n := by
  change MachineState.writeBytes ByteArray.empty _ 12 = _
  rw [hread]
  exact payload_read n hn

theorem returned_output (s : State) (src pc : UInt256) (rho : List UInt256) (n : Nat)
    (hn : Allowed n)
    (hread : MachineState.readPadded s.executionEnv.code src.toNat 20 =
      MachineState.readPadded payload (21*((203142/n)%14)) 20) :
    (returned (sized s src rho) pc rho).hReturn = paddedDigest n := by
  change MachineState.readPadded (copied s src rho).memory 0 32 = _
  rw [copied_memory s src rho n hn hread, ← digest_size n hn]
  exact Memory.readPadded_zero_size _

theorem returned_spec (s : State) (src pc : UInt256) (rho : List UInt256) (n : Nat)
    (hn : Allowed n) (hsize : s.executionEnv.calldata.size = n)
    (hzero : resultAcc s.executionEnv.calldata n = 0)
    (hread : MachineState.readPadded s.executionEnv.code src.toNat 20 =
      MachineState.readPadded payload (21*((203142/n)%14)) 20) :
    (returned (sized s src rho) pc rho).hReturn = Challenge.Ripemd160.spec s.executionEnv.calldata := by
  rw [returned_output s src pc rho n hn hread]
  exact (accepted_spec _ n hn hsize hzero).symm

#print axioms gasSteps_copy_size
#print axioms selected_nat
#print axioms returned_spec
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSelectorResult
