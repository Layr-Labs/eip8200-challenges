import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreLocated
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreEdges
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 300000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreComposed
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate HoistedStoreResearch HoistedStoreSites
open HoistedStoreLocated HoistedStoreEdges

/-- Gas-aware decoded success path on the exact candidate image. -/
def success (s : State) (rho : List UInt256) (e : Env s)
    (hs : rho.length ≤ 976) (ha : s.activeWords = UInt256.ofNat 0)
    (hsize : s.executionEnv.calldata.size = 1000)
    (hcond : Low64RepeatMath.condition s.executionEnv.calldata = 0)
    (hz : PcSeedRaw.mismatch s.executionEnv.calldata = 0) :
    GasSteps {s with pc := UInt256.ofNat 48, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho}
      {(stored s) with pc := UInt256.ofNat 9658, stack := rho, halt := .Returned, hReturn := Challenge.Ripemd160.spec s.executionEnv.calldata} := by
  have ew : Env (stored s) := ⟨e.code, e.fork, e.run, e.np⟩
  have hz' : newMismatch s.executionEnv.calldata (PcSeedRaw.seed s.executionEnv.calldata) (MachineState.readWord s.executionEnv.calldata 0) = 0 :=
    (scanner_zero_iff s.executionEnv.calldata).mp hz
  have hscan := gasSteps_scanner s rho e hs ha
  rw [hz'] at hscan
  have hr := gasSteps_return (stored s) rho ew hs (by rfl)
  have hd : MachineState.readPadded (stored s).memory 0 32 = Challenge.Ripemd160.spec s.executionEnv.calldata := by
    rw [stored_return_bytes]
    exact (accepted_spec s.executionEnv.calldata hsize hcond hz').symm
  rw [hd] at hr
  exact (gasSteps_seed s rho e hs).trans
    (hscan.trans ((gasSteps_branch_zero (stored s) rho ew hs).trans hr))

#print axioms success

/-- Gas-aware miss path rejoins the existing generic state after calldata copy. -/
def miss (s : State) (rho : List UInt256) (e : Env s)
    (hs : rho.length ≤ 975) (ha : s.activeWords = UInt256.ofNat 0)
    (hm : s.memory.size = 0) (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hpos : 0 < s.executionEnv.calldata.size)
    (hz : PcSeedRaw.mismatch s.executionEnv.calldata ≠ 0) :
    GasSteps {s with pc := UInt256.ofNat 48, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho}
      (RetainedFallback114.copied s (0 :: rho)) := by
  let c := newMismatch s.executionEnv.calldata (PcSeedRaw.seed s.executionEnv.calldata)
    (MachineState.readWord s.executionEnv.calldata 0)
  have hn : c.toNat ≠ 0 := by
    intro h
    exact hz ((scanner_zero_iff s.executionEnv.calldata).mpr (Word.word_ext h))
  have ew : Env (stored s) := ⟨e.code, e.fork, e.run, e.np⟩
  have hs32 : (stored s).memory.size = 32 := by
    simp [stored, MachineState.writeBytes_size, BytesLemmas.natToBytesPadded_size, hm]
  have hc := gasSteps_copy (stored s) (0 :: rho) ew (by simp; omega) hfit hpos hs32
  have heq : RetainedFallback114.copied (stored s) (0 :: rho) = RetainedFallback114.copied s (0 :: rho) := by
    simp only [RetainedFallback114.copied, stored, State.activeWordsAfterUInt256]
  rw [heq] at hc
  exact (gasSteps_seed s rho e (by omega)).trans
    ((gasSteps_scanner s rho e (by omega) ha).trans
      ((gasSteps_branch_nonzero (stored s) c rho ew (by omega) hn).trans
        ((gasSteps_miss_jump (stored s) rho ew (by omega)).trans
          ((gasSteps_cleanup (stored s) (0 :: rho) ew (by simp; omega) (by rfl)).trans hc))))

#print axioms miss
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreComposed
