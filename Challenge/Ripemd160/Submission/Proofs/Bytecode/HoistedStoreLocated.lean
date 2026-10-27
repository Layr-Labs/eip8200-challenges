import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreSites
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreLocated
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate HoistedStoreResearch HoistedStoreSites
def gasSteps_seed (s : State) (rho : List UInt256) (e : Env s) (hs : rho.length ≤ 976) :
    GasSteps {s with pc := UInt256.ofNat 48, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho}
      {s with pc := UInt256.ofNat 9709, stack := [PcSeedRaw.seed s.executionEnv.calldata,
        MachineState.readWord s.executionEnv.calldata 0] ++ rho} :=
  lift .seed s _ e _ (run_seed s rho (by omega) e.run (by rw [e.code]; exact valid_scanner))

def gasSteps_scanner (s : State) (rho : List UInt256) (e : Env s)
    (hs : rho.length ≤ 976) (ha : s.activeWords = UInt256.ofNat 0) :
    GasSteps {s with pc := UInt256.ofNat 9709, stack := [PcSeedRaw.seed s.executionEnv.calldata,
      MachineState.readWord s.executionEnv.calldata 0] ++ rho}
      {(stored s) with pc := UInt256.ofNat 9934, stack := newMismatch s.executionEnv.calldata (PcSeedRaw.seed s.executionEnv.calldata) (MachineState.readWord s.executionEnv.calldata 0) :: rho} :=
  lift .scanner s _ e _ (run_scanner s _ _ rho (by omega) e.run ha)


#print axioms gasSteps_seed
#print axioms gasSteps_scanner
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreLocated
