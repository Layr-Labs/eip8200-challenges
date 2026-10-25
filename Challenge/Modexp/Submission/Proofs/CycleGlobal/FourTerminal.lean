import Challenge.Modexp.Submission.Proofs.CycleGlobal.R5Route
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Terminal
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Fallback
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Width 4: the r5 route

From the width-4 special state: the leader's head path to 3751 (`R5Head`), then the r5 route,
which returns `Terminal.result 4 N A B k` or, on its prologue test, hands the call to the
general MODEXP route at 219 (`Fallback.correct`, any memory).
-/

namespace CycleSubmission.Global.FourTerminal
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast

theorem handled (input : ByteArray) (s : State) (mem : ByteArray) (bsize esize k N A B mi : Nat)
    (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (hactLe : s.activeWords.toNat ≤ 289)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hcalls : s.callStack = []) (hdata : s.executionEnv.calldata = input)
    (hvalid : Challenge.Modexp.ValidInput input)
    (hf : Exp.Frame mem 4 bsize mi) (hmi : mi < 2^256) (hmi1 : mi ≠ 1)
    (hinv : (N % Limbs.radix * mi + 1) % 2^256 = 0)
    (hmod : Model.FastRepresents mem 0 4 N)
    (ha : Model.FastRepresents mem 2112 4 A)
    (hb : Model.FastRepresents mem 256 4 B)
    (hodd : N % 2 = 1) (hA : A < N) (hB : B < N)
    (hout : Precompile.natToBytes (Terminal.result 4 N A B k) 128 = Challenge.Modexp.spec input)
    (hpos : 0 < Challenge.Modexp.modulusSize input) :
    FixedExponentRoute.Handled input (FixedDirectStates.special s mem 4 bsize esize 128 k) := by
  have hlow : (MachineState.readWord mem 96).toNat = N % Limbs.radix := by
    have h := Model.readWord_of_fastRepresents hmod (j := 3) (by decide)
    simpa using h
  have hmiw : (MachineState.readWord mem 2720).toNat = mi := by
    rw [hf.minvW, Exp.toNat_ofNat_self hmi]
  have hmachine : ((MachineState.readWord mem 96).toNat * mi + 1) % 2^256 = 0 := by
    rw [hlow]; exact hinv
  have head := R5Head.gasSteps_head s mem bsize esize k mi hk hk16 env hact hcds hf hmi hmi1 hmachine
  rcases R5Route.route s mem bsize esize k N A B hk hk16 env hact hmod ha hb
      (by rw [hmiw]; exact hinv) hodd hA hB with hout' | ⟨stk, m', htr, hlen⟩
  · obtain ⟨out⟩ := hout'
    have out' : CycleSubmission.Finish.Outcome (R5Head.entryState s mem bsize esize k)
        (Challenge.Modexp.spec input) := by
      rw [← hout]; exact out
    obtain ⟨final, ⟨tail⟩, hd, hr⟩ := Terminal.handled out' (by
      change s.callStack = []; exact hcalls)
    exact ⟨final, ⟨head.trans tail⟩, hd, hr⟩
  · obtain ⟨tr⟩ := htr
    obtain ⟨done, ⟨tail⟩, hd, hr⟩ := Fallback.correct
      {s with pc := UInt256.ofNat 219, stack := stk, memory := m'} (env.transfer rfl rfl) rfl hlen
      hactLe hcalls (by change Challenge.Modexp.ValidInput s.executionEnv.calldata; rwa [hdata])
      (by change 0 < Challenge.Modexp.modulusSize s.executionEnv.calldata; rwa [hdata])
    refine ⟨done, ⟨(head.trans tr).trans tail⟩, hd, ?_⟩
    change done.toResult = .returned (Challenge.Modexp.spec s.executionEnv.calldata) at hr
    simpa only [hdata] using hr

end CycleSubmission.Global.FourTerminal
