import Challenge.Modexp.Submission.Proofs.CycleGlobal.Fallback
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R5Route
import Challenge.Modexp.Submission.Proofs.CycleGlobal.TailFour
noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Global.TailFourRoute
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission CycleSubmission.Global CycleSubmission.Global.TailFour
theorem route4 (s : State) (mem : ByteArray) (bsize esize k N A B : Nat)
    
    (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat)
    (hmod : Model.FastRepresents mem 0 4 N)
    (ha : Model.FastRepresents mem 2112 4 A)
    (hb : Model.FastRepresents mem 256 4 B)
    (hinv : (N % Limbs.radix * (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0)
    (hodd : N % 2 = 1) (hA : A < N) (hB : B < N) :
    Nonempty (CycleSubmission.Finish.Outcome (DirectR5Reuse.result s mem (UInt256.ofNat (k-1)) bsize esize 128)
        (Precompile.natToBytes (R5Route.result N A B k) 128)) ∨
    ∃ (stk : List UInt256) (m' : ByteArray),
      Nonempty (GasSteps (DirectR5Reuse.result s mem (UInt256.ofNat (k-1)) bsize esize 128)
        {s with pc := UInt256.ofNat 207, stack := stk, memory := m'}) ∧ stk.length < 900 := by
  simpa only [DirectR5Reuse.result] using
    (R5Route.prologue_route s env hact mem
      (MachineState.readWord mem 1568) (UInt256.ofNat 4) (MachineState.readWord mem 1312) (MachineState.readWord mem 1344)
      (MachineState.readWord mem 1376) (MachineState.readWord mem 1408) (MachineState.readWord mem 1440) (MachineState.readWord mem 1472)
      (MachineState.readWord mem 1504) (MachineState.readWord mem 1632) (MachineState.readWord mem 1664) (MachineState.readWord mem 2720)
      (MachineState.readWord mem 1536) (UInt256.shiftRight (MachineState.readWord mem 32) (UInt256.ofNat 128)) (UInt256.ofNat (k-1)) (UInt256.ofNat bsize)
      ((SlimFrames.outer mem 4 bsize esize 128).drop 14)
      (by simp [SlimFrames.outer,CycleSubmission.Global.Fast.Shift.entrySlots,Exp.outer])
      k N A B hk hk16 rfl hmod ha hb hinv hodd hA hB)

theorem handled4 (input : ByteArray) (s : State) (mem : ByteArray) (bsize esize k N A B mi : Nat)
    
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
    FixedExponentRoute.Handled input (SlimFrames.special s mem 4 bsize esize 128 k) := by
  have hlow : (MachineState.readWord mem 96).toNat = N % Limbs.radix := by
    have h := Model.readWord_of_fastRepresents hmod (j := 3) (by decide)
    simpa using h
  have hmiw : (MachineState.readWord mem 2720).toNat = mi := by
    rw [hf.minvW, Exp.toNat_ofNat_self hmi]
  have hmachine : ((MachineState.readWord mem 96).toNat * mi + 1) % 2^256 = 0 := by
    rw [hlow]; exact hinv
  have head := head4 s mem bsize esize k mi hk hk16 env hact hcds hf hmi hmi1 hmachine
  rcases route4 s mem bsize esize k N A B hk hk16 env hact hmod ha hb
      (by rw [hmiw]; exact hinv) hodd hA hB with hout' | ⟨stk, m', htr, hlen⟩
  · obtain ⟨out⟩ := hout'
    have out' : CycleSubmission.Finish.Outcome (DirectR5Reuse.result s mem (UInt256.ofNat (k-1)) bsize esize 128)
        (Challenge.Modexp.spec input) := by
      rw [← hout]; exact out
    obtain ⟨final, ⟨tail⟩, hd, hr⟩ := Terminal.handled out' (by
      change s.callStack = []; exact hcalls)
    exact ⟨final, ⟨head.trans tail⟩, hd, hr⟩
  · obtain ⟨tr⟩ := htr
    obtain ⟨done, ⟨tail⟩, hd, hr⟩ := Fallback.correct
      {s with pc := UInt256.ofNat 207, stack := stk, memory := m'} (env.transfer rfl rfl) rfl hlen
      hactLe hcalls (by change Challenge.Modexp.ValidInput s.executionEnv.calldata; rwa [hdata])
      (by change 0 < Challenge.Modexp.modulusSize s.executionEnv.calldata; rwa [hdata])
    refine ⟨done, ⟨(head.trans tr).trans tail⟩, hd, ?_⟩
    change done.toResult = .returned (Challenge.Modexp.spec s.executionEnv.calldata) at hr
    simpa only [hdata] using hr

#print axioms route4
#print axioms handled4
end CycleSubmission.Global.TailFourRoute
