import Challenge.Modexp.Submission.Proofs.CycleCaller.OpaqueCore
import Challenge.Modexp.Submission.Proofs.CycleCaller.Prefix
import Challenge.Modexp.Submission.Proofs.CycleCaller.Arithmetic
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace CycleSubmission.CallerTerminal
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission.CallerPrefix CycleSubmission.CallerArithmetic

def result (N A B k : Nat) : Nat :=
  Model.montMul N R ((fun a => Model.montMul N R a a)^[k] A) B

/-- The real relocated caller, including operand staging and the cached all-ones
slot, followed by all repeated squares and the final returned bytes. -/
noncomputable opaque run (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256)
    (N A B : Nat) (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : tail.length ≤ 943) (hact : 88 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat 256)
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat 224)
    (hw : tail[1]? = some (UInt256.ofNat 256))
    (hn : tail[2]? = some (UInt256.ofNat 8))
    (hmod : Model.FastRepresents mem 0 8 N)
    (ha : Model.FastRepresents mem 2112 8 A)
    (hb : Model.FastRepresents mem 256 8 B)
    (hinv : (N*(MachineState.readWord mem 2720).toNat+1) % 2^256 = 0)
    (hN : 0 < N) (hodd : Odd N) (hB : B < N)
    (hg : (CallerPrefix.guardWord mem).toNat ≠ 0) :
    Finish.Outcome (call s mem k ret tail) (Precompile.natToBytes (result N A B k) 256) := by
  have lead := CallerPrefix.run s mem k ret tail env hcap hact hcds hs32 hml hw hn hg
  let entry := stateAt s mem k ret tail 5506
  have hmod' : Model.FastRepresents entry.memory 0 8 N :=
    CallerMemory.keep mem 0 8 N (Or.inl (by decide)) hmod
  have ha' : Model.FastRepresents entry.memory 2368 8 A := CallerMemory.represents mem A ha
  have hb' : Model.FastRepresents entry.memory 256 8 B :=
    CallerMemory.keep mem 256 8 B (Or.inl (by decide)) hb
  have hinv' : (N*(MachineState.readWord entry.memory 2720).toNat+1) % 2^256 = 0 := by
    rw [show MachineState.readWord entry.memory 2720 = MachineState.readWord mem 2720 from
      CallerMemory.readWord mem 2720 (Or.inr (by decide))]
    exact hinv
  obtain ⟨done, tr, halt, bytes, calls⟩ := CallerCore.run entry (frame mem k ret tail) k N A B
    (decode N A) hk hk16 (env.transfer rfl rfl) hcap hact rfl
    hmod' ha' hb' hinv' hN hodd hB (decode_form N A hN hodd)
    (CallerPrefix.guard_bound mem A ha' hg)
  change GasSteps entry done at tr
  refine ⟨done, lead.trans tr, halt, ?_, calls⟩
  rw [result, product_eq N A B k hN hodd]
  exact bytes

theorem correct_from_call (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256)
    (N A B : Nat) (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : tail.length ≤ 943) (hact : 88 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat 256)
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat 224)
    (hw : tail[1]? = some (UInt256.ofNat 256))
    (hn : tail[2]? = some (UInt256.ofNat 8))
    (hmod : Model.FastRepresents mem 0 8 N)
    (ha : Model.FastRepresents mem 2112 8 A)
    (hb : Model.FastRepresents mem 256 8 B)
    (hinv : (N*(MachineState.readWord mem 2720).toNat+1) % 2^256 = 0)
    (hN : 0 < N) (hodd : Odd N) (hB : B < N)
    (hg : (CallerPrefix.guardWord mem).toNat ≠ 0) (hcalls : s.callStack = []) :
    ∃ gas0, ∀ gas, gas0 ≤ gas → Eval (withGas (call s mem k ret tail) gas)
      (.returned (Precompile.natToBytes (result N A B k) 256)) :=
  (run s mem k ret tail N A B hk hk16 env hcap hact hcds hs32 hml hw hn hmod ha hb hinv hN hodd hB hg).eventually hcalls

end CycleSubmission.CallerTerminal
