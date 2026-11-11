import Challenge.Modexp.Submission.Proofs.CycleGlobal.DirectEightEntry
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Terminal
import Challenge.Modexp.Submission.Proofs.CycleCaller.OpaqueCore
import Challenge.Modexp.Submission.Proofs.CycleCaller.Arithmetic
noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 4096
namespace CycleSubmission.Global.DirectEightTerminal
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast

def run (s : State) (mem : ByteArray) (bsize esize k N A B : Nat)
 (hk : 1 ≤ k) (hk16 : k ≤ 16)
 (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
 (hact : 88 ≤ s.activeWords.toNat)
 (hmod : Model.FastRepresents mem 0 8 N)
 (ha : Model.FastRepresents mem 2112 8 A) (hb : Model.FastRepresents mem 256 8 B)
 (hinv : (N*(MachineState.readWord mem 2720).toNat+1) % 2^256 = 0)
 (hN : 0 < N) (hodd : Odd N) (hB : B < N)
 (hg : (DirectEightRaw.guardWord mem).toNat ≠ 0) :
 Finish.Outcome (SlimFrames.special s mem 8 bsize esize 256 k)
 (Precompile.natToBytes (Terminal.result 8 N A B k) 256) := by
 have lead := DirectEightEntry.hit s mem bsize esize k hact env hg
 let entry : State := {s with memory := DirectEightRaw.memory mem}
 let f := DirectEightRaw.frame mem (UInt256.ofNat (k-1)) (UInt256.ofNat 256) bsize esize
 have hn' : Model.FastRepresents entry.memory 0 8 N :=
  DirectEightRaw.keep mem 0 8 N (Or.inl (by decide)) hmod
 have ha' : Model.FastRepresents entry.memory 2368 8 A := DirectEightRaw.represents mem A ha
 have hb' : Model.FastRepresents entry.memory 256 8 B :=
  DirectEightRaw.keep mem 256 8 B (Or.inl (by decide)) hb
 have hinv' : (N*(MachineState.readWord entry.memory 2720).toNat+1) % 2^256 = 0 := by
  rw [show MachineState.readWord entry.memory 2720 = MachineState.readWord mem 2720 from
   DirectEightRaw.readWord mem 2720 (Or.inr (by decide))]
  exact hinv
 obtain ⟨done,tr,halt,bytes,calls⟩ := CallerCore.run entry f k N A B
  (CallerArithmetic.decode N A) hk hk16 (env.transfer rfl rfl)
  (by simp [f,DirectEightRaw.frame,SlimFrames.outer,CycleSubmission.Global.Fast.Shift.entrySlots,Exp.outer])
  hact rfl hn' ha' hb' hinv' hN hodd hB (CallerArithmetic.decode_form N A hN hodd)
  (DirectEightRaw.guard_bound mem A ha hg)
 change GasSteps (DirectEightRaw.entered s mem (UInt256.ofNat (k-1)) (UInt256.ofNat 256) bsize esize) done at tr
 have hcalls : done.callStack = (SlimFrames.special s mem 8 bsize esize 256 k).callStack := by
  rw [calls]; rfl
 refine ⟨done,lead.trans tr,halt,?_,hcalls⟩
 have hr : Limbs.radix^8 = CallerArithmetic.R := by norm_num [Limbs.radix,CallerArithmetic.R]
 rw [Terminal.result,hr,CallerArithmetic.product_eq N A B k hN hodd]
 exact bytes
#print axioms run
end CycleSubmission.Global.DirectEightTerminal
