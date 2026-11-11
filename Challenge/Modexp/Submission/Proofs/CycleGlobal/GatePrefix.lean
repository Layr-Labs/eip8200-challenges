import Challenge.Modexp.Submission.Proofs.CycleGlobal.GateRaw
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.StackPeak
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
noncomputable section
set_option warningAsError false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.GatePrefix
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission.Global.StackTail CycleSubmission.Global.StackPeak
open CycleSubmission.Global.GateRaw
def guardBlock : Block CycleSubmission.Artifact.artifact .Osaka 2310 guardProgram :=
 WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 1831 16 2310 guardProgram
  (by change 1831+16 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
  (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
  (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
  (by decide)
def hitPushBlock : Block CycleSubmission.Artifact.artifact .Osaka 2334 [.push 1 15] :=
 WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 1847 1 2334 [.push 1 15]
  (by change 1847+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
  (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
  (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
  (by decide)
def e3Block : Block CycleSubmission.Artifact.artifact .Osaka 2298 e3Program :=
 WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 1822 4 2298 e3Program
  (by change 1822+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
  (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
  (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
  (by decide)
theorem jumpDestGate : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2310 = true := by
 have h := CycleSubmission.Global.Binding.jumpDest 1831 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
 have hp : CycleSubmission.Artifact.artifact.instructionPC 1831 = 2310 := by
  rw [CycleSubmission.PCCertificate.selectedPC 1831 (by decide)]; decide
 simpa only [hp] using h
theorem jumpDestBail : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 207 = true := by
 have h := CycleSubmission.Global.Binding.jumpDest 135 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
 have hp : CycleSubmission.Artifact.artifact.instructionPC 135 = 207 := by
  rw [CycleSubmission.PCCertificate.selectedPC 135 (by decide)]; decide
 simpa only [hp] using h
theorem jumpDestSpecial : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2336 = true := by
 have h := CycleSubmission.Global.Binding.jumpDest 1848 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
 have hp : CycleSubmission.Artifact.artifact.instructionPC 1848 = 2336 := by
  rw [CycleSubmission.PCCertificate.selectedPC 1848 (by decide)]; decide
 simpa only [hp] using h
theorem exponent_eq (s : State) (input : ByteArray) (bsize : Nat)
 (hdata : s.executionEnv.calldata = input) :
 exponentWord s bsize = UInt256.ofNat (Precompile.bytesToNatPadded input (96+bsize) 3) := by
 have h := Bytes.shiftRight_readWord input (96+bsize) 3 (by omega) (by omega)
 rw [show (32-3)*8=232 by decide] at h
 simpa only [exponentWord, hdata] using h

theorem exponent_ne (s : State) (input : ByteArray) (bsize : Nat)
 (he : Precompile.bytesToNatPadded input (96+bsize) 3 ≠ 65537)
 (hdata : s.executionEnv.calldata = input) : exponentWord s bsize ≠ UInt256.ofNat 65537 := by
 rw [exponent_eq s input bsize hdata]
 intro h
 have h' := congrArg UInt256.toNat h
 have hl : Precompile.bytesToNatPadded input (96+bsize) 3 < 2^256 := by
  have hb := Bytes.bytesToNatPadded_lt_pow input (96+bsize) 3
  omega
 simp only [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hl] at h'
 exact he (by simpa using h')

def gasSteps_hit (s : State) (mem input : ByteArray) (n bsize msize : Nat)
 (rho : List UInt256) (hrho : rho.length ≤ 32) (hb : bsize ≤ 1024)
 (hbs : 32*n=bsize) (hsize : MachineState.readWord s.executionEnv.calldata 32 = UInt256.ofNat 3)
 (he : Precompile.bytesToNatPadded input (96+bsize) 3 = 65537)
 (hdata : s.executionEnv.calldata = input)
 (env : Environment CycleSubmission.Artifact.artifact .Osaka s) :
 GasSteps (append (entryState s mem n bsize 3 msize) rho)
 (append (SlimFrames.special s mem n bsize 3 msize 16) rho) := by
 have hg := blockSteps_append guardBlock
  (s := entryState s mem n bsize 3 msize) (env.transfer rfl rfl) rfl
  (run_guard_hit s mem n bsize msize hb hbs hsize (by rw [exponent_eq s input bsize hdata, he])) rho
  (by simp [entryState, frame, SlimFrames.outer, CycleSubmission.Global.Fast.Shift.entrySlots, Exp.outer, guardProgram, peakInstructions, pushes, pops, Operation.popArity, Operation.pushArity]; omega)
 have hp := blockSteps_append hitPushBlock
  (s := frame s mem 2334 n bsize 3 msize) (env.transfer rfl rfl) rfl
  (run_hitPush s mem n bsize msize) rho
  (by simp [frame, SlimFrames.outer, CycleSubmission.Global.Fast.Shift.entrySlots, Exp.outer, peakInstructions, pushes, pops, Operation.popArity, Operation.pushArity]; omega)
 exact hg.trans hp

def gasSteps_miss (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
 (rho : List UInt256) (hrho : rho.length ≤ 32) (hb : bsize ≤ 1024)
 (hbs : 32*n=bsize) (hsize : MachineState.readWord s.executionEnv.calldata 32 = UInt256.ofNat esize)
 (hc : UInt256.isTrue (guardValue s bsize esize))
 (env : Environment CycleSubmission.Artifact.artifact .Osaka s) :
 GasSteps (append (entryState s mem n bsize esize msize) rho)
 (append (SlimFrames.bailState s mem n bsize esize msize) rho) := by
 apply blockSteps_append guardBlock (s := entryState s mem n bsize esize msize) (env.transfer rfl rfl) rfl
  (run_miss s mem n bsize esize msize hb hbs hsize hc (by rw [env.code]; exact jumpDestBail)) rho
 simp [entryState, frame, SlimFrames.outer, CycleSubmission.Global.Fast.Shift.entrySlots, Exp.outer, guardProgram, peakInstructions, pushes, pops, Operation.popArity, Operation.pushArity]
 omega

def gasSteps_threeHit (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
 (rho : List UInt256) (hrho : rho.length ≤ 32)
 (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
 (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
 (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
 s.executionEnv.fork s.executionEnv.codeAddr = false) :
 GasSteps (append (e3go s mem n bsize esize msize) rho)
 (append (SlimFrames.special s mem n bsize esize msize 1) rho) := by
 let env : Environment CycleSubmission.Artifact.artifact .Osaka s := ⟨(by change CycleSubmission.Artifact.bytecode.size < 2^256; rw [CycleSubmission.Artifact.bytecodeSize]; norm_num),hcode,hfork,hrun,hnp⟩
 apply blockSteps_append e3Block (s := e3go s mem n bsize esize msize) (env.transfer rfl rfl) rfl
  (run_e3 s mem n bsize esize msize (by rw [hcode]; exact jumpDestSpecial)) rho
 simp [e3go, frame, SlimFrames.outer, CycleSubmission.Global.Fast.Shift.entrySlots, Exp.outer, e3Program, peakInstructions, pushes, pops, Operation.popArity, Operation.pushArity]
 omega
#print axioms gasSteps_hit
#print axioms gasSteps_miss
#print axioms gasSteps_threeHit
end CycleSubmission.Global.GatePrefix
