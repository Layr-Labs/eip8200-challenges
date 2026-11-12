import Challenge.Modexp.Submission.Proofs.CycleGlobal.GateRaw
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
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
open CycleSubmission.Global.GateRaw
def guardBlock : Block CycleSubmission.Artifact.artifact .Osaka 2310 guardProgram :=
 WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 1832 19 2310 guardProgram
  (by change 1832+19 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount] <;> decide)
  (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
  (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
  (by decide)
def bailBlock : Block CycleSubmission.Artifact.artifact .Osaka 2339 bailProgram :=
 WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 1851 2 2339 bailProgram
  (by change 1851+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount] <;> decide)
  (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
  (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
  (by decide)
def e3Block : Block CycleSubmission.Artifact.artifact .Osaka 2298 e3Program :=
 WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 1822 5 2298 e3Program
  (by change 1822+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount] <;> decide)
  (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
  (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
  (by decide)
theorem jumpDestGate : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2310 = true := by
 have h := CycleSubmission.Global.Binding.jumpDest 1832 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
 have hp : CycleSubmission.Artifact.artifact.instructionPC 1832 = 2310 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; decide
 simpa only [hp] using h
theorem jumpDestBail : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 207 = true := by
 have h := CycleSubmission.Global.Binding.jumpDest 135 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
 have hp : CycleSubmission.Artifact.artifact.instructionPC 135 = 207 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; decide
 simpa only [hp] using h
theorem jumpDestSpecial : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3213 = true := by
 have h := CycleSubmission.Global.Binding.jumpDest 2457 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
 have hp : CycleSubmission.Artifact.artifact.instructionPC 2457 = 3213 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; decide
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
 (hb : bsize ≤ 1024) (hbs : 32*n=bsize)
 (hsize : MachineState.readWord s.executionEnv.calldata 32 = UInt256.ofNat 3)
 (he : Precompile.bytesToNatPadded input (96+bsize) 3 = 65537)
 (hdata : s.executionEnv.calldata = input)
 (env : Environment CycleSubmission.Artifact.artifact .Osaka s) :
 GasSteps (entryState s mem n bsize 3 msize) (SlimFrames.special s mem n bsize 3 msize 16) :=
 guardBlock.steps (s := entryState s mem n bsize 3 msize) (env.transfer rfl rfl) rfl
  (run_guard_hit s mem n bsize msize hb hbs hsize (by rw [exponent_eq s input bsize hdata, he])
    (by rw [env.code]; exact jumpDestSpecial))

def gasSteps_miss (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
 (hb : bsize ≤ 1024) (hbs : 32*n=bsize)
 (hsize : MachineState.readWord s.executionEnv.calldata 32 = UInt256.ofNat esize)
 (hc : UInt256.isTrue (guardValue s bsize esize))
 (env : Environment CycleSubmission.Artifact.artifact .Osaka s) :
 GasSteps (entryState s mem n bsize esize msize) (SlimFrames.bailState s mem n bsize esize msize) := by
 have hg := guardBlock.steps (s := entryState s mem n bsize esize msize) (env.transfer rfl rfl) rfl
  (run_guard_miss s mem n bsize esize msize hb hbs hsize hc)
 have hb := bailBlock.steps (s := SlimFrames.guardFrame s mem 2339 n bsize esize msize)
  (env.transfer rfl rfl) rfl (run_bail s mem n bsize esize msize (by rw [env.code]; exact jumpDestBail))
 exact hg.trans hb

def gasSteps_threeHit (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
 (hbs : 32*n=bsize) (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
 (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
 (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
 s.executionEnv.fork s.executionEnv.codeAddr = false) :
 GasSteps (e3go s mem n bsize esize msize) (SlimFrames.special s mem n bsize esize msize 1) := by
 let env : Environment CycleSubmission.Artifact.artifact .Osaka s := ⟨(by change CycleSubmission.Artifact.bytecode.size < 2^256; rw [CycleSubmission.Artifact.bytecodeSize]; norm_num),hcode,hfork,hrun,hnp⟩
 exact e3Block.steps (s := e3go s mem n bsize esize msize) (env.transfer rfl rfl) rfl
  (run_e3 s mem n bsize esize msize hbs (by rw [hcode]; exact jumpDestSpecial))
#print axioms gasSteps_hit
#print axioms gasSteps_miss
#print axioms gasSteps_threeHit
end CycleSubmission.Global.GatePrefix
