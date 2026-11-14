import Challenge.Modexp.ProofSupport.InitialState
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
import Challenge.Modexp.Submission.Proofs.Bytecode.MemoLogic
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace CycleSubmission.CombinedMemoGuard
open Challenge.Modexp Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
def packedSum (input : ByteArray) : UInt256 :=
 MachineState.readWord input 0 + MachineState.readWord input 34
def packed (input : ByteArray) : UInt256 := UInt256.ofNat 131073 - packedSum input
def guard (input : ByteArray) : UInt256 :=
 UInt256.lor (UInt256.lor (MachineState.readWord input 100) (packed input)) (MemoLogic.widthGuard input)
theorem sum_toNat (input : ByteArray) (hvalid : ValidInput input) :
 (packedSum input).toNat = baseSize input + exponentSize input*65536 := by
 obtain ⟨_,hb,he,hm⟩ := hvalid
 have h34 := EarlyWordProgram.readWord34_toNat input (by omega) (by omega)
 have h0 : (MachineState.readWord input 0).toNat = baseSize input := Bytes.readWord_toNat input 0
 rw [packedSum,Word.word_toNat_add,h0,h34]
 exact Nat.mod_eq_of_lt (by omega)
theorem packed_zero_iff (input : ByteArray) (hvalid : ValidInput input) :
 packed input = 0 ↔ baseSize input = 1 ∧ exponentSize input = 2 := by
 have hs := sum_toNat input hvalid
 obtain ⟨_,hb,he,hm⟩ := hvalid
 have hc : (UInt256.ofNat 131073).toNat = 131073 := by decide
 rw [packed,MemoLogic.sub_eq_zero_iff]
 constructor
 · intro h
   have hn := congrArg UInt256.toNat h
   rw [hc,hs] at hn
   omega
 · rintro ⟨hb1,he2⟩
   apply Word.word_ext
   rw [hc,hs,hb1,he2]
theorem guard_zero_iff (input : ByteArray) (hvalid : ValidInput input) :
 guard input = 0 ↔ MemoLogic.Matches input := by
 simp only [guard,WindowGuardLogic.wordOr_eq_zero_iff,packed_zero_iff input hvalid,
  MemoLogic.widthGuard_eq_zero_iff,MemoLogic.Matches]
 constructor
 · rintro ⟨⟨h100,hb,he⟩,h68⟩
   exact ⟨hb,he,h68,h100⟩
 · rintro ⟨hb,he,h68,h100⟩
   exact ⟨⟨h100,hb,he⟩,h68⟩
theorem guardNat_zero_iff (input : ByteArray) (hvalid : ValidInput input) :
 (guard input).toNat = 0 ↔ MemoLogic.Matches input := by
 constructor
 · intro h
   apply (guard_zero_iff input hvalid).1
   exact MemoLogic.toNat_inj _ 0 h
 · intro h
   rw [(guard_zero_iff input hvalid).2 h]
   rfl
#print axioms sum_toNat
#print axioms packed_zero_iff
#print axioms guard_zero_iff
#print axioms guardNat_zero_iff
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
def program : List Instr :=
 [.push 5 137506062208,.push 1 68,.op .CALLDATALOAD,.op .SUB,
  .push 1 34,.op .CALLDATALOAD,.push 0 0,.op .CALLDATALOAD,.op .ADD,
  .push 3 131073,.op .SUB,.push 1 100,.op .CALLDATALOAD,.op .OR,.op .OR,
  .push 2 519,.op .JUMPI]
def result (s : State) (input : ByteArray) : State :=
 {s with pc := UInt256.ofNat (if (guard input).toNat = 0 then 933 else 519),stack := []}
theorem run (s : State) (input : ByteArray)
 (hdata : s.executionEnv.calldata = input)
 (hjump : Decode.isValidJumpDest s.executionEnv.code 519 = true) :
 runInstructions program {s with pc := UInt256.ofNat 903,stack := []} = some (result s input) := by
 have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
 have ht : (519 : UInt256).toNat = 519 := rfl
 by_cases hzero : (guard input).toNat = 0
 all_goals
  simp only [guard,packed,packedSum,MemoLogic.widthGuard,MemoLogic.tailConst] at hzero
  simp [program,result,guard,packed,packedSum,MemoLogic.widthGuard,MemoLogic.tailConst,
   runInstructions,Stepper.runInstr,hdata,hjump,hz,ht,UInt256.isTrue,
   Word.literal_eq_ofNat,Word.word_toNat_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod,hzero]
#print axioms run
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
def state (artifact : ProgramArtifact) (input : ByteArray) (pc : Nat) : State :=
 {initialState artifact.code input 0 with pc := UInt256.ofNat pc,stack := []}
def envEntry (artifact : ProgramArtifact) (input : ByteArray)
 (hsize : artifact.code.size < 2^256) : Environment artifact .Osaka (state artifact input 903) where
 sizeBound := hsize
 code := rfl
 forkEq := rfl
 running := rfl
 noPrecompile := deployAddress_not_precompile
noncomputable def traced (artifact : ProgramArtifact)
 (block : Block artifact .Osaka 903 program)
 (hsize : artifact.code.size < 2^256)
 (hjump : Decode.isValidJumpDest artifact.code 519 = true) (input : ByteArray) :
 GasSteps (state artifact input 903) (result (initialState artifact.code input 0) input) :=
 block.steps (envEntry artifact input hsize) rfl (run (initialState artifact.code input 0) input rfl hjump)
noncomputable def hit (artifact : ProgramArtifact)
 (block : Block artifact .Osaka 903 program)
 (hsize : artifact.code.size < 2^256)
 (hjump : Decode.isValidJumpDest artifact.code 519 = true) (input : ByteArray)
 (hvalid : ValidInput input) (hmatch : MemoLogic.Matches input) :
 GasSteps (state artifact input 903) (state artifact input 933) := by
 have h := traced artifact block hsize hjump input
 have hz := (guardNat_zero_iff input hvalid).2 hmatch
 simpa only [result,if_pos hz,state] using h
noncomputable def miss (artifact : ProgramArtifact)
 (block : Block artifact .Osaka 903 program)
 (hsize : artifact.code.size < 2^256)
 (hjump : Decode.isValidJumpDest artifact.code 519 = true) (input : ByteArray)
 (hvalid : ValidInput input) (hmiss : ¬ MemoLogic.Matches input) :
 GasSteps (state artifact input 903) (state artifact input 519) := by
 have h := traced artifact block hsize hjump input
 have hn : (guard input).toNat ≠ 0 := fun hz => hmiss ((guardNat_zero_iff input hvalid).1 hz)
 simpa only [result,if_neg hn,state] using h
#print axioms traced
#print axioms hit
#print axioms miss
end CycleSubmission.CombinedMemoGuard
