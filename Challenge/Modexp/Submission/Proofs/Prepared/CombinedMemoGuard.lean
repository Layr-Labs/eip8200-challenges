import Challenge.Modexp.ProofSupport.InitialState
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
import Challenge.Modexp.Submission.Proofs.Bytecode.MemoLogic
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.CombinedMemoGuard
open Challenge.Modexp Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
private theorem split_low (input : ByteArray) (off d : Nat) (hd : d ≤ 32)
 (hv : Precompile.bytesToNatPadded input off 32 < 256^(32-d)) :
 Precompile.bytesToNatPadded input off d = 0 ∧
 Precompile.bytesToNatPadded input (off+d) (32-d) = Precompile.bytesToNatPadded input off 32 := by
 have hs := Bytes.bytesToNatPadded_add input off d (32-d)
 rw [show d+(32-d)=32 by omega] at hs
 have hz : Precompile.bytesToNatPadded input off d = 0 := by
  by_contra hn
  have hp : 1 ≤ Precompile.bytesToNatPadded input off d := by omega
  have hmul := Nat.mul_le_mul_right (256^(32-d)) hp
  simp only [one_mul] at hmul
  omega
 exact ⟨hz,by simpa [hz] using hs.symm⟩
private theorem read_shift (input : ByteArray) (off d : Nat) (hd : d ≤ 32)
 (hv : Precompile.bytesToNatPadded input off 32 < 256^(32-d)) :
 (MachineState.readWord input (off+d)).toNat =
 Precompile.bytesToNatPadded input off 32 * 256^d +
 Precompile.bytesToNatPadded input (off+32) d := by
 rw [Bytes.readWord_toNat]
 have hs := Bytes.bytesToNatPadded_add input (off+d) (32-d) d
 rw [show 32-d+d=32 by omega,show off+d+(32-d)=off+32 by omega,
  (split_low input off d hd hv).2] at hs
 exact hs
def packedSum (input : ByteArray) : UInt256 :=
 MachineState.readWord input 68 + (MachineState.readWord input 40 + MachineState.readWord input 6)
def packed (input : ByteArray) : UInt256 := UInt256.xor (UInt256.ofNat 0x020001002003ffff80) (packedSum input)
def guard (input : ByteArray) : UInt256 := UInt256.lor (MachineState.readWord input 100) (packed input)
theorem reads (input : ByteArray) (hvalid : ValidInput input) :
 (MachineState.readWord input 6).toNat = baseSize input*281474976710656 ∧
 (MachineState.readWord input 40).toNat = exponentSize input*18446744073709551616 ∧
 (MachineState.readWord input 68).toNat < 281474976710656 := by
 obtain ⟨_,hb,he,hm⟩ := hvalid
 have h6 := read_shift input 0 6 (by omega) (by change baseSize input < _; norm_num; omega)
 have h40 := read_shift input 32 8 (by omega) (by change exponentSize input < _; norm_num; omega)
 have h68 := read_shift input 64 4 (by omega) (by change modulusSize input < _; norm_num; omega)
 have he0 := (split_low input 32 6 (by omega) (by change exponentSize input < _; norm_num; omega)).1
 have hm0 := (split_low input 64 8 (by omega) (by change modulusSize input < _; norm_num; omega)).1
 have hx := Bytes.bytesToNatPadded_lt_pow input 96 4
 norm_num at h6 h40 h68 hx
 change _ = baseSize input*281474976710656 + _ at h6
 change _ = exponentSize input*18446744073709551616 + _ at h40
 change _ = modulusSize input*4294967296 + _ at h68
 rw [he0,Nat.add_zero] at h6
 rw [hm0,Nat.add_zero] at h40
 exact ⟨h6,h40,by omega⟩
theorem sum_toNat (input : ByteArray) (hvalid : ValidInput input) :
 (packedSum input).toNat = (MachineState.readWord input 68).toNat +
 exponentSize input*18446744073709551616 + baseSize input*281474976710656 := by
 obtain ⟨h6,h40,h68⟩ := reads input hvalid
 obtain ⟨_,hb,he,hm⟩ := hvalid
 rw [packedSum,Word.word_toNat_add,Word.word_toNat_add,h6,h40,
  Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]
 omega
theorem packed_zero_iff (input : ByteArray) (hvalid : ValidInput input) :
 packed input = 0 ↔ baseSize input=1 ∧ exponentSize input=2 ∧
 MachineState.readWord input 68=UInt256.ofNat 137506062208 := by
 have hs := sum_toNat input hvalid
 have hw := (reads input hvalid).2.2
 obtain ⟨_,hb,he,hm⟩ := hvalid
 rw [packed,WindowGuardLogic.wordXor_eq_zero_iff]
 have hc : (UInt256.ofNat 0x020001002003ffff80).toNat = 36893769759901876096 := by decide
 have hd : (UInt256.ofNat 137506062208).toNat = 137506062208 := by decide
 constructor
 · intro h
   have hn := congrArg UInt256.toNat h
   rw [hc,hs] at hn
   have he2 : exponentSize input=2 := by omega
   have hb1 : baseSize input=1 := by omega
   refine ⟨hb1,he2,Word.word_ext ?_⟩
   rw [hd]
   omega
 · rintro ⟨hb1,he2,h68⟩
   apply Word.word_ext
   rw [hc,hs,hb1,he2,h68,hd]
theorem guard_zero_iff (input : ByteArray) (hvalid : ValidInput input) :
 guard input=0 ↔ MemoLogic.Matches input := by
 simp only [guard,WindowGuardLogic.wordOr_eq_zero_iff,packed_zero_iff input hvalid,MemoLogic.Matches]
 tauto
theorem guardNat_zero_iff (input : ByteArray) (hvalid : ValidInput input) :
 (guard input).toNat=0 ↔ MemoLogic.Matches input := by
 constructor
 · intro h
   exact (guard_zero_iff input hvalid).1 (Word.word_ext h)
 · intro h
   rw [(guard_zero_iff input hvalid).2 h]
   rfl
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
def program : List Instr :=
 [.push 1 6,.op .CALLDATALOAD,.push 1 40,.op .CALLDATALOAD,.op .ADD,
  .push 1 68,.op .CALLDATALOAD,.op .ADD,.push 9 36893769759901876096,.op .XOR,
  .push 1 100,.op .CALLDATALOAD,.op .OR,.push 2 519,.op .JUMPI]
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
