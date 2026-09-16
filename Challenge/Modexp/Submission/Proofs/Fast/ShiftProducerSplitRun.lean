import Challenge.Modexp.Submission.Proofs.Fast.ShiftProducerCore

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.ShiftProducerSplitRun
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open ShiftProducerCanonical

/-! Exact retained-accumulator producer fragments: the hit block calls the
leading-limb entry 4514 with only the return address, and the copy block moves
the reduced accumulator from 2112 to ACC. The run theorem is parameterized by
the actual code's jump fact, without claiming the artifact contains these
instructions. -/
def hitProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 1 96, .push 2 2112, .op .CALLDATACOPY,
   .push 0 0, .push 2 2080, .op .MSTORE,
   .push 2 2390, .push 2 4143, .op .JUMP]

def copyProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨0, by decide⟩), .push 2 2112, .push 2 256,
   .op .MCOPY]

def frame (s : State) (mem : ByteArray) (pc n : Nat) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat pc, memory := mem, stack := UInt256.ofNat (32*n) :: rest}

def csubEntry (s : State) (mem : ByteArray) (n : Nat) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 4143, memory := mem, stack := [UInt256.ofNat 2390, UInt256.ofNat (32*n)] ++ rest}

theorem run_hit (s : State) (mem input : ByteArray) (n : Nat) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hact : 89 ≤ s.activeWords.toNat) (hdata : s.executionEnv.calldata = input)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 4143 = true) :
    runInstructions hitProgram (frame s mem 2354 n rest) =
      some (csubEntry s (hitMemory mem input n) n rest) := by
  have hc1 : rest.length+1 < 1024 := by omega
  have hc2 : rest.length+2 < 1024 := by omega
  have hc3 : rest.length+3 < 1024 := by omega
  have hc4 : rest.length+4 < 1024 := by omega
  have hsz : 32*n % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 32*n := Nat.mod_eq_of_lt (by omega)
  have haT := Monpro.activeWords_fix s 2112 (32*n) (by omega) (by omega) (by omega)
  have haN := Monpro.activeWords_fix s 2080 32 (by decide) (by omega) (by omega)
  have hz : (⟨0⟩ : UInt256).toNat = 0 := rfl
  simp [hitProgram,runInstructions,Challenge.EvmProof.Stepper.runInstr,
    frame,csubEntry,hitMemory,Exp.storeWord,hdata,hjump,hc1,hc2,hc3,hc4,hsz,hz,
    State.activeWordsAfterUInt256,haT,haN,Nat.add_assoc,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_copy (s : State) (mem : ByteArray) (n : Nat) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hact : 89 ≤ s.activeWords.toNat) :
    runInstructions copyProgram (frame s mem 2390 n rest) =
      some (frame s (Exp.mcopyMem mem 256 2112 (32*n)) 2399 n rest) := by
  have hc1 : rest.length+1 < 1024 := by omega
  have hc2 : rest.length+2 < 1024 := by omega
  have hc3 : rest.length+3 < 1024 := by omega
  have hc4 : rest.length+4 < 1024 := by omega
  have hsz : 32*n % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 32*n := Nat.mod_eq_of_lt (by omega)
  have haD := Monpro.activeWords_fix s 256 (32*n) (by omega) (by omega) (by omega)
  have haB := Monpro.activeWords_fix s 2112 (32*n) (by omega) (by omega) (by omega)
  have haL := Monpro.activeWords_fix s 2752 32 (by decide) (by omega) (by omega)
  have haDN := Exp.activeWordsAfter_fix s.activeWords.toNat 256 (32*n) (by omega) (by omega) hact
  have haBN := Exp.activeWordsAfter_fix s.activeWords.toNat 2112 (32*n) (by omega) (by omega) hact
  have hamod : s.activeWords.toNat % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = s.activeWords.toNat :=
    Nat.mod_eq_of_lt s.activeWords.val.isLt
  have haSelf : UInt256.ofNat s.activeWords.toNat = s.activeWords :=
    (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  simp [copyProgram,runInstructions,Challenge.EvmProof.Stepper.runInstr,
    frame,Exp.mcopyMem,hc1,hc2,hc3,hc4,hsz,
    State.activeWordsAfterUInt256,State.activeWordsAfterUInt256_2,haD,haB,haL,haDN,haBN,hamod,haSelf,Nat.add_assoc,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

#print axioms run_hit
#print axioms run_copy
end Challenge.Modexp.Submission.Proofs.Fast.ShiftProducerSplitRun
