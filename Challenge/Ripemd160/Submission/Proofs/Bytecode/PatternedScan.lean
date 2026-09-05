import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedGuardSpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located := Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) : Located :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) : Located :=
  ⟨index, .push width value, hget, hwf⟩

def entryPath : List Located :=
  [opAt 2911 .JUMPDEST, pushAt 2912 0 0, pushAt 2913 0 0]

def loopPath : List Located :=
  [opAt 2914 .JUMPDEST,
   opAt 2915 (.Dup ⟨0, by decide⟩),
   pushAt 2916 1 251, opAt 2917 .DIV,
   pushAt 2918 1 11, opAt 2919 .MUL,
   opAt 2920 (.Dup ⟨1, by decide⟩),
   pushAt 2921 1 37, opAt 2922 .MUL,
   opAt 2923 .ADD, pushAt 2924 1 7, opAt 2925 .ADD,
   pushAt 2926 1 255, opAt 2927 .AND,
   opAt 2928 (.Dup ⟨1, by decide⟩),
   opAt 2929 .CALLDATALOAD,
   pushAt 2930 1 248, opAt 2931 .SHR,
   opAt 2932 .XOR,
   opAt 2933 (.Swap ⟨0, by decide⟩),
   opAt 2934 (.Swap ⟨1, by decide⟩),
   opAt 2935 .OR,
   opAt 2936 (.Swap ⟨0, by decide⟩),
   pushAt 2937 1 1, opAt 2938 .ADD,
   opAt 2939 (.Dup ⟨0, by decide⟩),
   pushAt 2940 2 1000, opAt 2941 .LT,
   pushAt 2942 2 5303, opAt 2943 .JUMPI]

def exitPath : List Located :=
  [opAt 2944 .POP, opAt 2945 .ISZERO,
   pushAt 2946 2 5354, opAt 2947 .JUMPI]

def missJumpPath : List Located :=
  [pushAt 2948 2 1006, opAt 2949 .JUMP]

def returnPath : List Located :=
  [opAt 2950 .JUMPDEST,
   pushAt 2951 20 766350606435067737561421097975693824639675460820,
   pushAt 2952 0 0, opAt 2953 .MSTORE,
   pushAt 2954 1 32, pushAt 2955 0 0, opAt 2956 .RETURN]

def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

def calldataByte (input : ByteArray) (i : Nat) : UInt256 :=
  UInt256.shiftRight (MachineState.readWord input i) (UInt256.ofNat 248)

def expectedWord (i : Nat) : UInt256 :=
  UInt256.ofNat (expectedByte i).toNat

def scanAcc (input : ByteArray) : Nat → UInt256
  | 0 => 0
  | n + 1 =>
      UInt256.lor
        (UInt256.xor (expectedWord n) (calldataByte input n))
        (scanAcc input n)

def patternedEntry (input : ByteArray) : State := atPC input 5300
def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5303
    stack := [UInt256.ofNat n, scanAcc input n] }
def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5344
    stack := [UInt256.ofNat 1000, scanAcc input 1000] }
def hitEntry (input : ByteArray) : State := atPC input 5354
def fallbackState (input : ByteArray) : State := atPC input 1006

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5382
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

private abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

@[simp] private theorem pc2911 : Artifact.submissionArtifact.instructionPC 2911 = 5300 := by rfl
@[simp] private theorem pc2912 : Artifact.submissionArtifact.instructionPC 2912 = 5301 := by rfl
@[simp] private theorem pc2913 : Artifact.submissionArtifact.instructionPC 2913 = 5302 := by rfl
@[simp] private theorem pc2914 : Artifact.submissionArtifact.instructionPC 2914 = 5303 := by rfl
@[simp] private theorem pc2915 : Artifact.submissionArtifact.instructionPC 2915 = 5304 := by rfl
@[simp] private theorem pc2916 : Artifact.submissionArtifact.instructionPC 2916 = 5305 := by rfl
@[simp] private theorem pc2917 : Artifact.submissionArtifact.instructionPC 2917 = 5307 := by rfl
@[simp] private theorem pc2918 : Artifact.submissionArtifact.instructionPC 2918 = 5308 := by rfl
@[simp] private theorem pc2919 : Artifact.submissionArtifact.instructionPC 2919 = 5310 := by rfl
@[simp] private theorem pc2920 : Artifact.submissionArtifact.instructionPC 2920 = 5311 := by rfl
@[simp] private theorem pc2921 : Artifact.submissionArtifact.instructionPC 2921 = 5312 := by rfl
@[simp] private theorem pc2922 : Artifact.submissionArtifact.instructionPC 2922 = 5314 := by rfl
@[simp] private theorem pc2923 : Artifact.submissionArtifact.instructionPC 2923 = 5315 := by rfl
@[simp] private theorem pc2924 : Artifact.submissionArtifact.instructionPC 2924 = 5316 := by rfl
@[simp] private theorem pc2925 : Artifact.submissionArtifact.instructionPC 2925 = 5318 := by rfl
@[simp] private theorem pc2926 : Artifact.submissionArtifact.instructionPC 2926 = 5319 := by rfl
@[simp] private theorem pc2927 : Artifact.submissionArtifact.instructionPC 2927 = 5321 := by rfl
@[simp] private theorem pc2928 : Artifact.submissionArtifact.instructionPC 2928 = 5322 := by rfl
@[simp] private theorem pc2929 : Artifact.submissionArtifact.instructionPC 2929 = 5323 := by rfl
@[simp] private theorem pc2930 : Artifact.submissionArtifact.instructionPC 2930 = 5324 := by rfl
@[simp] private theorem pc2931 : Artifact.submissionArtifact.instructionPC 2931 = 5326 := by rfl
@[simp] private theorem pc2932 : Artifact.submissionArtifact.instructionPC 2932 = 5327 := by rfl
@[simp] private theorem pc2933 : Artifact.submissionArtifact.instructionPC 2933 = 5328 := by rfl
@[simp] private theorem pc2934 : Artifact.submissionArtifact.instructionPC 2934 = 5329 := by rfl
@[simp] private theorem pc2935 : Artifact.submissionArtifact.instructionPC 2935 = 5330 := by rfl
@[simp] private theorem pc2936 : Artifact.submissionArtifact.instructionPC 2936 = 5331 := by rfl
@[simp] private theorem pc2937 : Artifact.submissionArtifact.instructionPC 2937 = 5332 := by rfl
@[simp] private theorem pc2938 : Artifact.submissionArtifact.instructionPC 2938 = 5334 := by rfl
@[simp] private theorem pc2939 : Artifact.submissionArtifact.instructionPC 2939 = 5335 := by rfl
@[simp] private theorem pc2940 : Artifact.submissionArtifact.instructionPC 2940 = 5336 := by rfl
@[simp] private theorem pc2941 : Artifact.submissionArtifact.instructionPC 2941 = 5339 := by rfl
@[simp] private theorem pc2942 : Artifact.submissionArtifact.instructionPC 2942 = 5340 := by rfl
@[simp] private theorem pc2943 : Artifact.submissionArtifact.instructionPC 2943 = 5343 := by rfl
@[simp] private theorem pc2944 : Artifact.submissionArtifact.instructionPC 2944 = 5344 := by rfl
@[simp] private theorem pc2945 : Artifact.submissionArtifact.instructionPC 2945 = 5345 := by rfl
@[simp] private theorem pc2946 : Artifact.submissionArtifact.instructionPC 2946 = 5346 := by rfl
@[simp] private theorem pc2947 : Artifact.submissionArtifact.instructionPC 2947 = 5349 := by rfl
@[simp] private theorem pc2948 : Artifact.submissionArtifact.instructionPC 2948 = 5350 := by rfl
@[simp] private theorem pc2949 : Artifact.submissionArtifact.instructionPC 2949 = 5353 := by rfl
@[simp] private theorem pc2950 : Artifact.submissionArtifact.instructionPC 2950 = 5354 := by rfl
@[simp] private theorem pc2951 : Artifact.submissionArtifact.instructionPC 2951 = 5355 := by rfl
@[simp] private theorem pc2952 : Artifact.submissionArtifact.instructionPC 2952 = 5376 := by rfl
@[simp] private theorem pc2953 : Artifact.submissionArtifact.instructionPC 2953 = 5377 := by rfl
@[simp] private theorem pc2954 : Artifact.submissionArtifact.instructionPC 2954 = 5378 := by rfl
@[simp] private theorem pc2955 : Artifact.submissionArtifact.instructionPC 2955 = 5380 := by rfl
@[simp] private theorem pc2956 : Artifact.submissionArtifact.instructionPC 2956 = 5381 := by rfl

private theorem ofNat_mul (a b : Nat) (h : a * b < 2 ^ 256) :
    UInt256.mul (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a * b) := by
  apply Challenge.EvmProof.Word.word_ext
  have hmul : (UInt256.mul (UInt256.ofNat a) (UInt256.ofNat b)).toNat =
      ((UInt256.ofNat a).toNat * (UInt256.ofNat b).toNat) % 2 ^ 256 := by
    change ((UInt256.ofNat a).val * (UInt256.ofNat b).val).val = _
    rw [Fin.val_mul]
    rfl
  rw [hmul, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mul_mod,
    Nat.mod_eq_of_lt h]

private theorem ofNat_land_ff (n : Nat) (hn : n < 2 ^ 256) :
    UInt256.land (UInt256.ofNat n) (UInt256.ofNat 255) =
      UInt256.ofNat (n % 256) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by norm_num : 255 < 2 ^ 256)]
  have hmod : n % 256 < 2 ^ 256 := Nat.lt_trans (Nat.mod_lt n (by decide)) (by norm_num)
  rw [Nat.mod_eq_of_lt hmod]
  change n &&& 255 = n % 256
  rw [show 255 = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]

theorem expectedByte_toNat (i : Nat) :
    (expectedByte i).toNat = (i * 37 + i / 251 * 11 + 7) % 256 := by
  unfold expectedByte
  rw [UInt8.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))

theorem expected_evm (n : Nat) (hn : n < 1000) :
    UInt256.land
      (UInt256.ofNat n * UInt256.ofNat 37 +
        UInt256.ofNat n / UInt256.ofNat 251 * UInt256.ofNat 11 +
        UInt256.ofNat 7)
      (UInt256.ofNat 255) = expectedWord n := by
  have hmul37 : n * 37 < 2 ^ 256 := by omega
  have hdiv : n / 251 ≤ 3 := by omega
  have hmul11 : (n / 251) * 11 < 2 ^ 256 := by omega
  have hsum : n * 37 + n / 251 * 11 + 7 < 2 ^ 256 := by omega
  have hmul : UInt256.mul (UInt256.ofNat n) (UInt256.ofNat 37) =
      UInt256.ofNat (n * 37) := ofNat_mul n 37 hmul37
  have hmulq : UInt256.mul (UInt256.ofNat (n / 251)) (UInt256.ofNat 11) =
      UInt256.ofNat ((n / 251) * 11) := ofNat_mul (n / 251) 11 hmul11
  have hdivv : UInt256.ofNat n / UInt256.ofNat 251 = UInt256.ofNat (n / 251) := by
    apply Challenge.EvmProof.Word.word_ext
    have hb : (UInt256.ofNat 251).toNat = 251 := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat]; decide
    have ha : (UInt256.ofNat n).toNat = n := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    change ((UInt256.ofNat n).val / (UInt256.ofNat 251).val).val = _
    -- Fin.div uses Nat.div on values
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    have hmod : n / 251 < 2 ^ 256 := by omega
    rw [Nat.mod_eq_of_lt hmod]
    change (UInt256.ofNat n).toNat / (UInt256.ofNat 251).toNat = n / 251
    rw [ha, hb]
  have hstar : UInt256.ofNat n * UInt256.ofNat 37 =
      UInt256.mul (UInt256.ofNat n) (UInt256.ofNat 37) := rfl
  have hstarq : UInt256.ofNat (n / 251) * UInt256.ofNat 11 =
      UInt256.mul (UInt256.ofNat (n / 251)) (UInt256.ofNat 11) := rfl
  rw [hstar, hmul, hdivv, hstarq, hmulq]
  have hadd₁ := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := n * 37) (b := (n / 251) * 11) (by omega)
  have hadd₂ := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := n * 37 + (n / 251) * 11) (b := 7) (by omega)
  rw [hadd₁, hadd₂, ofNat_land_ff _ (by omega), expectedWord,
    expectedByte_toNat]

theorem calldataByte_eq (input : ByteArray) (i : Nat) (hi : i < input.size) :
    calldataByte input i = UInt256.ofNat input[i].toNat := by
  have hshift := Challenge.EvmProof.Bytes.shiftRight_readWord
    input i 1 (by omega) (by omega)
  have hbyte : EVM.Precompile.bytesToNatPadded input i 1 = input[i].toNat := by
    unfold EVM.Precompile.bytesToNatPadded
    have hread := MachineState.readPadded_getElem?_getD (bs := input) (off := i)
      (width := 1) (j := 0)
    -- fall back to a small decide-friendly rewrite
    simp [MachineState.readPadded, Data.Bytes.bytesToBigEndianNat,
      Challenge.EvmProof.Bytecode.toList_eq_data] 
    have hget : input[i]?.getD 0 = input[i] := by
      rw [ByteArray.getElem?_eq_getElem hi, Option.getD_some]
    -- bytesToNatPadded of one in-range byte is that byte
    exact Challenge.EvmProof.Bytes.bytesToNatPadded_succ input i 0 |>.trans
      (by simp [YulSemantics.EVM.byteFrom, hget])
  simpa [calldataByte] using hshift.trans (congrArg UInt256.ofNat hbyte)

theorem calldataByte_patterned (i : Nat) (hi : i < 1000) :
    calldataByte patternedInput i = expectedWord i := by
  have hsize : i < patternedInput.size := by
    rw [patternedInput_size]; exact hi
  rw [calldataByte_eq patternedInput i hsize, patternedInput_getElem i hsize,
    expectedWord]

theorem scanAcc_zero_iff (input : ByteArray) (n : Nat)
    (hbound : ∀ i, i < n → i < input.size) :
    scanAcc input n = 0 ↔ ∀ i, i < n → input[i] = expectedByte i := by
  induction n with
  | zero =>
      simp [scanAcc]
  | succ n ih =>
      rw [scanAcc, KnownInputLogic.wordOr_eq_zero_iff,
        KnownInputLogic.wordXor_eq_zero_iff, ih (fun i hi => hbound i (by omega))]
      constructor
      · rintro ⟨hcur, hprev⟩
        intro i hi
        by_cases heq : i = n
        · subst i
          have hsz : n < input.size := hbound n (by omega)
          have hbyte := calldataByte_eq input n hsz
          rw [expectedWord, hbyte] at hcur
          apply UInt8.eq_of_toNat_eq
          have hn : (expectedByte n).toNat = (UInt256.ofNat (expectedByte n).toNat).toNat := by
            rw [Challenge.EvmProof.Word.word_toNat_ofNat]
            exact (Nat.mod_eq_of_lt (Nat.lt_trans (expectedByte n).toNat_lt (by norm_num))).symm
          have hg : input[n].toNat = (UInt256.ofNat input[n].toNat).toNat := by
            rw [Challenge.EvmProof.Word.word_toNat_ofNat]
            exact (Nat.mod_eq_of_lt (Nat.lt_trans input[n].toNat_lt (by norm_num))).symm
          rw [hn, hg, hcur]
        · exact hprev i (by omega)
      · intro hall
        have hsz : n < input.size := hbound n (by omega)
        refine ⟨?_, fun i hi => hall i (by omega)⟩
        rw [expectedWord, calldataByte_eq input n hsz, hall n (by omega)]

theorem scanAcc_patterned (n : Nat) (hn : n ≤ 1000) :
    scanAcc patternedInput n = 0 := by
  rw [scanAcc_zero_iff patternedInput n (fun i hi => by
    rw [patternedInput_size]; omega)]
  intro i hi
  have hsz : i < patternedInput.size := by
    rw [patternedInput_size]; omega
  exact patternedInput_getElem i hsz

theorem scanAcc_zero_iff_eq (input : ByteArray) (hsize : input.size = 1000) :
    scanAcc input 1000 = 0 ↔ input = patternedInput := by
  rw [scanAcc_zero_iff input 1000 (fun i hi => by rw [hsize]; exact hi)]
  constructor
  · intro hall
    apply ByteArray.ext
    · rw [hsize, patternedInput_size]
    · intro i hi₁ hi₂
      have hi : i < 1000 := by
        rw [hsize] at hi₁; exact hi₁
      rw [hall i hi, patternedInput_getElem i (by
        rw [patternedInput_size]; exact hi)]
  · intro h i hi
    subst input
    exact patternedInput_getElem i (by rw [patternedInput_size]; exact hi)

private def sound (path : List Located) {s t : State}
    (h : run path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) : GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    path hcode hfork h hrun hnp

theorem run_entry (input : ByteArray) :
    run entryPath (patternedEntry input) = some (loopState input 0) := by
  simp [entryPath, opAt, pushAt, wfOp, patternedEntry, atPC, loopState, scanAcc,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_loop_more (input : ByteArray) (n : Nat) (hn : n < 999)
    (hfit : n < input.size) :
    run loopPath (loopState input n) = some (loopState input (n + 1)) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 5303 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2914 (by rfl)
  have hexp := expected_evm n (by omega)
  have hbyte : calldataByte input n =
      UInt256.shiftRight (MachineState.readWord input n) (UInt256.ofNat 248) := rfl
  have hacc : scanAcc input (n + 1) =
      UInt256.lor (UInt256.xor (expectedWord n) (calldataByte input n))
        (scanAcc input n) := rfl
  have hlt : n + 1 < 1000 := by omega
  have hcond : (UInt256.lt (UInt256.ofNat (n + 1)) (UInt256.ofNat 1000)).toNat ≠ 0 := by
    unfold UInt256.lt
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : n + 1 < 2 ^ 256),
      Nat.mod_eq_of_lt (by norm_num : 1000 < 2 ^ 256), if_pos hlt]
    decide
  simp (config := { maxSteps := 1000000 })
    [loopPath, opAt, pushAt, wfOp, loopState, hdest, hexp, hbyte, hacc, hcond,
    List.exchange, UInt256.isTrue, BooleanSelect.xor_comm, Word.lor_comm,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_loop_last (input : ByteArray) (hfit : 999 < input.size) :
    run loopPath (loopState input 999) = some (loopExitState input) := by
  have hexp := expected_evm 999 (by decide)
  have hfalse : ¬ UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 1000) (UInt256.ofNat 1000)) := by decide
  have hcond : (UInt256.lt (UInt256.ofNat 1000) (UInt256.ofNat 1000)).toNat = 0 := by
    decide
  simp (config := { maxSteps := 1000000 })
    [loopPath, opAt, pushAt, wfOp, loopState, loopExitState, scanAcc, hexp,
    hfalse, hcond, List.exchange, UInt256.isTrue, BooleanSelect.xor_comm,
    Word.lor_comm,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_exit_hit (input : ByteArray) (hz : scanAcc input 1000 = 0) :
    run exitPath (loopExitState input) = some (hitEntry input) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 5354 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2950 (by rfl)
  have hfalse : ¬ UInt256.isTrue (scanAcc input 1000) := by
    rw [hz]; decide
  simp (config := { maxSteps := 1000000 })
    [exitPath, opAt, pushAt, wfOp, loopExitState, hitEntry, atPC, hz, hfalse,
    hdest, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_exit_miss (input : ByteArray) (hne : scanAcc input 1000 ≠ 0) :
    run (exitPath ++ missJumpPath) (loopExitState input) =
      some (fallbackState input) := by
  have htrue : UInt256.isTrue (scanAcc input 1000) := by
    intro hz
    apply hne
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have hdest : Decode.isValidJumpDest submissionBytecode 1006 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 682 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [exitPath, missJumpPath, opAt, pushAt, wfOp, loopExitState, fallbackState,
    atPC, htrue, hdest, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, List.append]

theorem run_return :
    run returnPath (hitEntry patternedInput) = some (returnedState patternedInput) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [returnPath, opAt, pushAt, wfOp, hitEntry, atPC, returnedState,
    answerMemory, storeWord, paddedDigestWord,
    MachineState.mstore, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

private def gasSteps_loop (input : ByteArray) (hsize : input.size = 1000) :
    GasSteps (loopState input 0) (loopExitState input) := by
  let step : ∀ n, n < 999 → GasSteps (loopState input n) (loopState input (n + 1)) :=
    fun n hn => sound loopPath (run_loop_more input n hn (by rw [hsize]; omega))
  exact (GasSteps.iterateBounded 999 step).trans
    (sound loopPath (run_loop_last input (by rw [hsize]; decide)))

def gasSteps_fromEntry_hit (input : ByteArray) (hsize : input.size = 1000)
    (hz : scanAcc input 1000 = 0) :
    GasSteps (patternedEntry input) (returnedState input) :=
  (sound entryPath (run_entry input)).trans
    ((gasSteps_loop input hsize).trans
      ((sound exitPath (run_exit_hit input hz)).trans
        (by
          have h := scanAcc_zero_iff_eq input hsize |>.1 hz
          subst input
          exact sound returnPath run_return)))

def gasSteps_fromEntry_miss (input : ByteArray) (hsize : input.size = 1000)
    (hne : scanAcc input 1000 ≠ 0) :
    GasSteps (patternedEntry input) (fallbackState input) :=
  (sound entryPath (run_entry input)).trans
    ((gasSteps_loop input hsize).trans
      (sound (exitPath ++ missJumpPath) (run_exit_miss input hne)))

def gasSteps_patterned :
    GasSteps (patternedEntry patternedInput) (returnedState patternedInput) :=
  gasSteps_fromEntry_hit patternedInput patternedInput_size
    (scanAcc_patterned 1000 (by decide))

def gasSteps_patterned_miss (input : ByteArray) (hsize : input.size = 1000)
    (hne : input ≠ patternedInput) :
    GasSteps (patternedEntry input) (fallbackState input) :=
  gasSteps_fromEntry_miss input hsize (by
    intro hz
    exact hne ((scanAcc_zero_iff_eq input hsize).1 hz))

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = paddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    wordBytes_eq_paddedDigest, paddedDigest_size] using h

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
