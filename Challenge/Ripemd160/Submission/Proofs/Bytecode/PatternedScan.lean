import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Word
import Challenge.EvmProof.Memory

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest

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
  []

def loopPath : List Located :=
  [opAt 2863 .JUMPDEST,
   opAt 2864 (.Dup ⟨0, by decide⟩),
   pushAt 2865 1 251, opAt 2866 .DIV,
   pushAt 2867 1 11, opAt 2868 .MUL,
   opAt 2869 (.Dup ⟨1, by decide⟩),
   pushAt 2870 1 37, opAt 2871 .MUL,
   opAt 2872 .ADD, pushAt 2873 1 7, opAt 2874 .ADD,
   pushAt 2875 1 255, opAt 2876 .AND,
   opAt 2877 (.Dup ⟨1, by decide⟩),
   opAt 2878 .CALLDATALOAD,
   pushAt 2879 0 0, opAt 2880 .BYTE,
   opAt 2881 .XOR,
   opAt 2882 (.Swap ⟨0, by decide⟩),
   opAt 2883 (.Swap ⟨1, by decide⟩),
   opAt 2884 .OR,
   opAt 2885 (.Swap ⟨0, by decide⟩),
   pushAt 2886 1 1, opAt 2887 .ADD,
   opAt 2888 (.Dup ⟨0, by decide⟩),
   pushAt 2889 2 1000, opAt 2890 .LT,
   pushAt 2891 2 4932, opAt 2892 .JUMPI]

def exitPath : List Located :=
  [opAt 2893 .POP, pushAt 2894 2 1006, opAt 2895 .JUMPI]

def returnPath : List Located :=
  [pushAt 2896 20 766350606435067737561421097975693824639675460820,
   pushAt 2897 0 0, opAt 2898 .MSTORE,
   pushAt 2899 1 32, pushAt 2900 0 0, opAt 2901 .RETURN]

def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

def calldataByte (input : ByteArray) (i : Nat) : UInt256 :=
  UInt256.byteAt ⟨0⟩ (MachineState.readWord input i)

def expectedWord (i : Nat) : UInt256 :=
  UInt256.ofNat (expectedByte i).toNat

def scanAcc (input : ByteArray) : Nat → UInt256
  | 0 => 0
  | n + 1 =>
      UInt256.lor
        (UInt256.xor (expectedWord n) (calldataByte input n))
        (scanAcc input n)

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4932
    stack := [UInt256.ofNat n, scanAcc input n] }
def patternedEntry (input : ByteArray) : State := loopState input 0
def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4972
    stack := [UInt256.ofNat 1000, scanAcc input 1000] }
def hitEntry (input : ByteArray) : State := atPC input 4977
def fallbackState (input : ByteArray) : State := atPC input 1006

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5004
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

private abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

@[simp] private theorem pc2863 : Artifact.submissionArtifact.instructionPC 2863 = 4932 := by rfl
@[simp] private theorem pc2864 : Artifact.submissionArtifact.instructionPC 2864 = 4933 := by rfl
@[simp] private theorem pc2865 : Artifact.submissionArtifact.instructionPC 2865 = 4934 := by rfl
@[simp] private theorem pc2866 : Artifact.submissionArtifact.instructionPC 2866 = 4936 := by rfl
@[simp] private theorem pc2867 : Artifact.submissionArtifact.instructionPC 2867 = 4937 := by rfl
@[simp] private theorem pc2868 : Artifact.submissionArtifact.instructionPC 2868 = 4939 := by rfl
@[simp] private theorem pc2869 : Artifact.submissionArtifact.instructionPC 2869 = 4940 := by rfl
@[simp] private theorem pc2870 : Artifact.submissionArtifact.instructionPC 2870 = 4941 := by rfl
@[simp] private theorem pc2871 : Artifact.submissionArtifact.instructionPC 2871 = 4943 := by rfl
@[simp] private theorem pc2872 : Artifact.submissionArtifact.instructionPC 2872 = 4944 := by rfl
@[simp] private theorem pc2873 : Artifact.submissionArtifact.instructionPC 2873 = 4945 := by rfl
@[simp] private theorem pc2874 : Artifact.submissionArtifact.instructionPC 2874 = 4947 := by rfl
@[simp] private theorem pc2875 : Artifact.submissionArtifact.instructionPC 2875 = 4948 := by rfl
@[simp] private theorem pc2876 : Artifact.submissionArtifact.instructionPC 2876 = 4950 := by rfl
@[simp] private theorem pc2877 : Artifact.submissionArtifact.instructionPC 2877 = 4951 := by rfl
@[simp] private theorem pc2878 : Artifact.submissionArtifact.instructionPC 2878 = 4952 := by rfl
@[simp] private theorem pc2879 : Artifact.submissionArtifact.instructionPC 2879 = 4953 := by rfl
@[simp] private theorem pc2880 : Artifact.submissionArtifact.instructionPC 2880 = 4954 := by rfl
@[simp] private theorem pc2881 : Artifact.submissionArtifact.instructionPC 2881 = 4955 := by rfl
@[simp] private theorem pc2882 : Artifact.submissionArtifact.instructionPC 2882 = 4956 := by rfl
@[simp] private theorem pc2883 : Artifact.submissionArtifact.instructionPC 2883 = 4957 := by rfl
@[simp] private theorem pc2884 : Artifact.submissionArtifact.instructionPC 2884 = 4958 := by rfl
@[simp] private theorem pc2885 : Artifact.submissionArtifact.instructionPC 2885 = 4959 := by rfl
@[simp] private theorem pc2886 : Artifact.submissionArtifact.instructionPC 2886 = 4960 := by rfl
@[simp] private theorem pc2887 : Artifact.submissionArtifact.instructionPC 2887 = 4962 := by rfl
@[simp] private theorem pc2888 : Artifact.submissionArtifact.instructionPC 2888 = 4963 := by rfl
@[simp] private theorem pc2889 : Artifact.submissionArtifact.instructionPC 2889 = 4964 := by rfl
@[simp] private theorem pc2890 : Artifact.submissionArtifact.instructionPC 2890 = 4967 := by rfl
@[simp] private theorem pc2891 : Artifact.submissionArtifact.instructionPC 2891 = 4968 := by rfl
@[simp] private theorem pc2892 : Artifact.submissionArtifact.instructionPC 2892 = 4971 := by rfl
@[simp] private theorem pc2893 : Artifact.submissionArtifact.instructionPC 2893 = 4972 := by rfl
@[simp] private theorem pc2894 : Artifact.submissionArtifact.instructionPC 2894 = 4973 := by rfl
@[simp] private theorem pc2895 : Artifact.submissionArtifact.instructionPC 2895 = 4976 := by rfl
@[simp] private theorem pc2896 : Artifact.submissionArtifact.instructionPC 2896 = 4977 := by rfl
@[simp] private theorem pc2897 : Artifact.submissionArtifact.instructionPC 2897 = 4998 := by rfl
@[simp] private theorem pc2898 : Artifact.submissionArtifact.instructionPC 2898 = 4999 := by rfl
@[simp] private theorem pc2899 : Artifact.submissionArtifact.instructionPC 2899 = 5000 := by rfl
@[simp] private theorem pc2900 : Artifact.submissionArtifact.instructionPC 2900 = 5002 := by rfl
@[simp] private theorem pc2901 : Artifact.submissionArtifact.instructionPC 2901 = 5003 := by rfl

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
  have hbyte := Challenge.EvmProof.Bytes.byteAt_zero_readWord input i
  have hfrom : (YulSemantics.EVM.byteFrom input.toList i).toNat = input[i].toNat := by
    simp [YulSemantics.EVM.byteFrom, List.getD, Challenge.EvmProof.Bytecode.toList_eq_data]
    rw [ByteArray.getElem?_eq_getElem hi, Option.getD_some]
  simpa [calldataByte, hfrom] using hbyte

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

def sound (path : List Located) {s t : State}
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
    patternedEntry input = loopState input 0 := by
  simp [patternedEntry, loopState, scanAcc]

theorem run_loop_more (input : ByteArray) (n : Nat) (hn : n < 999)
    (hfit : n < input.size) :
    run loopPath (loopState input n) = some (loopState input (n + 1)) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 4932 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2863 (by rfl)
  have hexp := expected_evm n (by omega)
  have hbyte : calldataByte input n =
      UInt256.byteAt ⟨0⟩ (MachineState.readWord input n) := rfl
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
  have hfalse : ¬ UInt256.isTrue (scanAcc input 1000) := by
    rw [hz]; decide
  simp (config := { maxSteps := 1000000 })
    [exitPath, opAt, pushAt, wfOp, loopExitState, hitEntry, atPC, hz, hfalse,
    UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_exit_miss (input : ByteArray) (hne : scanAcc input 1000 ≠ 0) :
    run exitPath (loopExitState input) = some (fallbackState input) := by
  have htrue : UInt256.isTrue (scanAcc input 1000) := by
    intro hz
    apply hne
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have hdest : Decode.isValidJumpDest submissionBytecode 1006 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 682 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [exitPath, opAt, pushAt, wfOp, loopExitState, fallbackState,
    atPC, htrue, hdest, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

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

/-- One 29-iteration slice. Matches the working 1000-a bound.
    `iterateBounded 50` in this file plus GuardSpec was `8b5c0254`. -/
def gasSteps_loop_slice (input : ByteArray) (hsize : input.size = 1000)
    (start len : Nat) (hstart : start + len ≤ 999) :
    GasSteps (loopState input start) (loopState input (start + len)) := by
  let step : ∀ n, n < len →
      GasSteps (loopState input (start + n)) (loopState input (start + n + 1)) :=
    fun n hn =>
      sound loopPath (run_loop_more input (start + n) (by omega)
        (by rw [hsize]; omega))
  simpa [Nat.add_assoc] using GasSteps.iterateBounded len step

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = paddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    wordBytes_eq_paddedDigest, paddedDigest_size] using h

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
