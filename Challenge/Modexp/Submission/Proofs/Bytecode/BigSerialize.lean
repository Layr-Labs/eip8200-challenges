import Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentGas
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
/-! # Certified multi-limb result serialization and return -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigSerialize

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open BigExponent

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def outerFinishGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 717 .JUMPDEST, opAt 718 (.Dup ⟨4, by decide⟩),
   opAt 719 (.Dup ⟨1, by decide⟩), opAt 720 .LT, opAt 721 .ISZERO,
   pushAt 722 2 1120, opAt 723 .JUMPI]

def serializerEntryPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 836 .JUMPDEST, opAt 837 .POP, pushAt 838 0 0]

def serializerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 839 .JUMPDEST, opAt 840 (.Dup ⟨5, by decide⟩),
   opAt 841 (.Dup ⟨1, by decide⟩), opAt 842 .LT, opAt 843 .ISZERO,
   pushAt 844 2 1182, opAt 845 .JUMPI]

def serializerBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 846 (.Dup ⟨0, by decide⟩), pushAt 847 1 1,
   opAt 848 (.Dup ⟨7, by decide⟩), opAt 849 .SUB, opAt 850 .SUB,
   opAt 851 (.Dup ⟨0, by decide⟩), pushAt 852 1 5, opAt 853 .SHR,
   pushAt 854 1 31, opAt 855 (.Dup ⟨2, by decide⟩), opAt 856 .AND,
   pushAt 857 1 3, opAt 858 .SHL, pushAt 859 1 255,
   opAt 860 (.Dup ⟨2, by decide⟩), pushAt 861 1 5, opAt 862 .SHL,
   pushAt 863 2 2048, opAt 864 .ADD, opAt 865 .MLOAD,
   opAt 866 (.Dup ⟨2, by decide⟩), opAt 867 .SHR, opAt 868 .AND,
   opAt 869 (.Dup ⟨4, by decide⟩), pushAt 870 2 6144,
   opAt 871 .ADD, opAt 872 .MSTORE8, opAt 873 .POP, opAt 874 .POP,
   opAt 875 .POP, pushAt 876 1 1, opAt 877 (.Dup ⟨1, by decide⟩),
   opAt 878 .ADD, opAt 879 (.Swap ⟨0, by decide⟩), opAt 880 .POP,
   pushAt 881 2 1123, opAt 882 .JUMP]

def serializerReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 883 .JUMPDEST, opAt 884 .POP, opAt 885 (.Dup ⟨4, by decide⟩),
   pushAt 886 2 6144, opAt 887 .RETURN]

def exponentOuterExit (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  { outerLoop s accumulatorWord count b e m baseOff expOff rest e with
    pc := UInt256.ofNat 1120 }

def serializerEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1120
           stack := [UInt256.ofNat e, accumulatorWord, UInt256.ofNat count,
             UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
             UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest }

def reverseIndex (m k : Nat) : UInt256 :=
  (UInt256.ofNat m - UInt256.ofNat 1) - UInt256.ofNat k

def serializerLimb (m k : Nat) : UInt256 :=
  UInt256.shiftRight (reverseIndex m k) (UInt256.ofNat 5)

def serializerShift (m k : Nat) : UInt256 :=
  UInt256.shiftLeft (UInt256.land (reverseIndex m k) (UInt256.ofNat 31))
    (UInt256.ofNat 3)

def serializedByte (memory : ByteArray) (m k : Nat) : UInt256 :=
  let word := MachineState.readWord memory
    (2048 + UInt256.shiftLeft (serializerLimb m k) (UInt256.ofNat 5)).toNat
  UInt256.land (UInt256.shiftRight word (serializerShift m k))
    (UInt256.ofNat 255)

def serializeMemory (memory : ByteArray) (m : Nat) : Nat → ByteArray
  | 0 => memory
  | k + 1 =>
      let before := serializeMemory memory m k
      MachineState.writeBytes before
        (ByteArray.mk #[UInt8.ofNat ((serializedByte before m k).toNat % 256)])
        (6144 + UInt256.ofNat k).toNat

def serializeWords (active : UInt256) (m : Nat) : Nat → UInt256
  | 0 => active
  | k + 1 =>
      let before := serializeWords active m k
      let loaded := UInt256.ofNat (MachineState.activeWordsAfter before.toNat
        (2048 + UInt256.shiftLeft (serializerLimb m k) (UInt256.ofNat 5)).toNat 32)
      UInt256.ofNat (MachineState.activeWordsAfter loaded.toNat
        (6144 + UInt256.ofNat k).toNat 1)

def serializeProgress (s : State) (m : Nat) (k : Nat) : State :=
  { s with memory := serializeMemory s.memory m k
           activeWords := serializeWords s.activeWords m k }

@[simp] theorem serializeProgress_halt (s : State) (m k : Nat) :
    (serializeProgress s m k).halt = s.halt := by
  rfl

@[simp] theorem serializeProgress_executionEnv (s : State) (m k : Nat) :
    (serializeProgress s m k).executionEnv = s.executionEnv := by
  rfl

def serializerLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (k : Nat) : State :=
  { serializeProgress s m k with
    pc := UInt256.ofNat 1123
    stack := [UInt256.ofNat k, accumulatorWord, UInt256.ofNat count,
      UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
      UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest }

def serializerBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (k : Nat) : State :=
  { serializerLoop s accumulatorWord count b e m baseOff expOff rest k with
    pc := UInt256.ofNat 1132 }

def serializerExit (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  { serializerLoop s accumulatorWord count b e m baseOff expOff rest m with
    pc := UInt256.ofNat 1182 }

def bigReturned (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  let current := serializeProgress s m m
  { current with
    pc := UInt256.ofNat 1188
    stack := [accumulatorWord, UInt256.ofNat count, UInt256.ofNat b,
      UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff,
      UInt256.ofNat expOff] ++ rest
    halt := .Returned
    hReturn := MachineState.readPadded current.memory 6144 m
    activeWords := UInt256.ofNat
      (MachineState.activeWordsAfter current.activeWords.toNat 6144 m) }

@[simp] private theorem outerFinishPCs (i : Nat)
    (hi : 717 ≤ i) (hii : i ≤ 723) :
    Artifact.submissionArtifact.instructionPC i =
      ([951,952,953,954,955,956,959] : List Nat)[i - 717]! := by
  interval_cases i <;> decide

@[simp] private theorem serializerPCs (i : Nat)
    (hi : 836 ≤ i) (hii : i ≤ 887) :
    Artifact.submissionArtifact.instructionPC i =
      ([1120,1121,1122,1123,1124,1125,1126,1127,1128,1131,1132,1133,1135,1136,1137,1138,1139,1141,1142,1144,1145,1146,1148,1149,1151,1152,1154,1155,1158,1159,1160,1161,1162,1163,1164,1167,1168,1169,1170,1171,1172,1174,1175,1176,1177,1178,1181,1182,1183,1184,1185,1188] : List Nat)[i - 836]! := by
  interval_cases i <;> decide

private theorem jump1118 :
    Decode.isValidJumpDest submissionBytecode 1120 = true :=
  Artifact.isValidJumpDest_index 836 (by rfl)

private theorem jump1121 :
    Decode.isValidJumpDest submissionBytecode 1123 = true :=
  Artifact.isValidJumpDest_index 839 (by rfl)

private theorem jump1180 :
    Decode.isValidJumpDest submissionBytecode 1182 = true :=
  Artifact.isValidJumpDest_index 883 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_outerFinishGuard (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 1014) (_he : e < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outerFinishGuardPath
      (outerLoop s accumulatorWord count b e m baseOff expOff rest e) =
      some (exponentOuterExit s accumulatorWord count b e m baseOff expOff
        rest) := by
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have h1118 : (1120 : UInt256).toNat = 1120 := by decide
  have h1118Word : (1120 : UInt256) = UInt256.ofNat 1120 := by decide
  simp [outerFinishGuardPath, opAt, pushAt, wfOp, outerLoop,
    exponentOuterExit, outerFinishPCs,
    hcode, hrun, hzeroFalse, h1118, h1118Word, jump1118,
    hc8, hc9, hc10, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_serializerEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 1016) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock serializerEntryPath
      (serializerEntry s accumulatorWord count b e m baseOff expOff rest) =
      some (serializerLoop s accumulatorWord count b e m baseOff expOff rest
        0) := by
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp [serializerEntryPath, opAt, pushAt, wfOp, serializerEntry,
    serializerLoop, serializeProgress, serializeMemory, serializeWords,
    serializerPCs, hrun, hzero, hc7, hc8,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_serializerGuard (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff k : Nat) (rest : List UInt256)
    (hcap : rest.length < 1014) (hm : m < 2 ^ 256) (hk : k < m)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock serializerGuardPath
      (serializerLoop s accumulatorWord count b e m baseOff expOff rest k) =
      some (serializerBody s accumulatorWord count b e m baseOff expOff rest
        k) := by
  have hk256 : k < 2 ^ 256 := hk.trans hm
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat k) (UInt256.ofNat m) = 1 := by
    rw [UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hk256, Nat.mod_eq_of_lt hm, if_pos hk]
    decide
  have honeNat : (1 : UInt256).toNat = 1 := by decide
  simp [serializerGuardPath, opAt, pushAt, wfOp, serializerLoop,
    serializerBody, serializerPCs, hrun, hlt, honeNat, hc8, hc9, hc10,
    UInt256.isTrue, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_serializerBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff k : Nat) (rest : List UInt256)
    (hcap : rest.length < 1008) (hm : m < 2 ^ 256) (hk : k < m)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock serializerBodyPath
      (serializerBody s accumulatorWord count b e m baseOff expOff rest k) =
      some (serializerLoop s accumulatorWord count b e m baseOff expOff rest
        (k + 1)) := by
  have hk256 : k + 1 < 2 ^ 256 := by omega
  have hkm : k + 1 ≤ m := by omega
  have hmPos : 1 ≤ m := by omega
  have hsubM := Challenge.EvmProof.Word.ofNat_sub_ofNat hmPos
    (by exact hm)
  have hsubK := Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega : k ≤ m - 1)
    (by omega : m - 1 < 2 ^ 256)
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := k) (b := 1) hk256
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have h1121 : (1123 : UInt256).toNat = 1123 := by decide
  have h1121Word : (1123 : UInt256) = UInt256.ofNat 1123 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hthree : (3 : UInt256) = UInt256.ofNat 3 := by decide
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have h31 : (31 : UInt256) = UInt256.ofNat 31 := by decide
  have h255 : (255 : UInt256) = UInt256.ofNat 255 := by decide
  simp (config := { maxSteps := 400000 })
    [serializerBodyPath, opAt, pushAt, wfOp, serializerBody, serializerLoop,
      serializeProgress, serializeMemory, serializeWords, serializedByte,
      serializerLimb, serializerShift, reverseIndex, serializerPCs,
      hcode, hrun, hm, hk, hkm, hsubM, hsubK, hinc, jump1121,
      h1121, h1121Word, hone, hthree, hfive, h31, h255,
      hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_serializerFinishGuard (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 1014) (_hm : m < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock serializerGuardPath
      (serializerLoop s accumulatorWord count b e m baseOff expOff rest m) =
      some (serializerExit s accumulatorWord count b e m baseOff expOff
        rest) := by
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have h1180 : (1182 : UInt256).toNat = 1182 := by decide
  have h1180Word : (1182 : UInt256) = UInt256.ofNat 1182 := by decide
  simp [serializerGuardPath, opAt, pushAt, wfOp, serializerLoop,
    serializerExit, serializerPCs, hcode, hrun, hzeroFalse,
    h1180, h1180Word, jump1180, hc8, hc9, hc10,
    UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_serializerReturn (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 1014) (hm : m < 2 ^ 256)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock serializerReturnPath
      (serializerExit s accumulatorWord count b e m baseOff expOff rest) =
      some (bigReturned s accumulatorWord count b e m baseOff expOff rest) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have h6144 : (6144 : UInt256).toNat = 6144 := by decide
  have hmNat : (UInt256.ofNat m).toNat = m := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hm]
  simp [serializerReturnPath, opAt, pushAt, wfOp, serializerExit,
    serializerLoop, bigReturned, serializerPCs, hrun, h6144, hmNat,
    hc7, hc8, hc9, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

def gasSteps_serializerIteration (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff k : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (hm : m < 2 ^ 256) (hk : k < m)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (serializerLoop s accumulatorWord count b e m baseOff expOff rest k)
      (serializerLoop s accumulatorWord count b e m baseOff expOff rest
        (k + 1)) := by
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka serializerGuardPath
      (by simpa [serializerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [serializerLoop, State.fork] using hfork)
      (run_serializerGuard s accumulatorWord count b e m baseOff expOff k rest
        (by omega) hm hk hrun)
      (by simpa [serializerLoop] using hrun)
      (by simpa [serializerLoop, State.fork] using hnp)
  have hbody := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka serializerBodyPath
      (by simpa [serializerBody, serializerLoop,
        Artifact.submissionArtifact] using hcode)
      (by simpa [serializerBody, serializerLoop, State.fork] using hfork)
      (run_serializerBody s accumulatorWord count b e m baseOff expOff k rest
        (by omega) hm hk hcode hrun)
      (by simpa [serializerBody, serializerLoop] using hrun)
      (by simpa [serializerBody, serializerLoop, State.fork] using hnp)
  exact hguard.trans hbody

theorem gasSteps_serializerIteration_cost_potential (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff k : Nat)
    (rest : List UInt256) (hcap : rest.length < 968)
    (hm : m < 2 ^ 256) (hk : k < m)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_serializerIteration s accumulatorWord count b e m baseOff expOff
      k rest hcap hm hk hcode hfork hrun hnp).cost +
        MachineState.memCost
          (serializerLoop s accumulatorWord count b e m baseOff expOff rest
            k).activeWords.toNat =
      138 + MachineState.memCost
        (serializerLoop s accumulatorWord count b e m baseOff expOff rest
          (k + 1)).activeWords.toNat := by
  have hguard :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      serializerGuardPath 26
        (run_serializerGuard s accumulatorWord count b e m baseOff expOff k
          rest (by omega) hm hk hrun)
        (by simpa [serializerLoop, State.fork] using hfork)
        (by decide) (by decide)
  have hbody :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      serializerBodyPath 112
        (run_serializerBody s accumulatorWord count b e m baseOff expOff k
          rest (by omega) hm hk hcode hrun)
        (by simpa [serializerBody, serializerLoop, State.fork] using hfork)
        (by decide) (by decide)
  unfold gasSteps_serializerIteration
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [serializerLoop, serializerBody] at hguard hbody ⊢
  omega

def gasSteps_serializerLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (hm : m < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (serializerLoop s accumulatorWord count b e m baseOff expOff rest 0)
      (serializerLoop s accumulatorWord count b e m baseOff expOff rest m) :=
  Challenge.EvmProof.GasSteps.iterateBounded m fun k hk =>
    gasSteps_serializerIteration s accumulatorWord count b e m baseOff expOff k
      rest hcap hm hk hcode hfork hrun hnp

theorem gasSteps_serializerLoop_cost_potential (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) (hcap : rest.length < 968)
    (hm : m < 2 ^ 256) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_serializerLoop s accumulatorWord count b e m baseOff expOff rest
      hcap hm hcode hfork hrun hnp).cost +
        MachineState.memCost
          (serializerLoop s accumulatorWord count b e m baseOff expOff rest
            0).activeWords.toNat =
      m * 138 + MachineState.memCost
        (serializerLoop s accumulatorWord count b e m baseOff expOff rest
          m).activeWords.toNat := by
  unfold gasSteps_serializerLoop
  apply Challenge.EvmProof.Meter.iterateBounded_cost_potential_add
  intro k hk
  simpa [Nat.mul_comm] using
    gasSteps_serializerIteration_cost_potential s accumulatorWord count b e m
      baseOff expOff k rest hcap hm hk hcode hfork hrun hnp

def gasSteps_serializerFinish (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (hm : m < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (serializerLoop s accumulatorWord count b e m baseOff expOff rest m)
      (bigReturned s accumulatorWord count b e m baseOff expOff rest) := by
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka serializerGuardPath
      (by simpa [serializerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [serializerLoop, State.fork] using hfork)
      (run_serializerFinishGuard s accumulatorWord count b e m baseOff expOff
        rest (by omega) hm hcode hrun)
      (by simpa [serializerLoop] using hrun)
      (by simpa [serializerLoop, State.fork] using hnp)
  have hreturn := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka serializerReturnPath
      (by simpa [serializerExit, serializerLoop,
        Artifact.submissionArtifact] using hcode)
      (by simpa [serializerExit, serializerLoop, State.fork] using hfork)
      (run_serializerReturn s accumulatorWord count b e m baseOff expOff rest
        (by omega) hm hrun)
      (by simpa [serializerExit, serializerLoop] using hrun)
      (by simpa [serializerExit, serializerLoop, State.fork] using hnp)
  exact hguard.trans hreturn

theorem gasSteps_serializerFinish_cost_potential (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) (hcap : rest.length < 968)
    (hm : m < 2 ^ 256) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_serializerFinish s accumulatorWord count b e m baseOff expOff
      rest hcap hm hcode hfork hrun hnp).cost +
        MachineState.memCost
          (serializerLoop s accumulatorWord count b e m baseOff expOff rest
            m).activeWords.toNat =
      35 + MachineState.memCost
        (bigReturned s accumulatorWord count b e m baseOff expOff rest).activeWords.toNat := by
  have hguard :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      serializerGuardPath 26
        (run_serializerFinishGuard s accumulatorWord count b e m baseOff expOff
          rest (by omega) hm hcode hrun)
        (by simpa [serializerLoop, State.fork] using hfork)
        (by decide) (by decide)
  have hreturn :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      serializerReturnPath 9
        (run_serializerReturn s accumulatorWord count b e m baseOff expOff rest
          (by omega) hm hrun)
        (by simpa [serializerExit, serializerLoop, State.fork] using hfork)
        (by decide) (by decide)
  unfold gasSteps_serializerFinish
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [serializerLoop, serializerExit, bigReturned] at hguard hreturn ⊢
  omega

def gasSteps_serializeResult (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (he : e < 2 ^ 256) (hm : m < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (outerLoop s accumulatorWord count b e m baseOff expOff rest e)
      (bigReturned s accumulatorWord count b e m baseOff expOff rest) := by
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka outerFinishGuardPath
      (by simpa [outerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [outerLoop, State.fork] using hfork)
      (run_outerFinishGuard s accumulatorWord count b e m baseOff expOff rest
        (by omega) he hcode hrun)
      (by simpa [outerLoop] using hrun)
      (by simpa [outerLoop, State.fork] using hnp)
  have hentry := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka serializerEntryPath
      (by simpa [serializerEntry, Artifact.submissionArtifact] using hcode)
      (by simpa [serializerEntry, State.fork] using hfork)
      (run_serializerEntry s accumulatorWord count b e m baseOff expOff rest
        (by omega) hrun)
      (by simpa [serializerEntry] using hrun)
      (by simpa [serializerEntry, State.fork] using hnp)
  have hloop := gasSteps_serializerLoop s accumulatorWord count b e m baseOff
    expOff rest hcap hm hcode hfork hrun hnp
  have hfinish := gasSteps_serializerFinish s accumulatorWord count b e m
    baseOff expOff rest hcap hm hcode hfork hrun hnp
  exact Challenge.EvmProof.GasSteps.cast
    (hguard.trans (hentry.trans (hloop.trans hfinish))) rfl rfl

theorem gasSteps_serializeResult_cost_potential (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) (hcap : rest.length < 968)
    (he : e < 2 ^ 256) (hm : m < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_serializeResult s accumulatorWord count b e m baseOff expOff rest
      hcap he hm hcode hfork hrun hnp).cost +
        MachineState.memCost
          (outerLoop s accumulatorWord count b e m baseOff expOff rest
            e).activeWords.toNat =
      (66 + m * 138) + MachineState.memCost
        (bigReturned s accumulatorWord count b e m baseOff expOff rest).activeWords.toNat := by
  have hguard :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      outerFinishGuardPath 26
        (run_outerFinishGuard s accumulatorWord count b e m baseOff expOff rest
          (by omega) he hcode hrun)
        (by simpa [outerLoop, State.fork] using hfork)
        (by decide) (by decide)
  have hentry :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      serializerEntryPath 5
        (run_serializerEntry s accumulatorWord count b e m baseOff expOff rest
          (by omega) hrun)
        (by simpa [serializerEntry, State.fork] using hfork)
        (by decide) (by decide)
  have hloop := gasSteps_serializerLoop_cost_potential s accumulatorWord count b
    e m baseOff expOff rest hcap hm hcode hfork hrun hnp
  have hfinish := gasSteps_serializerFinish_cost_potential s accumulatorWord
    count b e m baseOff expOff rest hcap hm hcode hfork hrun hnp
  unfold gasSteps_serializeResult
  simp only [Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [outerLoop, exponentOuterExit, serializerEntry, serializerLoop,
    bigReturned] at hguard hentry hloop hfinish ⊢
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.BigSerialize
