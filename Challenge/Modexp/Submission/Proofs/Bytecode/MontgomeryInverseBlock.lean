import Challenge.EvmProof.Meter
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Montgomery.InverseArithmetic

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# Exact EVM bridge for the six-update Montgomery inverse block

The block at PC 1447 computes the negative inverse of an odd UInt256 word.
It preserves the caller suffix and every state field except the declared
program counter and stack frame.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryInverseBlock

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Montgomery

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
    (hget : Artifact.submissionInstructions[index]? =
      some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def inverseSeedPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1072 .JUMPDEST, opAt 1073 (.Dup ⟨0, by decide⟩), pushAt 1074 1 3,
   opAt 1075 .MUL, pushAt 1076 1 2, opAt 1077 (.CompBit .XOR)]

def inverseRefinePath1 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1078 (.Dup ⟨0, by decide⟩), opAt 1079 (.Dup ⟨2, by decide⟩),
   opAt 1080 .MUL, pushAt 1081 1 2, opAt 1082 .SUB, opAt 1083 .MUL]

def inverseRefinePath2 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1084 (.Dup ⟨0, by decide⟩), opAt 1085 (.Dup ⟨2, by decide⟩),
   opAt 1086 .MUL, pushAt 1087 1 2, opAt 1088 .SUB, opAt 1089 .MUL]

def inverseRefinePath3 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1090 (.Dup ⟨0, by decide⟩), opAt 1091 (.Dup ⟨2, by decide⟩),
   opAt 1092 .MUL, pushAt 1093 1 2, opAt 1094 .SUB, opAt 1095 .MUL]

def inverseRefinePath4 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1096 (.Dup ⟨0, by decide⟩), opAt 1097 (.Dup ⟨2, by decide⟩),
   opAt 1098 .MUL, pushAt 1099 1 2, opAt 1100 .SUB, opAt 1101 .MUL]

def inverseRefinePath5 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1102 (.Dup ⟨0, by decide⟩), opAt 1103 (.Dup ⟨2, by decide⟩),
   opAt 1104 .MUL, pushAt 1105 1 2, opAt 1106 .SUB, opAt 1107 .MUL]

def inverseRefinePath6 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1108 (.Dup ⟨0, by decide⟩), opAt 1109 (.Dup ⟨2, by decide⟩),
   opAt 1110 .MUL, pushAt 1111 1 2, opAt 1112 .SUB, opAt 1113 .MUL]

def inverseTailPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1114 0 0, opAt 1115 .SUB, opAt 1116 (.Swap ⟨0, by decide⟩),
   opAt 1117 .POP, opAt 1118 (.Swap ⟨0, by decide⟩), opAt 1119 .JUMP]

def inversePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  inverseSeedPath ++ inverseRefinePath1 ++ inverseRefinePath2 ++
    inverseRefinePath3 ++ inverseRefinePath4 ++ inverseRefinePath5 ++
    inverseRefinePath6 ++ inverseTailPath

def inverseEntry (s : State) (m returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1447
           stack := [m, returnDest] ++ rest }

def inverseReturned (s : State) (m returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := returnDest
           stack := [InverseArithmetic.nprime m] ++ rest }

@[simp] private theorem inversePCs (i : Nat) (hi : 1072 ≤ i) (hii : i ≤ 1119) :
    Artifact.submissionArtifact.instructionPC i =
      [1447,1448,1449,1451,1452,1454,1455,1456,1457,1458,1460,1461,
       1462,1463,1464,1465,1467,1468,1469,1470,1471,1472,1474,1475,
       1476,1477,1478,1479,1481,1482,1483,1484,1485,1486,1488,1489,
       1490,1491,1492,1493,1495,1496,1497,1498,1499,1500,1501,1502][i - 1072]! := by
  interval_cases i <;> decide

@[simp] private theorem inverseJumpDest :
    Decode.isValidJumpDest submissionBytecode 1447 = true :=
  Artifact.isValidJumpDest_index 1072 (by rfl)

private def inverseRound (s : State) (pc : Nat) (v m returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [v, m, returnDest] ++ rest }

private theorem xor_comm (a b : UInt256) :
    UInt256.xor a b = UInt256.xor b a := by
  apply Challenge.EvmProof.Word.word_ext
  change (Fin.xor a.val b.val).val = (Fin.xor b.val a.val).val
  simp [Fin.xor, Nat.xor_comm]

set_option linter.unusedSimpArgs false in
private theorem run_refine_six
    (a b c d e f :
      Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka)
    (p : Nat) (s : State) (v m returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1019)
    (ha : a.instruction = .op (.Dup ⟨0, by decide⟩))
    (hb : b.instruction = .op (.Dup ⟨2, by decide⟩))
    (hc : c.instruction = .op .MUL)
    (hd : d.instruction = .push 1 (UInt256.ofNat 2))
    (he : e.instruction = .op .SUB)
    (hf : f.instruction = .op .MUL)
    (hpa : Artifact.submissionArtifact.instructionPC a.index = p)
    (hpb : Artifact.submissionArtifact.instructionPC b.index = p + 1)
    (hpc : Artifact.submissionArtifact.instructionPC c.index = p + 2)
    (hpd : Artifact.submissionArtifact.instructionPC d.index = p + 3)
    (hpe : Artifact.submissionArtifact.instructionPC e.index = p + 5)
    (hpf : Artifact.submissionArtifact.instructionPC f.index = p + 6)
    (hp : p + 6 < 2 ^ 256)
    (hrun : (inverseRound s p v m returnDest rest).halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock [a, b, c, d, e, f]
      (inverseRound s p v m returnDest rest) =
        some (inverseRound s (p + 7) (InverseArithmetic.refine m v)
          m returnDest rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hp0 : p < 2 ^ 256 := by omega
  have hp1 : p + 1 < 2 ^ 256 := by omega
  have hp2 : p + 2 < 2 ^ 256 := by omega
  have hp3 : p + 3 < 2 ^ 256 := by omega
  have hp5 : p + 5 < 2 ^ 256 := by omega
  have hp6 : p + 6 < 2 ^ 256 := hp
  have hrun' : s.halt = .Running := by
    simpa [inverseRound] using hrun
  have hpc' : p + 1 + 1 + 1 + 2 + 1 + 1 = p + 7 := by omega
  have htwo : (UInt256.ofNat 2 : UInt256) = 2 := by decide
  have htwoNat : (2 : UInt256).toNat = 2 := by decide
  have hpce : (p + 1 + 1 + 1 + 2) % 2 ^ 256 = p + 5 := by
    rw [Nat.mod_eq_of_lt hp5]
  have hpcf :
      ((UInt256.ofNat (p + 1 + 1 + 1) + (2 : UInt256)).succ).toNat = p + 6 := by
    change ((UInt256.ofNat (p + 1 + 1 + 1) + UInt256.ofNat 2).succ).toNat = p + 6
    rw [Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hp6]
  have hpcout :
      (UInt256.ofNat (p + 1 + 1 + 1) + (2 : UInt256)).succ.succ =
        UInt256.ofNat (p + 7) := by
    change (UInt256.ofNat (p + 1 + 1 + 1) + UInt256.ofNat 2).succ.succ =
      UInt256.ofNat (p + 7)
    rw [Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]
  have hmul : (2 - m * v) * v = v * (2 - m * v) := by
    apply Challenge.EvmProof.Word.word_ext
    change ((2 - m * v).val * v.val).val =
      (v.val * (2 - m * v).val).val
    rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]
  norm_num at hp0 hp1 hp2 hp3 hp5 hp6
  simp (config := { maxSteps := 100000 })
    [Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated,
     Challenge.EvmProof.Stepper.runInstr, inverseRound,
     Challenge.EvmProof.Word.word_toNat_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt,
     State.fork, State.activeWordsAfterUInt256, ha, hb, hc, hd, he, hf,
     hpa, hpb, hpc, hpd, hpe, hpf, hrun, hc3, hc4, hc5,
     InverseArithmetic.refine, mul_comm, hp, hp0, hp1, hp2, hp3, hp5, hp6,
     hrun', hpc', htwo, htwoNat, hpce, hpcf, hpcout, hmul]

set_option linter.unusedSimpArgs false in
private theorem run_seed (s : State) (m returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1019)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock inverseSeedPath
      (inverseEntry s m returnDest rest) =
        some (inverseRound s 1455 (InverseArithmetic.seed m)
          m returnDest rest) := by
  have hc2 : rest.length + 1 + 1 < 1024 := by omega
  have hc3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have hc4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hrun' : (inverseEntry s m returnDest rest).halt = .Running := by
    simpa [inverseEntry] using hrun
  have hpc : (UInt256.ofNat 1447).succ = UInt256.ofNat 1448 := by
    exact Challenge.EvmProof.Word.succ_ofNat_mod 1447
  have hseedxor : UInt256.xor 2 (3 * m) = InverseArithmetic.seed m := by
    change UInt256.xor 2 (3 * m) = UInt256.xor (3 * m) 2
    exact xor_comm _ _
  simp (config := { maxSteps := 100000 })
    [inverseSeedPath, opAt, pushAt, wfOp, inverseEntry, inverseRound,
     inversePCs, Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     Challenge.EvmProof.Word.word_toNat_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt,
     State.fork, State.activeWordsAfterUInt256, hcap, hc2, hc3, hc4, hc5,
     hrun', hpc, hrun, InverseArithmetic.seed, hseedxor, mul_comm]

set_option linter.unusedSimpArgs false in
private theorem run_tail (s : State) (m returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1019)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock inverseTailPath
      (inverseRound s 1497 (InverseArithmetic.inverse m) m returnDest rest) =
        some (inverseReturned s m returnDest rest) := by
  have hc2 : rest.length + 1 + 1 < 1024 := by omega
  have hc3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have hc4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcode' :
      (inverseRound s 1497 (InverseArithmetic.inverse m) m returnDest rest).executionEnv.code =
        submissionBytecode := by
    simpa [inverseRound] using hcode
  have hrun' :
      (inverseRound s 1497 (InverseArithmetic.inverse m) m returnDest rest).halt = .Running := by
    simpa [inverseRound] using hrun
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzero' : (UInt256.ofNat 0 : UInt256) = 0 := by decide
  simp (config := { maxSteps := 100000 })
    [inverseTailPath, opAt, pushAt, wfOp, inverseRound, inverseReturned,
     inversePCs, Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     Challenge.EvmProof.Word.word_toNat_ofNat,
     Challenge.EvmProof.Word.word_toNat_sub,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt,
     State.fork, State.activeWordsAfterUInt256, hcap, hc2, hc3, hc4, hc5,
     hcode', hrun', hcode, hrun, hvalid, hzero, hzero', inverseJumpDest,
     InverseArithmetic.inverse, InverseArithmetic.nprime, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_inverse (s : State) (m returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1019)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock inversePath
      (inverseEntry s m returnDest rest) =
        some (inverseReturned s m returnDest rest) := by
  let v0 := InverseArithmetic.seed m
  let v1 := InverseArithmetic.refine m v0
  let v2 := InverseArithmetic.refine m v1
  let v3 := InverseArithmetic.refine m v2
  let v4 := InverseArithmetic.refine m v3
  let v5 := InverseArithmetic.refine m v4
  let v6 := InverseArithmetic.refine m v5
  have hv6 : v6 = InverseArithmetic.inverse m := by
    rfl
  have hseed := run_seed s m returnDest rest hcap hrun
  have h1 :
      Challenge.EvmProof.Stepper.runLocatedBlock inverseRefinePath1
        (inverseRound s 1455 v0 m returnDest rest) =
          some (inverseRound s 1462 v1 m returnDest rest) := by
    simpa [inverseRefinePath1, v0, v1] using
      (run_refine_six
        (opAt 1078 (.Dup ⟨0, by decide⟩))
        (opAt 1079 (.Dup ⟨2, by decide⟩))
        (opAt 1080 .MUL) (pushAt 1081 1 2) (opAt 1082 .SUB)
        (opAt 1083 .MUL) 1455 s v0 m returnDest rest hcap
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by simpa [inverseRound] using hrun))
  have h2 :
      Challenge.EvmProof.Stepper.runLocatedBlock inverseRefinePath2
        (inverseRound s 1462 v1 m returnDest rest) =
          some (inverseRound s 1469 v2 m returnDest rest) := by
    simpa [inverseRefinePath2, v1, v2] using
      (run_refine_six
        (opAt 1084 (.Dup ⟨0, by decide⟩))
        (opAt 1085 (.Dup ⟨2, by decide⟩))
        (opAt 1086 .MUL) (pushAt 1087 1 2) (opAt 1088 .SUB)
        (opAt 1089 .MUL) 1462 s v1 m returnDest rest hcap
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by simpa [inverseRound] using hrun))
  have h3 :
      Challenge.EvmProof.Stepper.runLocatedBlock inverseRefinePath3
        (inverseRound s 1469 v2 m returnDest rest) =
          some (inverseRound s 1476 v3 m returnDest rest) := by
    simpa [inverseRefinePath3, v2, v3] using
      (run_refine_six
        (opAt 1090 (.Dup ⟨0, by decide⟩))
        (opAt 1091 (.Dup ⟨2, by decide⟩))
        (opAt 1092 .MUL) (pushAt 1093 1 2) (opAt 1094 .SUB)
        (opAt 1095 .MUL) 1469 s v2 m returnDest rest hcap
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by simpa [inverseRound] using hrun))
  have h4 :
      Challenge.EvmProof.Stepper.runLocatedBlock inverseRefinePath4
        (inverseRound s 1476 v3 m returnDest rest) =
          some (inverseRound s 1483 v4 m returnDest rest) := by
    simpa [inverseRefinePath4, v3, v4] using
      (run_refine_six
        (opAt 1096 (.Dup ⟨0, by decide⟩))
        (opAt 1097 (.Dup ⟨2, by decide⟩))
        (opAt 1098 .MUL) (pushAt 1099 1 2) (opAt 1100 .SUB)
        (opAt 1101 .MUL) 1476 s v3 m returnDest rest hcap
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by simpa [inverseRound] using hrun))
  have h5 :
      Challenge.EvmProof.Stepper.runLocatedBlock inverseRefinePath5
        (inverseRound s 1483 v4 m returnDest rest) =
          some (inverseRound s 1490 v5 m returnDest rest) := by
    simpa [inverseRefinePath5, v4, v5] using
      (run_refine_six
        (opAt 1102 (.Dup ⟨0, by decide⟩))
        (opAt 1103 (.Dup ⟨2, by decide⟩))
        (opAt 1104 .MUL) (pushAt 1105 1 2) (opAt 1106 .SUB)
        (opAt 1107 .MUL) 1483 s v4 m returnDest rest hcap
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by simpa [inverseRound] using hrun))
  have h6 :
      Challenge.EvmProof.Stepper.runLocatedBlock inverseRefinePath6
        (inverseRound s 1490 v5 m returnDest rest) =
          some (inverseRound s 1497 v6 m returnDest rest) := by
    simpa [inverseRefinePath6, v5, v6] using
      (run_refine_six
        (opAt 1108 (.Dup ⟨0, by decide⟩))
        (opAt 1109 (.Dup ⟨2, by decide⟩))
        (opAt 1110 .MUL) (pushAt 1111 1 2) (opAt 1112 .SUB)
        (opAt 1113 .MUL) 1490 s v5 m returnDest rest hcap
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by simpa [inverseRound] using hrun))
  have hseed' :
      Challenge.EvmProof.Stepper.runLocatedBlock inverseSeedPath
        (inverseEntry s m returnDest rest) =
          some (inverseRound s 1455 v0 m returnDest rest) := by
    simpa [v0] using hseed
  have hr0 : (inverseRound s 1455 v0 m returnDest rest).halt = .Running := by
    simpa [inverseRound] using hrun
  have hr1 : (inverseRound s 1462 v1 m returnDest rest).halt = .Running := by
    simpa [inverseRound] using hrun
  have hr2 : (inverseRound s 1469 v2 m returnDest rest).halt = .Running := by
    simpa [inverseRound] using hrun
  have hr3 : (inverseRound s 1476 v3 m returnDest rest).halt = .Running := by
    simpa [inverseRound] using hrun
  have hr4 : (inverseRound s 1483 v4 m returnDest rest).halt = .Running := by
    simpa [inverseRound] using hrun
  have hr5 : (inverseRound s 1490 v5 m returnDest rest).halt = .Running := by
    simpa [inverseRound] using hrun
  have hr6 : (inverseRound s 1497 v6 m returnDest rest).halt = .Running := by
    simpa [inverseRound, hv6] using hrun
  have h01 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    inverseSeedPath inverseRefinePath1
    (inverseEntry s m returnDest rest) (inverseRound s 1455 v0 m returnDest rest)
    (inverseRound s 1462 v1 m returnDest rest) hseed' hr0 h1
  have h012 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    (inverseSeedPath ++ inverseRefinePath1) inverseRefinePath2
    (inverseEntry s m returnDest rest) (inverseRound s 1462 v1 m returnDest rest)
    (inverseRound s 1469 v2 m returnDest rest) h01 hr1 h2
  have h0123 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    ((inverseSeedPath ++ inverseRefinePath1) ++ inverseRefinePath2)
      inverseRefinePath3
    (inverseEntry s m returnDest rest) (inverseRound s 1469 v2 m returnDest rest)
    (inverseRound s 1476 v3 m returnDest rest) h012 hr2 h3
  have h01234 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    (((inverseSeedPath ++ inverseRefinePath1) ++ inverseRefinePath2) ++
      inverseRefinePath3) inverseRefinePath4
    (inverseEntry s m returnDest rest) (inverseRound s 1476 v3 m returnDest rest)
    (inverseRound s 1483 v4 m returnDest rest) h0123 hr3 h4
  have h012345 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    ((((inverseSeedPath ++ inverseRefinePath1) ++ inverseRefinePath2) ++
      inverseRefinePath3) ++ inverseRefinePath4) inverseRefinePath5
    (inverseEntry s m returnDest rest) (inverseRound s 1483 v4 m returnDest rest)
    (inverseRound s 1490 v5 m returnDest rest) h01234 hr4 h5
  have h0123456 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    (((((inverseSeedPath ++ inverseRefinePath1) ++ inverseRefinePath2) ++
      inverseRefinePath3) ++ inverseRefinePath4) ++ inverseRefinePath5)
      inverseRefinePath6
    (inverseEntry s m returnDest rest) (inverseRound s 1490 v5 m returnDest rest)
    (inverseRound s 1497 v6 m returnDest rest) h012345 hr5 h6
  have htail := run_tail s m returnDest rest hcap hcode hvalid hrun
  have hfull := Challenge.EvmProof.Stepper.runLocatedBlock_append
    ((((((inverseSeedPath ++ inverseRefinePath1) ++ inverseRefinePath2) ++
      inverseRefinePath3) ++ inverseRefinePath4) ++ inverseRefinePath5) ++
      inverseRefinePath6) inverseTailPath
    (inverseEntry s m returnDest rest) (inverseRound s 1497 v6 m returnDest rest)
    (inverseReturned s m returnDest rest) h0123456 hr6 (by
      simpa [hv6] using htail)
  simpa [inversePath, hv6] using hfull

def gasSteps_inverse (s : State) (m returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1019)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (inverseEntry s m returnDest rest)
      (inverseReturned s m returnDest rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka inversePath
      (by simpa [inverseEntry, Artifact.submissionArtifact] using hcode)
      (by simpa [inverseEntry, State.fork] using hfork)
      (run_inverse s m returnDest rest hcap hcode hvalid hrun)
      (by simpa [inverseEntry] using hrun)
      (by simpa [inverseEntry, State.fork] using hnp)

theorem gasSteps_inverse_cost (s : State) (m returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1019)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (gasSteps_inverse s m returnDest rest hcap hcode hfork hvalid hrun hnp).cost =
      171 := by
  have hstatic : Challenge.EvmProof.Meter.runLocatedBlockStaticCost inversePath = 171 := by
    decide
  have hpotential :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      inversePath 171
      (run_inverse s m returnDest rest hcap hcode hvalid hrun)
      (by simpa [inverseEntry, State.fork] using hfork)
      (by decide) hstatic
  have hzeroMem :
      MachineState.memCost (inverseEntry s m returnDest rest).activeWords.toNat =
        MachineState.memCost (inverseReturned s m returnDest rest).activeWords.toNat := by
    rfl
  change Challenge.EvmProof.Stepper.runLocatedBlockCost inversePath
      (inverseEntry s m returnDest rest) = 171
  have hgasCost :
      Challenge.EvmProof.Stepper.runLocatedBlockCost inversePath
          (inverseEntry s m returnDest rest) +
        MachineState.memCost (inverseEntry s m returnDest rest).activeWords.toNat =
      171 + MachineState.memCost (inverseReturned s m returnDest rest).activeWords.toNat :=
    hpotential
  rw [hzeroMem] at hgasCost
  omega

theorem inverse_result_congruence (m : UInt256) (hodd : m.toNat % 2 = 1) :
    (m.toNat * (InverseArithmetic.nprime m).toNat + 1) % (2 ^ 256) = 0 :=
  InverseArithmetic.nprime_correct m hodd

theorem inverseReturned_toNat (s : State) (m returnDest : UInt256)
    (rest : List UInt256) :
    (inverseReturned s m returnDest rest).stack.head? =
      some (InverseArithmetic.nprime m) := by
  rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryInverseBlock
