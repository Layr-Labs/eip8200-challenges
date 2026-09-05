import Challenge.EvmProof.Meter
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryHighBlock
import Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWordBlock

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Montgomery
open Challenge.EvmProof

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def setupPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1120 .JUMPDEST,
   pushAt 1121 0 0,
   pushAt 1122 0 0]

def guardPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1123 .JUMPDEST,
   opAt 1124 (.Dup ⟨5, by decide⟩),
   opAt 1125 (.Dup ⟨1, by decide⟩),
   opAt 1126 .LT,
   opAt 1127 .ISZERO,
   pushAt 1128 2 1584,
   opAt 1129 .JUMPI]

def toHighPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1130 (.Dup ⟨0, by decide⟩),
   pushAt 1131 1 5,
   opAt 1132 .SHL,
   opAt 1133 (.Dup ⟨4, by decide⟩),
   opAt 1134 .ADD,
   opAt 1135 .MLOAD,
   opAt 1136 (.Dup ⟨0, by decide⟩),
   opAt 1137 (.Dup ⟨6, by decide⟩),
   opAt 1138 .MUL,
   pushAt 1139 2 1535,
   opAt 1140 (.Dup ⟨1, by decide⟩),
   opAt 1141 (.Dup ⟨8, by decide⟩),
   opAt 1142 (.Dup ⟨4, by decide⟩),
   pushAt 1143 2 1427,
   opAt 1144 .JUMP]

def fromHighPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1145 .JUMPDEST,
   opAt 1146 (.Swap ⟨1, by decide⟩),
   opAt 1147 .POP,
   opAt 1148 (.Dup ⟨2, by decide⟩),
   pushAt 1149 1 5,
   opAt 1150 .SHL,
   opAt 1151 (.Dup ⟨5, by decide⟩),
   opAt 1152 .ADD,
   opAt 1153 .MLOAD,
   opAt 1154 (.Dup ⟨0, by decide⟩),
   opAt 1155 (.Dup ⟨2, by decide⟩),
   opAt 1156 .ADD,
   opAt 1157 (.Dup ⟨1, by decide⟩),
   opAt 1158 (.Dup ⟨1, by decide⟩),
   opAt 1159 .LT,
   opAt 1160 (.Dup ⟨1, by decide⟩),
   opAt 1161 (.Dup ⟨7, by decide⟩),
   opAt 1162 .ADD,
   opAt 1163 (.Dup ⟨2, by decide⟩),
   opAt 1164 (.Dup ⟨1, by decide⟩),
   opAt 1165 .LT,
   opAt 1166 (.Dup ⟨2, by decide⟩),
   opAt 1167 .ADD,
   opAt 1168 (.Dup ⟨6, by decide⟩),
   opAt 1169 .ADD,
   opAt 1170 (.Dup ⟨1, by decide⟩),
   opAt 1171 (.Dup ⟨8, by decide⟩),
   pushAt 1172 1 5,
   opAt 1173 .SHL,
   opAt 1174 (.Dup ⟨11, by decide⟩),
   opAt 1175 .ADD,
   opAt 1176 .MSTORE,
   opAt 1177 (.Swap ⟨7, by decide⟩),
   opAt 1178 .POP,
   opAt 1179 .POP,
   opAt 1180 .POP,
   opAt 1181 .POP,
   opAt 1182 .POP,
   opAt 1183 .POP,
   opAt 1184 .POP,
   pushAt 1185 1 1,
   opAt 1186 .ADD,
   pushAt 1187 2 1506,
   opAt 1188 .JUMP]

def foldPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1189 .JUMPDEST,
   opAt 1190 (.Dup ⟨5, by decide⟩),
   pushAt 1191 1 5,
   opAt 1192 .SHL,
   opAt 1193 (.Dup ⟨3, by decide⟩),
   opAt 1194 .ADD,
   opAt 1195 (.Dup ⟨0, by decide⟩),
   opAt 1196 .MLOAD,
   opAt 1197 (.Dup ⟨1, by decide⟩),
   pushAt 1198 1 32,
   opAt 1199 .ADD,
   opAt 1200 .MLOAD,
   opAt 1201 (.Dup ⟨1, by decide⟩),
   opAt 1202 (.Dup ⟨5, by decide⟩),
   opAt 1203 .ADD,
   opAt 1204 (.Dup ⟨2, by decide⟩),
   opAt 1205 (.Dup ⟨1, by decide⟩),
   opAt 1206 .LT,
   opAt 1207 (.Dup ⟨2, by decide⟩),
   opAt 1208 .ADD,
   opAt 1209 (.Dup ⟨1, by decide⟩),
   opAt 1210 (.Dup ⟨5, by decide⟩),
   opAt 1211 .MSTORE,
   opAt 1212 (.Dup ⟨4, by decide⟩),
   pushAt 1213 1 32,
   opAt 1214 .ADD,
   opAt 1215 .MSTORE]

def cleanupPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1216 .POP,
   opAt 1217 .POP,
   opAt 1218 .POP,
   opAt 1219 .POP,
   opAt 1220 .POP,
   opAt 1221 .POP,
   opAt 1222 .POP,
   opAt 1223 .POP,
   opAt 1224 .POP,
   opAt 1225 .POP,
   opAt 1226 .JUMP]

@[simp] private theorem wordPCs (i : Nat) (hi : 1120 ≤ i) (hii : i ≤ 1226) :
    Artifact.submissionArtifact.instructionPC i =
      [1503,1504,1505,1506,1507,1508,1509,1510,1511,1514,1515,1516,1518,1519,1520,1521,1522,1523,1524,1525,1528,1529,1530,1531,1534,1535,1536,1537,1538,1539,1541,1542,1543,1544,1545,1546,1547,1548,1549,1550,1551,1552,1553,1554,1555,1556,1557,1558,1559,1560,1561,1562,1563,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1579,1580,1583,1584,1585,1586,1588,1589,1590,1591,1592,1593,1594,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624][i - 1120]! := by
  interval_cases i <;> decide

@[simp] private theorem loopDest :
    Decode.isValidJumpDest submissionBytecode 1506 = true :=
  Artifact.isValidJumpDest_index 1123 (by rfl)

@[simp] private theorem highDest :
    Decode.isValidJumpDest submissionBytecode 1427 = true :=
  Artifact.isValidJumpDest_index 1052 (by rfl)

@[simp] private theorem highReturnDest :
    Decode.isValidJumpDest submissionBytecode 1535 = true :=
  Artifact.isValidJumpDest_index 1145 (by rfl)

@[simp] private theorem finishDest :
    Decode.isValidJumpDest submissionBytecode 1584 = true :=
  Artifact.isValidJumpDest_index 1189 (by rfl)

private theorem word_mul_comm (a b : UInt256) : a * b = b * a := by
  apply Word.word_ext
  change (a.val * b.val).val = (b.val * a.val).val
  rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]

private theorem wordAddress (p : UInt256) (j : Nat)
    (hfit : p.toNat + 32 * j < 2 ^ 256) :
    p + UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 5) =
      UInt256.ofNat (p.toNat + 32 * j) := by
  have hj : j < 2 ^ 256 := by omega
  have hm : j * 2 ^ 5 < 2 ^ 256 := by norm_num; omega
  rw [Word.shiftLeft_ofNat hj (by decide) hm]
  apply Word.word_ext
  simp [Word.word_toNat_add, Nat.mul_comm]

-- The appended word loop starts at PC1503. Every pre-existing byte is unchanged.
def entry (s : State) (t x word : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1503
           stack := [t, x, word, UInt256.ofNat n, ret] ++ rest }

def memoryCarry (memory : ByteArray) (x t : Nat) (word : UInt256) :
    Nat → ByteArray × UInt256
  | 0 => (memory, 0)
  | j + 1 =>
      let p := memoryCarry memory x t word j
      WordMemory.wordStep p.1 x t j word p.2

def touch (active : UInt256) (address : Nat) : UInt256 :=
  UInt256.ofNat (MachineState.activeWordsAfter active.toNat address 32)

-- MLOAD x[j], MLOAD t[j], MSTORE t[j], in that order.
def bodyActive (active : UInt256) (x t j : Nat) : UInt256 :=
  touch (touch (touch active (x + 32 * j)) (t + 32 * j)) (t + 32 * j)

def activeProgress (active : UInt256) (x t : Nat) : Nat → UInt256
  | 0 => active
  | j + 1 => bodyActive (activeProgress active x t j) x t j

-- Both top words are loaded before either store.
def foldActive (active : UInt256) (t n : Nat) : UInt256 :=
  let topAt := t + 32 * n
  touch (touch (touch (touch active topAt) (topAt + 32)) topAt) (topAt + 32)

def returned (s : State) (t x word : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) : State :=
  let p := memoryCarry s.memory x.toNat t.toNat word n
  { s with pc := ret
           stack := rest
           memory := WordMemory.foldTop p.1 t.toNat n p.2
           activeWords := foldActive
             (activeProgress s.activeWords x.toNat t.toNat n) t.toNat n }

def progressed (s : State) (x t : Nat) (word : UInt256) (j : Nat) : State :=
  { s with memory := (memoryCarry s.memory x t word j).1
           activeWords := activeProgress s.activeWords x t j }

def loop (s : State) (t x word : UInt256) (n j : Nat)
    (ret : UInt256) (rest : List UInt256) : State :=
  { progressed s x.toNat t.toNat word j with
    pc := UInt256.ofNat 1506
    stack := [UInt256.ofNat j, (memoryCarry s.memory x.toNat t.toNat word j).2,
      t, x, word, UInt256.ofNat n, ret] ++ rest }

def bodyEntry (s : State) (t x word : UInt256) (n j : Nat)
    (ret : UInt256) (rest : List UInt256) : State :=
  { loop s t x word n j ret rest with pc := UInt256.ofNat 1515 }

def highEntry (s : State) (t x word : UInt256) (n j : Nat)
    (ret : UInt256) (rest : List UInt256) : State :=
  let p := progressed s x.toNat t.toNat word j
  let xv := MachineState.readWord p.memory (x.toNat + 32 * j)
  let lo := xv * word
  { p with pc := UInt256.ofNat 1427
           activeWords := touch p.activeWords (x.toNat + 32 * j)
           stack := [xv, word, lo, 1535, lo, xv] ++ (loop s t x word n j ret rest).stack }

def highReturned (s : State) (t x word : UInt256) (n j : Nat)
    (ret : UInt256) (rest : List UInt256) : State :=
  let p := progressed s x.toNat t.toNat word j
  let xv := MachineState.readWord p.memory (x.toNat + 32 * j)
  { p with pc := UInt256.ofNat 1535
           activeWords := touch p.activeWords (x.toNat + 32 * j)
           stack := [HighArithmetic.fullHighWord xv word, xv * word, xv] ++
             (loop s t x word n j ret rest).stack }

def finish (s : State) (t x word : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) : State :=
  { loop s t x word n n ret rest with pc := UInt256.ofNat 1584 }

-- These are exact model equations, not claims of an EVM trace.
theorem memoryCarry_zero (memory : ByteArray) (x t : Nat) (word : UInt256) :
    memoryCarry memory x t word 0 = (memory, 0) := rfl

theorem memoryCarry_succ (memory : ByteArray) (x t : Nat) (word : UInt256) (j : Nat) :
    memoryCarry memory x t word (j + 1) =
      WordMemory.wordStep (memoryCarry memory x t word j).1 x t j word
        (memoryCarry memory x t word j).2 := rfl

theorem returned_memory (s : State) (t x word : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) :
    (returned s t x word n ret rest).memory =
      WordMemory.foldTop (memoryCarry s.memory x.toNat t.toNat word n).1
        t.toNat n (memoryCarry s.memory x.toNat t.toNat word n).2 := rfl

-- Reset only the fields that the model changes. Equality of the full record
-- retains every other field, including accountMap, substate and callStack.
theorem progressed_frame (s : State) (x t : Nat) (word : UInt256) (j : Nat) :
    { progressed s x t word j with memory := s.memory, activeWords := s.activeWords } = s := by
  cases s
  rfl

theorem returned_frame (s : State) (t x word : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) :
    { returned s t x word n ret rest with
      pc := s.pc
      stack := s.stack
      memory := s.memory
      activeWords := s.activeWords } = s := by
  cases s
  rfl

theorem returned_active (s : State) (t x word : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) :
    (returned s t x word n ret rest).activeWords =
      foldActive (activeProgress s.activeWords x.toNat t.toNat n) t.toNat n := rfl

theorem read_next_after_top (memory : ByteArray) (topAt : Nat) (z : UInt256) :
    MachineState.readWord (MachineState.writeBytes memory
      (Data.Bytes.natToBytesPadded z.toNat 32) topAt) (topAt + 32) =
      MachineState.readWord memory (topAt + 32) := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  right
  simp [Data.Bytes.natToBytesPadded, ByteArray.size]

-- The alternative access order in the Yul source: load top, store top,
-- load next, store next. The private proposed EVM uses load/load/store/store.
def foldTopAfterStore (memory : ByteArray) (t n : Nat) (carry : UInt256) : ByteArray :=
  let topAt := t + 32 * n
  let h := MachineState.readWord memory topAt
  let z := h + carry
  let e := UInt256.lt z h
  let afterTop := MachineState.writeBytes memory
    (Data.Bytes.natToBytesPadded z.toNat 32) topAt
  let k := MachineState.readWord afterTop (topAt + 32)
  MachineState.writeBytes afterTop
    (Data.Bytes.natToBytesPadded (k + e).toNat 32) (topAt + 32)

theorem foldTopAfterStore_eq (memory : ByteArray) (t n : Nat) (carry : UInt256) :
    foldTopAfterStore memory t n carry = WordMemory.foldTop memory t n carry := by
  unfold foldTopAfterStore WordMemory.foldTop
  dsimp only
  rw [read_next_after_top]

def cleanupEntry (s : State) (t x word : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) : State :=
  let p := memoryCarry s.memory x.toNat t.toNat word n
  let topAt := t.toNat + 32 * n
  let h := MachineState.readWord p.1 topAt
  let k := MachineState.readWord p.1 (topAt + 32)
  { returned s t x word n ret rest with
    pc := UInt256.ofNat 1614
    stack := [h + p.2, k, h, UInt256.ofNat topAt, UInt256.ofNat n,
      p.2, t, x, word, UInt256.ofNat n, ret] ++ rest }

set_option linter.unusedSimpArgs false in
theorem run_setup (s : State) (t x word : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock setupPath (entry s t x word n ret rest) =
      some (loop s t x word n 0 ret rest) := by
  have cap : ∀ k, k ≤ 24 → rest.length + k < 1024 := by omega
  simp [setupPath, opAt, pushAt, wfOp, entry, loop, progressed,
    memoryCarry, activeProgress, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, Word.succ_ofNat_mod, Word.ofNat_add_mod, Nat.add_assoc, cap, hrun]
  decide

set_option linter.unusedSimpArgs false in
theorem run_guard (s : State) (t x word : UInt256) (n j : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hn : n ≤ 32) (hj : j < n) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock guardPath (loop s t x word n j ret rest) =
      some (bodyEntry s t x word n j ret rest) := by
  have cap : ∀ k, k ≤ 24 → rest.length + k < 1024 := by omega
  have hnj : n < 2^256 ∧ j < 2^256 := by omega
  have hlt : UInt256.lt (UInt256.ofNat j) (UInt256.ofNat n) = UInt256.ofNat 1 := by
    simp only [UInt256.lt, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hnj.1, Nat.mod_eq_of_lt hnj.2, if_pos hj]
  have hc : ¬ UInt256.isTrue (UInt256.isZero
      (UInt256.lt (UInt256.ofNat j) (UInt256.ofNat n))) := by
    rw [hlt]
    decide
  simp [guardPath, opAt, pushAt, wfOp, bodyEntry, loop, progressed,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Nat.add_assoc, cap, hrun, hc]

set_option linter.unusedSimpArgs false in
theorem run_guard_finish (s : State) (t x word : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock guardPath (loop s t x word n n ret rest) =
      some (finish s t x word n ret rest) := by
  have cap : ∀ k, k ≤ 24 → rest.length + k < 1024 := by omega
  have hc : UInt256.isTrue (UInt256.isZero
      (UInt256.lt (UInt256.ofNat n) (UInt256.ofNat n))) := by
    simp [UInt256.isTrue, UInt256.isZero, UInt256.lt]
  simp [guardPath, opAt, pushAt, wfOp, finish, loop, progressed,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc, hcode]

set_option linter.unusedSimpArgs false in
theorem run_toHigh (s : State) (t x word : UInt256) (n j : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hxfit : x.toNat + 32*j < 2^256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock toHighPath (bodyEntry s t x word n j ret rest) =
      some (highEntry s t x word n j ret rest) := by
  have cap : ∀ k, k ≤ 24 → rest.length + k < 1024 := by omega
  have haddr := wordAddress x j hxfit
  have hxmod := Nat.mod_eq_of_lt hxfit
  norm_num at hxmod
  simp (config := {maxSteps := 200000})
    [toHighPath, opAt, pushAt, wfOp, bodyEntry, highEntry, loop, progressed,
     touch, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
     Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
     State.activeWordsAfterUInt256,
     Nat.add_assoc, cap, hrun, hcode, haddr, Nat.mod_eq_of_lt hxmod, word_mul_comm]

set_option linter.unusedSimpArgs false in
theorem run_fromHigh (s : State) (t x word : UInt256) (n j : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (htfit : t.toNat + 32*j < 2^256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock fromHighPath (highReturned s t x word n j ret rest) =
      some (loop s t x word n (j+1) ret rest) := by
  have cap : ∀ k, k ≤ 24 → rest.length + k < 1024 := by omega
  have haddr := wordAddress t j htfit
  have htmod := Nat.mod_eq_of_lt htfit
  norm_num at htmod
  simp (config := {maxSteps := 400000})
    [fromHighPath, opAt, pushAt, wfOp, highReturned, loop, progressed,
     memoryCarry_succ, WordMemory.wordStep, activeProgress, bodyActive,
     touch, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
     Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
     State.activeWordsAfterUInt256, List.exchange, Nat.add_assoc, cap, hrun, hcode,
     haddr, Nat.mod_eq_of_lt htmod, Word.word_add_comm]

set_option linter.unusedSimpArgs false in
theorem run_fold (s : State) (t x word : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (htfit : t.toNat + 32*n + 64 < 2^256)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock foldPath (finish s t x word n ret rest) =
      some (cleanupEntry s t x word n ret rest) := by
  have cap : ∀ k, k ≤ 24 → rest.length + k < 1024 := by omega
  have ht : t.toNat + 32*n < 2^256 := by omega
  have ht' : t.toNat + 32*n + 32 < 2^256 := by omega
  have haddr := wordAddress t n ht
  have htmod := Nat.mod_eq_of_lt ht
  have htmod' := Nat.mod_eq_of_lt ht'
  norm_num at htmod htmod'
  have hnext : 32 + (t.toNat + 32*n) = t.toNat + (32*n + 32) := by omega
  simp only [Nat.add_assoc] at htmod'
  simp (config := {maxSteps := 400000})
    [foldPath, opAt, pushAt, wfOp, finish, loop, progressed, cleanupEntry,
     returned, WordMemory.foldTop, foldActive, touch,
     Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
     Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
     State.activeWordsAfterUInt256, Nat.add_assoc, cap, hrun, haddr,
     Nat.mod_eq_of_lt htmod, Nat.mod_eq_of_lt htmod', hnext, Word.word_add_comm]

set_option linter.unusedSimpArgs false in
theorem run_cleanup (s : State) (t x word : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    Stepper.runLocatedBlock cleanupPath (cleanupEntry s t x word n ret rest) =
      some (returned s t x word n ret rest) := by
  have cap : ∀ k, k ≤ 24 → rest.length + k < 1024 := by omega
  simp [cleanupPath, opAt, pushAt, wfOp, cleanupEntry, returned,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Nat.add_assoc, cap, hrun, hcode, hret]

def gasSteps_highCall (s : State) (t x word : UInt256) (n j : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (highEntry s t x word n j ret rest)
      (highReturned s t x word n j ret rest) := by
  let p := progressed s x.toNat t.toNat word j
  let xv := MachineState.readWord p.memory (x.toNat + 32*j)
  let base := { p with activeWords := touch p.activeWords (x.toNat + 32*j) }
  let tail := [xv * word, xv] ++ (loop s t x word n j ret rest).stack
  have htail : tail.length < 1017 := by
    simp only [tail, loop, List.length_append, List.length_cons, List.length_nil]
    omega
  exact MontgomeryHighBlock.gasSteps_high base xv word (xv * word) 1535 tail
    htail rfl hcode hfork (by change Decode.isValidJumpDest submissionBytecode 1535 = true; exact highReturnDest)
    hrun hnp

theorem gasSteps_highCall_cost (s : State) (t x word : UInt256) (n j : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (gasSteps_highCall s t x word n j ret rest hcap hcode hfork hrun hnp).cost = 64 := by
  unfold gasSteps_highCall
  apply MontgomeryHighBlock.gasSteps_high_cost

def gasSteps_iteration (s : State) (t x word : UInt256) (n j : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hn : n ≤ 32) (hj : j < n)
    (hxfit : x.toNat + 32*j < 2^256)
    (htfit : t.toNat + 32*j < 2^256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loop s t x word n j ret rest)
      (loop s t x word n (j+1) ret rest) :=
  ((Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka guardPath
    (s := loop s t x word n j ret rest)
    hcode hfork (run_guard s t x word n j ret rest hcap hn hj hrun) hrun hnp).trans
    (Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka toHighPath
      (s := bodyEntry s t x word n j ret rest)
      hcode hfork (run_toHigh s t x word n j ret rest hcap hxfit hcode hrun) hrun hnp)).trans
    ((gasSteps_highCall s t x word n j ret rest hcap hcode hfork hrun hnp).trans
      (Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka fromHighPath
        (s := highReturned s t x word n j ret rest)
        hcode hfork (run_fromHigh s t x word n j ret rest hcap htfit hcode hrun) hrun hnp))

theorem gasSteps_iteration_cost_potential (s : State) (t x word : UInt256) (n j : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hn : n ≤ 32) (hj : j < n)
    (hxfit : x.toNat + 32*j < 2^256)
    (htfit : t.toNat + 32*j < 2^256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (gasSteps_iteration s t x word n j ret rest hcap hn hj hxfit htfit
      hcode hfork hrun hnp).cost +
        MachineState.memCost (loop s t x word n j ret rest).activeWords.toNat =
      269 + MachineState.memCost (loop s t x word n (j+1) ret rest).activeWords.toNat := by
  have hguard := Meter.runLocatedBlock_cost_potential_of_copyFree guardPath 26
    (run_guard s t x word n j ret rest hcap hn hj hrun) hfork (by decide) (by decide)
  have hto := Meter.runLocatedBlock_cost_potential_of_copyFree toHighPath 52
    (run_toHigh s t x word n j ret rest hcap hxfit hcode hrun) hfork (by decide) (by decide)
  have hfrom := Meter.runLocatedBlock_cost_potential_of_copyFree fromHighPath 127
    (run_fromHigh s t x word n j ret rest hcap htfit hcode hrun) hfork (by decide) (by decide)
  have hhigh := gasSteps_highCall_cost s t x word n j ret rest hcap hcode hfork hrun hnp
  have hsame : (highEntry s t x word n j ret rest).activeWords =
      (highReturned s t x word n j ret rest).activeWords := rfl
  simp only [gasSteps_iteration, GasSteps.trans_cost, Stepper.runLocatedBlock_sound_cost]
  rw [hsame] at hto
  omega

def gasSteps_word (s : State) (t x word : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hn : n ≤ 32)
    (hxfit : x.toNat + 32*n < 2^256)
    (htfit : t.toNat + 32*n + 64 < 2^256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    GasSteps (entry s t x word n ret rest) (returned s t x word n ret rest) :=
  (Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka setupPath
    (s := entry s t x word n ret rest)
    hcode hfork (run_setup s t x word n ret rest hcap hrun) hrun hnp).trans
    ((GasSteps.iterateBounded n (fun j hj =>
      gasSteps_iteration s t x word n j ret rest hcap hn hj
        (by omega) (by omega) hcode hfork hrun hnp)).trans
      ((Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka guardPath
        (s := loop s t x word n n ret rest)
        hcode hfork (run_guard_finish s t x word n ret rest hcap hcode hrun) hrun hnp).trans
        ((Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka foldPath
          (s := finish s t x word n ret rest)
          hcode hfork (run_fold s t x word n ret rest hcap htfit hrun) hrun hnp).trans
          (Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka cleanupPath
            (s := cleanupEntry s t x word n ret rest)
            hcode hfork (run_cleanup s t x word n ret rest hcap hcode hrun hret) hrun hnp))))

theorem gasSteps_word_cost_potential (s : State) (t x word : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hn : n ≤ 32)
    (hxfit : x.toNat + 32*n < 2^256)
    (htfit : t.toNat + 32*n + 64 < 2^256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    (gasSteps_word s t x word n ret rest hcap hn hxfit htfit hcode hfork hrun hnp hret).cost +
        MachineState.memCost s.activeWords.toNat =
      138 + 269*n + MachineState.memCost (returned s t x word n ret rest).activeWords.toNat := by
  have hsetup := Meter.runLocatedBlock_cost_potential_of_copyFree setupPath 5
    (run_setup s t x word n ret rest hcap hrun) hfork (by decide) (by decide)
  have hloop := Meter.iterateBounded_cost_potential_add n 269
    (fun j hj => gasSteps_iteration s t x word n j ret rest hcap hn hj
      (by omega) (by omega) hcode hfork hrun hnp)
    (fun j hj => gasSteps_iteration_cost_potential s t x word n j ret rest hcap hn hj
      (by omega) (by omega) hcode hfork hrun hnp)
  have hguard := Meter.runLocatedBlock_cost_potential_of_copyFree guardPath 26
    (run_guard_finish s t x word n ret rest hcap hcode hrun) hfork (by decide) (by decide)
  have hfold := Meter.runLocatedBlock_cost_potential_of_copyFree foldPath 79
    (run_fold s t x word n ret rest hcap htfit hrun) hfork (by decide) (by decide)
  have hcleanup := Meter.runLocatedBlock_cost_potential_of_copyFree cleanupPath 28
    (run_cleanup s t x word n ret rest hcap hcode hrun hret) hfork (by decide) (by decide)
  change _ + MachineState.memCost s.activeWords.toNat = _ at hsetup
  simp only [gasSteps_word, GasSteps.trans_cost, Stepper.runLocatedBlock_sound_cost]
  simp only [Nat.mul_comm n 269] at hloop
  omega

theorem gasSteps_word_cost (s : State) (t x word : UInt256) (n : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length < 1000)
    (hn : n ≤ 32)
    (hxfit : x.toNat + 32*n < 2^256)
    (htfit : t.toNat + 32*n + 64 < 2^256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    (gasSteps_word s t x word n ret rest hcap hn hxfit htfit hcode hfork hrun hnp hret).cost =
      138 + 269*n + MachineState.memCost (returned s t x word n ret rest).activeWords.toNat -
        MachineState.memCost s.activeWords.toNat := by
  have h := gasSteps_word_cost_potential s t x word n ret rest hcap hn hxfit htfit
    hcode hfork hrun hnp hret
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWordBlock
