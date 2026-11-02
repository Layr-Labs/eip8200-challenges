import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace HistoricalSearch.GeneratedColumns
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast

/-- Keep the semantic model in the inherited subtraction normal form while
executing no zero addition. This rewrite avoids reducing the byte-array model. -/
theorem normalizer_add_zero (w : UInt256) : w + UInt256.ofNat 0 = w := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  simp only [Nat.zero_mod, Nat.add_zero]
  exact Nat.mod_eq_of_lt w.val.isLt


theorem addC (a b : UInt256) : a + b = b + a := Challenge.EvmProof.Word.word_add_comm a b
theorem mulC (a b : UInt256) : a * b = b * a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val * b.val).val = (b.val * a.val).val
  rw [mul_comm]
theorem addA (a b c : UInt256) : (a + b) + c = a + (b + c) := by
  apply Challenge.EvmProof.Word.word_ext
  change ((a.val + b.val) + c.val).val = (a.val + (b.val + c.val)).val
  rw [add_assoc]
theorem addL (a b c : UInt256) : a + (b + c) = b + (a + c) := by
  rw [← addA, addC a b, addA]
theorem mmC (a b m : UInt256) : UInt256.mulMod a b m = UInt256.mulMod b a m := by
  simp [UInt256.mulMod, Nat.mul_comm]
theorem amC (a b m : UInt256) : UInt256.addMod a b m = UInt256.addMod b a m := by
  simp [UInt256.addMod, Nat.add_comm]
theorem andC (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val &&& b.val).val = (b.val &&& a.val).val
  simp only [Fin.and_val, Nat.and_comm]
theorem orC (a b : UInt256) : UInt256.lor a b = UInt256.lor b a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val ||| b.val).val = (b.val ||| a.val).val
  simp only [Fin.or_val, Nat.or_comm]
theorem xorC (a b : UInt256) : UInt256.xor a b = UInt256.xor b a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val ^^^ b.val).val = (b.val ^^^ a.val).val
  simp only [Fin.xor_val, Nat.xor_comm]
theorem eqC (a b : UInt256) : UInt256.eq a b = UInt256.eq b a := by
  simp [UInt256.eq, eq_comm]
theorem read_32_write_64 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 64) 32 =
    MachineState.readWord mem 32 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_32_write_96 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 96) 32 =
    MachineState.readWord mem 32 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_32_write_128 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 128) 32 =
    MachineState.readWord mem 32 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_32_write_160 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 160) 32 =
    MachineState.readWord mem 32 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_32_write_768 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 768) 32 =
    MachineState.readWord mem 32 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_64_write_32 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 32) 64 =
    MachineState.readWord mem 64 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_64_write_96 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 96) 64 =
    MachineState.readWord mem 64 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_64_write_128 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 128) 64 =
    MachineState.readWord mem 64 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_64_write_160 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 160) 64 =
    MachineState.readWord mem 64 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_64_write_768 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 768) 64 =
    MachineState.readWord mem 64 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_96_write_32 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 32) 96 =
    MachineState.readWord mem 96 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_96_write_64 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 64) 96 =
    MachineState.readWord mem 96 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_96_write_128 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 128) 96 =
    MachineState.readWord mem 96 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_96_write_160 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 160) 96 =
    MachineState.readWord mem 96 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_96_write_768 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 768) 96 =
    MachineState.readWord mem 96 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_128_write_32 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 32) 128 =
    MachineState.readWord mem 128 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_128_write_64 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 64) 128 =
    MachineState.readWord mem 128 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_128_write_96 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 96) 128 =
    MachineState.readWord mem 128 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_128_write_160 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 160) 128 =
    MachineState.readWord mem 128 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_128_write_768 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 768) 128 =
    MachineState.readWord mem 128 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_160_write_32 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 32) 160 =
    MachineState.readWord mem 160 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_160_write_64 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 64) 160 =
    MachineState.readWord mem 160 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_160_write_96 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 96) 160 =
    MachineState.readWord mem 160 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_160_write_128 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 128) 160 =
    MachineState.readWord mem 160 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_160_write_768 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 768) 160 =
    MachineState.readWord mem 160 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_768_write_32 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 32) 768 =
    MachineState.readWord mem 768 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_768_write_64 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 64) 768 =
    MachineState.readWord mem 768 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_768_write_96 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 96) 768 =
    MachineState.readWord mem 768 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_768_write_128 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 128) 768 =
    MachineState.readWord mem 768 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_768_write_160 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 160) 768 =
    MachineState.readWord mem 768 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_1344_write_32 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 32) 1344 =
    MachineState.readWord mem 1344 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_1344_write_64 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 64) 1344 =
    MachineState.readWord mem 1344 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_1344_write_96 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 96) 1344 =
    MachineState.readWord mem 1344 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_1344_write_128 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 128) 1344 =
    MachineState.readWord mem 1344 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_1344_write_160 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 160) 1344 =
    MachineState.readWord mem 1344 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_1344_write_768 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 768) 1344 =
    MachineState.readWord mem 1344 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_1376_write_32 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 32) 1376 =
    MachineState.readWord mem 1376 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_1376_write_64 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 64) 1376 =
    MachineState.readWord mem 1376 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_1376_write_96 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 96) 1376 =
    MachineState.readWord mem 1376 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_1376_write_128 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 128) 1376 =
    MachineState.readWord mem 1376 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_1376_write_160 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 160) 1376 =
    MachineState.readWord mem 1376 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
theorem read_1376_write_768 (mem : ByteArray) (v : UInt256) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v.toNat 32) 768) 1376 =
    MachineState.readWord mem 1376 := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega
def preparedNormalizepart0Program : List Instr :=
  [.op .JUMPDEST,
   .push 3 768,
   .op .MLOAD,
   .push 2 1344,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .LT]

def preparedNormalizepart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 768
  let v1 : UInt256 := MachineState.readWord s.memory 1344
  let v2 : UInt256 := UInt256.lt v0 v1
  {s with pc := UInt256.ofNat 10569, memory := s.memory, stack := v2 :: v1 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem preparedNormalizepart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedNormalizepart0Program {s with pc := UInt256.ofNat 10556, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (preparedNormalizepart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha768 : (768 : UInt256).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha1344 : (1344 : UInt256).toNat = 1344 := rfl
  have hf1344 := Monpro.activeWords_fix s 1344 32 (by decide) (by norm_num) hact
  simp [hz, hzn, preparedNormalizepart0Program, preparedNormalizepart0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha768, hf768, ha1344, hf1344]


def preparedNormalizepart1Program : List Instr :=
  [.op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .push 2 768,
   .op .MSTORE,
   .push 10 1376,
   .op .MLOAD]

def preparedNormalizepart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x2 - x1
  let v1 : UInt256 := UInt256.land x13 v0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 768
  let v3 : UInt256 := MachineState.readWord v2 1376
  {s with pc := UInt256.ofNat 10589, memory := v2, stack := v3 :: x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem preparedNormalizepart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedNormalizepart1Program {s with pc := UInt256.ofNat 10569, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (preparedNormalizepart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha768 : (768 : UInt256).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha1376 : (1376 : UInt256).toNat = 1376 := rfl
  have hf1376 := Monpro.activeWords_fix s 1376 32 (by decide) (by norm_num) hact
  simp [hz, hzn, preparedNormalizepart1Program, preparedNormalizepart1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha768, hf768, ha1376, hf1376]


def preparedNormalizepart2Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Swap ⟨4, by decide⟩),
   .op .LT]

def preparedNormalizepart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := x5 - v0
  let v2 : UInt256 := UInt256.land x12 v1
  let v3 : UInt256 := UInt256.lt x5 v0
  {s with pc := UInt256.ofNat 10597, memory := s.memory, stack := v3 :: x2 :: x3 :: x4 :: v2 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem preparedNormalizepart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedNormalizepart2Program {s with pc := UInt256.ofNat 10589, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (preparedNormalizepart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz, hzn, preparedNormalizepart2Program, preparedNormalizepart2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity]


def preparedNormalizepart3Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Swap ⟨5, by decide⟩)]

def preparedNormalizepart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x1 + x0
  let v1 : UInt256 := x5 - v0
  let v2 : UInt256 := UInt256.land x11 v1
  {s with pc := UInt256.ofNat 10605, memory := s.memory, stack := x5 :: v0 :: x1 :: x2 :: x3 :: x4 :: v2 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem preparedNormalizepart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedNormalizepart3Program {s with pc := UInt256.ofNat 10597, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (preparedNormalizepart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz, hzn, preparedNormalizepart3Program, preparedNormalizepart3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity]


def preparedNormalizepart4Program : List Instr :=
  [.op .LT,
   .op (.Dup ⟨13, by decide⟩),
   .op .ADD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .SUB]

def preparedNormalizepart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lt x0 x1
  let v1 : UInt256 := x14 + v0
  let v2 : UInt256 := MachineState.readWord s.memory 32
  let v3 : UInt256 := v2 - v1
  {s with pc := UInt256.ofNat 10614, memory := s.memory, stack := v3 :: v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem preparedNormalizepart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedNormalizepart4Program {s with pc := UInt256.ofNat 10605, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (preparedNormalizepart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, preparedNormalizepart4Program, preparedNormalizepart4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha32, hf32]


def preparedNormalizepart5Program : List Instr :=
  [.op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push 3 32,
   .op .MSTORE,
   .op .LT,
   .op (.Dup ⟨3, by decide⟩),
   .op .ADD,
   .push 1 64,
   .op .MLOAD]

def preparedNormalizepart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x13 x0
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 32
  let v2 : UInt256 := UInt256.lt x1 x2
  let v3 : UInt256 := x5 + v2
  let v4 : UInt256 := MachineState.readWord v1 64
  {s with pc := UInt256.ofNat 10627, memory := v1, stack := v4 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem preparedNormalizepart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedNormalizepart5Program {s with pc := UInt256.ofNat 10614, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (preparedNormalizepart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, preparedNormalizepart5Program, preparedNormalizepart5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha32, hf32, ha64, hf64]


def preparedNormalizepart6Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push 3 64,
   .op .MSTORE,
   .op .LT]

def preparedNormalizepart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 - x1
  let v1 : UInt256 := UInt256.land x12 v0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 64
  let v3 : UInt256 := UInt256.lt x0 x1
  {s with pc := UInt256.ofNat 10638, memory := v2, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem preparedNormalizepart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedNormalizepart6Program {s with pc := UInt256.ofNat 10627, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (preparedNormalizepart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, preparedNormalizepart6Program, preparedNormalizepart6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha64, hf64]


def preparedNormalizepart7Program : List Instr :=
  [.op (.Dup ⟨6, by decide⟩),
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨13, by decide⟩)]

def preparedNormalizepart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x6 + x0
  let v1 : UInt256 := MachineState.readWord s.memory 96
  let v2 : UInt256 := v1 - v0
  {s with pc := UInt256.ofNat 10647, memory := s.memory, stack := x11 :: v2 :: v1 :: v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem preparedNormalizepart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedNormalizepart7Program {s with pc := UInt256.ofNat 10638, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (preparedNormalizepart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, preparedNormalizepart7Program, preparedNormalizepart7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha96, hf96]


def preparedNormalizepart8Program : List Instr :=
  [.op .AND,
   .push 3 96,
   .op .MSTORE,
   .op .LT,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .push 1 128,
   .op .MLOAD]

def preparedNormalizepart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x0 x1
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 96
  let v2 : UInt256 := UInt256.lt x2 x3
  let v3 : UInt256 := x5 + v2
  let v4 : UInt256 := MachineState.readWord v1 128
  {s with pc := UInt256.ofNat 10659, memory := v1, stack := v4 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem preparedNormalizepart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedNormalizepart8Program {s with pc := UInt256.ofNat 10647, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (preparedNormalizepart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, preparedNormalizepart8Program, preparedNormalizepart8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha96, hf96, ha128, hf128]


def preparedNormalizepart9Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push 3 128,
   .op .MSTORE,
   .op .LT]

def preparedNormalizepart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 - x1
  let v1 : UInt256 := UInt256.land x12 v0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 128
  let v3 : UInt256 := UInt256.lt x0 x1
  {s with pc := UInt256.ofNat 10670, memory := v2, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem preparedNormalizepart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedNormalizepart9Program {s with pc := UInt256.ofNat 10659, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (preparedNormalizepart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, preparedNormalizepart9Program, preparedNormalizepart9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha128, hf128]


def preparedNormalizepart10Program : List Instr :=
  [.op (.Dup ⟨7, by decide⟩),
   .op .ADD,
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨13, by decide⟩)]

def preparedNormalizepart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x7 + x0
  let v1 : UInt256 := MachineState.readWord s.memory 160
  let v2 : UInt256 := v1 - v0
  {s with pc := UInt256.ofNat 10679, memory := s.memory, stack := x11 :: v2 :: v1 :: v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem preparedNormalizepart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedNormalizepart10Program {s with pc := UInt256.ofNat 10670, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (preparedNormalizepart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, preparedNormalizepart10Program, preparedNormalizepart10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha160, hf160]


def preparedNormalizepart11Program : List Instr :=
  [.op .AND,
   .push 3 160,
   .op .MSTORE,
   .op .LT,
   .op (.Dup ⟨9, by decide⟩),
   .op .ADD,
   .push 3 1344,
   .op (.Swap ⟨14, by decide⟩)]

def preparedNormalizepart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x0 x1
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 160
  let v2 : UInt256 := UInt256.lt x2 x3
  let v3 : UInt256 := x12 + v2
  {s with pc := UInt256.ofNat 10693, memory := v1, stack := x17 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: (UInt256.ofNat 1344) :: rest}

theorem preparedNormalizepart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedNormalizepart11Program {s with pc := UInt256.ofNat 10679, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (preparedNormalizepart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, preparedNormalizepart11Program, preparedNormalizepart11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha160, hf160]


def preparedNormalizepart12Program : List Instr :=
  [.op .SUB,
   .op (.Swap ⟨13, by decide⟩),
   .op .MLOAD,
   .op (.Swap ⟨11, by decide⟩)]

def preparedNormalizepart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 - x1
  let v1 : UInt256 := MachineState.readWord s.memory 1344
  {s with pc := UInt256.ofNat 10697, memory := s.memory, stack := x13 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: v1 :: x14 :: v0 :: rest}

theorem preparedNormalizepart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) (hk_x15 : x15 = UInt256.ofNat 1344) :
    runInstructions preparedNormalizepart12Program {s with pc := UInt256.ofNat 10693, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (preparedNormalizepart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  have ha1344 : (1344 : UInt256).toNat = 1344 := rfl
  have hf1344 := Monpro.activeWords_fix s 1344 32 (by decide) (by norm_num) hact
  simp [hk_x15, hz, hzn, preparedNormalizepart12Program, preparedNormalizepart12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha1344, hf1344]


def preparedNormalizeProgram : List Instr :=
  [.op .JUMPDEST,
   .push 3 768,
   .op .MLOAD,
   .push 2 1344,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .LT,
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .push 2 768,
   .op .MSTORE,
   .push 10 1376,
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Swap ⟨4, by decide⟩),
   .op .LT,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Swap ⟨5, by decide⟩),
   .op .LT,
   .op (.Dup ⟨13, by decide⟩),
   .op .ADD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push 3 32,
   .op .MSTORE,
   .op .LT,
   .op (.Dup ⟨3, by decide⟩),
   .op .ADD,
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push 3 64,
   .op .MSTORE,
   .op .LT,
   .op (.Dup ⟨6, by decide⟩),
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push 3 96,
   .op .MSTORE,
   .op .LT,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push 3 128,
   .op .MSTORE,
   .op .LT,
   .op (.Dup ⟨7, by decide⟩),
   .op .ADD,
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push 3 160,
   .op .MSTORE,
   .op .LT,
   .op (.Dup ⟨9, by decide⟩),
   .op .ADD,
   .push 3 1344,
   .op (.Swap ⟨14, by decide⟩),
   .op .SUB,
   .op (.Swap ⟨13, by decide⟩),
   .op .MLOAD,
   .op (.Swap ⟨11, by decide⟩)]

def preparedNormalizeModel (s : State) (n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 768
  let v1 : UInt256 := MachineState.readWord s.memory 1344
  let v2 : UInt256 := UInt256.lt v0 v1
  let v3 : UInt256 := v0 - v1
  let v4 : UInt256 := UInt256.land MASK v3
  let v5 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v4.toNat 32) 768
  let v6 : UInt256 := MachineState.readWord v5 1376
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := a1 - v7
  let v9 : UInt256 := UInt256.land MASK v8
  let v10 : UInt256 := UInt256.lt a1 v7
  let v11 : UInt256 := n2 + v10
  let v12 : UInt256 := a2 - v11
  let v13 : UInt256 := UInt256.land MASK v12
  let v14 : UInt256 := UInt256.lt a2 v11
  let v15 : UInt256 := n3 + v14
  let v16 : UInt256 := MachineState.readWord v5 32
  let v17 : UInt256 := v16 - v15
  let v18 : UInt256 := UInt256.land MASK v17
  let v19 : ByteArray := MachineState.writeBytes v5 (Data.Bytes.natToBytesPadded v18.toNat 32) 32
  let v20 : UInt256 := UInt256.lt v16 v15
  let v21 : UInt256 := n4 + v20
  let v22 : UInt256 := MachineState.readWord v19 64
  let v23 : UInt256 := v22 - v21
  let v24 : UInt256 := UInt256.land MASK v23
  let v25 : ByteArray := MachineState.writeBytes v19 (Data.Bytes.natToBytesPadded v24.toNat 32) 64
  let v26 : UInt256 := UInt256.lt v22 v21
  let v27 : UInt256 := n5 + v26
  let v28 : UInt256 := MachineState.readWord v25 96
  let v29 : UInt256 := v28 - v27
  let v30 : UInt256 := UInt256.land MASK v29
  let v31 : ByteArray := MachineState.writeBytes v25 (Data.Bytes.natToBytesPadded v30.toNat 32) 96
  let v32 : UInt256 := UInt256.lt v28 v27
  let v33 : UInt256 := n6 + v32
  let v34 : UInt256 := MachineState.readWord v31 128
  let v35 : UInt256 := v34 - v33
  let v36 : UInt256 := UInt256.land MASK v35
  let v37 : ByteArray := MachineState.writeBytes v31 (Data.Bytes.natToBytesPadded v36.toNat 32) 128
  let v38 : UInt256 := UInt256.lt v34 v33
  let v39 : UInt256 := n7 + v38
  let v40 : UInt256 := MachineState.readWord v37 160
  let v41 : UInt256 := v40 - v39
  let v42 : UInt256 := UInt256.land MASK v41
  let v43 : ByteArray := MachineState.writeBytes v37 (Data.Bytes.natToBytesPadded v42.toNat 32) 160
  let v44 : UInt256 := UInt256.lt v40 v39
  let v45 : UInt256 := n8 + v44
  let v46 : UInt256 := a8 - v45
  let v47 : UInt256 := MachineState.readWord v43 1344
  {s with pc := UInt256.ofNat 10697, memory := v43, stack := n0 :: n2 :: n6 :: n4 :: v9 :: v13 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: v47 :: n3 :: v46 :: rest}

theorem preparedNormalize_run (s : State) (n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedNormalizeProgram {s with pc := UInt256.ofNat 10556, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} =
      some (preparedNormalizeModel s n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 768
  let v1 : UInt256 := MachineState.readWord s.memory 1344
  let v2 : UInt256 := UInt256.lt v0 v1
  let v3 : UInt256 := v0 - v1
  let v4 : UInt256 := UInt256.land MASK v3
  let v5 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v4.toNat 32) 768
  let v6 : UInt256 := MachineState.readWord v5 1376
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := a1 - v7
  let v9 : UInt256 := UInt256.land MASK v8
  let v10 : UInt256 := UInt256.lt a1 v7
  let v11 : UInt256 := n2 + v10
  let v12 : UInt256 := a2 - v11
  let v13 : UInt256 := UInt256.land MASK v12
  let v14 : UInt256 := UInt256.lt a2 v11
  let v15 : UInt256 := n3 + v14
  let v16 : UInt256 := MachineState.readWord v5 32
  let v17 : UInt256 := v16 - v15
  let v18 : UInt256 := UInt256.land MASK v17
  let v19 : ByteArray := MachineState.writeBytes v5 (Data.Bytes.natToBytesPadded v18.toNat 32) 32
  let v20 : UInt256 := UInt256.lt v16 v15
  let v21 : UInt256 := n4 + v20
  let v22 : UInt256 := MachineState.readWord v19 64
  let v23 : UInt256 := v22 - v21
  let v24 : UInt256 := UInt256.land MASK v23
  let v25 : ByteArray := MachineState.writeBytes v19 (Data.Bytes.natToBytesPadded v24.toNat 32) 64
  let v26 : UInt256 := UInt256.lt v22 v21
  let v27 : UInt256 := n5 + v26
  let v28 : UInt256 := MachineState.readWord v25 96
  let v29 : UInt256 := v28 - v27
  let v30 : UInt256 := UInt256.land MASK v29
  let v31 : ByteArray := MachineState.writeBytes v25 (Data.Bytes.natToBytesPadded v30.toNat 32) 96
  let v32 : UInt256 := UInt256.lt v28 v27
  let v33 : UInt256 := n6 + v32
  let v34 : UInt256 := MachineState.readWord v31 128
  let v35 : UInt256 := v34 - v33
  let v36 : UInt256 := UInt256.land MASK v35
  let v37 : ByteArray := MachineState.writeBytes v31 (Data.Bytes.natToBytesPadded v36.toNat 32) 128
  let v38 : UInt256 := UInt256.lt v34 v33
  let v39 : UInt256 := n7 + v38
  let v40 : UInt256 := MachineState.readWord v37 160
  let v41 : UInt256 := v40 - v39
  let v42 : UInt256 := UInt256.land MASK v41
  let v43 : ByteArray := MachineState.writeBytes v37 (Data.Bytes.natToBytesPadded v42.toNat 32) 160
  let v44 : UInt256 := UInt256.lt v40 v39
  let v45 : UInt256 := n8 + v44
  let v46 : UInt256 := a8 - v45
  let v47 : UInt256 := MachineState.readWord v43 1344
  have h0 : runInstructions preparedNormalizepart0Program {s with pc := UInt256.ofNat 10556, memory := s.memory, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10569, memory := s.memory, stack := v2 :: v1 :: v0 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [preparedNormalizepart0Model, v0, v1, v2] using preparedNormalizepart0_run (s) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h1 : runInstructions preparedNormalizepart1Program {s with pc := UInt256.ofNat 10569, memory := s.memory, stack := v2 :: v1 :: v0 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10589, memory := v5, stack := v6 :: v2 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [preparedNormalizepart1Model, v3, v4, v5, v6] using preparedNormalizepart1_run (s) (v2) (v1) (v0) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h2 : runInstructions preparedNormalizepart2Program {s with pc := UInt256.ofNat 10589, memory := v5, stack := v6 :: v2 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10597, memory := v5, stack := v10 :: n2 :: n6 :: n4 :: v9 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [preparedNormalizepart2Model, v7, v8, v9, v10] using preparedNormalizepart2_run ({s with memory := v5}) (v6) (v2) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h3 : runInstructions preparedNormalizepart3Program {s with pc := UInt256.ofNat 10597, memory := v5, stack := v10 :: n2 :: n6 :: n4 :: v9 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10605, memory := v5, stack := a2 :: v11 :: n2 :: n6 :: n4 :: v9 :: v13 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [preparedNormalizepart3Model, v11, v12, v13] using preparedNormalizepart3_run ({s with memory := v5}) (v10) (n2) (n6) (n4) (v9) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h4 : runInstructions preparedNormalizepart4Program {s with pc := UInt256.ofNat 10605, memory := v5, stack := a2 :: v11 :: n2 :: n6 :: n4 :: v9 :: v13 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10614, memory := v5, stack := v17 :: v16 :: v15 :: n2 :: n6 :: n4 :: v9 :: v13 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [preparedNormalizepart4Model, v14, v15, v16, v17] using preparedNormalizepart4_run ({s with memory := v5}) (a2) (v11) (n2) (n6) (n4) (v9) (v13) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h5 : runInstructions preparedNormalizepart5Program {s with pc := UInt256.ofNat 10614, memory := v5, stack := v17 :: v16 :: v15 :: n2 :: n6 :: n4 :: v9 :: v13 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10627, memory := v19, stack := v22 :: v21 :: n2 :: n6 :: n4 :: v9 :: v13 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [preparedNormalizepart5Model, v18, v19, v20, v21, v22] using preparedNormalizepart5_run ({s with memory := v5}) (v17) (v16) (v15) (n2) (n6) (n4) (v9) (v13) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h6 : runInstructions preparedNormalizepart6Program {s with pc := UInt256.ofNat 10627, memory := v19, stack := v22 :: v21 :: n2 :: n6 :: n4 :: v9 :: v13 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10638, memory := v25, stack := v26 :: n2 :: n6 :: n4 :: v9 :: v13 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [preparedNormalizepart6Model, v23, v24, v25, v26] using preparedNormalizepart6_run ({s with memory := v19}) (v22) (v21) (n2) (n6) (n4) (v9) (v13) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h7 : runInstructions preparedNormalizepart7Program {s with pc := UInt256.ofNat 10638, memory := v25, stack := v26 :: n2 :: n6 :: n4 :: v9 :: v13 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10647, memory := v25, stack := MASK :: v29 :: v28 :: v27 :: n2 :: n6 :: n4 :: v9 :: v13 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [preparedNormalizepart7Model, v27, v28, v29] using preparedNormalizepart7_run ({s with memory := v25}) (v26) (n2) (n6) (n4) (v9) (v13) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h8 : runInstructions preparedNormalizepart8Program {s with pc := UInt256.ofNat 10647, memory := v25, stack := MASK :: v29 :: v28 :: v27 :: n2 :: n6 :: n4 :: v9 :: v13 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10659, memory := v31, stack := v34 :: v33 :: n2 :: n6 :: n4 :: v9 :: v13 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [preparedNormalizepart8Model, v30, v31, v32, v33, v34] using preparedNormalizepart8_run ({s with memory := v25}) (MASK) (v29) (v28) (v27) (n2) (n6) (n4) (v9) (v13) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h9 : runInstructions preparedNormalizepart9Program {s with pc := UInt256.ofNat 10659, memory := v31, stack := v34 :: v33 :: n2 :: n6 :: n4 :: v9 :: v13 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10670, memory := v37, stack := v38 :: n2 :: n6 :: n4 :: v9 :: v13 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [preparedNormalizepart9Model, v35, v36, v37, v38] using preparedNormalizepart9_run ({s with memory := v31}) (v34) (v33) (n2) (n6) (n4) (v9) (v13) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h10 : runInstructions preparedNormalizepart10Program {s with pc := UInt256.ofNat 10670, memory := v37, stack := v38 :: n2 :: n6 :: n4 :: v9 :: v13 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10679, memory := v37, stack := MASK :: v41 :: v40 :: v39 :: n2 :: n6 :: n4 :: v9 :: v13 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [preparedNormalizepart10Model, v39, v40, v41] using preparedNormalizepart10_run ({s with memory := v37}) (v38) (n2) (n6) (n4) (v9) (v13) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h11 : runInstructions preparedNormalizepart11Program {s with pc := UInt256.ofNat 10679, memory := v37, stack := MASK :: v41 :: v40 :: v39 :: n2 :: n6 :: n4 :: v9 :: v13 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10693, memory := v43, stack := a8 :: v45 :: n2 :: n6 :: n4 :: v9 :: v13 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: (UInt256.ofNat 1344) :: rest} := by
    simpa only [preparedNormalizepart11Model, v42, v43, v44, v45] using preparedNormalizepart11_run ({s with memory := v37}) (MASK) (v41) (v40) (v39) (n2) (n6) (n4) (v9) (v13) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h12 : runInstructions preparedNormalizepart12Program {s with pc := UInt256.ofNat 10693, memory := v43, stack := a8 :: v45 :: n2 :: n6 :: n4 :: v9 :: v13 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: (UInt256.ofNat 1344) :: rest} = some {s with pc := UInt256.ofNat 10697, memory := v43, stack := n0 :: n2 :: n6 :: n4 :: v9 :: v13 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: v47 :: n3 :: v46 :: rest} := by
    simpa only [preparedNormalizepart12Model, v46, v47] using preparedNormalizepart12_run ({s with memory := v43}) (a8) (v45) (n2) (n6) (n4) (v9) (v13) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) ((UInt256.ofNat 1344)) rest hcap hact (by rfl)
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))

#print axioms preparedNormalize_run

def preparedOldModel (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1344
  let v1 : UInt256 := MachineState.readWord s.memory 768
  let v2 : UInt256 := UInt256.lt v1 v0
  let v3 : UInt256 := v1 - v0
  let v4 : UInt256 := UInt256.land x10 v3
  let v5 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v4.toNat 32) 768
  let v6 : UInt256 := MachineState.readWord v5 1376
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := UInt256.lt x3 v7
  let v9 : UInt256 := x3 - v7
  let v10 : UInt256 := UInt256.land x10 v9
  let v11 : UInt256 := x0 + v8
  let v12 : UInt256 := UInt256.lt x4 v11
  let v13 : UInt256 := x4 - v11
  let v14 : UInt256 := UInt256.land x10 v13
  let v15 : UInt256 := x12 + v12
  let v16 : UInt256 := MachineState.readWord v5 32
  let v17 : UInt256 := UInt256.lt v16 v15
  let v18 : UInt256 := v16 - v15
  let v19 : UInt256 := UInt256.land x10 v18
  let v20 : ByteArray := MachineState.writeBytes v5 (Data.Bytes.natToBytesPadded v19.toNat 32) 32
  let v21 : UInt256 := x2 + v17
  let v22 : UInt256 := MachineState.readWord v20 64
  let v23 : UInt256 := UInt256.lt v22 v21
  let v24 : UInt256 := v22 - v21
  let v25 : UInt256 := UInt256.land x10 v24
  let v26 : ByteArray := MachineState.writeBytes v20 (Data.Bytes.natToBytesPadded v25.toNat 32) 64
  let v27 : UInt256 := x5 + v23
  let v28 : UInt256 := MachineState.readWord v26 96
  let v29 : UInt256 := UInt256.lt v28 v27
  let v30 : UInt256 := v28 - v27
  let v31 : UInt256 := UInt256.land x10 v30
  let v32 : ByteArray := MachineState.writeBytes v26 (Data.Bytes.natToBytesPadded v31.toNat 32) 96
  let v33 : UInt256 := x1 + v29
  let v34 : UInt256 := MachineState.readWord v32 128
  let v35 : UInt256 := UInt256.lt v34 v33
  let v36 : UInt256 := v34 - v33
  let v37 : UInt256 := UInt256.land x10 v36
  let v38 : ByteArray := MachineState.writeBytes v32 (Data.Bytes.natToBytesPadded v37.toNat 32) 128
  let v39 : UInt256 := x6 + v35
  let v40 : UInt256 := MachineState.readWord v38 160
  let v41 : UInt256 := UInt256.lt v40 v39
  let v42 : UInt256 := v40 - v39
  let v43 : UInt256 := UInt256.land x10 v42
  let v44 : ByteArray := MachineState.writeBytes v38 (Data.Bytes.natToBytesPadded v43.toNat 32) 160
  let v45 : UInt256 := x8 + v41
  let v46 : UInt256 := x13 - v45
  let v47 : UInt256 := MachineState.readWord v44 1344
  {s with pc := UInt256.ofNat 10697, memory := v44, stack := x11 :: x0 :: x1 :: x2 :: v10 :: v14 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: v47 :: x12 :: v46 :: rest}

theorem prepared_old_new (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) :
    preparedOldModel s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest = preparedNormalizeModel s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest := by
  simp only [preparedOldModel, preparedNormalizeModel, addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_32_write_64, read_32_write_96, read_32_write_128, read_32_write_160, read_32_write_768, read_64_write_32, read_64_write_96, read_64_write_128, read_64_write_160, read_64_write_768, read_96_write_32, read_96_write_64, read_96_write_128, read_96_write_160, read_96_write_768, read_128_write_32, read_128_write_64, read_128_write_96, read_128_write_160, read_128_write_768, read_160_write_32, read_160_write_64, read_160_write_96, read_160_write_128, read_160_write_768, read_768_write_32, read_768_write_64, read_768_write_96, read_768_write_128, read_768_write_160, read_1344_write_32, read_1344_write_64, read_1344_write_96, read_1344_write_128, read_1344_write_160, read_1344_write_768, read_1376_write_32, read_1376_write_64, read_1376_write_96, read_1376_write_128, read_1376_write_160, read_1376_write_768]

def normalizeProgram : List Instr := preparedNormalizeProgram

def normalizeModel (s : State) (n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1344
  let v1 : UInt256 := v0 + (UInt256.ofNat 0)
  let v2 : UInt256 := MachineState.readWord s.memory 768
  let v3 : UInt256 := UInt256.lt v2 v1
  let v4 : UInt256 := v2 - v1
  let v5 : UInt256 := UInt256.land MASK v4
  let v6 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v5.toNat 32) 768
  let v7 : UInt256 := MachineState.readWord v6 1376
  let v8 : UInt256 := v7 + v3
  let v9 : UInt256 := UInt256.lt a1 v8
  let v10 : UInt256 := a1 - v8
  let v11 : UInt256 := UInt256.land MASK v10
  let v12 : UInt256 := n2 + v9
  let v13 : UInt256 := UInt256.lt a2 v12
  let v14 : UInt256 := a2 - v12
  let v15 : UInt256 := UInt256.land MASK v14
  let v16 : UInt256 := n3 + v13
  let v17 : UInt256 := MachineState.readWord v6 32
  let v18 : UInt256 := UInt256.lt v17 v16
  let v19 : UInt256 := v17 - v16
  let v20 : UInt256 := UInt256.land MASK v19
  let v21 : ByteArray := MachineState.writeBytes v6 (Data.Bytes.natToBytesPadded v20.toNat 32) 32
  let v22 : UInt256 := n4 + v18
  let v23 : UInt256 := MachineState.readWord v21 64
  let v24 : UInt256 := UInt256.lt v23 v22
  let v25 : UInt256 := v23 - v22
  let v26 : UInt256 := UInt256.land MASK v25
  let v27 : ByteArray := MachineState.writeBytes v21 (Data.Bytes.natToBytesPadded v26.toNat 32) 64
  let v28 : UInt256 := n5 + v24
  let v29 : UInt256 := MachineState.readWord v27 96
  let v30 : UInt256 := UInt256.lt v29 v28
  let v31 : UInt256 := v29 - v28
  let v32 : UInt256 := UInt256.land MASK v31
  let v33 : ByteArray := MachineState.writeBytes v27 (Data.Bytes.natToBytesPadded v32.toNat 32) 96
  let v34 : UInt256 := n6 + v30
  let v35 : UInt256 := MachineState.readWord v33 128
  let v36 : UInt256 := UInt256.lt v35 v34
  let v37 : UInt256 := v35 - v34
  let v38 : UInt256 := UInt256.land MASK v37
  let v39 : ByteArray := MachineState.writeBytes v33 (Data.Bytes.natToBytesPadded v38.toNat 32) 128
  let v40 : UInt256 := n7 + v36
  let v41 : UInt256 := MachineState.readWord v39 160
  let v42 : UInt256 := UInt256.lt v41 v40
  let v43 : UInt256 := v41 - v40
  let v44 : UInt256 := UInt256.land MASK v43
  let v45 : ByteArray := MachineState.writeBytes v39 (Data.Bytes.natToBytesPadded v44.toNat 32) 160
  let v46 : UInt256 := n8 + v42
  let v47 : UInt256 := UInt256.lt a8 v46
  let v48 : UInt256 := a8 - v46
  let v49 : UInt256 := MachineState.readWord v45 1344
  {s with pc := UInt256.ofNat 10697, memory := v45, stack := n0 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: v49 :: n3 :: v48 :: rest}

theorem normalizeModel_eq_old (s : State) (n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 : UInt256) (rest : List UInt256) :
    normalizeModel s n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 rest = preparedOldModel s n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 rest := by
  simp only [normalizeModel, preparedOldModel, normalizer_add_zero]

theorem normalize_run (s : State) (n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normalizeProgram {s with pc := UInt256.ofNat 10556, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} =
      some (normalizeModel s n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 rest) := by
  change runInstructions preparedNormalizeProgram _ = _
  rw [preparedNormalize_run s n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 rest hcap hact]
  exact congrArg some ((prepared_old_new s n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 rest).symm.trans (normalizeModel_eq_old s n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 rest).symm)

#print axioms normalize_run
end HistoricalSearch.GeneratedColumns
