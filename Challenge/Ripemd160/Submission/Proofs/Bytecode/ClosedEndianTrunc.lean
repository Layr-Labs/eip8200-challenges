import Challenge.Ripemd160.Submission.Proofs.Bytecode.ClosedEndianReuse
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentOutput
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedOutputMath
import Batteries.Tactic.OpenPrivate

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-!
The first output byte-swap stage, with its byte mask materialised as a literal
instead of the runtime quotient `(2^256 - 1) / 257`.

The literal keeps only the low 160 bits of `mask8`. This is sound because the
stage only ever sees the packed five-word digest, which is below `2^160`.
The mask is applied to `(value >>> 8) ^^^ value`, which is then below `2^160` too,
and bits of `mask8` at or above bit 160 cannot survive the AND.
-/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ClosedEndianTrunc

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.EvmProof.Word
open StackRoundTrace DenseScheduleTemplate DenseScheduleTrace

open private word_add_assoc word_add_ofNat_assoc add_ofNat_assoc
  add_ofNat_assoc_hAdd add_ofNat_assoc_add add_assoc_explicit
  add_assoc_explicit_hAdd add_assoc_hAdd_explicit mul_op
  from Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace

/-- The low 160 bits of `mask8`, as a 19-byte literal. -/
def mask8Low : UInt256 :=
  UInt256.ofNat 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff

theorem mask8Low_toNat : mask8Low.toNat = mask8.toNat % 2 ^ 160 := by
  simp only [mask8Low, mask8, Word.word_toNat_ofNat]
  norm_num

private theorem xor_toNat (a b : UInt256) :
    (UInt256.xor a b).toNat = (a.toNat ^^^ b.toNat) := by
  cases a with | mk a =>
  cases b with | mk b =>
  simp only [UInt256.xor, UInt256.toNat]
  unfold Fin.xor
  simp only
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow a.isLt b.isLt)

private theorem and_mod_of_lt (m y : Nat) (hy : y < 2 ^ 160) :
    (m % 2 ^ 160) &&& y = m &&& y := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow]
  by_cases hi : i < 160
  · simp [hi]
  · have hyi : y.testBit i = false := by
      apply Nat.testBit_lt_two_pow
      exact Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp [hi, hyi]

theorem land_mask8Low (value : UInt256) (hv : value.toNat < 2 ^ 160) :
    UInt256.land mask8Low
        (UInt256.xor (UInt256.shiftRight value (UInt256.ofNat 8)) value) =
      UInt256.land mask8
        (UInt256.xor (UInt256.shiftRight value (UInt256.ofNat 8)) value) := by
  apply Word.word_ext
  rw [Word.word_toNat_land, Word.word_toNat_land, xor_toNat,
    Word.shiftRight_toNat value (by norm_num), mask8Low_toNat]
  apply and_mod_of_lt
  exact Nat.xor_lt_two_pow
    (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hv) hv

private theorem packedHash_eq_pack5 (h : Compression.HashState) :
    StaggerPersistentOutput.packedHash h = PackedOutputMath.pack5 h.h0 h.h1 h.h2 h.h3 h.h4 := by
  simp only [StaggerPersistentOutput.packedHash, PackedOutputMath.pack5, PackedOutputMath.append32,
    Word.lor_comm]

theorem packedHash_lt (h : Compression.HashState) :
    (StaggerPersistentOutput.packedHash h).toNat < 2 ^ 160 := by
  rw [packedHash_eq_pack5]
  exact PackedOutputMath.pack5_lt_pow160 h.h0 h.h1 h.h2 h.h3 h.h4

/-- Stage 8 with a literal, truncated mask. The factor is kept below the XOR operands. -/
def code : List Instr :=
  [ClosedEndianReuse.factorPush 8, .op (.Dup ⟨1, by decide⟩), dup1,
   push1 (UInt256.ofNat 8), op .SHR, op .XOR,
   .push ⟨19, by decide⟩ mask8Low, op .AND, op .MUL, op .XOR]

theorem run_endian (s : State) (startPC value : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1019)
    (hv : value.toNat < 2 ^ 160)
    (hrun : s.halt = .Running) :
    runInstrSeq code {s with pc := startPC, stack := value :: rest} =
      some {s with
        pc := pcAfter startPC code
        stack := packedStage value 8 mask8 :: rest} := by
  have hcap (m : Nat) (hm : m ≤ 5) : rest.length + m < 1024 := by omega
  have hcap2 : rest.length + 1 + 1 < 1024 := by omega
  have hcap3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have hcap4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hsemantic :
      UInt256.xor
        (UInt256.mul (endianFactor 8)
          (UInt256.land mask8Low
            (UInt256.xor (UInt256.shiftRight value (UInt256.ofNat 8)) value))) value =
        packedStage value 8 mask8 := by
    rw [land_mask8Low value hv, Word.land_comm mask8]
    simpa only [multipliedStage, endianDelta, endianFactor] using
      DenseEndianMultiply.multipliedStage8_eq_packedStage value
  simp only [endianFactor] at hsemantic
  norm_num at hsemantic
  simp (config := { maxSteps := 1000000 })
    [code, ClosedEndianReuse.factorPush, endianFactorPush, endianFactor,
      op, push1, push2, push3, dup1,
      runInstrSeq, Stepper.runInstr, pcAfter, hrun, hcap, hcap2, hcap3, hcap4, hcap5,
      UInt256.succ, Instr.size, Instr.size_push, Instr.size_op, Word.literal_eq_ofNat,
      Word.word_toNat_ofNat, Word.ofNat_add_mod, Word.succ_ofNat,
      List.exchange, List.getElem?_cons_zero, List.getElem?_cons_succ,
      word_add_assoc, word_add_ofNat_assoc, hsemantic]
  repeat first
    | rw [add_ofNat_assoc_hAdd]
    | rw [add_ofNat_assoc_add]
    | rw [add_ofNat_assoc]
  simp only [add_assoc_explicit, add_assoc_explicit_hAdd,
    add_assoc_hAdd_explicit, word_add_assoc]
  simp [Word.ofNat_add_mod, Nat.add_assoc]
  rw [mul_op]
  convert hsemantic using 1
  all_goals
    simp [UInt256.mul, Fin.mul_def, Nat.mul_comm]

theorem advances {instruction : Instr} {s t : State}
    (hmem : instruction ∈ code) (hrun : Stepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  simp only [code, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply DenseScheduleLift.runInstr_pc_of_advances ?_ hrun
  all_goals first
    | exact Or.inl (Or.inr (Or.inr rfl))
    | exact Or.inr (Or.inr rfl)
    | exact Or.inl (Or.inl (by constructor))

theorem run_located {artifact : ProgramArtifact} {fork : Fork}
    (site : StackRoundTemplate.GenericRoundSite artifact fork code)
    (s : State) (value : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1019)
    (hv : value.toNat < 2 ^ 160)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock site.path {s with pc := site.startPC, stack := value :: rest} =
      some {s with pc := site.endPC, stack := packedStage value 8 mask8 :: rest} := by
  have hend : site.endPC = pcAfter site.startPC code := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  have hraw : Stepper.runLocatedBlock site.path
      {s with pc := site.startPC, stack := value :: rest} =
      runInstrSeq code {s with pc := site.startPC, stack := value :: rest} := by
    apply runLocatedBlock_eq_runInstrSeq_site site _ rfl
    intro located hmem u v hresult
    apply advances ?_ hresult
    rw [← site.instruction_eq]
    exact List.mem_map_of_mem hmem
  rw [hraw, run_endian s site.startPC value rest hstack hv hrun, ← hend]

def gasSteps_endian {artifact : ProgramArtifact} {fork : Fork}
    (site : StackRoundTemplate.GenericRoundSite artifact fork code)
    (s : State) (value : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1019)
    (hv : value.toNat < 2 ^ 160)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := site.startPC, stack := value :: rest}
      {s with pc := site.endPC, stack := packedStage value 8 mask8 :: rest} := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact run_located site s value rest hstack hv hrun
  · exact hrun
  · exact hnp

#print axioms land_mask8Low
#print axioms packedHash_lt
#print axioms run_endian
#print axioms advances
#print axioms run_located
#print axioms gasSteps_endian

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ClosedEndianTrunc
