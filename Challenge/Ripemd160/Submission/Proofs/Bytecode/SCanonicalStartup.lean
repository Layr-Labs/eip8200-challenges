import Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWord
import Challenge.EvmProof.Word
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneUInt256Bridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedDerivedStartup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleLift
import Init.Data.BitVec.Bitblast

set_option warningAsError true

/-!
S canonical multiply startup: raw execution module.

33 ops / 48 bytes. Keeps L/U/P cache construction, derives `R = 1 + 2^128` as `P / L`,
then five `PUSH address; MLOAD; DUP; MUL` loads for 160/128/96/64/32 with
`DUP2..DUP6`, restores `F` via `PUSH5 F; SWAP6; POP`.

Under five canonical hash-load bounds the result stack equals
`PairedDerivedStartup.resultStack` exactly.

The duplication arithmetic (`dupFactor`, `mul_dupFactor`) and execution
proof are reused from the previously promoted compact-startup implementation.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SCanonicalStartup

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTrace DenseScheduleTemplate
open PairedLaneUInt256Bridge

/-- The 17-byte duplication literal `R = 1 + 2 ^ 128` pushed by the S startup. -/
def dupFactor : UInt256 := UInt256.ofNat (1 + 2 ^ 128)

/-- `2 ^ 128 < 2 ^ 256`: small decides only, no giant evaluation. -/
private theorem pow128_lt_size : (2 ^ 128 : Nat) < 2 ^ 256 :=
  Nat.pow_lt_pow_right (by decide) (by decide)

/-- The literal fits in a word: derived from `pow128_lt_size` by `omega`. -/
private theorem dupLit_lt_size : (1 + 2 ^ 128 : Nat) < 2 ^ 256 := by
  have h := pow128_lt_size
  omega

theorem dupFactor_toNat : dupFactor.toNat = 1 + 2 ^ 128 := by
  unfold dupFactor
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt dupLit_lt_size]

/-- A canonical 32-bit word has no bits at or above index 32. -/
private theorem getLsbD_eq_false_of_canonical (x : BitVec 256)
    (h : x.toNat < 2 ^ 32) {i : Nat} (hi : 32 ≤ i) :
    x.getLsbD i = false := by
  have hlt : x.toNat < 2 ^ i :=
    lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hi)
  have hbit : x.toNat.testBit i = false := Nat.testBit_lt_two_pow hlt
  rwa [BitVec.testBit_toNat] at hbit

/-- The 128-shifted copy of a canonical word is disjoint from the original. -/
private theorem shift128_disjoint (x : BitVec 256) (h : x.toNat < 2 ^ 32) :
    (x <<< 128) &&& x = 0#256 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  by_cases hlo : i < 128
  · simp [hlo]
  · have hx : x.getLsbD i = false :=
      getLsbD_eq_false_of_canonical x h (by omega)
    simp [hx]

/-- `twoPow 256 128` denotes `2 ^ 128`. -/
private theorem twoPow128_toNat : (BitVec.twoPow 256 128).toNat = 2 ^ 128 :=
  BitVec.toNat_twoPow_of_lt (by decide)

/-- Factor split by toNat congruence: no 256-bit `decide`. -/
private theorem factor_split :
    BitVec.ofNat 256 (1 + 2 ^ 128) = BitVec.twoPow 256 128 + 1#256 := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (BitVec.ofNat 256 (1 + 2 ^ 128)).toNat = 1 + 2 ^ 128 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt dupLit_lt_size]
  have h2 : (BitVec.twoPow 256 128 + 1#256).toNat = 1 + 2 ^ 128 := by
    rw [BitVec.toNat_add, BitVec.toNat_one (by decide), twoPow128_toNat,
      Nat.add_comm (2 ^ 128) 1, Nat.mod_eq_of_lt dupLit_lt_size]
  rw [h1, h2]

/-- Bit-vector form: scaling a canonical word by `1 + 2 ^ 128` copies it. -/
theorem bits_mul_dupFactor (x : BitVec 256) (h : x.toNat < 2 ^ 32) :
    x * BitVec.ofNat 256 (1 + 2 ^ 128) = (x <<< 128) ||| x := by
  rw [factor_split,
    BitVec.mul_add, BitVec.mul_twoPow_eq_shiftLeft, BitVec.mul_one]
  exact BitVec.add_eq_or_of_and_eq_zero _ _ (shift128_disjoint x h)

/-- EVM-word form: `x * (1 + 2 ^ 128) = x OR (x << 128)` for canonical `x`. -/
theorem mul_dupFactor (x : UInt256) (h : x.toNat < 2 ^ 32) :
    UInt256.mul x dupFactor =
      UInt256.lor x (UInt256.shiftLeft x (UInt256.ofNat 128)) := by
  have hb : (bits x).toNat < 2 ^ 32 := by
    rw [bits_toNat]
    exact h
  have key := bits_mul_dupFactor (bits x) hb
  apply bits_injective
  unfold dupFactor
  rw [bits_mul, bits_ofNat, bits_lor, bits_shl x 128 (by decide),
    BitVec.or_comm]
  exact key

/-- Word multiply on toNat: `change` avoids unfolding `UInt256.size`. -/
private theorem mul_toNat (a b : UInt256) :
    (UInt256.mul a b).toNat = (a.toNat * b.toNat) % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl

private theorem uint_mul_comm (a b : UInt256) :
    UInt256.mul a b = UInt256.mul b a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [mul_toNat, mul_toNat, Nat.mul_comm]

def loadMulTemplate (address : Nat) (dup : Operation.DupOp) : List Instr :=
  [push1 (UInt256.ofNat address), .op .MLOAD, .op (.Dup dup), .op .MUL]

theorem div_pair_lower :
    PairedDerivedStartup.pairWord / PairedDerivedStartup.lowerWord = dupFactor := by decide

def template : List Instr :=
  [.push ⟨4, by decide⟩ PairedDerivedStartup.lowerWord,
   dup1, push1 (UInt256.ofNat 128), .op .SHL,
   dup1, .op (.Dup ⟨2, by decide⟩), .op .OR,
   .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .DIV] ++
   loadMulTemplate 160 ⟨1, by decide⟩ ++
   loadMulTemplate 128 ⟨2, by decide⟩ ++
   loadMulTemplate 96 ⟨3, by decide⟩ ++
   loadMulTemplate 64 ⟨4, by decide⟩ ++
   loadMulTemplate 32 ⟨5, by decide⟩ ++
   [.push ⟨5, by decide⟩ PairedDerivedStartup.factorWord,
    .op (.Swap ⟨5, by decide⟩), .op .POP]

theorem template_length : template.length = 33 := by
  norm_num [template, loadMulTemplate]

theorem template_bytes : (template.map Instr.size).sum = 48 := by
  norm_num [template, loadMulTemplate, push1, dup1, Instr.size]

theorem lower_toNat :
    PairedDerivedStartup.lowerWord.toNat = 0xffffffff := by
  unfold PairedDerivedStartup.lowerWord
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have h1 : 0xffffffff < 2 ^ 32 := by decide
  have h2 : (2 ^ 32 : Nat) ≤ 2 ^ 256 :=
    Nat.pow_le_pow_right (by decide) (by decide)
  omega

theorem land_lower_canonical (x : UInt256) (h : x.toNat < 2 ^ 32) :
    UInt256.land PairedDerivedStartup.lowerWord x = x := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land, lower_toNat, Nat.and_comm,
    show 0xffffffff = 2 ^ 32 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

theorem mul_eq_packedHash (memory : ByteArray) (address : Nat)
    (h : (MachineState.readWord memory address).toNat < 2 ^ 32) :
    dupFactor * MachineState.readWord memory address =
      PairedDerivedStartup.packedHash memory address := by
  have hmul : UInt256.mul (MachineState.readWord memory address) dupFactor =
      PairedDerivedStartup.packedHash memory address := by
    unfold PairedDerivedStartup.packedHash
    rw [land_lower_canonical _ h]
    rw [mul_dupFactor _ h]
    exact Challenge.Ripemd160.Submission.Proofs.Bytecode.Word.lor_comm _ _
  have hstar : dupFactor * MachineState.readWord memory address =
      UInt256.mul dupFactor (MachineState.readWord memory address) := rfl
  rw [hstar, uint_mul_comm]
  exact hmul

theorem run_template (s : State) (pc : UInt256) (rho : List UInt256)
    (h32 : (MachineState.readWord s.memory 32).toNat < 2 ^ 32)
    (h64 : (MachineState.readWord s.memory 64).toNat < 2 ^ 32)
    (h96 : (MachineState.readWord s.memory 96).toNat < 2 ^ 32)
    (h128 : (MachineState.readWord s.memory 128).toNat < 2 ^ 32)
    (h160 : (MachineState.readWord s.memory 160).toNat < 2 ^ 32)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc template, stack := PairedDerivedStartup.resultStack s.memory rho} := by
  have hcap (n : Nat) (hn : n ≤ 11) : rho.length + n < 1024 := by omega
  have h0 : rho.length < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 160) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords :=
    PairedDerivedStartup.active_preserved s.activeWords address hactive haddress
  have hmul160 := mul_eq_packedHash s.memory 160 h160
  have hmul128 := mul_eq_packedHash s.memory 128 h128
  have hmul96 := mul_eq_packedHash s.memory 96 h96
  have hmul64 := mul_eq_packedHash s.memory 64 h64
  have hmul32 := mul_eq_packedHash s.memory 32 h32
  simp (discharger := omega) [template, loadMulTemplate, push1, dup1,
    PairedDerivedStartup.packedHash, PairedDerivedStartup.resultStack,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, hrun, hcap, h0, Nat.add_assoc,
    PairedDerivedStartup.upper_from_lower, PairedDerivedStartup.pair_from_lower,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat, div_pair_lower,
    List.exchange, hmul160, hmul128, hmul96, hmul64, hmul32]
  rfl

#print axioms template_length
#print axioms template_bytes
#print axioms land_lower_canonical
#print axioms mul_eq_packedHash
#print axioms run_template

open Challenge.EvmProof StackRoundTemplate

/-- Flat 33-op expansion of `template` for the advancement case split. -/
def frozenInstructions : List Instr :=
  [.push ⟨4, by decide⟩ PairedDerivedStartup.lowerWord,
   DenseScheduleTemplate.dup1, DenseScheduleTemplate.push1 (UInt256.ofNat 128), .op .SHL,
   DenseScheduleTemplate.dup1, .op (.Dup ⟨2, by decide⟩), .op .OR,
   .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .DIV,
   DenseScheduleTemplate.push1 (UInt256.ofNat 160), .op .MLOAD, .op (.Dup ⟨1, by decide⟩), .op .MUL,
   DenseScheduleTemplate.push1 (UInt256.ofNat 128), .op .MLOAD, .op (.Dup ⟨2, by decide⟩), .op .MUL,
   DenseScheduleTemplate.push1 (UInt256.ofNat 96), .op .MLOAD, .op (.Dup ⟨3, by decide⟩), .op .MUL,
   DenseScheduleTemplate.push1 (UInt256.ofNat 64), .op .MLOAD, .op (.Dup ⟨4, by decide⟩), .op .MUL,
   DenseScheduleTemplate.push1 (UInt256.ofNat 32), .op .MLOAD, .op (.Dup ⟨5, by decide⟩), .op .MUL,
   .push ⟨5, by decide⟩ PairedDerivedStartup.factorWord,
   .op (.Swap ⟨5, by decide⟩), .op .POP]

theorem template_eq_frozenInstructions : template = frozenInstructions := by
  rfl

theorem template_advances {instruction : Instr} {s t : State}
    (hmem : instruction ∈ template)
    (hrun : Stepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  rw [template_eq_frozenInstructions] at hmem
  simp only [frozenInstructions, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact RepeatedByteWord.runInstr_pc_div hrun
    | apply DenseScheduleLift.runInstr_pc_of_advances ?_ hrun
  all_goals first
    | exact Or.inl (Or.inl (StraightLine.push _ _))
    | exact Or.inl (Or.inl StraightLine.shl)
    | exact Or.inl (Or.inl StraightLine.or)
    | exact Or.inl (Or.inl StraightLine.mload)
    | exact Or.inl (Or.inl (StraightLine.dup _))
    | exact Or.inl (Or.inl (StraightLine.swap _))
    | exact Or.inl (Or.inl StraightLine.pop)
    | exact Or.inr (Or.inr rfl)

theorem runLocatedBlock_template {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork template)
    (s : State) (rho : List UInt256)
    (h32 : (MachineState.readWord s.memory 32).toNat < 2 ^ 32)
    (h64 : (MachineState.readWord s.memory 64).toNat < 2 ^ 32)
    (h96 : (MachineState.readWord s.memory 96).toNat < 2 ^ 32)
    (h128 : (MachineState.readWord s.memory 128).toNat < 2 ^ 32)
    (h160 : (MachineState.readWord s.memory 160).toNat < 2 ^ 32)
    (hstack : rho.length ≤ 1002)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat) :
    Stepper.runLocatedBlock site.path {s with pc := site.startPC, stack := rho} =
      some {s with pc := site.endPC, stack := PairedDerivedStartup.resultStack s.memory rho} := by
  have hend : site.endPC = pcAfter site.startPC template := by
    have h := StackRoundTrace.endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  have hraw : Stepper.runLocatedBlock site.path
      {s with pc := site.startPC, stack := rho} =
      runInstrSeq template {s with pc := site.startPC, stack := rho} := by
    apply runLocatedBlock_eq_runInstrSeq_site site _ rfl
    intro located hmem u v hresult
    apply template_advances ?_ hresult
    rw [← site.instruction_eq]
    exact List.mem_map_of_mem hmem
  rw [hraw]
  have h := run_template s site.startPC rho h32 h64 h96 h128 h160 hstack hrun hactive
  rw [← hend] at h
  exact h

def gasSteps_template {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork template)
    (s : State) (rho : List UInt256)
    (h32 : (MachineState.readWord s.memory 32).toNat < 2 ^ 32)
    (h64 : (MachineState.readWord s.memory 64).toNat < 2 ^ 32)
    (h96 : (MachineState.readWord s.memory 96).toNat < 2 ^ 32)
    (h128 : (MachineState.readWord s.memory 128).toNat < 2 ^ 32)
    (h160 : (MachineState.readWord s.memory 160).toNat < 2 ^ 32)
    (hstack : rho.length ≤ 1002)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := site.startPC, stack := rho}
      {s with pc := site.endPC, stack := PairedDerivedStartup.resultStack s.memory rho} := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_template site s rho h32 h64 h96 h128 h160 hstack hrun hactive
  · exact hrun
  · exact hnp

#print axioms template_eq_frozenInstructions
#print axioms template_advances
#print axioms runLocatedBlock_template
#print axioms gasSteps_template

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SCanonicalStartup
