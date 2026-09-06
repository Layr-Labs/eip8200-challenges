import Challenge.Ripemd160.Submission.Proofs.Bytecode.newMaskHelperTemplates
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newMaskProjection
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskHelperTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskProjection
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadGapTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRound
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

def shiftedFactor (r : Nat) : UInt256 :=
  UInt256.ofNat ((0x100000001 : Nat) <<< r)

theorem shiftedFactor_eq_shiftLeft (r : Nat)
    (hr0 : 0 < r) (hr32 : r < 32) :
    shiftedFactor r =
      UInt256.shiftLeft (UInt256.ofNat (0x100000001 : Nat))
        (UInt256.ofNat r) := by
  have hbound : (0x100000001 : Nat) * 2 ^ r < 2 ^ 256 := by
    have hpow : 2 ^ r ≤ 2 ^ 31 := by
      exact Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    calc
      (0x100000001 : Nat) * 2 ^ r ≤ 0x100000001 * 2 ^ 31 :=
        Nat.mul_le_mul_left _ hpow
      _ < 2 ^ 256 := by norm_num [← Nat.pow_add]
  unfold shiftedFactor
  symm
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by norm_num) (by omega) hbound]
  congr 1
  simp [Nat.shiftLeft_eq]

def maskLeft0Template (_constant : UInt256) : List Instr :=
  [op .JUMPDEST, op .MLOAD, d 10, d 12, op .XOR, d 13, op .XOR,
    op .ADD, w 0, w 8, op .ADD, d 13, op .AND, op .MUL,
    push1 (UInt256.ofNat 32), op .SHR, d 11, op .ADD, d 12, op .AND,
    w 8, d 13, op .MUL, push1 c22, op .SHR, w 0, op .MLOAD,
    d 9, d 9, op .XOR, d 2, op .XOR, op .ADD, w 0, w 10, op .ADD,
    d 11, op .AND, op .MUL, push1 (UInt256.ofNat 32), op .SHR,
    d 8, op .ADD, d 10, op .AND, w 5, d 11, op .MUL,
    push1 c22, op .SHR, w 7, w 0, op .MLOAD, d 6, d 8, op .XOR,
    d 9, op .XOR, op .ADD, op .ADD, d 9, op .AND, op .MUL,
    push1 (UInt256.ofNat 32), op .SHR, d 7, op .ADD, d 8, op .AND,
    w 4, d 9, op .MUL, push1 c22, op .SHR, w 0, op .MLOAD,
    d 5, d 5, op .XOR, d 2, op .XOR, op .ADD, w 0, w 6, op .ADD,
    d 7, op .AND, op .MUL, push1 (UInt256.ofNat 32), op .SHR,
    d 4, op .ADD, d 6, op .AND, w 1, d 7, op .MUL, push1 c22,
    op .SHR, w 3, w 0]

theorem maskLeft0_length (constant : UInt256) :
    (maskLeft0Template constant).length = 101 := by rfl

/-- Instruction edits preserve the old Boolean and addition order. -/
def leftLongEdit (i : Nat) (instruction : Instr) : Instr :=
  match i with
  | 14 => d 13
  | 18 => push1 (UInt256.ofNat 32)
  | 22 => d 12
  | 25 => d 13
  | 43 => d 11
  | 47 => push1 (UInt256.ofNat 32)
  | 51 => d 10
  | 54 => d 11
  | 71 => d 9
  | 75 => push1 (UInt256.ofNat 32)
  | 79 => d 8
  | 82 => d 9
  | 100 => d 7
  | 104 => push1 (UInt256.ofNat 32)
  | 108 => d 6
  | 111 => d 7
  | _ => instruction

def leftShortEdit (i : Nat) (instruction : Instr) : Instr :=
  match i with
  | 15 => d 13
  | 19 => push1 (UInt256.ofNat 32)
  | 23 => d 12
  | 26 => d 13
  | 45 => d 11
  | 49 => push1 (UInt256.ofNat 32)
  | 53 => d 10
  | 56 => d 11
  | 74 => d 9
  | 78 => push1 (UInt256.ofNat 32)
  | 82 => d 8
  | 85 => d 9
  | 104 => d 7
  | 108 => push1 (UInt256.ofNat 32)
  | 112 => d 6
  | 115 => d 7
  | _ => instruction

def leftZeroEdit (i : Nat) (instruction : Instr) : Instr :=
  match i with
  | 11 => d 13
  | 15 => push1 (UInt256.ofNat 32)
  | 19 => d 12
  | 22 => d 13
  | 37 => d 11
  | 41 => push1 (UInt256.ofNat 32)
  | 45 => d 10
  | 48 => d 11
  | 62 => d 9
  | 66 => push1 (UInt256.ofNat 32)
  | 70 => d 8
  | 73 => d 9
  | 88 => d 7
  | 92 => push1 (UInt256.ofNat 32)
  | 96 => d 6
  | 99 => d 7
  | _ => instruction

def eraseAt (i : Nat) (xs : List Instr) : List Instr :=
  xs.take i ++ xs.drop (i + 1)

def leftLift (j : Nat) (constant : UInt256) : List Instr :=
  let edited := (quadBeforeJumpTemplate j constant).mapIdx (fun i instruction =>
    match j with
    | 0 => leftZeroEdit i instruction
    | 1 | 3 => leftShortEdit i instruction
    | 2 | 4 => leftLongEdit i instruction
    | _ => instruction)
  match j with
  | 0 => eraseAt 13 (eraseAt 39 (eraseAt 64 (eraseAt 90 edited)))
  | 1 | 3 => eraseAt 17 (eraseAt 47 (eraseAt 76 (eraseAt 106 edited)))
  | 2 | 4 => eraseAt 16 (eraseAt 45 (eraseAt 73 (eraseAt 102 edited)))
  | _ => edited

theorem leftTemplate_eq_lift (group : Fin 5) :
    MaskHelperTemplates.leftTemplate group (leftConstant (16 * group.val)) =
      leftLift group.val (leftConstant (16 * group.val)) := by
  fin_cases group <;> rfl

theorem maskLeft0Template_eq_leftTemplate (constant : UInt256) :
    maskLeft0Template constant = MaskHelperTemplates.leftTemplate ⟨0, by decide⟩ 0 := by
  rfl

set_option linter.unusedSimpArgs false in
/-- Insert the cached mask and convert each variable rotation to the old form. -/
theorem left_relation
    (group : Fin 5)
    (s : State) (startPC p0 p1 p2 p3 returnPC : UInt256)
    (r0 r1 r2 r3 : Nat)
    (working : Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression.EvmWorking)
    (rho : List UInt256)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hrot0 : 0 < r0) (hrot0' : r0 < 32)
    (hrot1 : 0 < r1) (hrot1' : r1 < 32)
    (hrot2 : 0 < r2) (hrot2' : r2 < 32)
    (hrot3 : 0 < r3) (hrot3' : r3 < 32) :
    runInstrSeq
        (Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskHelperTemplates.leftTemplate
          group (leftConstant (16 * group.val)))
        (maskQuadHelperEntry s startPC p0 p1 p2 p3 returnPC
          (shiftedFactor r0) (shiftedFactor r1)
          (shiftedFactor r2) (shiftedFactor r3) working rho) =
      Option.map (fun out => {out with
        pc := pcAfter startPC
          (Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskHelperTemplates.leftTemplate
            group (leftConstant (16 * group.val))),
        stack := out.stack.take 6 ++ [MaskProjection.mask] ++ out.stack.drop 6})
        (runInstrSeq (quadBeforeJumpTemplate group.val
          (leftConstant (16 * group.val)))
          (quadHelperEntry s startPC p0 p1 p2 p3 returnPC
            r0 r1 r2 r3 working rho)) := by
  rw [leftTemplate_eq_lift group]
  have hrot (u : UInt256) (r : Nat) (hr0 : 0 < r) (hr32 : r < 32) :
      UInt256.shiftRight
        (UInt256.land (UInt256.ofNat 0xffffffff) u * shiftedFactor r)
        (UInt256.ofNat 32) =
      UInt256.shiftRight
        (UInt256.ofNat 0x100000001 * UInt256.land (UInt256.ofNat 0xffffffff) u)
        (UInt256.ofNat (32 - r)) := by
    rw [shiftedFactor_eq_shiftLeft r hr0 hr32]
    exact (MaskProjection.left_factor_shift_eq _ r
      (SharedRoundTrace.mask_land_toNat_lt u) hr0 hr32).symm
  have hrotMasked0 (u : UInt256) := hrot u r0 hrot0 hrot0'
  have hrotMasked1 (u : UInt256) := hrot u r1 hrot1 hrot1'
  have hrotMasked2 (u : UInt256) := hrot u r2 hrot2 hrot2'
  have hrotMasked3 (u : UInt256) := hrot u r3 hrot3 hrot3'
  have activeWordsAfter_lt (curr off : Nat)
      (hcurr : curr < UInt256.size) (hoff : off < UInt256.size) :
      MachineState.activeWordsAfter curr off 32 < UInt256.size := by
    unfold MachineState.activeWordsAfter
    split
    · exact hcurr
    · dsimp only
      rw [Nat.max_lt]
      constructor
      · exact hcurr
      · simp only [UInt256.size]
        have hoff' : off < 2 ^ 256 := by
          simpa only [UInt256.size] using hoff
        have hdiv : (off + 32 - 1) / 32 < 2 ^ 256 - 1 := by
          apply (Nat.div_lt_iff_lt_mul (by norm_num)).2
          calc
            off + 32 - 1 ≤ (2 ^ 256 - 1) + 31 := by omega
            _ < (2 ^ 256 - 1) * 32 := by norm_num
        omega
  have hactive0 :
      MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32 <
        UInt256.size :=
    activeWordsAfter_lt s.activeWords.toNat p0.toNat
      s.activeWords.val.isLt p0.val.isLt
  have hactive0mod := Nat.mod_eq_of_lt hactive0
  have hactive0mod' :
      MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32 %
          (2 ^ 256) =
        MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32 := by
    simpa only [UInt256.size] using hactive0mod
  have hactive1 :
      MachineState.activeWordsAfter
          (MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32)
          p1.toNat 32 < UInt256.size :=
    activeWordsAfter_lt
      (MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32)
      p1.toNat hactive0 p1.val.isLt
  have hactive1mod := Nat.mod_eq_of_lt hactive1
  have hactive1mod' :
      MachineState.activeWordsAfter
          (MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32)
          p1.toNat 32 % (2 ^ 256) =
        MachineState.activeWordsAfter
          (MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32)
          p1.toNat 32 := by
    simpa only [UInt256.size] using hactive1mod
  have hactive2 :
      MachineState.activeWordsAfter
          (MachineState.activeWordsAfter
            (MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32)
            p1.toNat 32)
          p2.toNat 32 < UInt256.size :=
    activeWordsAfter_lt
      (MachineState.activeWordsAfter
        (MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32)
        p1.toNat 32)
      p2.toNat hactive1 p2.val.isLt
  have hactive2mod := Nat.mod_eq_of_lt hactive2
  have hactive2mod' :
      MachineState.activeWordsAfter
          (MachineState.activeWordsAfter
            (MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32)
            p1.toNat 32)
          p2.toNat 32 % (2 ^ 256) =
        MachineState.activeWordsAfter
          (MachineState.activeWordsAfter
            (MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32)
            p1.toNat 32)
          p2.toNat 32 := by
    simpa only [UInt256.size] using hactive2mod
  have hactiveEq :
      UInt256.ofNat
          (MachineState.activeWordsAfter
            (MachineState.activeWordsAfter
              (MachineState.activeWordsAfter
                (MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32 %
                  UInt256.size) p1.toNat 32 % UInt256.size)
                p2.toNat 32 % UInt256.size) p3.toNat 32) =
        UInt256.ofNat
          (MachineState.activeWordsAfter
            (MachineState.activeWordsAfter
              (MachineState.activeWordsAfter
                (MachineState.activeWordsAfter s.activeWords.toNat p0.toNat 32)
                  p1.toNat 32 % UInt256.size)
                p2.toNat 32) p3.toNat 32) := by
    rw [hactive0mod, hactive1mod, hactive2mod]
  have hcap (m : Nat) (hm : m ≤ 18) : rho.length + m < 1024 := by
    omega
  have hadd (u v : UInt256) : u.add v = u + v := by rfl
  have hcomm (u v : UInt256) : u.add v = v.add u := by
    exact word_add_comm u v
  have word_add_assoc (u v w : UInt256) :
      (u + v) + w = u + (v + w) := by
    apply word_ext
    change ((u.val + v.val) + w.val).val =
      (u.val + (v.val + w.val)).val
    simp [Fin.add_def, Nat.add_assoc]
  have word_add_ofNat_assoc (u : UInt256) (a b : Nat) :
      (u + UInt256.ofNat a) + UInt256.ofNat b =
        u + UInt256.ofNat (a + b) := by
    rw [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  have add_ofNat_assoc_hAdd (u : UInt256) (a b : Nat) :
      (UInt256.add u (UInt256.ofNat a)) + UInt256.ofNat b =
        u + UInt256.ofNat (a + b) := by
    change (u + UInt256.ofNat a) + UInt256.ofNat b =
      u + UInt256.ofNat (a + b)
    exact word_add_ofNat_assoc u a b
  have add_ofNat_assoc_add (u : UInt256) (a b : Nat) :
      UInt256.add (u + UInt256.ofNat a) (UInt256.ofNat b) =
        u + UInt256.ofNat (a + b) := by
    change (u + UInt256.ofNat a) + UInt256.ofNat b =
      u + UInt256.ofNat (a + b)
    exact word_add_ofNat_assoc u a b
  have add_assoc_explicit (u v w : UInt256) :
      UInt256.add (UInt256.add u v) w =
        UInt256.add u (UInt256.add v w) := by
    change (u + v) + w = u + (v + w)
    exact word_add_assoc u v w
  have add_assoc_explicit_hAdd (u v w : UInt256) :
      (UInt256.add u v) + w = u + (v + w) := by
    change (u + v) + w = u + (v + w)
    exact word_add_assoc u v w
  have add_assoc_hAdd_explicit (u v w : UInt256) :
      UInt256.add (u + v) w = u + (v + w) := by
    change (u + v) + w = u + (v + w)
    exact word_add_assoc u v w
  fin_cases group <;>
    simp (config := { maxSteps := 5000000 })
    [leftLift, eraseAt, leftLongEdit, leftShortEdit, leftZeroEdit,
     quadBeforeJumpTemplate, oldQuadBeforeJumpTemplate, firstFTemplate,
     cachedTailFTemplate, firstBoolean, secondBoolean, d, w,
     cachedQrot10, cachedCfold9, cachedQrot8, cachedCfold7,
     cachedDup10, cachedDup9, cachedDup8, cachedDup7,
     pairFirstBooleanOps,
     pairSecondBooleanOps,
     pairSwap5, pairSwap7,
     pairDup7, pairDup8,
     pairDup9, pairDup10,
     quadHelperEntry, maskQuadHelperEntry, roundWords,
     op, push1, push4, dup1, dup2, dup3, dup4, dup5, dup6,
     swap1, swap2, swap3, swap4,
     runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter,
     List.exchange, hrun, hcap, UInt256.succ, Instr.size,
     Instr.size_op, Instr.size_push, State.activeWordsAfterUInt256,
     pairHelperEntry,
     State.activeWordsAfterUInt256_2,
     MaskProjection.mask, StackRoundTemplate.mask, QuadRoundTemplate.factor,
     hadd, hcomm, hrotMasked0, hrotMasked1, hrotMasked2, hrotMasked3,
     hactive0, hactive0mod, hactive1, hactive1mod, hactive2, hactive2mod,
     hactive0mod', hactive1mod', hactive2mod',
     UInt256.size,
     Challenge.EvmProof.Word.word_add_comm,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat, Nat.add_assoc,
     word_add_assoc, word_add_ofNat_assoc,
     add_assoc_explicit, add_assoc_explicit_hAdd,
     add_assoc_hAdd_explicit]

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_maskLeft
    (group : Fin 5)
    (s : State) (startPC p0 p1 p2 p3 returnPC : UInt256)
    (r0 r1 r2 r3 : Nat)
    (working : Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression.EvmWorking)
    (rho : List UInt256)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hrot0 : 0 < r0) (hrot0' : r0 < 32)
    (hrot1 : 0 < r1) (hrot1' : r1 < 32)
    (hrot2 : 0 < r2) (hrot2' : r2 < 32)
    (hrot3 : 0 < r3) (hrot3' : r3 < 32) :
    runInstrSeq
        (Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskHelperTemplates.leftTemplate
          group (leftConstant (16 * group.val)))
        (maskQuadHelperEntry s startPC p0 p1 p2 p3 returnPC
          (shiftedFactor r0) (shiftedFactor r1)
          (shiftedFactor r2) (shiftedFactor r3) working rho) =
      some (maskQuadAfterHelperBeforeJump s
        (pcAfter startPC
          (Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskHelperTemplates.leftTemplate
            group (leftConstant (16 * group.val))))
        returnPC group.val working
        p0 p1 p2 p3 r0 r1 r2 r3
        (leftConstant (16 * group.val)) rho) := by
  have hzero : group.val = 0 →
      leftConstant (16 * group.val) = 0 := by
    fin_cases group <;> decide
  have hraw := QuadRoundTrace.runInstrSeq_quad group.val (by omega)
    s startPC p0 p1 p2 p3 returnPC r0 r1 r2 r3 working
    (leftConstant (16 * group.val)) rho hzero (by omega) hrun
    (by omega) (by omega) (by omega) (by omega)
  have hrelation := left_relation group s startPC p0 p1 p2 p3 returnPC
    r0 r1 r2 r3 working rho hstack hrun
    hrot0 hrot0' hrot1 hrot1' hrot2 hrot2' hrot3 hrot3'
  rw [hraw] at hrelation
  simpa [maskQuadAfterHelperBeforeJump, quadAfterHelperBeforeJump,
    pairAfterHelperBeforeJump, quadWorking, quadFirstState,
    quadFirstWorking, quadActiveWordsAfterUInt256_4, roundWords,
    QuadRoundTemplate.factor] using hrelation

theorem runInstrSeq_maskLeft0
    (s : State) (startPC p0 p1 p2 p3 returnPC : UInt256)
    (r0 r1 r2 r3 : Nat) (working : Compression.EvmWorking)
    (rho : List UInt256)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hrot0 : 0 < r0) (hrot0' : r0 < 32)
    (hrot1 : 0 < r1) (hrot1' : r1 < 32)
    (hrot2 : 0 < r2) (hrot2' : r2 < 32)
    (hrot3 : 0 < r3) (hrot3' : r3 < 32) :
    runInstrSeq (maskLeft0Template 0)
      (maskQuadHelperEntry s startPC p0 p1 p2 p3 returnPC
        (shiftedFactor r0) (shiftedFactor r1) (shiftedFactor r2)
        (shiftedFactor r3) working rho) =
      some (maskQuadAfterHelperBeforeJump s
        (pcAfter startPC (maskLeft0Template 0)) returnPC 0 working
        p0 p1 p2 p3 r0 r1 r2 r3 0 rho) := by
  have h := runInstrSeq_maskLeft ⟨0, by decide⟩
    s startPC p0 p1 p2 p3 returnPC r0 r1 r2 r3 working rho hstack hrun
    hrot0 hrot0' hrot1 hrot1' hrot2 hrot2' hrot3 hrot3'
  have hconstant : leftConstant (16 * (⟨0, by decide⟩ : Fin 5).val) = 0 := by rfl
  rw [hconstant] at h
  rw [maskLeft0Template_eq_leftTemplate]
  exact h

end Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskHelperTrace
