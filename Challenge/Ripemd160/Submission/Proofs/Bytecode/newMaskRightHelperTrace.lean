import Challenge.Ripemd160.Submission.Proofs.Bytecode.newMaskHelperTemplates
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newMaskProjection
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskRightHelperTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskProjection
open Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskHelperTemplates
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadGapTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRound
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData

def rightLongEdit (i : Nat) (instruction : Instr) : Instr :=
  match i with
  | 14 => d 13
  | 16 => d 14
  | 22 => d 12
  | 25 => d 13
  | 43 => d 11
  | 45 => d 12
  | 51 => d 10
  | 54 => d 11
  | 71 => d 9
  | 73 => d 10
  | 79 => d 8
  | 82 => d 9
  | 100 => d 7
  | 102 => d 8
  | 108 => d 6
  | 111 => d 7
  | _ => instruction

def rightShortEdit (i : Nat) (instruction : Instr) : Instr :=
  match i with
  | 15 => d 13
  | 17 => d 14
  | 23 => d 12
  | 26 => d 13
  | 45 => d 11
  | 47 => d 12
  | 53 => d 10
  | 56 => d 11
  | 74 => d 9
  | 76 => d 10
  | 82 => d 8
  | 85 => d 9
  | 104 => d 7
  | 106 => d 8
  | 112 => d 6
  | 115 => d 7
  | _ => instruction

def rightZeroEdit (i : Nat) (instruction : Instr) : Instr :=
  match i with
  | 11 => d 13
  | 13 => d 14
  | 19 => d 12
  | 22 => d 13
  | 37 => d 11
  | 39 => d 12
  | 45 => d 10
  | 48 => d 11
  | 62 => d 9
  | 64 => d 10
  | 70 => d 8
  | 73 => d 9
  | 88 => d 7
  | 90 => d 8
  | 96 => d 6
  | 99 => d 7
  | _ => instruction

def rightLift (j : Nat) (constant : UInt256) : List Instr :=
  (quadBeforeJumpTemplate j constant).mapIdx (fun i instruction =>
    match j with
    | 0 => rightZeroEdit i instruction
    | 1 | 3 => rightShortEdit i instruction
    | 2 | 4 => rightLongEdit i instruction
    | _ => instruction)

theorem rightTemplate_eq_lift (group : Fin 5) :
    Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskHelperTemplates.rightTemplate
        group (rightConstant (16 * group.val)) =
      rightLift (4 - group.val) (rightConstant (16 * group.val)) := by
  fin_cases group <;> rfl

set_option linter.unusedSimpArgs false in
theorem right_relation
    (group : Fin 5)
    (s : State) (startPC p0 p1 p2 p3 returnPC : UInt256)
    (r0 r1 r2 r3 : Nat)
    (working : Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression.EvmWorking)
    (rho : List UInt256)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    :
    runInstrSeq
        (Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskHelperTemplates.rightTemplate
          group (rightConstant (16 * group.val)))
        (maskQuadHelperEntry s startPC p0 p1 p2 p3 returnPC
          (UInt256.ofNat (32 - r0)) (UInt256.ofNat (32 - r1))
          (UInt256.ofNat (32 - r2)) (UInt256.ofNat (32 - r3)) working rho) =
      Option.map (fun out => {out with
        pc := pcAfter startPC
          (Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskHelperTemplates.rightTemplate
            group (rightConstant (16 * group.val))),
        stack := out.stack.take 6 ++ [MaskProjection.mask] ++ out.stack.drop 6})
        (runInstrSeq (quadBeforeJumpTemplate (4 - group.val)
          (rightConstant (16 * group.val)))
          (quadHelperEntry s startPC p0 p1 p2 p3 returnPC
            r0 r1 r2 r3 working rho)) := by
  rw [rightTemplate_eq_lift group]
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
    [rightLift, rightLongEdit, rightShortEdit, rightZeroEdit,
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
     hadd, hcomm,
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
theorem group4_relation
    (s : State) (startPC p0 p1 p2 p3 returnPC : UInt256)
    (r0 r1 r2 r3 : Nat)
    (working : Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression.EvmWorking)
    (rho : List UInt256)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running) :
    runInstrSeq
        (Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskHelperTemplates.rightTemplate
          ⟨4, by decide⟩ (rightConstant (16 * 4)))
        (maskQuadHelperEntry s startPC p0 p1 p2 p3 returnPC
          (UInt256.ofNat (32 - r0)) (UInt256.ofNat (32 - r1))
          (UInt256.ofNat (32 - r2)) (UInt256.ofNat (32 - r3)) working rho) =
      Option.map (fun out => {out with
        pc := pcAfter startPC
          (Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskHelperTemplates.rightTemplate
            ⟨4, by decide⟩ (rightConstant (16 * 4))),
        stack := out.stack.take 6 ++ [MaskProjection.mask] ++ out.stack.drop 6})
        (runInstrSeq (quadBeforeJumpTemplate 0 (rightConstant (16 * 4)))
          (quadHelperEntry s startPC p0 p1 p2 p3 returnPC
            r0 r1 r2 r3 working rho)) := by
  simpa using right_relation ⟨4, by decide⟩ s startPC p0 p1 p2 p3 returnPC
    r0 r1 r2 r3 working rho hstack hrun

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_maskRight
    (group : Fin 5)
    (s : State) (startPC p0 p1 p2 p3 returnPC : UInt256)
    (r0 r1 r2 r3 : Nat)
    (working : Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression.EvmWorking)
    (rho : List UInt256)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hrot0 : r0 ≤ 32) (hrot1 : r1 ≤ 32)
    (hrot2 : r2 ≤ 32) (hrot3 : r3 ≤ 32) :
    runInstrSeq
        (Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskHelperTemplates.rightTemplate
          group (rightConstant (16 * group.val)))
        (maskQuadHelperEntry s startPC p0 p1 p2 p3 returnPC
          (UInt256.ofNat (32 - r0)) (UInt256.ofNat (32 - r1))
          (UInt256.ofNat (32 - r2)) (UInt256.ofNat (32 - r3)) working rho) =
      some (maskQuadAfterHelperBeforeJump s
        (pcAfter startPC
          (Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskHelperTemplates.rightTemplate
            group (rightConstant (16 * group.val))))
        returnPC (4 - group.val) working
        p0 p1 p2 p3 r0 r1 r2 r3
        (rightConstant (16 * group.val)) rho) := by
  have hzero : 4 - group.val = 0 →
      rightConstant (16 * group.val) = 0 := by
    fin_cases group <;> decide
  have hraw := QuadRoundTrace.runInstrSeq_quad (4 - group.val) (by omega)
    s startPC p0 p1 p2 p3 returnPC r0 r1 r2 r3 working
    (rightConstant (16 * group.val)) rho hzero (by omega) hrun
    hrot0 hrot1 hrot2 hrot3
  have hrelation := right_relation group s startPC p0 p1 p2 p3 returnPC
    r0 r1 r2 r3 working rho hstack hrun
  rw [hraw] at hrelation
  simpa [maskQuadAfterHelperBeforeJump, quadAfterHelperBeforeJump,
    pairAfterHelperBeforeJump, quadWorking, quadFirstState,
    quadFirstWorking, quadActiveWordsAfterUInt256_4, roundWords,
    QuadRoundTemplate.factor] using hrelation

end Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskRightHelperTrace
