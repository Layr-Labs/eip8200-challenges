import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundTrace

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# H12 shared round raw traces for the negated Boolean forms

This file proves the generic evaluator traces for helper groups `2` and `4`.
The proof stops immediately before the helper's final `JUMP`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedNegatedRoundTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRound
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedRoundTrace

private theorem word_add_assoc (u v w : UInt256) :
    (u + v) + w = u + (v + w) := by
  apply word_ext
  change ((u.val + v.val) + w.val).val =
    (u.val + (v.val + w.val)).val
  simp [Fin.add_def, Nat.add_assoc]

private theorem maskedRotateAdd (q e r r' : UInt256) :
    UInt256.land mask
        (UInt256.add
          (((mask.land q).shiftLeft r).lor
            ((mask.land q).shiftRight r')) e) =
      UInt256.land
        (UInt256.add
          (((q.land mask).shiftLeft r).lor
            ((q.land mask).shiftRight r')) e) mask := by
  rw [Word.land_comm mask q]
  exact Word.land_comm _ _

/-! ## Direct group 2 evaluator trace -/

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_f2 (s : State) (startPC xAddress returnPC : UInt256)
    (rotation : Nat) (working : Compression.EvmWorking)
    (constant : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1013)
    (hrun : s.halt = .Running) (hrot : rotation ≤ 32) :
    runInstrSeq
        (helperBeforeJumpTemplate 2 xAddress rotation constant)
        (helperEntry s startPC xAddress rotation returnPC working rest) =
      some (afterHelperBeforeJump s
        (pcAfter startPC (helperBeforeJumpTemplate 2 xAddress rotation constant))
        returnPC 2 working xAddress rotation constant rest) := by
  have hcap (m : Nat) (hm : m ≤ 11) : rest.length + m < 1024 := by
    omega
  have hswap1 (u v : UInt256) (rho : List UInt256) :
      (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho
  have hswap2 (u v w : UInt256) (rho : List UInt256) :
      (u :: v :: w :: rho).exchange 0 2 =
        some (w :: v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u w [v] rho
  have hswap3 (u v w z : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: rho).exchange 0 3 =
        some (z :: v :: w :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u z [v, w] rho
  have hswap4 (u v w z q : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: q :: rho).exchange 0 4 =
        some (q :: v :: w :: z :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u q [v, w, z] rho
  have hswap5 (u v w z q r : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: q :: r :: rho).exchange 0 5 =
        some (r :: v :: w :: z :: q :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u r [v, w, z, q] rho
  have hadd (u v : UInt256) : u + v = u.add v := by
    rfl
  have hcomm (u v : UInt256) : u.add v = v.add u := by
    exact word_add_comm u v
  have hmask : mask.land (working.d.xor
      (working.b.lor working.c.lnot)) =
      (working.d.xor (working.b.lor working.c.lnot)).land mask := by
    exact Word.land_comm mask (working.d.xor (working.b.lor working.c.lnot))
  have hbase : constant.add
      (working.a.add ((MachineState.readWord s.memory xAddress.toNat).add
        ((working.d.xor (working.b.lor working.c.lnot)).land mask))) =
      constant.add ((working.a.add ((working.d.xor (working.b.lor working.c.lnot)).land mask)).add
        (MachineState.readWord s.memory xAddress.toNat)) := by
    apply congrArg (fun z : UInt256 => constant.add z)
    rw [hcomm (MachineState.readWord s.memory xAddress.toNat)
      ((working.d.xor (working.b.lor working.c.lnot)).land mask)]
    exact (word_add_assoc working.a ((working.d.xor (working.b.lor working.c.lnot)).land mask)
      (MachineState.readWord s.memory xAddress.toNat)).symm
  have hsub : (UInt256.ofNat 32) - (UInt256.ofNat rotation) =
      UInt256.ofNat (32 - rotation) := by
    exact ofNat_sub_ofNat hrot (by norm_num)
  simp only [mask] at hmask hbase
  simp (config := { maxSteps := 3000000 })
    [helperBeforeJumpTemplate, booleanOps, op, push1, push4, dup1, dup2,
      dup3, dup4, dup5, dup6, dup7, dup8, swap1, swap2, swap3, swap4, swap5,
      mask, c10, c22, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
      helperEntry, afterHelperBeforeJump, roundWords,
      pcAfter, StackRound.stackRound, StackRound.stackF,
      StackRound.stackSum, StackRound.stackRawRot, StackRound.stackC10,
      Word.mask32, List.exchange, hrun, hcap, hswap1, hswap2, hswap3,
      hswap4, hswap5, UInt256.succ, Instr.size, Instr.size_push,
      Instr.size_op, Nat.add_assoc, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat, Word.land_comm,
      Word.lor_comm, BooleanSelect.xor_comm,
      State.activeWordsAfterUInt256, hadd, hcomm, hsub]
  constructor
  · rw [hcomm working.e, hmask, hbase, hcomm working.e]
    exact maskedRotateAdd _ _ _ _
  · exact Word.land_comm _ _

/-! ## Direct group 4 evaluator trace -/

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_f4 (s : State) (startPC xAddress returnPC : UInt256)
    (rotation : Nat) (working : Compression.EvmWorking)
    (constant : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1013)
    (hrun : s.halt = .Running) (hrot : rotation ≤ 32) :
    runInstrSeq
        (helperBeforeJumpTemplate 4 xAddress rotation constant)
        (helperEntry s startPC xAddress rotation returnPC working rest) =
      some (afterHelperBeforeJump s
        (pcAfter startPC (helperBeforeJumpTemplate 4 xAddress rotation constant))
        returnPC 4 working xAddress rotation constant rest) := by
  have hcap (m : Nat) (hm : m ≤ 11) : rest.length + m < 1024 := by
    omega
  have hswap1 (u v : UInt256) (rho : List UInt256) :
      (u :: v :: rho).exchange 0 1 = some (v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) rho
  have hswap2 (u v w : UInt256) (rho : List UInt256) :
      (u :: v :: w :: rho).exchange 0 2 =
        some (w :: v :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u w [v] rho
  have hswap3 (u v w z : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: rho).exchange 0 3 =
        some (z :: v :: w :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u z [v, w] rho
  have hswap4 (u v w z q : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: q :: rho).exchange 0 4 =
        some (q :: v :: w :: z :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u q [v, w, z] rho
  have hswap5 (u v w z q r : UInt256) (rho : List UInt256) :
      (u :: v :: w :: z :: q :: r :: rho).exchange 0 5 =
        some (r :: v :: w :: z :: q :: u :: rho) := by
    simpa using YulEvmCompiler.exchange_swap u r [v, w, z, q] rho
  have hadd (u v : UInt256) : u + v = u.add v := by
    rfl
  have hcomm (u v : UInt256) : u.add v = v.add u := by
    exact word_add_comm u v
  have hmask : mask.land (working.b.xor
      (working.c.lor working.d.lnot)) =
      (working.b.xor (working.c.lor working.d.lnot)).land mask := by
    exact Word.land_comm mask (working.b.xor (working.c.lor working.d.lnot))
  have hbase : constant.add
      (working.a.add ((MachineState.readWord s.memory xAddress.toNat).add
        ((working.b.xor (working.c.lor working.d.lnot)).land mask))) =
      constant.add ((working.a.add ((working.b.xor (working.c.lor working.d.lnot)).land mask)).add
        (MachineState.readWord s.memory xAddress.toNat)) := by
    apply congrArg (fun z : UInt256 => constant.add z)
    rw [hcomm (MachineState.readWord s.memory xAddress.toNat)
      ((working.b.xor (working.c.lor working.d.lnot)).land mask)]
    exact (word_add_assoc working.a ((working.b.xor (working.c.lor working.d.lnot)).land mask)
      (MachineState.readWord s.memory xAddress.toNat)).symm
  have hsub : (UInt256.ofNat 32) - (UInt256.ofNat rotation) =
      UInt256.ofNat (32 - rotation) := by
    exact ofNat_sub_ofNat hrot (by norm_num)
  simp only [mask] at hmask hbase
  simp (config := { maxSteps := 3000000 })
    [helperBeforeJumpTemplate, booleanOps, op, push1, push4, dup1, dup2,
      dup3, dup4, dup5, dup6, dup7, dup8, swap1, swap2, swap3, swap4, swap5,
      mask, c10, c22, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
      helperEntry, afterHelperBeforeJump, roundWords,
      pcAfter, StackRound.stackRound, StackRound.stackF,
      StackRound.stackSum, StackRound.stackRawRot, StackRound.stackC10,
      Word.mask32, List.exchange, hrun, hcap, hswap1, hswap2, hswap3,
      hswap4, hswap5, UInt256.succ, Instr.size, Instr.size_push,
      Instr.size_op, Nat.add_assoc, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat, Word.land_comm,
      Word.lor_comm, BooleanSelect.xor_comm,
      State.activeWordsAfterUInt256, hadd, hcomm, hsub]
  constructor
  · rw [hcomm working.e, hmask, hbase, hcomm working.e]
    exact maskedRotateAdd _ _ _ _
  · exact Word.land_comm _ _

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedNegatedRoundTrace
