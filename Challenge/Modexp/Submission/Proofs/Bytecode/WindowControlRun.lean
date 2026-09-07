import Challenge.Modexp.Submission.Proofs.Bytecode.WindowControlDefs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowControlTrace

open EvmSemantics EvmSemantics.EVM
open WindowControlDefs

private def framed (template : State) (pc : Nat) (stack : List UInt256) : State :=
  { template with pc := UInt256.ofNat pc, stack := stack }

private def guardValue (b e m : UInt256) : UInt256 :=
  UInt256.lor (UInt256.xor m (UInt256.ofNat 32))
    (UInt256.lor (UInt256.xor e (UInt256.ofNat 32))
      (UInt256.xor b (UInt256.ofNat 32)))

private theorem xor_comm (a b : UInt256) : UInt256.xor a b = UInt256.xor b a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val ^^^ b.val).val = (b.val ^^^ a.val).val
  rw [Fin.xor_val, Fin.xor_val, Nat.xor_comm]

set_option linter.unusedSimpArgs false in
private theorem run_guard_generic (template : State) (b e m : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hrun : template.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock guardPath
      (framed template 3000 (b :: e :: m :: rest)) =
    some (framed template 3016
      (UInt256.isZero (guardValue b e m) :: b :: e :: m :: rest)) := by
  have hcap (n : Nat) (hn : n ≤ 6) : rest.length + n < 1024 := by omega
  simp (disch := omega) [guardPath, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    framed, guardValue, hrun, hcap, routePCs, xor_comm,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Nat.add_assoc,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
private theorem run_branch_true_generic (template : State) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) (hrun : template.halt = .Running)
    (hcode : template.executionEnv.code = submissionBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock branchPath
      (framed template 3016 (UInt256.ofNat 1 :: rest)) =
    some (framed template 5372 rest) := by
  have hcap (n : Nat) (hn : n ≤ 3) : rest.length + n < 1024 := by omega
  simp (disch := omega) [branchPath, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    framed, hrun, hcode, hcap, routePCs, jump5372, UInt256.isTrue, Nat.add_assoc,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
private theorem run_branch_false_generic (template : State) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) (hrun : template.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock branchPath
      (framed template 3016 (UInt256.ofNat 0 :: rest)) =
    some (framed template 3020 rest) := by
  have hcap (n : Nat) (hn : n ≤ 3) : rest.length + n < 1024 := by omega
  simp (disch := omega) [branchPath, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    framed, hrun, hcap, routePCs, UInt256.isTrue, Nat.add_assoc,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
private theorem run_miss_generic (template : State) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) (hrun : template.halt = .Running)
    (hcode : template.executionEnv.code = submissionBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock missPath
      (framed template 3020 rest) = some (framed template 517 rest) := by
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  simp (disch := omega) [missPath, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    framed, hrun, hcode, hcap0, hcap1, routePCs, jump517, Nat.add_assoc,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem diff_isZero_one (input : ByteArray)
    (h : WindowGuardLogic.guardDiff input = 0) :
    UInt256.isZero (WindowGuardLogic.guardDiff input) = UInt256.ofNat 1 := by
  rw [h]
  decide

theorem diff_isZero_zero (input : ByteArray)
    (h : WindowGuardLogic.guardDiff input ≠ 0) :
    UInt256.isZero (WindowGuardLogic.guardDiff input) = UInt256.ofNat 0 := by
  have hnat : (WindowGuardLogic.guardDiff input).toNat ≠ 0 := by
    intro hz
    apply h
    apply Challenge.EvmProof.Word.word_ext
    rw [show (0 : UInt256).toNat = 0 by decide]
    exact hz
  simp [UInt256.isZero, hnat]

theorem word_isZero_zero {word : UInt256} (hword : word ≠ 0) :
    UInt256.isZero word = UInt256.ofNat 0 := by
  have hnat : word.toNat ≠ 0 := by
    intro hz
    apply hword
    apply Challenge.EvmProof.Word.word_ext
    rw [show (0 : UInt256).toNat = 0 by decide]
    exact hz
  simp [UInt256.isZero, hnat]

theorem run_guard (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock guardPath
      (Dispatch.wordRouteEntryState input) = some (conditionState input) := by
  have h := run_guard_generic (Dispatch.wordEntryState input)
    (UInt256.ofNat (baseSize input)) (UInt256.ofNat (exponentSize input))
    (UInt256.ofNat (modulusSize input)) ((routeStack input).drop 3)
    (by simp [routeStack]) rfl
  simpa only [framed, guardValue, Dispatch.wordRouteEntryState, conditionState,
    WindowGuardLogic.guardDiff, routeStack, Dispatch.wordEntryState,
    List.drop_succ_cons, List.drop_zero, Nat.add_assoc] using h

theorem run_branch_match (input : ByteArray)
    (hmatch : WindowGuardLogic.Matches input) :
    Challenge.EvmProof.Stepper.runLocatedBlock branchPath
      (conditionState input) = some (baseZeroEntryState input) := by
  have hiszero := diff_isZero_one input
    ((WindowGuardLogic.guardDiff_eq_zero_iff input).2 hmatch)
  have h := run_branch_true_generic (Dispatch.wordEntryState input)
    (routeStack input) (by simp [routeStack]) rfl rfl
  simpa only [framed, conditionState, baseZeroEntryState, hiszero,
    routeStack_eq_entry] using h

set_option linter.unusedSimpArgs false in
theorem run_baseZeroGuard_hit (input : ByteArray)
    (hbase : shortcutBaseWord input = 0)
    (hexponent : shortcutExponentWord input ≠ 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseZeroGuardPath
      (baseZeroEntryState input) = some (baseZeroHandlerState input) := by
  have hcap (n : Nat) (hn : n ≤ 16) :
      (routeStack input).length + n < 1024 := by omega
  have hzero : UInt256.isZero (shortcutExponentWord input) =
      UInt256.ofNat 0 := word_isZero_zero hexponent
  simp (disch := omega) [baseZeroGuardPath, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    baseZeroEntryState, baseZeroHandlerState, shortcutBaseWord,
    shortcutExponentWord, hbase, hexponent, hzero, routeStack, jump5391,
    baseZeroPCs, Dispatch.wordEntryState, hcap,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Nat.add_assoc, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_baseZeroGuard_miss (input : ByteArray)
    (hmiss : ¬ baseZeroMatches input) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseZeroGuardPath
      (baseZeroEntryState input) = some (hitState input) := by
  by_cases hbase : shortcutBaseWord input = 0
  · have hexponent : shortcutExponentWord input = 0 := by
      by_contra hne
      exact hmiss ⟨hbase, hne⟩
    have hcap (n : Nat) (hn : n ≤ 16) :
        (routeStack input).length + n < 1024 := by omega
    have hzero : UInt256.isZero (shortcutExponentWord input) =
        UInt256.ofNat 0 := by
      apply word_isZero_zero
      exact hexponent
    simp (disch := omega) [baseZeroGuardPath, Main.opAt, Main.pushAt, Main.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseZeroEntryState, hitState, shortcutBaseWord,
      shortcutExponentWord, hbase, hexponent, hzero, routeStack, jump3024,
      baseZeroPCs, Dispatch.wordEntryState, hcap,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      Nat.add_assoc, Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  · have hcap (n : Nat) (hn : n ≤ 16) :
        (routeStack input).length + n < 1024 := by omega
    have hzero : UInt256.isZero (shortcutBaseWord input) =
        UInt256.ofNat 0 := word_isZero_zero hbase
    simp (disch := omega) [baseZeroGuardPath, Main.opAt, Main.pushAt, Main.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseZeroEntryState, hitState, shortcutBaseWord,
      shortcutExponentWord, hbase, hzero, routeStack, jump3024,
      baseZeroPCs, Dispatch.wordEntryState, hcap,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      Nat.add_assoc, Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_baseZeroHandler (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseZeroHandlerPath
      (baseZeroHandlerState input) = some (baseZeroReturnState input) := by
  have hcap (n : Nat) (hn : n ≤ 6) :
      (routeStack input).length + n < 1024 := by omega
  simp (disch := omega) [baseZeroHandlerPath, Main.opAt, Main.pushAt,
    Main.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, baseZeroHandlerState,
    baseZeroReturnState, routeStack, jump3563, baseZeroPCs,
    Dispatch.wordEntryState, hcap,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Nat.add_assoc, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]
theorem run_branch_miss (input : ByteArray)
    (hmatch : ¬ WindowGuardLogic.Matches input) :
    Challenge.EvmProof.Stepper.runLocatedBlock branchPath
      (conditionState input) = some (missState input) := by
  have hdiff : WindowGuardLogic.guardDiff input ≠ 0 := by
    intro hz
    exact hmatch ((WindowGuardLogic.guardDiff_eq_zero_iff input).1 hz)
  have hiszero := diff_isZero_zero input hdiff
  have h := run_branch_false_generic (Dispatch.wordEntryState input)
    (routeStack input) (by simp [routeStack]) rfl
  simpa only [framed, conditionState, missState, hiszero, routeStack_eq_entry] using h

theorem run_miss (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock missPath (missState input) =
      some (Dispatch.wordEntryState input) := by
  have h := run_miss_generic (Dispatch.wordEntryState input)
    (routeStack input) (by simp [routeStack]) rfl rfl
  simpa only [framed, missState, routeStack_eq_entry, Dispatch.wordEntryState] using h

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowControlTrace
