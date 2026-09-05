import Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryReduceBlock

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof

/-- Entry to the old subtract loop, with an explicit incoming high word. -/
def reduceEntry (s : State) (dst modulus high : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 174
           stack := [0, 0, high, 0, dst, 0, 0, modulus,
             UInt256.ofNat count, returnDest] ++ rest }

/-- Subtraction starts from INITIAL memory, with no assumed add phase. -/
def rawSubtractLoop (s : State) (dst modulus high : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let progress := BigHelpers.subtractProgress s.memory s.activeWords dst modulus i
  { s with pc := UInt256.ofNat 174
           stack := [UInt256.ofNat i, progress.borrow, high, 0, dst, 0, 0,
             modulus, UInt256.ofNat count, returnDest] ++ rest
           memory := progress.memory
           activeWords := progress.activeWords }

def rawSubtractBody (s : State) (dst modulus high : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { rawSubtractLoop s dst modulus high count i returnDest rest with
      pc := UInt256.ofNat 183 }

def reduceUseSub (s : State) (dst modulus high : UInt256) (count : Nat) : UInt256 :=
  UInt256.lor high (UInt256.isZero
    (BigHelpers.subtractProgress s.memory s.activeWords dst modulus count).borrow)

def rawSelectLoop (s : State) (dst modulus high : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let subtracted := BigHelpers.subtractProgress s.memory s.activeWords dst modulus count
  let mask := 0 - reduceUseSub s dst modulus high count
  let progress := BigHelpers.selectProgress subtracted.memory subtracted.activeWords dst mask i
  { s with pc := UInt256.ofNat 245
           stack := [UInt256.ofNat i, mask, subtracted.borrow, high, 0, dst, 0, 0,
             modulus, UInt256.ofNat count, returnDest] ++ rest
           memory := progress.memory
           activeWords := progress.activeWords }

def rawSelectBody (s : State) (dst modulus high : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { rawSelectLoop s dst modulus high count i returnDest rest with
      pc := UInt256.ofNat 254 }

def rawSelectExit (s : State) (dst modulus high : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { rawSelectLoop s dst modulus high count count returnDest rest with
      pc := UInt256.ofNat 293 }

def reduceReturned (s : State) (dst modulus high : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let subtracted := BigHelpers.subtractProgress s.memory s.activeWords dst modulus count
  let progress := BigHelpers.selectProgress subtracted.memory subtracted.activeWords dst
    (0 - reduceUseSub s dst modulus high count) count
  { s with pc := returnDest
           stack := rest
           memory := progress.memory
           activeWords := progress.activeWords }

/-- All arithmetic is natural-address arithmetic; word pointers must fit. -/
structure Layout (dst modulus count : Nat) : Prop where
  dstFit : dst + 32 * count < 2 ^ 256
  modulusFit : modulus + 32 * count < 2 ^ 256
  candidateFit : 5120 + 32 * count < 2 ^ 256
  dstCandidate : dst + 32 * count ≤ 5120 ∨ 5120 + 32 * count ≤ dst
  modulusCandidate : modulus + 32 * count ≤ 5120 ∨ 5120 + 32 * count ≤ modulus
  dstModulus : dst + 32 * count ≤ modulus ∨ modulus + 32 * count ≤ dst


open BigHelpers

private theorem word_mk_eq_ofNat (n : Nat) (h : n < 2 ^ 256) :
    ({ val := ⟨n, h⟩ } : UInt256) = UInt256.ofNat n :=
  Challenge.EvmProof.Word.word_eq_ofNat_toNat _

attribute [local simp] word_mk_eq_ofNat

-- Reduce each original path by definitional equality; do not create replacement paths.
@[simp] private theorem subtractPCs (i : Nat) (hi : 147 ≤ i) (hii : i ≤ 209) :
    Artifact.submissionArtifact.instructionPC i =
      ([174,175,176,177,178,179,182,183,184,186,187,188,189,190,191,192,
       193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,
       209,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,
       228,229,232,233,234,235,236,237,238,239,240,241,242,243,244])[i - 147]! := by
  interval_cases i <;> decide

@[simp] private theorem jump174 :
    Decode.isValidJumpDest submissionBytecode 174 = true :=
  Artifact.isValidJumpDest_index 147 (by rfl)

@[simp] private theorem jump236 :
  Decode.isValidJumpDest submissionBytecode 236 = true :=
  Artifact.isValidJumpDest_index 201 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_subtractGuard (s : State) (dst modulus high : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hi : i < count) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock subtractGuardPath
      (rawSubtractLoop s dst modulus high count i returnDest rest) =
        some (rawSubtractBody s dst modulus high count i returnDest rest) := by
  conv_lhs =>
    arg 1
    run_conv Lean.Elab.Tactic.Conv.changeLhs (← Lean.Meta.reduce (← Lean.Elab.Tactic.Conv.getLhs))
  have hi256 : i < 2 ^ 256 := hi.trans hcount
  have hlt : i % 2 ^ 256 < count % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt hcount]
    exact hi
  have hltLiteral :
      i % 115792089237316195423570985008687907853269984665640564039457584007913129639936 <
        count % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num at hlt ⊢
    exact hlt
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  have hpc : UInt256.ofNat 179 + UInt256.ofNat 3 = UInt256.ofNat 182 := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  simp [subtractGuardPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rawSubtractLoop, rawSubtractBody, subtractPCs, hc10, hc11, hc12, hrun,
    UInt256.lt, UInt256.isTrue, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hltLiteral, honeIsZero, hpc]

set_option linter.unusedSimpArgs false in
theorem run_subtractBody (s : State) (dst modulus high : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hi : i + 1 < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock subtractBodyPath
      (rawSubtractBody s dst modulus high count i returnDest rest) =
        some (rawSubtractLoop s dst modulus high count (i + 1)
          returnDest rest) := by
  conv_lhs =>
    arg 1
    run_conv Lean.Elab.Tactic.Conv.changeLhs (← Lean.Meta.reduce (← Lean.Elab.Tactic.Conv.getLhs))
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have hfiveK : (5120 : UInt256) = UInt256.ofNat 5120 := by decide
  have hloop : (174 : UInt256) = UInt256.ofNat 174 := by decide
  have hloopNat : (174 : UInt256).toNat = 174 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (174 : UInt256).toNat = true := by
    rw [hloopNat]
    exact jump174
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := 1) hi
  have hincLeft : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) :=
    (Challenge.EvmProof.Word.word_add_comm _ _).trans hinc
  simp (config := { maxSteps := 1000000 })
    [subtractBodyPath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      rawSubtractBody, rawSubtractLoop, subtractProgress,
      subtractPCs, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18,
      hc19, hc20, hcode, hrun, hone, hfive, hfiveK, hinc, hincLeft, hloop, hloopNat,
      hjump, jump174, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_subtractFinishGuard (s : State) (dst modulus high : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock subtractGuardPath
      (rawSubtractLoop s dst modulus high count count returnDest rest) =
        some { rawSubtractLoop s dst modulus high count count returnDest rest with
          pc := UInt256.ofNat 236 } := by
  conv_lhs =>
    arg 1
    run_conv Lean.Elab.Tactic.Conv.changeLhs (← Lean.Meta.reduce (← Lean.Elab.Tactic.Conv.getLhs))
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have hdest : (236 : UInt256) = UInt256.ofNat 236 := by decide
  have hdestNat : (236 : UInt256).toNat = 236 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (236 : UInt256).toNat = true := by
    rw [hdestNat]
    exact jump236
  have hpc : UInt256.ofNat 179 + UInt256.ofNat 3 = UInt256.ofNat 182 := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  simp [subtractGuardPath, rawSubtractLoop, subtractPCs,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hc10, hc11, hc12, hcode, hrun, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hzeroFalse, hdest, hdestNat, hjump, jump236, hpc]

set_option linter.unusedSimpArgs false in
theorem run_subtractToSelect (s : State) (dst modulus high : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock subtractToSelectPath
      { rawSubtractLoop s dst modulus high count count returnDest rest with
        pc := UInt256.ofNat 236 } =
      some (rawSelectLoop s dst modulus high count 0 returnDest rest) := by
  conv_lhs =>
    arg 1
    run_conv Lean.Elab.Tactic.Conv.changeLhs (← Lean.Meta.reduce (← Lean.Elab.Tactic.Conv.getLhs))
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzero' : UInt256.ofNat 0 = (0 : UInt256) := by decide
  simp [subtractToSelectPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rawSubtractLoop, rawSelectLoop, selectProgress, reduceUseSub, reduceUseSub, subtractPCs, hc9, hc10, hc11, hc12,
    hrun, hzero, hzero', Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]


private theorem word_toNat_xor (a b : UInt256) :
    (UInt256.xor a b).toNat = a.toNat ^^^ b.toNat := by
  exact Fin.xor_val_of_two_pow (w := 256) a.val b.val

private theorem selectXor_eq_selectWord (sum reduced mask : UInt256) :
    UInt256.xor (UInt256.land mask (UInt256.xor sum reduced)) sum =
      UInt256.lor (UInt256.land reduced mask)
        (UInt256.land sum (UInt256.lnot mask)) := by
  apply Challenge.EvmProof.Word.word_ext
  have hnot : (UInt256.lnot mask).toNat = 2 ^ 256 - 1 - mask.toNat := by
    change (2 ^ 256 - 1 - mask.toNat) % 2 ^ 256 = _
    apply Nat.mod_eq_of_lt
    have hpos : 0 < 2 ^ 256 := by decide
    omega
  simp only [word_toNat_xor, Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_lor, hnot]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or]
  rw [Nat.sub_sub, Nat.add_comm 1 mask.toNat,
    Nat.testBit_two_pow_sub_succ (x := mask.toNat) (n := 256)
      (by exact mask.val.isLt) i]
  by_cases hi : i < 256
  · simp only [hi, decide_true, Bool.true_and]
    cases sum.toNat.testBit i <;> cases reduced.toNat.testBit i <;>
      cases mask.toNat.testBit i <;> rfl
  · have hs : sum.toNat.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le sum.val.isLt
        (Nat.pow_le_pow_right (by decide) (by omega)))
    have hr : reduced.toNat.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le reduced.val.isLt
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hi, hs, hr]


@[simp] private theorem selectPCs (i : Nat) (hi : 210 ≤ i) (hii : i ≤ 261) :
    Artifact.submissionArtifact.instructionPC i =
      [245,246,247,248,249,250,253,254,255,257,258,259,260,261,262,263,
       266,267,268,269,270,271,272,273,274,275,276,277,278,280,281,284,
       285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,
       301,302,303,304][i - 210]! := by
  interval_cases i <;> decide

@[simp] private theorem jump245 :
    Decode.isValidJumpDest submissionBytecode 245 = true :=
  Artifact.isValidJumpDest_index 210 (by rfl)

@[simp] private theorem jump293 :
    Decode.isValidJumpDest submissionBytecode 293 = true :=
  Artifact.isValidJumpDest_index 250 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_selectGuard (s : State) (dst modulus high : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hi : i < count) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock selectGuardPath
      (rawSelectLoop s dst modulus high count i returnDest rest) =
        some (rawSelectBody s dst modulus high count i returnDest rest) := by
  conv_lhs =>
    arg 1
    run_conv Lean.Elab.Tactic.Conv.changeLhs (← Lean.Meta.reduce (← Lean.Elab.Tactic.Conv.getLhs))
  have hi256 : i < 2 ^ 256 := hi.trans hcount
  have hlt : i % 2 ^ 256 < count % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt hcount]
    exact hi
  have hltLiteral :
      i % 115792089237316195423570985008687907853269984665640564039457584007913129639936 <
        count % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num at hlt ⊢
    exact hlt
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  have hpc : UInt256.ofNat 250 + UInt256.ofNat 3 = UInt256.ofNat 253 := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  simp [selectGuardPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rawSelectLoop, rawSelectBody, selectPCs, hc11, hc12, hc13, hrun,
    UInt256.lt, UInt256.isTrue, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hltLiteral, honeIsZero, hpc]

set_option linter.unusedSimpArgs false in
theorem run_selectBody (s : State) (dst modulus high : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hi : i + 1 < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock selectBodyPath
      (rawSelectBody s dst modulus high count i returnDest rest) =
        some (rawSelectLoop s dst modulus high count (i + 1)
          returnDest rest) := by
  conv_lhs =>
    arg 1
    run_conv Lean.Elab.Tactic.Conv.changeLhs (← Lean.Meta.reduce (← Lean.Elab.Tactic.Conv.getLhs))
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have hfiveK : (5120 : UInt256) = UInt256.ofNat 5120 := by decide
  have hloop : (245 : UInt256) = UInt256.ofNat 245 := by decide
  have hloopNat : (245 : UInt256).toNat = 245 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (245 : UInt256).toNat = true := by
    rw [hloopNat]
    exact jump245
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := 1) hi
  have hincLeft : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) :=
    (Challenge.EvmProof.Word.word_add_comm _ _).trans hinc
  simp (config := { maxSteps := 800000 })
    [selectBodyPath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      rawSelectBody, rawSelectLoop, selectProgress, reduceUseSub, selectXor_eq_selectWord,
      selectPCs, hc11, hc12, hc13, hc14, hc15, hc16, hc17,
      hcode, hrun, hone, hfive, hfiveK, hinc, hincLeft, hloop, hloopNat,
      hjump, jump245, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_selectFinishGuard (s : State) (dst modulus high : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock selectGuardPath
      (rawSelectLoop s dst modulus high count count returnDest rest) =
        some (rawSelectExit s dst modulus high count returnDest rest) := by
  conv_lhs =>
    arg 1
    run_conv Lean.Elab.Tactic.Conv.changeLhs (← Lean.Meta.reduce (← Lean.Elab.Tactic.Conv.getLhs))
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have hdest : (293 : UInt256) = UInt256.ofNat 293 := by decide
  have hdestNat : (293 : UInt256).toNat = 293 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode
      (293 : UInt256).toNat = true := by
    rw [hdestNat]
    exact jump293
  have hpc : UInt256.ofNat 250 + UInt256.ofNat 3 = UInt256.ofNat 253 := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  simp [selectGuardPath, rawSelectLoop, rawSelectExit, selectPCs,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hc11, hc12, hc13, hcode, hrun, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hzeroFalse, hdest, hdestNat, hjump, jump293, hpc]

set_option linter.unusedSimpArgs false in
theorem run_selectExit (s : State) (dst modulus high : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock selectExitPath
      (rawSelectExit s dst modulus high count returnDest rest) =
        some (reduceReturned s dst modulus high count returnDest rest) := by
  conv_lhs =>
    arg 1
    run_conv Lean.Elab.Tactic.Conv.changeLhs (← Lean.Meta.reduce (← Lean.Elab.Tactic.Conv.getLhs))
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  simp [selectExitPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    rawSelectExit, rawSelectLoop, reduceReturned, reduceUseSub, selectPCs, hc1, hc2, hc3, hc4,
    hc5, hc6, hc7, hc8, hc9, hc10, hc11, hcode, hvalid, hrun,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]


def gasSteps_subtractIteration (s : State) (dst modulus high : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (rawSubtractLoop s dst modulus high count i returnDest rest)
      (rawSubtractLoop s dst modulus high count (i + 1) returnDest rest) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka subtractGuardPath
        (by simpa [rawSubtractLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [rawSubtractLoop, State.fork] using hfork)
        (run_subtractGuard s dst modulus high count i returnDest rest hcap
          hcount hi hrun)
        (by simpa [rawSubtractLoop] using hrun)
        (by simpa [rawSubtractLoop, State.fork] using hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka subtractBodyPath
        (by simpa [rawSubtractBody, rawSubtractLoop,
          Artifact.submissionArtifact] using hcode)
        (by simpa [rawSubtractBody, rawSubtractLoop, State.fork] using hfork)
        (run_subtractBody s dst modulus high count i returnDest rest hcap
          (by omega) hcode hrun)
        (by simpa [rawSubtractBody, rawSubtractLoop] using hrun)
        (by simpa [rawSubtractBody, rawSubtractLoop, State.fork] using hnp))

def gasSteps_subtractLoop (s : State) (dst modulus high : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (rawSubtractLoop s dst modulus high count 0 returnDest rest)
      (rawSubtractLoop s dst modulus high count count returnDest rest) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded count fun i hi =>
    gasSteps_subtractIteration s dst modulus high count i returnDest rest
      hcap hcount hi hcode hfork hrun hnp

def gasSteps_subtractToSelect (s : State) (dst modulus high : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (rawSubtractLoop s dst modulus high count count returnDest rest)
      (rawSelectLoop s dst modulus high count 0 returnDest rest) := by
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka subtractGuardPath
      (by simpa [rawSubtractLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [rawSubtractLoop, State.fork] using hfork)
      (run_subtractFinishGuard s dst modulus high count returnDest rest hcap
        hcode hrun)
      (by simpa [rawSubtractLoop] using hrun)
      (by simpa [rawSubtractLoop, State.fork] using hnp)
  have htransition := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka subtractToSelectPath
      (by simpa [rawSubtractLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [rawSubtractLoop, State.fork] using hfork)
      (run_subtractToSelect s dst modulus high count returnDest rest hcap hrun)
      (by simpa [rawSubtractLoop] using hrun)
      (by simpa [rawSubtractLoop, State.fork] using hnp)
  exact hguard.trans htransition

def gasSteps_selectIteration (s : State) (dst modulus high : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (rawSelectLoop s dst modulus high count i returnDest rest)
      (rawSelectLoop s dst modulus high count (i + 1) returnDest rest) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka selectGuardPath
        (by simpa [rawSelectLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [rawSelectLoop, State.fork] using hfork)
        (run_selectGuard s dst modulus high count i returnDest rest hcap
          hcount hi hrun)
        (by simpa [rawSelectLoop] using hrun)
        (by simpa [rawSelectLoop, State.fork] using hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka selectBodyPath
        (by simpa [rawSelectBody, rawSelectLoop,
          Artifact.submissionArtifact] using hcode)
        (by simpa [rawSelectBody, rawSelectLoop, State.fork] using hfork)
        (run_selectBody s dst modulus high count i returnDest rest hcap
          (by omega) hcode hrun)
        (by simpa [rawSelectBody, rawSelectLoop] using hrun)
        (by simpa [rawSelectBody, rawSelectLoop, State.fork] using hnp))

def gasSteps_selectLoop (s : State) (dst modulus high : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (rawSelectLoop s dst modulus high count 0 returnDest rest)
      (rawSelectLoop s dst modulus high count count returnDest rest) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded count fun i hi =>
    gasSteps_selectIteration s dst modulus high count i returnDest rest
      hcap hcount hi hcode hfork hrun hnp

def gasSteps_selectFinish (s : State) (dst modulus high : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (rawSelectLoop s dst modulus high count count returnDest rest)
      (reduceReturned s dst modulus high count returnDest rest) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka selectGuardPath
        (by simpa [rawSelectLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [rawSelectLoop, State.fork] using hfork)
        (run_selectFinishGuard s dst modulus high count returnDest rest hcap
          hcode hrun)
        (by simpa [rawSelectLoop] using hrun)
        (by simpa [rawSelectLoop, State.fork] using hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka selectExitPath
        (by simpa [rawSelectExit, rawSelectLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [rawSelectExit, rawSelectLoop, State.fork] using hfork)
        (run_selectExit s dst modulus high count returnDest rest hcap hcode
          hvalid hrun)
        (by simpa [rawSelectExit, rawSelectLoop] using hrun)
        (by simpa [rawSelectExit, rawSelectLoop, State.fork] using hnp))


/-- The old PC174..304 paths reduce the raw destination in place. -/
def gasSteps_reduce (s : State) (dst modulus high : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    GasSteps (reduceEntry s dst modulus high count returnDest rest)
      (reduceReturned s dst modulus high count returnDest rest) :=
  (gasSteps_subtractLoop s dst modulus high count returnDest rest hcap hcount
    hcode hfork hrun hnp).trans <|
  (gasSteps_subtractToSelect s dst modulus high count returnDest rest hcap
    hcode hfork hrun hnp).trans <|
  (gasSteps_selectLoop s dst modulus high count returnDest rest hcap hcount
    hcode hfork hrun hnp).trans <|
  gasSteps_selectFinish s dst modulus high count returnDest rest hcap
    hcode hfork hrun hnp hvalid

/-! ### Raw-total normalization, including total >= R -/

/-- The high word and useSub are Boolean, and the selected value is total mod m. -/
theorem reduceFacts (s : State) (dst modulus count total m : Nat) (high : UInt256)
    (layout : Layout dst modulus count)
    (_hm : 0 < m) (hmR : m < Limbs.radix ^ count) (htotal : total < 2 * m)
    (hdst : Limbs.Represents s.memory dst count (total % Limbs.radix ^ count))
    (hmodulus : Limbs.Represents s.memory modulus count m)
    (hhigh : high.toNat = total / Limbs.radix ^ count) :
    let subtracted := subtractProgress s.memory s.activeWords
      (UInt256.ofNat dst) (UInt256.ofNat modulus) count
    let useSub := reduceUseSub s (UInt256.ofNat dst) (UInt256.ofNat modulus) high count
    high.toNat ≤ 1 ∧ useSub.toNat ≤ 1 ∧
      (useSub.toNat = 1 ↔ m ≤ total) ∧
      (if useSub.toNat = 1 then
        Nat.ofDigits Limbs.radix (Limbs.memoryLimbs subtracted.memory 5120 count)
       else total % Limbs.radix ^ count) = total % m := by
  let bound := Limbs.radix ^ count
  let wrapped := total % bound
  let subtracted := subtractProgress s.memory s.activeWords
    (UInt256.ofNat dst) (UInt256.ofNat modulus) count
  let candidate := Nat.ofDigits Limbs.radix (Limbs.memoryLimbs subtracted.memory 5120 count)
  let useSub := reduceUseSub s (UInt256.ofNat dst) (UInt256.ofNat modulus) high count
  have hbound : 0 < bound := pow_pos Limbs.radix_pos _
  have hwrapped : wrapped < bound := Nat.mod_lt _ hbound
  have hhighLe : high.toNat ≤ 1 := by
    rw [hhigh]
    have hdiv : total / bound < 2 :=
      (Nat.div_lt_iff_lt_mul hbound).mpr (by dsimp [bound]; omega)
    exact Nat.le_of_lt_succ hdiv
  have hsplit : wrapped + bound * high.toNat = total := by
    rw [hhigh]
    exact Nat.mod_add_div total bound
  have hsub : candidate + m = wrapped + bound * subtracted.borrow.toNat ∧
      subtracted.borrow.toNat ≤ 1 :=
    subtractProgress_value_borrow s.memory s.activeWords dst modulus count wrapped m
      layout.dstFit layout.modulusFit layout.candidateFit layout.dstCandidate
      layout.modulusCandidate hdst hmodulus
  have hcandidate : candidate < bound := memoryLimbs_value_lt subtracted.memory 5120 count
  have hcarryIff : high.toNat = 1 ↔ bound ≤ total :=
    carry_eq_one_iff hwrapped hhighLe hsplit
  have hborrowIff : subtracted.borrow.toNat = 0 ↔ m ≤ wrapped :=
    borrow_eq_zero_iff hcandidate hmR hsub.2 hsub.1
  have huseLe : useSub.toNat ≤ 1 := useSub_toNat_le_one high subtracted.borrow hhighLe hsub.2
  have huseIff : useSub.toNat = 1 ↔ m ≤ total :=
    useSub_eq_one_iff high subtracted.borrow hmR rfl hhighLe hsub.2 hcarryIff hborrowIff
  refine ⟨hhighLe, huseLe, huseIff, ?_⟩
  change (if useSub.toNat = 1 then candidate else wrapped) = total % m
  rw [Limbs.mod_eq_cond_sub htotal]
  by_cases hlt : total < m
  · rw [if_pos hlt, if_neg (fun h => (Nat.not_le_of_lt hlt) (huseIff.mp h))]
    exact Nat.mod_eq_of_lt (hlt.trans hmR)
  · have hge : m ≤ total := Nat.le_of_not_gt hlt
    rw [if_neg hlt, if_pos (huseIff.mpr hge)]
    let carryNat := high.toNat
    let borrowNat := subtracted.borrow.toNat
    have hcarryNat : carryNat ≤ 1 := hhighLe
    have hborrowNat : borrowNat ≤ 1 := hsub.2
    have hsplit' : wrapped + bound * carryNat = total := hsplit
    have hsub' : candidate + m = wrapped + bound * borrowNat := hsub.1
    interval_cases carryNat <;> interval_cases borrowNat <;> omega

theorem reduceReturned_represents_mod (s : State) (dst modulus count total m : Nat)
    (high returnDest : UInt256) (rest : List UInt256)
    (layout : Layout dst modulus count)
    (hm : 0 < m) (hmR : m < Limbs.radix ^ count) (htotal : total < 2 * m)
    (hdst : Limbs.Represents s.memory dst count (total % Limbs.radix ^ count))
    (hmodulus : Limbs.Represents s.memory modulus count m)
    (hhigh : high.toNat = total / Limbs.radix ^ count) :
    Limbs.Represents
      (reduceReturned s (UInt256.ofNat dst) (UInt256.ofNat modulus) high count
        returnDest rest).memory dst count (total % m) := by
  let subtracted := subtractProgress s.memory s.activeWords
    (UInt256.ofNat dst) (UInt256.ofNat modulus) count
  let candidate := Nat.ofDigits Limbs.radix (Limbs.memoryLimbs subtracted.memory 5120 count)
  have facts := reduceFacts s dst modulus count total m high layout hm hmR htotal
    hdst hmodulus hhigh
  have hsum : Limbs.Represents subtracted.memory dst count (total % Limbs.radix ^ count) :=
    represents_subtractProgress_input s.memory s.activeWords (UInt256.ofNat dst)
      (UInt256.ofNat modulus) dst count count _ (by omega) layout.candidateFit
      layout.dstCandidate hdst
  have hcandidate : Limbs.Represents subtracted.memory 5120 count candidate :=
    represents_memoryLimbs_value subtracted.memory 5120 count
  exact selectProgress_represents subtracted.memory subtracted.activeWords dst count
    (total % Limbs.radix ^ count) candidate (total % m)
    (reduceUseSub s (UInt256.ofNat dst) (UInt256.ofNat modulus) high count)
    facts.2.1 layout.dstFit layout.dstCandidate hsum hcandidate facts.2.2.2.symm
    ((Nat.mod_lt total hm).trans hmR)


/-! ### Padded-byte and source-region preservation -/

private theorem padded_word_size (value : Nat) :
    (Data.Bytes.natToBytesPadded value 32).size = 32 := by
  simp [Data.Bytes.natToBytesPadded, ByteArray.size]

private theorem subtract_byte_outside (memory : ByteArray)
    (activeWords dst modulus : UInt256) (count iter a : Nat)
    (hiter : iter ≤ count) (hfit : 5120 + 32 * count < 2 ^ 256)
    (hout : a < 5120 ∨ 5120 + 32 * count ≤ a) :
    (subtractProgress memory activeWords dst modulus iter).memory[a]?.getD 0 =
      memory[a]?.getD 0 := by
  induction iter with
  | zero => rfl
  | succ iter ih =>
      rw [subtractProgress, MachineState.writeBytes_getElem?_getD, padded_word_size,
        addOffset_toNat 5120 iter (by omega), if_neg (by omega)]
      exact ih (by omega)

private theorem select_byte_outside (memory : ByteArray)
    (activeWords mask : UInt256) (dst count iter a : Nat)
    (hiter : iter ≤ count) (hfit : dst + 32 * count < 2 ^ 256)
    (hout : a < dst ∨ dst + 32 * count ≤ a) :
    (selectProgress memory activeWords (UInt256.ofNat dst) mask iter).memory[a]?.getD 0 =
      memory[a]?.getD 0 := by
  induction iter with
  | zero => rfl
  | succ iter ih =>
      rw [selectProgress, MachineState.writeBytes_getElem?_getD, padded_word_size,
        addOffset_toNat dst iter (by omega), if_neg (by omega)]
      exact ih (by omega)

theorem reduceReturned_byte_outside (s : State) (dst modulus count a : Nat)
    (high returnDest : UInt256) (rest : List UInt256)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (houtDst : a < dst ∨ dst + 32 * count ≤ a)
    (houtCandidate : a < 5120 ∨ 5120 + 32 * count ≤ a) :
    (reduceReturned s (UInt256.ofNat dst) (UInt256.ofNat modulus) high count
      returnDest rest).memory[a]?.getD 0 = s.memory[a]?.getD 0 := by
  let subtracted := subtractProgress s.memory s.activeWords
    (UInt256.ofNat dst) (UInt256.ofNat modulus) count
  exact (select_byte_outside subtracted.memory subtracted.activeWords
    (0 - reduceUseSub s (UInt256.ofNat dst) (UInt256.ofNat modulus) high count)
    dst count count a (by omega) hdstFit houtDst).trans
      (subtract_byte_outside s.memory s.activeWords (UInt256.ofNat dst)
        (UInt256.ofNat modulus) count count a (by omega) hcandidateFit houtCandidate)

/-- The preserved source may have a different limb count from the destination. -/
theorem reduceReturned_preserves_region (s : State)
    (dst modulus count ptr regionCount value : Nat) (high returnDest : UInt256)
    (rest : List UInt256)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (hptrDst : dst + 32 * count ≤ ptr ∨ ptr + 32 * regionCount ≤ dst)
    (hptrCandidate : 5120 + 32 * count ≤ ptr ∨ ptr + 32 * regionCount ≤ 5120)
    (hrep : Limbs.Represents s.memory ptr regionCount value) :
    Limbs.Represents
      (reduceReturned s (UInt256.ofNat dst) (UInt256.ofNat modulus) high count
        returnDest rest).memory ptr regionCount value := by
  refine ⟨hrep.1, ?_⟩
  rw [← hrep.2]
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro j hj
  have hjlt : j < regionCount := List.mem_range.mp hj
  have hbytes :
      MachineState.readPadded
        (reduceReturned s (UInt256.ofNat dst) (UInt256.ofNat modulus) high count
          returnDest rest).memory (ptr + 32 * j) 32 =
      MachineState.readPadded s.memory (ptr + 32 * j) 32 := by
    apply Challenge.EvmProof.Memory.readPadded_congr
    intro i hi
    exact reduceReturned_byte_outside s dst modulus count (ptr + 32 * j + i)
      high returnDest rest hdstFit hcandidateFit (by omega) (by omega)
  simp only [MachineState.readWord, hbytes]

theorem reduceReturned_preserves_modulus (s : State) (dst modulus count m : Nat)
    (high returnDest : UInt256) (rest : List UInt256)
    (layout : Layout dst modulus count)
    (hmodulus : Limbs.Represents s.memory modulus count m) :
    Limbs.Represents
      (reduceReturned s (UInt256.ofNat dst) (UInt256.ofNat modulus) high count
        returnDest rest).memory modulus count m :=
  reduceReturned_preserves_region s dst modulus count modulus count m high returnDest rest
    layout.dstFit layout.candidateFit layout.dstModulus
    (by rcases layout.modulusCandidate with h | h <;> omega) hmodulus

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryReduceBlock
