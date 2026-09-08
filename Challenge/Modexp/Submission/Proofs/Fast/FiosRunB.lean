import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Fast.Csub
import Challenge.Modexp.Submission.Proofs.Fast.FiosPC
import Challenge.Modexp.Submission.Proofs.Fast.FiosBlocks
import Challenge.Modexp.Submission.Proofs.Fast.FiosDefs

/-
FiosRun.lean -- the value model, states, block reductions and loop certificates for
`artifact/fios-k9.hex`.  Supersedes FiosEvm.lean sections 2-5; keep that file as the
design note.

THE MAIN FINDING, and it makes this whole layer small:

  The engine's fused body is LITERALLY TWO OF `Monpro`'s EXISTING MAC STEPS.
  `Monpro.lean` already says "Both CIOS limb loops execute the same instruction
  sequence" and gives

      Monpro.mulHi   x y     = UInt256.mulMod x y maxWord - (x * y + lt (mulMod x y maxWord) (x * y))
      Monpro.macSum  x y t c = c + (t + x * y)
      Monpro.macCarry x y t c = lt (c + (t + x*y)) c + (lt (t + x*y) t + mulHi x y)
      Monpro.macSpec x y t c : (macCarry …).toNat * 2^256 + (macSum …).toNat
                                 = t.toNat + x.toNat * y.toNat + c.toNat

  I checked the TERM ORDER against the emitted opcodes, not just the value:
    * `MUL` pops the memory limb then the multiplier, so it is `x * y` with x the
      loaded limb -- `mulHi`'s own convention.
    * `t + x*y` and then `c + (t + x*y)` are the orders `add3` and `DUP4 ADD` produce.
    * `macCarry`'s two `lt`s are the `DUP3 LT` and `DUP4 LT` in that order.
  So the fused body is
      u  = macSum  b_j a_i t_j C1        C1' = macCarry b_j a_i t_j C1
      v  = macSum  N_j m   u   C2        C2' = macCarry N_j m   u   C2
  and NO new value function is needed anywhere.  `macSpec` applied twice is exactly
  `Fios.two_split` from FIOS_MATH.lean, one level down.

ADDRESSES -- all four verified against a running trace (n=4, pa=pb=5120, j=0,1,2):
      p_t   = 8224 + 32 * (n - j - 1)          reads t[j+1]
      p_b   = pa   + 32 * (n - j - 2)          reads b[j+1]
      p_n   =        32 * (n - j - 2)          reads N[j+1]
      store = 8256 + 32 * (n - j - 1)          writes t[j]

CONFIDENCE MARKERS: every step I am not certain of carries `-- ?N` and is listed at the
bottom.  Compile those first.
-/
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Fios

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

attribute [local simp] List.getElem?_cons_zero


set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem run_Row3 (s : State) (mem : ByteArray) (n pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (i : Nat)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hi : i < n)
    :
    Challenge.EvmProof.Stepper.runLocatedBlock blkFiosRow3
        (fiosRowB s mem n pa pb pdst ret rest i)
      = some (fiosRowC s mem n pa pb pdst ret rest i) := by
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
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have h115792089237316195423570985008687907853269984665640564039457584007913129639935' :
      (115792089237316195423570985008687907853269984665640564039457584007913129639935 :
        UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide
  have hdNw := dN_toNat n hn2 hn32
  have hnTop := nTopAddr_mod n hn2 hn32
  have hmod_32xnm1 : (32 * (n - 1)) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 32 * (n - 1) := Nat.mod_eq_of_lt (by omega)
  have hact_32xnm1 : UInt256.ofNat (MachineState.activeWordsAfter
      s.activeWords.toNat (32 * (n - 1)) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 }) [blkFiosRow3, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, fiosRowB, fiosRowC, rowFrame, peelN0, peelM,
    Monpro.mulHi, Monpro.maxWord, Csub.ptrAt, Csub.ptrAt_succ, fastPCFios1, fastPCFios2,
    hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hc16, hc17, hc18, hcode, hrun,
    h115792089237316195423570985008687907853269984665640564039457584007913129639935',
    hdNw, hnTop, hmod_32xnm1, hact_32xnm1, UInt256.gt, UInt256.isTrue,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem run_Row4 (s : State) (mem : ByteArray) (n pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (i : Nat)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hi : i < n)
    :
    Challenge.EvmProof.Stepper.runLocatedBlock blkFiosRow4
        (fiosRowC s mem n pa pb pdst ret rest i)
      = some (fiosBody s mem n pa pb pdst ret rest i 0) := by
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
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have h115792089237316195423570985008687907853269984665640564039457584007913129639904' :
      (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
        UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by decide
  simp (config := { maxSteps := 400000 }) [blkFiosRow4, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, fiosRowC, fiosBody, rowFrame, bodyFrame,
    peelC2, peelC1, peelM, peelAi, c1At, c2At, mAt, aiAt, memAt, bodyW_zero, rowsMem,
    Csub.ptrAt, Csub.ptrAt_succ, fastPCFios2, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8,
    hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hcode, hrun,
    h115792089237316195423570985008687907853269984665640564039457584007913129639904',
    ofNat_K_comm, UInt256.gt, UInt256.isTrue, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat,
    List.exchange]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem run_BodyB (s : State) (mem : ByteArray) (n pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (i j : Nat)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hj : j + 1 < n)
    (hi : i < n)
    :
    Challenge.EvmProof.Stepper.runLocatedBlock blkFiosBodyB
        (fiosBodyA s mem n pa pb pdst ret rest i j)
      = some (fiosBodyB s mem n pa pb pdst ret rest i j) := by
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
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have htNat := tAddr_mod n j hn32 (by omega)
  have hmod_8224p32xnmjm1 : (8224 + 32 * (n - j - 1)) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 8224 + 32 * (n - j - 1) := Nat.mod_eq_of_lt (by omega)
  have hact_8224p32xnmjm1 : UInt256.ofNat (MachineState.activeWordsAfter
      s.activeWords.toNat (8224 + 32 * (n - j - 1)) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 }) [blkFiosBodyB, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, fiosBodyA, fiosBodyB, bodyFrame, rowFrame,
    bodyW_succ, tAt, uAt, c1At, c2At, bAt, aiAt, mAt, memAt, Monpro.macSum,
    Monpro.macCarry, Monpro.mulHi, Csub.ptrAt, Csub.ptrAt_succ, fastPCFios2,
    fastPCFios3, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13,
    hc14, hc15, hc16, hc17, hc18, hc19, hcode, hrun, htNat, hmod_8224p32xnmjm1,
    hact_8224p32xnmjm1, UInt256.gt, UInt256.isTrue, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat,
    List.exchange]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem run_BodyC (s : State) (mem : ByteArray) (n pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (i j : Nat)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hj : j + 1 < n)
    (hi : i < n)
    :
    Challenge.EvmProof.Stepper.runLocatedBlock blkFiosBodyC
        (fiosBodyB s mem n pa pb pdst ret rest i j)
      = some (fiosBodyC s mem n pa pb pdst ret rest i j) := by
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
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have h115792089237316195423570985008687907853269984665640564039457584007913129639935' :
      (115792089237316195423570985008687907853269984665640564039457584007913129639935 :
        UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide
  have hdNw := dN_toNat n hn2 hn32
  have hnNat := nAddr_mod n j hn2 hn32 (by omega)
  have hmod_32xnmjm2 : (32 * (n - j - 2)) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 32 * (n - j - 2) := Nat.mod_eq_of_lt (by omega)
  have hact_32xnmjm2 : UInt256.ofNat (MachineState.activeWordsAfter
      s.activeWords.toNat (32 * (n - j - 2)) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 }) [blkFiosBodyC, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, fiosBodyB, fiosBodyC, bodyFrame, rowFrame,
    bodyW_succ, nAt, uAt, c1At, c2At, mAt, aiAt, memAt, Monpro.mulHi, Monpro.maxWord,
    Csub.ptrAt, Csub.ptrAt_succ, fastPCFios3, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8,
    hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hcode, hrun,
    h115792089237316195423570985008687907853269984665640564039457584007913129639935',
    hdNw, hnNat, hmod_32xnmjm2, hact_32xnmjm2, UInt256.gt, UInt256.isTrue,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem run_BodyD (s : State) (mem : ByteArray) (n pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (i j : Nat)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hj : j + 1 < n)
    (hi : i < n)
    :
    Challenge.EvmProof.Stepper.runLocatedBlock blkFiosBodyD
        (fiosBodyC s mem n pa pb pdst ret rest i j)
      = some (fiosBodyD s mem n pa pb pdst ret rest i j) := by
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
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  simp (config := { maxSteps := 400000 }) [blkFiosBodyD, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, fiosBodyC, fiosBodyD, bodyFrame, rowFrame,
    bodyW_succ, nAt, uAt, tAt, bAt, c1At, c2At, mAt, aiAt, memAt, Monpro.macSum,
    Monpro.macCarry, Monpro.mulHi, Challenge.EvmProof.Word.word_add_comm, lt_add_symm, Monpro.maxWord, Csub.ptrAt,
    Csub.ptrAt_succ, fastPCFios3, fastPCFios4, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8,
    hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hcode, hrun,
    UInt256.gt, UInt256.isTrue, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat,
    List.exchange]


end Challenge.Modexp.Submission.Proofs.Fast.Fios
