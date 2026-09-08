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
theorem run_BodyEA (s : State) (mem : ByteArray) (n pa pb : Nat)
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
    Challenge.EvmProof.Stepper.runLocatedBlock blkFiosBodyEA
        (fiosBodyD s mem n pa pb pdst ret rest i j)
      = some (fiosBodyM s mem n pa pb pdst ret rest i j) := by
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
  have h32' : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h32 : (32 : UInt256).toNat = 32 := by decide
  have h115792089237316195423570985008687907853269984665640564039457584007913129639904' :
      (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
        UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by decide
  have hsNat := storeAddr_mod n j hn32 (by omega)
  have hptNat := tAddr_mod n j hn32 (by omega)
  have hmod_8256p32xnmjm1 : (8256 + 32 * (n - j - 1)) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 8256 + 32 * (n - j - 1) := Nat.mod_eq_of_lt (by omega)
  have hact_8256p32xnmjm1 : UInt256.ofNat (MachineState.activeWordsAfter
      s.activeWords.toNat (8256 + 32 * (n - j - 1)) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 }) [blkFiosBodyEA, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, fiosBodyD, fiosBodyM, fiosBody, bodyFrame,
    rowFrame, bodyW_succ, memAt, c1At, c2At, mAt, aiAt, uAt, nAt, bAt, tAt,
    Monpro.macSum, Monpro.macCarry, Challenge.EvmProof.Word.word_toNat_add,
    ofNat_K_step, Csub.ptrAt, Csub.ptrAt_succ, fastPCFios4, hc1, hc2, hc3, hc4, hc5,
    hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hcode,
    hrun, h32',
    h115792089237316195423570985008687907853269984665640564039457584007913129639904',
    h32, hsNat, hptNat, hmod_8256p32xnmjm1, hact_8256p32xnmjm1, UInt256.gt,
    UInt256.isTrue, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat,
    List.exchange]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem run_BodyEB_taken (s : State) (mem : ByteArray) (n pa pb : Nat)
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
    (hjp : j + 2 < n)
    :
    Challenge.EvmProof.Stepper.runLocatedBlock blkFiosBodyEB
        (fiosBodyM s mem n pa pb pdst ret rest i j)
      = some (fiosBody s mem n pa pb pdst ret rest i (j + 1)) := by
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
  have h8224' : (8224 : UInt256) = UInt256.ofNat 8224 := by decide
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have h5653' : (5653 : UInt256) = UInt256.ofNat 5653 := by decide
  have h5653 : (5653 : UInt256).toNat = 5653 := by decide
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (5653 : UInt256).toNat = true := by
    rw [h5653]; exact jumpDest5653
  have hstepNat := tAddr_mod n (j + 1) hn32 (by omega)
  have hcondE : 8224 < 8224 + 32 * (n - (j + 1) - 1) := by omega
  simp (config := { maxSteps := 400000 }) [blkFiosBodyEB, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, fiosBodyM, fiosBody, bodyFrame, rowFrame,
    Csub.ptrAt, Csub.ptrAt_succ, fastPCFios4, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8,
    hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hcode, hrun, h8224', h5653',
    h8224, h5653, hjump, jumpDest5653, hstepNat, hcondE, UInt256.gt, UInt256.isTrue,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange]

/-- **`run_BodyE_taken`, recomposed.  THE STATEMENT IS UNCHANGED.**  Same failure and
same cure as `blkFiosTail`: this block does the body's only `MSTORE` and then branches,
so the `JUMPI` leaves both arms in the goal and each arm carries the full store term.
Cut at pc 5829 -- after the store and the pointer step -- `blkFiosBodyEA` has the memory
work and no branch and `blkFiosBodyEB` has `PUSH2 0x2020; DUP2; GT; PUSH2 …; JUMPI` and
nothing else at all.

The intermediate state is the cheapest one in the file: after the step, the machine IS
`fiosBody … i (j+1)` apart from its pc, so `fiosBodyM` introduces no new stack shape. -/
theorem run_BodyE_taken (s : State) (mem : ByteArray) (n pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (i j : Nat)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hj : j + 1 < n) (hi : i < n) (hjp : j + 2 < n)
    :
    Challenge.EvmProof.Stepper.runLocatedBlock blkFiosBodyE
        (fiosBodyD s mem n pa pb pdst ret rest i j)
      = some (fiosBody s mem n pa pb pdst ret rest i (j + 1)) := by
  rw [blkFiosBodyE_split]
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append blkFiosBodyEA blkFiosBodyEB
    (fiosBodyD s mem n pa pb pdst ret rest i j)
    (fiosBodyM s mem n pa pb pdst ret rest i j)
    (fiosBody s mem n pa pb pdst ret rest i (j + 1))
    (run_BodyEA s mem n pa pb pdst ret rest i j hcap hcode hrun hact hn2 hn32 hpa hpaFit
      hpb hpbFit hj hi)
    hrun
    (run_BodyEB_taken s mem n pa pb pdst ret rest i j hcap hcode hrun hact hn2 hn32 hpa
      hpaFit hpb hpbFit hj hi hjp)

end Challenge.Modexp.Submission.Proofs.Fast.Fios
