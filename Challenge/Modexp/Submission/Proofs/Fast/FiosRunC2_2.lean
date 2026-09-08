import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Fast.Csub
import Challenge.Modexp.Submission.Proofs.Fast.FiosPC
import Challenge.Modexp.Submission.Proofs.Fast.FiosBlocks
import Challenge.Modexp.Submission.Proofs.Fast.FiosDefs
import Challenge.Modexp.Submission.Proofs.Fast.FiosRunC2_1

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
theorem run_TailB_exit (s : State) (mem : ByteArray) (n pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    :
    Challenge.EvmProof.Stepper.runLocatedBlock blkFiosTailB
        (fiosTailM s mem n pa pb pdst ret rest (n - 1))
      = some (fiosDone s mem n pa pb pdst ret rest) := by
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
  have h5488' : (5488 : UInt256) = UInt256.ofNat 5488 := by decide
  have h5488 : (5488 : UInt256).toNat = 5488 := by decide
  have h115792089237316195423570985008687907853269984665640564039457584007913129639904' :
      (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
        UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by decide
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (5488 : UInt256).toNat = true := by
    rw [h5488]; exact jumpDest5488
  have hix : n - 1 + 1 = n := by omega
  have hpbNat := pbBase_mod pb n hpb hpbFit
  have hbExit2 := bRowSteppedExit_mod pb n hpb hpbFit hn2
  have hrows : rowsMem mem pa pb n n
      = rowMem (rowsMem mem pa pb n (n - 1)) pa pb n (n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, rowsMem]
  have hbExit := bRowExit_mod pb n hpb hpbFit
  simp (config := { maxSteps := 400000 }) [blkFiosTailB, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, fiosTailM, fiosDone, rowFrame, rowsMem,
    ofNat_K_step, Csub.ptrAt, Csub.ptrAt_succ, fastPCFios5, hc1, hc2, hc3, hc4, hc5,
    hc6, hc7, hc8, hc9, hc10, hc11, hc12, hcode, hrun, h5488',
    h115792089237316195423570985008687907853269984665640564039457584007913129639904',
    h5488, hjump, jumpDest5488, hix, hpbNat, hbExit2, hbExit, hrows, UInt256.gt, UInt256.isTrue,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange]

theorem run_Tail_exit (s : State) (mem : ByteArray) (n pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    :
    Challenge.EvmProof.Stepper.runLocatedBlock blkFiosTail
        (fiosTail s mem n pa pb pdst ret rest (n - 1))
      = some (fiosDone s mem n pa pb pdst ret rest) := by
  rw [blkFiosTail_split]
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append blkFiosTailA blkFiosTailB _ _ _
    (run_TailA s mem n pa pb pdst ret rest (n - 1) hcap hcode hrun hact hn2 hn32 hpa
      hpaFit hpb hpbFit (by omega))
    hrun
    (run_TailB_exit s mem n pa pb pdst ret rest hcap hcode hrun hact hn2 hn32 hpa hpaFit
      hpb hpbFit)


set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem run_Exit (s : State) (mem : ByteArray) (n pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    :
    Challenge.EvmProof.Stepper.runLocatedBlock blkFiosExit
        (fiosDone s mem n pa pb pdst ret rest)
      = some (Csub.csEntryState s (rowsMem mem pa pb n n) pdst ret rest) := by
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
  have h2637' : (2637 : UInt256) = UInt256.ofNat 2637 := by decide
  have h2637 : (2637 : UInt256).toNat = 2637 := by decide
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (2637 : UInt256).toNat = true := by
    rw [h2637]; exact jumpDest2642
  simp (config := { maxSteps := 400000 }) [blkFiosExit, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, fiosDone, rowFrame, Csub.csEntryState,
    Csub.ptrAt, Csub.ptrAt_succ, fastPCFios5, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8,
    hc9, hc10, hcode, hrun, h2637', h2637, hjump, jumpDest2642, UInt256.gt,
    UInt256.isTrue, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat,
    List.exchange]






end Challenge.Modexp.Submission.Proofs.Fast.Fios
