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
theorem run_TailA (s : State) (mem : ByteArray) (n pa pb : Nat)
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
    Challenge.EvmProof.Stepper.runLocatedBlock blkFiosTailA
        (fiosTail s mem n pa pb pdst ret rest i)
      = some (fiosTailM s mem n pa pb pdst ret rest i) := by
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
  have h8256' : (8256 : UInt256) = UInt256.ofNat 8256 := by decide
  have h8256 : (8256 : UInt256).toNat = 8256 := by decide
  have htNat := tAddr_mod n (n - 1) hn32 (by omega)
  have hsNat := storeAddr_mod n (n - 1) hn32 (by omega)
  have hix0 : n - (n - 1) - 1 = 0 := by omega
  have hr2 : 8224 + 32 * n - 32 * n = 8224 := by omega
  have hmod_8224 : (8224) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 8224 := Nat.mod_eq_of_lt (by omega)
  have hact_8224 : UInt256.ofNat (MachineState.activeWordsAfter
      s.activeWords.toNat (8224) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hmod_8256 : (8256) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 8256 := Nat.mod_eq_of_lt (by omega)
  have hact_8256 : UInt256.ofNat (MachineState.activeWordsAfter
      s.activeWords.toNat (8256) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 }) [blkFiosTailA, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, fiosTail, fiosTailM, fiosBody, bodyFrame,
    rowFrame, rowsMem, rowMem, memAt, c1At, c2At, mAt, aiAt, Csub.ptrAt,
    Csub.ptrAt_succ, fastPCFios4, fastPCFios5, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8,
    hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hcode, hrun, h8224', h8256',
    h8224, h8256, htNat, hsNat, hix0, hr2, hmod_8224, hact_8224, hmod_8256, hact_8256,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, UInt256.gt, UInt256.isTrue,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem run_TailB_taken (s : State) (mem : ByteArray) (n pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (i : Nat)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hi : i + 1 < n)
    :
    Challenge.EvmProof.Stepper.runLocatedBlock blkFiosTailB
        (fiosTailM s mem n pa pb pdst ret rest i)
      = some (fiosRow s mem n pa pb pdst ret rest (i + 1)) := by
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
  have hpbNat := pbBase_mod pb n hpb hpbFit
  have hbStep := bRowStep_mod pb n i hpb hpbFit hi
  have hbStep2 := bRowStepped_mod pb n i hpb hpbFit hi
  have hcondT : pb - 32 < pb + 32 * (n - i - 2) := by omega
  simp (config := { maxSteps := 400000 }) [blkFiosTailB, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, fiosTailM, fiosRow, rowFrame, rowsMem,
    ofNat_K_step, Csub.ptrAt, Csub.ptrAt_succ, fastPCFios5, hc1, hc2, hc3, hc4, hc5,
    hc6, hc7, hc8, hc9, hc10, hc11, hc12, hcode, hrun, h5488',
    h115792089237316195423570985008687907853269984665640564039457584007913129639904',
    h5488, hjump, jumpDest5488, hpbNat, hbStep2, hbStep, hcondT, UInt256.gt, UInt256.isTrue,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange]

/-- **`run_Tail_taken`, recomposed.  THE STATEMENT IS UNCHANGED**, so `gasSteps_Tail_taken`
and every chain above it see exactly the lemma they saw before -- no wrapper needs
regenerating and nothing downstream moves.

The 29-instruction `blkFiosTail` needed 27 GB in a single `simp`.  It is the only block
that multiplies two `MSTORE`s against a `JUMPI`: the branch leaves both arms in the goal
and each arm carries the full two-store memory term.  Split at pc 5866 the two halves
never meet -- `blkFiosTailA` has all the memory work and no branch, `blkFiosTailB` has
the branch and touches no memory at all.

`Stepper.runLocatedBlock_append` is the tree's own composition lemma, and its docstring
says this is what it is for: "lets large bytecode certificates cache and reuse
independently checked basic blocks".  Its `hrunning` obligation is
`(fiosTailM …).halt = .Running`, which is `s.halt = .Running` definitionally because
`fiosTailM` is a `{s with …}` update, so `hrun` discharges it as it stands. -/
theorem run_Tail_taken (s : State) (mem : ByteArray) (n pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (i : Nat)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hi : i + 1 < n)
    :
    Challenge.EvmProof.Stepper.runLocatedBlock blkFiosTail
        (fiosTail s mem n pa pb pdst ret rest i)
      = some (fiosRow s mem n pa pb pdst ret rest (i + 1)) := by
  rw [blkFiosTail_split]
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append blkFiosTailA blkFiosTailB
    (fiosTail s mem n pa pb pdst ret rest i)
    (fiosTailM s mem n pa pb pdst ret rest i)
    (fiosRow s mem n pa pb pdst ret rest (i + 1))
    (run_TailA s mem n pa pb pdst ret rest i hcap hcode hrun hact hn2 hn32 hpa hpaFit
      hpb hpbFit (by omega))
    hrun
    (run_TailB_taken s mem n pa pb pdst ret rest i hcap hcode hrun hact hn2 hn32 hpa
      hpaFit hpb hpbFit hi)

end Challenge.Modexp.Submission.Proofs.Fast.Fios
