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
theorem run_BodyA (s : State) (mem : ByteArray) (n pa pb i j : Nat) (pdst ret : UInt256)
    (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hj : j + 1 < n) (hi : i < n) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkFiosBodyA
        (fiosBody s mem n pa pb pdst ret rest i j)
      = some (fiosBodyA s mem n pa pb pdst ret rest i j) := by
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
  have hmax :
      (115792089237316195423570985008687907853269984665640564039457584007913129639935 :
        UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639935 := by
    decide
  -- the b-limb address, in the RAW NAT MODULAR form the goal has -- this is the fix
  -- for the first `run_BodyA` residual: `hbAddr` was true but unusable, because it
  -- spoke about a `UInt256` addition while the goal is a `Nat` `%` expression.
  have hbNat := bAddr_mod pa n j hpa hpaFit (by omega)
  have hactB : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pa + 32 * (n - j - 2)) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 }) [blkFiosBodyA, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    fiosBody, fiosBodyA, bodyFrame, rowFrame, bAt, aiAt, c1At, c2At, mAt, memAt,
    dB, dN, Csub.ptrAt, Csub.ptrAt_succ,
    Monpro.mulHi, Monpro.maxWord,
    fastPCFios2,
    hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hc16, hc17, hc18, hc19, hcode, hrun,
    hmax, hbNat, hactB,
    UInt256.gt, UInt256.isTrue, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem run_stub1379 (s : State) (mem : ByteArray) (n pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    :
    Challenge.EvmProof.Stepper.runLocatedBlock blkFiosStub
        (Monpro.mpEntryState s mem pa pb pdst ret rest)
      = some (fiosEntry s mem pa pb pdst ret rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have h5351' : (5351 : UInt256) = UInt256.ofNat 5351 := by decide
  have h5351 : (5351 : UInt256).toNat = 5351 := by decide
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (5351 : UInt256).toNat = true := by
    rw [h5351]; exact jumpDest5351
  simp (config := { maxSteps := 400000 }) [blkFiosStub, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, Monpro.mpEntryState, fiosEntry, Csub.ptrAt,
    Csub.ptrAt_succ, fastPC10, hc1, hc2, hc3, hc4, hc5, hcode, hrun, h5351', h5351,
    hjump, jumpDest5351, UInt256.gt, UInt256.isTrue, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat,
    List.exchange]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem run_Setup (s : State) (mem : ByteArray) (n pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn2 : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 8192)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    :
    Challenge.EvmProof.Stepper.runLocatedBlock blkFiosSetup
        (fiosEntry s mem pa pb pdst ret rest)
      = some (fiosRow s (Monpro.mpZeroed s mem n) n pa pb pdst ret rest 0) := by
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
  have h64' : (64 : UInt256) = UInt256.ofNat 64 := by decide
  have h64 : (64 : UInt256).toNat = 64 := by decide
  have h8192' : (8192 : UInt256) = UInt256.ofNat 8192 := by decide
  have h8192 : (8192 : UInt256).toNat = 8192 := by decide
  have h9344' : (9344 : UInt256) = UInt256.ofNat 9344 := by decide
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  have h9408' : (9408 : UInt256) = UInt256.ofNat 9408 := by decide
  have h9408 : (9408 : UInt256).toNat = 9408 := by decide
  have h9440' : (9440 : UInt256) = UInt256.ofNat 9440 := by decide
  have h9440 : (9440 : UInt256).toNat = 9440 := by decide
  have h115792089237316195423570985008687907853269984665640564039457584007913129639904' :
      (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
        UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by decide
  have hsizeN : (64 + 32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 64 + 32 * n := Nat.mod_eq_of_lt (by omega)
  have hcdsN : s.executionEnv.calldata.size %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = s.executionEnv.calldata.size := Nat.mod_eq_of_lt (by omega)
  have hactC : UInt256.ofNat (MachineState.activeWordsAfter
      s.activeWords.toNat 8192 (64 + 32 * n)) = s.activeWords :=
    Csub.activeWords_fix s 8192 (64 + 32 * n) (by omega) (by omega) hact
  have hz9344 : MachineState.readWord (Monpro.mpZeroed s mem n) 9344
      = UInt256.ofNat (32 * n) :=
    (Monpro.readWord_mpZeroed s mem n 9344 hn32 (by omega)).trans hs32
  have hz9408 : MachineState.readWord (Monpro.mpZeroed s mem n) 9408
      = UInt256.ofNat (32 * n - 32) :=
    (Monpro.readWord_mpZeroed s mem n 9408 hn32 (by omega)).trans hml
  have hz9440 : MachineState.readWord (Monpro.mpZeroed s mem n) 9440
      = UInt256.ofNat (8224 + 32 * n) :=
    (Monpro.readWord_mpZeroed s mem n 9440 hn32 (by omega)).trans htl
  have hdB := deltaB_eq pa n hpa hpaFit
  have hdBp := deltaB_eq' pa n hpa hpaFit
  have hdBc := deltaB_eq_comm pa n hpa hpaFit
  have hdN := deltaN_eq n hn2 hn32
  have hcomm1 : 115792089237316195423570985008687907853269984665640564039457584007913129639904 + (pb + 32 * n)
      = pb + 32 * n + 115792089237316195423570985008687907853269984665640564039457584007913129639904 := by omega
  have hcomm2 : 115792089237316195423570985008687907853269984665640564039457584007913129639904 + pb
      = pb + 115792089237316195423570985008687907853269984665640564039457584007913129639904 := by omega
  have hzdef : MachineState.writeBytes mem
      (MachineState.readPadded s.executionEnv.calldata s.executionEnv.calldata.size
        (64 + 32 * n)) 8192 = Monpro.mpZeroed s mem n := rfl
  have hmod_9344 : (9344) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 9344 := Nat.mod_eq_of_lt (by omega)
  have hact_9344 : UInt256.ofNat (MachineState.activeWordsAfter
      s.activeWords.toNat (9344) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hmod_9408 : (9408) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 9408 := Nat.mod_eq_of_lt (by omega)
  have hact_9408 : UInt256.ofNat (MachineState.activeWordsAfter
      s.activeWords.toNat (9408) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hmod_9440 : (9440) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 9440 := Nat.mod_eq_of_lt (by omega)
  have hact_9440 : UInt256.ofNat (MachineState.activeWordsAfter
      s.activeWords.toNat (9440) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 }) [blkFiosSetup, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, fiosEntry, fiosRow, rowFrame, rowsMem, dB, dN,
    Csub.ptrAt, Csub.ptrAt_succ, fastPCFios0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8,
    hc9, hc10, hc11, hcode, hrun, h64', h8192', h9344', h9408', h9440',
    h115792089237316195423570985008687907853269984665640564039457584007913129639904',
    h64, h8192, h9344, h9408, h9440, hsizeN, hcdsN, hactC, hz9344, hz9408, hz9440, hdB, hdBc,
    hdBp, hdN, hcomm1, hcomm2, hzdef, hmod_9344, hact_9344, hmod_9408, hact_9408,
    hmod_9440, hact_9440, hs32, hml, htl, ofNat_K_comm, UInt256.gt, UInt256.isTrue,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem run_Row1 (s : State) (mem : ByteArray) (n pa pb : Nat)
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
    Challenge.EvmProof.Stepper.runLocatedBlock blkFiosRow1
        (fiosRow s mem n pa pb pdst ret rest i)
      = some (fiosRowA s mem n pa pb pdst ret rest i) := by
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
  have h115792089237316195423570985008687907853269984665640564039457584007913129639935' :
      (115792089237316195423570985008687907853269984665640564039457584007913129639935 :
        UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639935 := by decide
  have haNat := aTopAddr_mod pa n hpa hpaFit hn2
  have hbrNat := bRowAddr_mod pb n i hpb hpbFit hi
  have hmod_pbp32xnm1mi : (pb + 32 * (n - 1 - i)) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = pb + 32 * (n - 1 - i) := Nat.mod_eq_of_lt (by omega)
  have hact_pbp32xnm1mi : UInt256.ofNat (MachineState.activeWordsAfter
      s.activeWords.toNat (pb + 32 * (n - 1 - i)) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hmod_pap32xnm1 : (pa + 32 * (n - 1)) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = pa + 32 * (n - 1) := Nat.mod_eq_of_lt (by omega)
  have hact_pap32xnm1 : UInt256.ofNat (MachineState.activeWordsAfter
      s.activeWords.toNat (pa + 32 * (n - 1)) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 }) [blkFiosRow1, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, fiosRow, fiosRowA, rowFrame, peelAi, peelB0,
    Monpro.mulHi, Monpro.maxWord, Csub.ptrAt, Csub.ptrAt_succ, fastPCFios0, fastPCFios1,
    hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hcode, hrun,
    h115792089237316195423570985008687907853269984665640564039457584007913129639935',
    haNat, hbrNat, hmod_pbp32xnm1mi, hact_pbp32xnm1mi, hmod_pap32xnm1, hact_pap32xnm1,
    UInt256.gt, UInt256.isTrue, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat,
    List.exchange]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
theorem run_Row2 (s : State) (mem : ByteArray) (n pa pb : Nat)
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
    Challenge.EvmProof.Stepper.runLocatedBlock blkFiosRow2
        (fiosRowA s mem n pa pb pdst ret rest i)
      = some (fiosRowB s mem n pa pb pdst ret rest i) := by
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
  have h9376' : (9376 : UInt256) = UInt256.ofNat 9376 := by decide
  have h9376 : (9376 : UInt256).toNat = 9376 := by decide
  have hmod_8224p32xn : (8224 + 32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 8224 + 32 * n := Nat.mod_eq_of_lt (by omega)
  have hact_8224p32xn : UInt256.ofNat (MachineState.activeWordsAfter
      s.activeWords.toNat (8224 + 32 * n) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hmod_9376 : (9376) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 9376 := Nat.mod_eq_of_lt (by omega)
  have hact_9376 : UInt256.ofNat (MachineState.activeWordsAfter
      s.activeWords.toNat (9376) 32) = s.activeWords :=
    Csub.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 }) [blkFiosRow2, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, fiosRowA, fiosRowB, rowFrame, peelS, peelC1,
    peelM, peelT0, Monpro.mulHi, Csub.ptrAt, Csub.ptrAt_succ, fastPCFios1, hc1, hc2,
    hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hcode, hrun,
    h9376', h9376, hmod_8224p32xn, hact_8224p32xn, hmod_9376, hact_9376, UInt256.gt,
    UInt256.isTrue, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat,
    List.exchange]


end Challenge.Modexp.Submission.Proofs.Fast.Fios
