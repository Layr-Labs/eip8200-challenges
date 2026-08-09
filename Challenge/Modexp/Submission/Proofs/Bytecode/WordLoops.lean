import Challenge.Modexp.Submission.Proofs.Bytecode.Word
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# One-word MODEXP loop composition

Two loops instead of the reference's three: a word-at-a-time base Horner loop
(`bsize / 32` turns) and a byte-at-a-time exponent loop (`esize` turns, each a
straight-line unrolled body of two 4-bit windows).  The 16-entry window table
is built once, between them, by a straight-line block chain.

The exit certificates here are the ones constraint C1 depends on: the byte loop
leaves only through `run_byteJumpi_exit`, and that leads to `0x029d`, whose
only continuation is a `RETURN`.  Nothing in this module re-enters the
dispatcher, so the big path can never observe the window table in
`[0x0000, 0x0200)`.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops

open EvmSemantics
open EvmSemantics.EVM
open Word

private def sound {s t : State}
    (path : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka))
    (h : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
        s.executionEnv.fork s.executionEnv.codeAddr = false := by
      exact deployAddress_not_precompile) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

/-! ## Word-at-a-time base reduction -/

def gasSteps_baseIteration (input : ByteArray) (k : Nat) (base : UInt256)
    (hb : baseSize input ≤ 1024) (hk : k < baseSize input / 32) :
    Challenge.EvmProof.GasSteps (baseLoopState input k base)
      (baseLoopState input (k + 1) (hornerStep input k base)) := by
  have hlw : leadWidth input < 32 := leadWidth_lt input
  have hlwv : leadWidth input = baseSize input % 32 := rfl
  have hptrv : basePtr input k = 96 + leadWidth input + 32 * k := rfl
  have hexpv : expOffset input = 96 + baseSize input := rfl
  have hcond : baseCond input k = UInt256.ofNat 0 :=
    baseCond_lt input k (by omega) (by omega)
  exact ((sound baseTestPath (run_baseTest input k base)).trans
    (sound baseJumpiPath (run_baseJumpi_continue input k base hcond))).trans
    ((sound baseBodyPath (run_baseBody input k base hb hk)).trans
      (sound baseLoopJumpPath
        (run_baseLoopJump input k (hornerStep input k base))))

def gasSteps_baseLoop (input : ByteArray) (hb : baseSize input ≤ 1024) :
    Challenge.EvmProof.GasSteps (baseLoopState input 0 (baseInit input))
      (baseLoopState input (baseSize input / 32)
        (hornerAfter input (baseSize input / 32))) :=
  Challenge.EvmProof.GasSteps.iterateBounded
    (I := fun k => baseLoopState input k (hornerAfter input k))
    (baseSize input / 32)
    (fun k hk => gasSteps_baseIteration input k (hornerAfter input k) hb hk)

def gasSteps_baseExit (input : ByteArray) (base : UInt256)
    (hb : baseSize input ≤ 1024) :
    Challenge.EvmProof.GasSteps
      (baseLoopState input (baseSize input / 32) base)
      (baseExitState input base) := by
  have hlw : leadWidth input < 32 := leadWidth_lt input
  have hlwv : leadWidth input = baseSize input % 32 := rfl
  have hptrv : basePtr input (baseSize input / 32) =
      96 + leadWidth input + 32 * (baseSize input / 32) := rfl
  have hexpv : expOffset input = 96 + baseSize input := rfl
  have hcond : baseCond input (baseSize input / 32) = UInt256.ofNat 1 :=
    baseCond_ge input (baseSize input / 32) (by omega) (by omega)
  exact (sound baseTestPath (run_baseTest input (baseSize input / 32) base)).trans
    (sound baseJumpiPath (run_baseJumpi_exit input base hcond))

/-! ## Building the window table -/

def gasSteps_table (input : ByteArray) (base : UInt256) :
    Challenge.EvmProof.GasSteps (baseExitState input base)
      (byteLoopState input base 0 0 (powTab input base 0)) :=
  (sound tableInitPath (run_tableInit input base)).trans <|
  (sound table2Path (run_table2 input base)).trans <|
  (sound tablePath3 (run_table3 input base)).trans <|
  (sound tablePath4 (run_table4 input base)).trans <|
  (sound tablePath5 (run_table5 input base)).trans <|
  (sound tablePath6 (run_table6 input base)).trans <|
  (sound tablePath7 (run_table7 input base)).trans <|
  (sound tablePath8 (run_table8 input base)).trans <|
  (sound tablePath9 (run_table9 input base)).trans <|
  (sound tablePath10 (run_table10 input base)).trans <|
  (sound tablePath11 (run_table11 input base)).trans <|
  (sound tablePath12 (run_table12 input base)).trans <|
  (sound tablePath13 (run_table13 input base)).trans <|
  (sound tablePath14 (run_table14 input base)).trans <|
  (sound tablePath15 (run_table15 input base)).trans <|
  sound tableLoadPath (run_tableLoad input base)

/-! ## The exponent byte loop -/

theorem byteWord_lt (input : ByteArray) (off : Nat) :
    (byteWord input off).toNat < 256 := by
  unfold byteWord Accessors.calldataByteValue UInt256.byteAt
  rw [if_neg (by decide : ¬ (⟨0⟩ : UInt256).toNat ≥ 32),
    Challenge.EvmProof.Word.word_toNat_ofNat]
  have hmask :
      (MachineState.readWord (Dispatch.wordEntryState input).executionEnv.calldata
        (UInt256.ofNat off).toNat).toNat >>>
          (8 * (31 - (⟨0⟩ : UInt256).toNat)) &&& 0xff < 256 := by
    rw [show (0xff : Nat) = 2 ^ 8 - 1 by norm_num,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  omega

/-- The dead byte register at the top of each turn: `0` before the first, then
the byte just consumed. -/
def wordW (input : ByteArray) : Nat → UInt256
  | 0 => 0
  | i + 1 => byteWord input (expOffset input + i)

/-- The accumulator after `i` exponent bytes. -/
def wordAcc (input : ByteArray) (base : UInt256) : Nat → UInt256
  | 0 => powTab input base 0
  | i + 1 =>
      windowStep input base (byteWord input (expOffset input + i))
        (wordAcc input base i)

def gasSteps_byteIteration (input : ByteArray) (base : UInt256) (i : Nat)
    (w acc : UInt256) (hb : baseSize input ≤ 1024)
    (he : exponentSize input ≤ 1024) (hi : i < exponentSize input) :
    Challenge.EvmProof.GasSteps (byteLoopState input base i w acc)
      (byteLoopState input base (i + 1) (byteWord input (expOffset input + i))
        (windowStep input base (byteWord input (expOffset input + i)) acc)) := by
  have hexpv : expOffset input = 96 + baseSize input := rfl
  have hmodv : modulusOffset input = expOffset input + exponentSize input := rfl
  have hcond : byteCond input i = UInt256.ofNat 0 :=
    byteCond_lt input i hi hb he
  have hw : (byteWord input (expOffset input + i)).toNat < 256 :=
    byteWord_lt input (expOffset input + i)
  exact ((sound byteTestPath (run_byteTest input base i w acc)).trans
      (sound byteJumpiPath (run_byteJumpi_continue input base i w acc hcond))).trans <|
    ((sound byteLoadPath (run_byteLoad input base i w acc hb he hi)).trans
      (sound byteSq1Path
        (run_byteSq1 input base i (byteWord input (expOffset input + i)) acc))).trans <|
    ((sound byteHiPath
        (run_byteHi input base i (byteWord input (expOffset input + i))
          (sq4 input acc) hw)).trans
      (sound byteSq2Path
        (run_byteSq2 input base i (byteWord input (expOffset input + i))
          (UInt256.mulMod (sq4 input acc)
            (tabHi input base (byteWord input (expOffset input + i)))
            (UInt256.ofNat (modulusValue input)))))).trans <|
    (sound byteLoPath
        (run_byteLo input base i (byteWord input (expOffset input + i))
          (sq4 input
            (UInt256.mulMod (sq4 input acc)
              (tabHi input base (byteWord input (expOffset input + i)))
              (UInt256.ofNat (modulusValue input)))) hw)).trans <|
    (sound byteAdvancePath
        (run_byteAdvance input base i (byteWord input (expOffset input + i))
          (windowStep input base (byteWord input (expOffset input + i)) acc)
          hb he hi)).trans
      (sound byteLoopJumpPath
        (run_byteLoopJump input base i (byteWord input (expOffset input + i))
          (windowStep input base (byteWord input (expOffset input + i)) acc)))

def gasSteps_byteLoop (input : ByteArray) (base : UInt256)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024) :
    Challenge.EvmProof.GasSteps
      (byteLoopState input base 0 0 (powTab input base 0))
      (byteLoopState input base (exponentSize input)
        (wordW input (exponentSize input))
        (wordAcc input base (exponentSize input))) :=
  Challenge.EvmProof.GasSteps.iterateBounded
    (I := fun i => byteLoopState input base i (wordW input i) (wordAcc input base i))
    (exponentSize input)
    (fun i hi =>
      gasSteps_byteIteration input base i (wordW input i) (wordAcc input base i)
        hb he hi)

def gasSteps_byteExit (input : ByteArray) (base : UInt256) (w acc : UInt256)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024) :
    Challenge.EvmProof.GasSteps
      (byteLoopState input base (exponentSize input) w acc)
      (wordExitState input base acc) := by
  have hcond : byteCond input (exponentSize input) = UInt256.ofNat 1 :=
    byteCond_ge input hb he
  exact ((sound byteTestPath
      (run_byteTest input base (exponentSize input) w acc)).trans
    (sound byteJumpiPath
      (run_byteJumpi_exit input base w acc hcond))).trans <|
    (sound byteExitPath (run_byteExit input base w acc)).trans
      (sound byteExitJumpPath (run_byteExitJump input base acc))

/-! ## The whole appended body -/

def wordBase (input : ByteArray) : UInt256 :=
  hornerAfter input (baseSize input / 32)

def wordResult (input : ByteArray) : UInt256 :=
  wordAcc input (wordBase input) (exponentSize input)

def gasSteps_wordBody (input : ByteArray) (hvalid : ValidInput input)
    (hword : modulusSize input ≤ 32) (hmodpos : 0 < modulusValue input) :
    Challenge.EvmProof.GasSteps (wordBodyState input)
      (wordExitState input (wordBase input) (wordResult input)) := by
  obtain ⟨hsize, hb, he, hm⟩ := hvalid
  exact ((sound newPath (run_new input ⟨hsize, hb, he, hm⟩ hword hmodpos)).trans
    (gasSteps_baseLoop input hb)).trans <|
    ((gasSteps_baseExit input (wordBase input) hb).trans
      (gasSteps_table input (wordBase input))).trans <|
    (gasSteps_byteLoop input (wordBase input) hb he).trans
      (gasSteps_byteExit input (wordBase input) (wordW input (exponentSize input))
        (wordResult input) hb he)

def gasSteps_wordEntry (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodpos : 0 < modulusValue input) :
    Challenge.EvmProof.GasSteps (Dispatch.wordEntryState input)
      (wordExitState input (wordBase input) (wordResult input)) :=
  ((gasSteps_start input hvalid hmsize hword hmodpos).trans
    (gasSteps_enterBody input)).trans
    (gasSteps_wordBody input hvalid hword hmodpos)

end Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops
