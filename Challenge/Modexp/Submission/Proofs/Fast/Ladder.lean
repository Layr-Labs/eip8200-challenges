import Challenge.Modexp.Submission.Proofs.Fast.Ccb

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# The appended R² ladder

`CCB` reaches `radix * R mod m` from `R mod m` by one modular doubling followed
by eight Montgomery squarings.  Each squaring **doubles** the exponent
(`2^e·R ↦ 2^(2e)·R`, since `monpro u u = u²/R`) while each `modadd` doubling
**increments** it, so the eight squarings take the exponent `1 → 2^8 = 256` and
land on `2^256·R = Limbs.radix · R`.

A doubling is far cheaper than a Montgomery squaring — measured, `add(x,x,x)` at
pc 2467 is 1,145 gas at n = 4 against `monpro`'s 6,288 — so the ladder buys the
first exponent steps with doublings instead.  It performs `a` doublings and then
`s` squarings with

    a = 8 <<< lt,   s = 5 - lt,   lt = (128 < 32n)

and `a * 2 ^ s = 256` in both branches (`8 * 32` and `16 * 16`), which is the
whole correctness argument: the exponent still arrives at 256.

The block is appended past the old end of the program, so **every existing
instruction index and program counter is unchanged**; the only edit inside the
old program is the `PUSH2` at pc 1551, whose immediate was the sole reference to
2863.  `CCB` itself is untouched and still proved — the ladder rejoins it at
pc 2877, its loop head, having already put the counter on the stack.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Ladder

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

attribute [local simp] List.getElem?_cons_zero

/-! ## Artifact facts for the appended block

Indices 2642..2669, program counters 4016..3964. -/

/-- PC table for the appended R² ladder. -/
@[simp] theorem fastPC25 (i : Nat) (hi : 2642 ≤ i) (hii : i ≤ 2669) :
    Artifact.submissionArtifact.instructionPC i =
      [4016,4017,4020,4021,4023,4024,4025,4027,4028,4029,4030,4033,4034,
       4035,4036,4039,4040,4041,4042,4043,4044,4045,4048,4049,4050,4052,
       4053,4056][i - 2642]! := by
  interval_cases i <;> decide

/-- The ladder entry.  Discharged against the instruction certificate, not read
off the byte: `isValidJumpDest` is a fact about `submissionBytecode`, and the
byte and the Lean literal are different sources (PLAYBOOK 72). -/
theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4016 = true :=
  Artifact.isValidJumpDest_index 2642 (by rfl)

/-- The doubling-loop head. -/
theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4029 = true :=
  Artifact.isValidJumpDest_index 2651 (by rfl)

/-- The doubling-loop return point. -/
theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4040 = true :=
  Artifact.isValidJumpDest_index 2658 (by rfl)


/-! ## The ladder's sizing rule

`lt` is the comparison the block computes, `a` the doubling count it derives,
`sq` the squaring counter it hands to `CCB`.  The identity `a * 2 ^ sq = 256` is
the whole correctness argument. -/

/-- `lt = (128 < 32n)`, the block's own comparison. -/
def ltOf (n : Nat) : Nat := if 128 < 32 * n then 1 else 0

/-- `a = 8 <<< lt`, the number of modular doublings. -/
def aOf (n : Nat) : Nat := 8 * 2 ^ ltOf n

/-- `sq = 5 - lt`, the number of Montgomery squarings handed to `CCB`. -/
def sqOf (n : Nat) : Nat := 5 - ltOf n

theorem ltOf_le_one (n : Nat) : ltOf n ≤ 1 := by unfold ltOf; split <;> omega

theorem aOf_pos (n : Nat) : 0 < aOf n := by
  unfold aOf; positivity

theorem aOf_le (n : Nat) : aOf n ≤ 16 := by
  unfold aOf ltOf; split <;> norm_num

theorem sqOf_pos (n : Nat) : 0 < sqOf n := by
  unfold sqOf ltOf; split <;> omega

theorem sqOf_le_eight (n : Nat) : sqOf n ≤ 8 := by
  unfold sqOf; omega

/-- **The sizing identity.**  Whichever branch the comparison takes, the ladder
performs exactly 256 exponent-doublings' worth of work: `8 * 2^5 = 16 * 2^4`. -/
theorem aOf_mul_pow_sqOf (n : Nat) : aOf n * 2 ^ sqOf n = 256 := by
  unfold aOf sqOf ltOf; split <;> norm_num

/-! ## Located blocks -/

/-- Instructions 2642..2650, pc 4016..3936: read `32n`, form `a = 8 <<< lt`. -/
def blk2642 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2642 .JUMPDEST,
   pushAt 2643 2 9344,
   opAt 2644 .MLOAD,
   pushAt 2645 1 128,
   opAt 2646 .LT,
   opAt 2647 (.Dup ⟨0, by decide⟩),
   pushAt 2648 1 8,
   opAt 2649 (.Swap ⟨0, by decide⟩),
   opAt 2650 .SHL]

/-- Instructions 2651..2657, pc 4029..3947: `ADDMOD(px, px) → px`. -/
def blk2651 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2651 .JUMPDEST,
   pushAt 2652 2 4040,
   opAt 2653 (.Dup ⟨3, by decide⟩),
   opAt 2654 (.Dup ⟨0, by decide⟩),
   opAt 2655 (.Dup ⟨0, by decide⟩),
   pushAt 2656 2 2467,
   opAt 2657 .JUMP]

/-- Instructions 2658..2664, pc 4040..3956: decrement and loop. -/
def blk2658 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2658 .JUMPDEST,
   pushAt 2659 0 0,
   opAt 2660 .NOT,
   opAt 2661 .ADD,
   opAt 2662 (.Dup ⟨0, by decide⟩),
   pushAt 2663 2 4029,
   opAt 2664 .JUMPI]

/-- Instructions 2665..2669, pc 4049..3964: form `sq = 5 - lt`, rejoin `CCB`. -/
def blk2665 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2665 .POP,
   pushAt 2666 1 5,
   opAt 2667 .SUB,
   pushAt 2668 2 2877,
   opAt 2669 .JUMP]

/-! ## States at the block boundaries -/

/-- Ladder entry, pc 4016, stack `[px, ret]`. -/
def entryState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4016
           stack := [UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- The doubling-loop head, pc 4029, stack `[cnt, lt, px, ret]`. -/
def loopState (s : State) (mem : ByteArray) (px cnt lt : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4029
           stack := [UInt256.ofNat cnt, UInt256.ofNat lt, UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- The `ADDMOD` call, pc 2467, frame `[px, px, px, 4040]`. -/
def amCallState (s : State) (mem : ByteArray) (px cnt lt : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2467
           stack := [UInt256.ofNat px, UInt256.ofNat px, UInt256.ofNat px,
                     UInt256.ofNat 4040] ++
                    ([UInt256.ofNat cnt, UInt256.ofNat lt, UInt256.ofNat px, ret] ++ rest)
           memory := mem }

/-- The doubling return point, pc 4040, counter still at `cnt`. -/
def retState (s : State) (mem : ByteArray) (px cnt lt : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4040
           stack := [UInt256.ofNat cnt, UInt256.ofNat lt, UInt256.ofNat px, ret] ++ rest
           memory := mem }

/-- The loop exit, pc 4049, counter at zero. -/
def exitState (s : State) (mem : ByteArray) (px lt : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4049
           stack := [UInt256.ofNat 0, UInt256.ofNat lt, UInt256.ofNat px, ret] ++ rest
           memory := mem }


/-! ## Word-level facts for the prep block -/

/-- The ladder touches no memory beyond the configuration word at 9344, so the
active-word count is unchanged.  (Stated locally rather than imported: the
sibling copies live in `Csub`/`Lz`/`Monpro`, none of which is in this module's
import closure, and the proof is three lines.) -/
theorem activeWordsAfter_fix (curr off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 9472) (hcurr : 296 ≤ curr) :
    MachineState.activeWordsAfter curr off sz = curr := by
  unfold MachineState.activeWordsAfter
  simp only [hsz, if_false]
  have hle : (off + sz - 1) / 32 + 1 ≤ curr := by omega
  exact Nat.max_eq_left hle

theorem activeWords_fix (s : State) (off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 9472) (hact : 296 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat off sz) =
      s.activeWords := by
  rw [activeWordsAfter_fix _ off sz hsz hoff hact]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm

/-- The block's `LT`: `128 < 32n` as a word. -/
theorem lt_128 (n : Nat) (hn32 : n ≤ 32) :
    UInt256.lt (UInt256.ofNat 128) (UInt256.ofNat (32 * n)) =
      UInt256.ofNat (ltOf n) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_lt,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num), Nat.mod_eq_of_lt (by omega)]
  unfold ltOf
  split <;> simp [Challenge.EvmProof.Word.word_toNat_ofNat]

/-- The block's `SHL`: `8 <<< lt = a`. -/
theorem shl_eight (n : Nat) :
    UInt256.shiftLeft (UInt256.ofNat 8) (UInt256.ofNat (ltOf n)) =
      UInt256.ofNat (aOf n) := by
  have h1 := ltOf_le_one n
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (value := 8) (shift := ltOf n)
    (by norm_num) (by omega)
    (by unfold ltOf at *; split <;> norm_num)]
  rfl

/-! ## Block reductions -/

set_option linter.unusedSimpArgs false in
/-- `blk2642` (pc 4016..3936): read `32n`, compare, and form the doubling
counter.  Falls through to the loop head at pc 4029. -/
theorem run_prep (s : State) (mem : ByteArray) (px n : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008) (hn32 : n ≤ 32)
    (hact : 298 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2642
      (entryState s mem px ret rest) =
      some (loopState s mem px (aOf n) (ltOf n) ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hfix : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      9344 32) = s.activeWords :=
    activeWords_fix s 9344 32 (by omega) (by omega) (by omega)
  have hlt := lt_128 n hn32
  have hshl := shl_eight n
  simp (config := { maxSteps := 400000 }) [blk2642, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    entryState, loopState, fastPC25, hc2, hc3, hc4, hc5, hrun, hs32,
    hfix, hlt, hshl, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]


set_option linter.unusedSimpArgs false in
/-- `blk2651` (pc 4029..3947): push the `ADDMOD` frame and jump to pc 2467. -/
theorem run_call (s : State) (mem : ByteArray) (px cnt lt : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2651
      (loopState s mem px cnt lt ret rest) =
      some (amCallState s mem px cnt lt ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have h4040 : (4040 : UInt256) = UInt256.ofNat 4040 := by decide
  have h2467 : (2467 : UInt256) = UInt256.ofNat 2467 := by decide
  have h2467Nat : (UInt256.ofNat 2467).toNat = 2467 := by decide
  simp (config := { maxSteps := 400000 }) [blk2651, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopState, amCallState, fastPC25, hc4, hc5, hc6, hc7, hc8, hc9, hcode, hrun,
    h4040, h2467, h2467Nat, jumpDest2467,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk2658` (pc 4040..3956) with the counter above one: decrement and jump
back to the loop head. -/
theorem run_ret (s : State) (mem : ByteArray) (px cnt cnt' lt : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hk : cnt = cnt' + 1) (hk' : 1 ≤ cnt') (hk16 : cnt ≤ 16)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2658
      (retState s mem px cnt lt ret rest) =
      some (loopState s mem px cnt' lt ret rest) := by
  subst hk
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hzero : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have h4029 : (4029 : UInt256) = UInt256.ofNat 4029 := by decide
  have h4029Nat : (UInt256.ofNat 4029).toNat = 4029 := by decide
  have hk15 : cnt' ≤ 15 := by omega
  have hdec : UInt256.lnot ({ val := 0 } : UInt256) + UInt256.ofNat (cnt' + 1) =
      UInt256.ofNat cnt' := by
    interval_cases cnt' <;> decide
  have htrue : UInt256.isTrue (UInt256.ofNat cnt') := by
    show (UInt256.ofNat cnt').toNat ≠ 0
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  simp (config := { maxSteps := 400000 }) [blk2658, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    retState, loopState, fastPC25, hc4, hc5, hc6, hcode, hrun,
    hzero, h4029, h4029Nat, hdec, htrue, jumpDest4029, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
/-- `blk2658` with the counter at one: fall through to the exit. -/
theorem run_retLast (s : State) (mem : ByteArray) (px lt : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2658
      (retState s mem px 1 lt ret rest) =
      some (exitState s mem px lt ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hzero : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have h4029 : (4029 : UInt256) = UInt256.ofNat 4029 := by decide
  have hdec : UInt256.lnot ({ val := 0 } : UInt256) + UInt256.ofNat 1 =
      UInt256.ofNat 0 := by decide
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  simp (config := { maxSteps := 400000 }) [blk2658, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    retState, exitState, fastPC25, hc4, hc5, hc6, hrun,
    hzero, h4029, hdec, hfalse, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

/-- The block's `SUB`: `5 - lt = sq`. -/
theorem sub_five (n : Nat) :
    UInt256.ofNat 5 - UInt256.ofNat (ltOf n) = UInt256.ofNat (sqOf n) := by
  have h1 := ltOf_le_one n
  unfold sqOf
  interval_cases h : ltOf n <;> decide

set_option linter.unusedSimpArgs false in
/-- `blk2665` (pc 4049..3964): drop the spent counter, form the squaring
counter `sq = 5 - lt`, and jump to `CCB`'s loop head at pc 2877. -/
theorem run_exit (s : State) (mem : ByteArray) (px n : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk2665
      (exitState s mem px (ltOf n) ret rest) =
      some (Ccb.loopState s mem px (sqOf n) ret rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have h2877 : (2877 : UInt256) = UInt256.ofNat 2877 := by decide
  have h2877Nat : (UInt256.ofNat 2877).toNat = 2877 := by decide
  have hsub := sub_five n
  simp (config := { maxSteps := 400000 }) [blk2665, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    exitState, Ccb.loopState, Ccb.loopStack, fastPC25, hc3, hc4, hc5, hcode, hrun,
    h2877, h2877Nat, hsub, jumpDest2877,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]


/-! ## Execution certificates -/

def gasSteps_prep (s : State) (mem : ByteArray) (px n : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008) (hn32 : n ≤ 32)
    (hact : 298 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entryState s mem px ret rest)
      (loopState s mem px (aOf n) (ltOf n) ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk2642 hcode hfork
      (run_prep s mem px n ret rest hcap hn32 hact hs32 hrun) hrun hnp

def gasSteps_call (s : State) (mem : ByteArray) (px cnt lt : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (loopState s mem px cnt lt ret rest)
      (amCallState s mem px cnt lt ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk2651 hcode hfork
      (run_call s mem px cnt lt ret rest hcap hcode hrun) hrun hnp

def gasSteps_ret (s : State) (mem : ByteArray) (px cnt cnt' lt : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hk : cnt = cnt' + 1) (hk' : 1 ≤ cnt') (hk16 : cnt ≤ 16)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (retState s mem px cnt lt ret rest)
      (loopState s mem px cnt' lt ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk2658 hcode hfork
      (run_ret s mem px cnt cnt' lt ret rest hcap hk hk' hk16 hcode hrun) hrun hnp

def gasSteps_retLast (s : State) (mem : ByteArray) (px lt : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (retState s mem px 1 lt ret rest)
      (exitState s mem px lt ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk2658 hcode hfork
      (run_retLast s mem px lt ret rest hcap hrun) hrun hnp

def gasSteps_exit (s : State) (mem : ByteArray) (px n : Nat) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (exitState s mem px (ltOf n) ret rest)
      (Ccb.loopState s mem px (sqOf n) ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk2665 hcode hfork
      (run_exit s mem px n ret rest hcap hcode hrun) hrun hnp

/-! ## The doubling loop -/

/-- The indexed loop-head family: after `i` `ADDMOD` calls the counter stands
at `a - i`. -/
def dblFamily (s : State) (px lt : Nat) (ret : UInt256) (rest : List UInt256)
    (mems : Nat → ByteArray) (a i : Nat) : State :=
  loopState s (mems i) px (a - i) lt ret rest

/-- One doubling: call `ADDMOD(px, px) → px` and decrement the counter. -/
def gasSteps_dblIteration (s : State) (px lt : Nat) (ret : UInt256)
    (rest : List UInt256) (mems : Nat → ByteArray) (a : Nat) (ha16 : a ≤ 16)
    (addmod : ∀ i, i < a →
      Challenge.EvmProof.GasSteps (amCallState s (mems i) px (a - i) lt ret rest)
        (retState s (mems (i + 1)) px (a - i) lt ret rest))
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (i : Nat) (hi : i + 1 < a) :
    Challenge.EvmProof.GasSteps (dblFamily s px lt ret rest mems a i)
      (dblFamily s px lt ret rest mems a (i + 1)) :=
  ((gasSteps_call s (mems i) px (a - i) lt ret rest hcap hcode hfork hrun hnp).trans
      (addmod i (by omega))).trans
    (gasSteps_ret s (mems (i + 1)) px (a - i) (a - (i + 1)) lt ret rest hcap
      (by omega) (by omega) (by omega) hcode hfork hrun hnp)

/-- The `a - 1` doublings that end at the loop head with the counter at one. -/
def gasSteps_dblLoop (s : State) (px lt : Nat) (ret : UInt256)
    (rest : List UInt256) (mems : Nat → ByteArray) (a : Nat) (ha0 : 0 < a)
    (ha16 : a ≤ 16)
    (addmod : ∀ i, i < a →
      Challenge.EvmProof.GasSteps (amCallState s (mems i) px (a - i) lt ret rest)
        (retState s (mems (i + 1)) px (a - i) lt ret rest))
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (loopState s (mems 0) px a lt ret rest)
      (loopState s (mems (a - 1)) px 1 lt ret rest) := by
  have h := Challenge.EvmProof.GasSteps.iterateBounded
    (I := dblFamily s px lt ret rest mems a) (a - 1)
    (fun i hi => gasSteps_dblIteration s px lt ret rest mems a ha16 addmod hcap
      hcode hfork hrun hnp i (by omega))
  have h0 : dblFamily s px lt ret rest mems a 0
      = loopState s (mems 0) px a lt ret rest := by
    simp [dblFamily]
  have h1 : dblFamily s px lt ret rest mems a (a - 1)
      = loopState s (mems (a - 1)) px 1 lt ret rest := by
    unfold dblFamily
    rw [show a - (a - 1) = 1 by omega]
  rw [h0, h1] at h
  exact h

/-- **The ladder, end to end.**  From pc 4016 with `[px, ret]`, perform `a`
modular doublings and hand over to `CCB`'s loop head at pc 2877 with the
squaring counter `sq` on the stack. -/
def gasSteps_ladder (s : State) (px n : Nat) (ret : UInt256)
    (rest : List UInt256) (mems : Nat → ByteArray) (hcap : rest.length ≤ 1008)
    (hn32 : n ≤ 32) (hact : 298 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord (mems 0) 9344 = UInt256.ofNat (32 * n))
    (addmod : ∀ i, i < aOf n →
      Challenge.EvmProof.GasSteps
        (amCallState s (mems i) px (aOf n - i) (ltOf n) ret rest)
        (retState s (mems (i + 1)) px (aOf n - i) (ltOf n) ret rest))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entryState s (mems 0) px ret rest)
      (Ccb.loopState s (mems (aOf n)) px (sqOf n) ret rest) := by
  have hlast := addmod (aOf n - 1) (by have := aOf_pos n; omega)
  rw [show aOf n - (aOf n - 1) = 1 by have := aOf_pos n; omega,
    show aOf n - 1 + 1 = aOf n by have := aOf_pos n; omega] at hlast
  exact ((gasSteps_prep s (mems 0) px n ret rest hcap hn32 hact hs32 hcode hfork
      hrun hnp).trans
    ((gasSteps_dblLoop s px (ltOf n) ret rest mems (aOf n) (aOf_pos n) (aOf_le n)
        addmod hcap hcode hfork hrun hnp).trans
      ((gasSteps_call s (mems (aOf n - 1)) px 1 (ltOf n) ret rest hcap hcode hfork
          hrun hnp).trans hlast))).trans
    ((gasSteps_retLast s (mems (aOf n)) px (ltOf n) ret rest hcap hcode hfork hrun
        hnp).trans
      (gasSteps_exit s (mems (aOf n)) px n ret rest hcap hcode hfork hrun hnp))


/-! ## The doubling value model

Kept here rather than in `Exp.lean` because it is pure `Nat` arithmetic: the
memory-level glue, which needs `SubSpec`, lives beside `ccSqMem`. -/

/-- The value after `i` modular doublings. -/
def dblVal (mm y : Nat) : Nat → Nat
  | 0 => y
  | i + 1 => (dblVal mm y i + dblVal mm y i) % mm

theorem dblVal_succ (mm y i : Nat) :
    dblVal mm y (i + 1) = (dblVal mm y i + dblVal mm y i) % mm := rfl

theorem dblVal_lt {mm y : Nat} (hm : 0 < mm) (hy : y < mm) :
    ∀ i, dblVal mm y i < mm := by
  intro i
  induction i with
  | zero => exact hy
  | succ i _ => exact Nat.mod_lt _ hm

/-- **The doubling invariant.**  `i` modular doublings multiply the represented
value by `2 ^ i`.  This is the counterpart of `ccSq_form`: a squaring *doubles*
the exponent, a doubling *increments* it, which is why `a * 2 ^ sq = 256` is the
condition for the two routes to agree. -/
theorem dblVal_form {mm y v : Nat} (hy : y ≡ v [MOD mm]) :
    ∀ i, dblVal mm y i ≡ 2 ^ i * v [MOD mm] := by
  intro i
  induction i with
  | zero =>
      show (y : Nat) ≡ 2 ^ 0 * v [MOD mm]
      simpa using hy
  | succ i ih =>
      rw [dblVal_succ]
      calc (dblVal mm y i + dblVal mm y i) % mm
          ≡ dblVal mm y i + dblVal mm y i [MOD mm] := Nat.mod_modEq _ mm
        _ ≡ 2 ^ i * v + 2 ^ i * v [MOD mm] := Nat.ModEq.add ih ih
        _ = 2 ^ (i + 1) * v := by rw [pow_succ]; ring

end Challenge.Modexp.Submission.Proofs.Fast.Ladder
