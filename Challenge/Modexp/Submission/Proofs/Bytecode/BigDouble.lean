import Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

/-! # Specialized modular doubling

The appended routine implements the addition phase of
`addMaskedMod(dst, dst, 1, modulus, count)` with one load per limb.  It then
enters the existing subtraction/selection tail, and consequently has exactly
the same functional endpoint as the general helper.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigDouble

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def setupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1587 .JUMPDEST, opAt 1588 (.Dup ⟨2, by decide⟩), pushAt 1589 0 0,
   opAt 1590 .SUB, pushAt 1591 0 0, pushAt 1592 0 0]

def guardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1593 .JUMPDEST, opAt 1594 (.Dup ⟨7, by decide⟩),
   opAt 1595 (.Dup ⟨1, by decide⟩), opAt 1596 .EQ,
   pushAt 1597 2 170, opAt 1598 .JUMPI]

def bodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1599 (.Dup ⟨0, by decide⟩), pushAt 1600 1 5, opAt 1601 .SHL,
   opAt 1602 (.Dup ⟨0, by decide⟩), opAt 1603 (.Dup ⟨5, by decide⟩),
   opAt 1604 .ADD, opAt 1605 .MLOAD,
   opAt 1606 (.Dup ⟨0, by decide⟩), pushAt 1607 1 255, opAt 1608 .SHR,
   opAt 1609 (.Swap ⟨0, by decide⟩), opAt 1610 (.Dup ⟨0, by decide⟩),
   opAt 1611 .ADD, opAt 1612 (.Dup ⟨4, by decide⟩), opAt 1613 .ADD,
   opAt 1614 (.Dup ⟨2, by decide⟩), opAt 1615 (.Dup ⟨7, by decide⟩),
   opAt 1616 .ADD, opAt 1617 .MSTORE,
   opAt 1618 (.Swap ⟨2, by decide⟩), opAt 1619 .POP, opAt 1620 .POP,
   pushAt 1621 1 1, opAt 1622 .ADD, pushAt 1623 2 2193, opAt 1624 .JUMP]

def entry (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2187
           stack := [dst, dst, 1, modulus, UInt256.ofNat count,
             returnDest] ++ rest }

def loop (s : State) (dst modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let mask : UInt256 := 0 - 1
  let progress := BigHelpers.addProgress s.memory s.activeWords dst dst mask i
  { s with pc := UInt256.ofNat 2193
           stack := [UInt256.ofNat i, progress.carry, mask, dst, dst, 1,
             modulus, UInt256.ofNat count, returnDest] ++ rest
           memory := progress.memory
           activeWords := progress.activeWords }

def bodyEntry (s : State) (dst modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { loop s dst modulus count i returnDest rest with pc := UInt256.ofNat 2201 }

@[simp] private theorem doublePCs (i : Nat) (hi : 1587 ≤ i) (hii : i ≤ 1624) :
    Artifact.submissionArtifact.instructionPC i =
      [2187,2188,2189,2190,2191,2192,2193,2194,2195,2196,2197,2200,
       2201,2202,2204,2205,2206,2207,2208,2209,2210,2212,2213,2214,
       2215,2216,2217,2218,2219,2220,2221,2222,2223,2224,2225,2227,
       2228,2231][i - 1587]! := by
  interval_cases i <;> decide

private theorem jump2193 :
    Decode.isValidJumpDest submissionBytecode 2193 = true :=
  Artifact.isValidJumpDest_index 1593 (by rfl)

private theorem jump170 :
    Decode.isValidJumpDest submissionBytecode 170 = true :=
  Artifact.isValidJumpDest_index 143 (by rfl)

private theorem addProgress_carry_le_one (memory : ByteArray)
    (activeWords dst src mask : UInt256) (i : Nat) :
    (BigHelpers.addProgress memory activeWords dst src mask i).carry.toNat ≤ 1 := by
  induction i with
  | zero =>
      simp only [BigHelpers.addProgress]
      decide
  | succ i ih =>
      let before := BigHelpers.addProgress memory activeWords dst src mask i
      let off := UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)
      let x := MachineState.readWord before.memory (dst + off).toNat
      let y := UInt256.land (MachineState.readWord before.memory (src + off).toNat) mask
      have hstep := BigHelpers.addLimbStep_toNat x y before.carry (by simpa [before] using ih)
      simp only [BigHelpers.addProgress]
      rw [hstep.2]
      have hx : x.toNat < 2 ^ 256 := x.val.isLt
      have hy : y.toNat < 2 ^ 256 := y.val.isLt
      have hc : before.carry.toNat ≤ 1 := by simpa [before] using ih
      have htotal : x.toNat + y.toNat + before.carry.toNat <
          2 * Limbs.radix := by
        simp only [Limbs.radix]
        omega
      have hdiv : (x.toNat + y.toNat + before.carry.toNat) /
          Limbs.radix < 2 := by
        exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using htotal)
      omega

private theorem land_neg_one (x : UInt256) : UInt256.land x (0 - 1) = x := by
  apply Challenge.EvmProof.Word.word_ext
  have h := BigHelpers.land_sub_zero_take_toNat x (take := 1) (by omega)
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simpa only [hone, Nat.one_mul] using h

set_option linter.unusedSimpArgs false in
private theorem activeWordsAfter32_lt (active offset : UInt256) :
    MachineState.activeWordsAfter active.toNat offset.toNat 32 < 2 ^ 256 := by
  unfold MachineState.activeWordsAfter
  simp only [if_false]
  apply (Nat.max_lt).2
  constructor
  · exact active.val.isLt
  · have hoff : offset.toNat < 2 ^ 256 := offset.val.isLt
    have hdiv : (offset.toNat + 32 - 1) / 32 < 2 ^ 256 := by
      apply Nat.div_lt_of_lt_mul
      omega
    omega

@[simp] private theorem activeWordsAfter32_word_toNat (active offset : UInt256) :
    (UInt256.ofNat
      (MachineState.activeWordsAfter active.toNat offset.toNat 32)).toNat =
        MachineState.activeWordsAfter active.toNat offset.toNat 32 := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (activeWordsAfter32_lt active offset)]

private theorem activeWordsAfter32_idem (active offset : Nat) :
    MachineState.activeWordsAfter
        (MachineState.activeWordsAfter active offset 32) offset 32 =
      MachineState.activeWordsAfter active offset 32 := by
  simp [MachineState.activeWordsAfter]

@[simp] private theorem activeWordsAfter32_word_idem
    (active offset : UInt256) :
    UInt256.ofNat (MachineState.activeWordsAfter
        (UInt256.ofNat
          (MachineState.activeWordsAfter active.toNat offset.toNat 32)).toNat
        offset.toNat 32) =
      UInt256.ofNat
        (MachineState.activeWordsAfter active.toNat offset.toNat 32) := by
  rw [activeWordsAfter32_word_toNat, activeWordsAfter32_idem]

@[simp] private theorem activeWordsAfter32_word_twice_eq_thrice
    (active offset : UInt256) :
    UInt256.ofNat (MachineState.activeWordsAfter
        (MachineState.activeWordsAfter active.toNat offset.toNat 32 % 2 ^ 256)
        offset.toNat 32) =
      UInt256.ofNat (MachineState.activeWordsAfter
        (MachineState.activeWordsAfter
          (MachineState.activeWordsAfter active.toNat offset.toNat 32 % 2 ^ 256)
          offset.toNat 32 % 2 ^ 256)
        offset.toNat 32) := by
  have hlt := activeWordsAfter32_lt active offset
  simp only [Nat.mod_eq_of_lt hlt, activeWordsAfter32_idem]

private theorem doubleCarry_eq (x carry : UInt256)
    (hcarry : carry.toNat ≤ 1) :
    UInt256.shiftRight x (UInt256.ofNat 255) =
      UInt256.lor (UInt256.lt (x + x) x)
        (UInt256.lt ((x + x) + carry) (x + x)) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.shiftRight_toNat x (by omega)]
  rw [(BigHelpers.addLimbStep_toNat x x carry hcarry).2]
  rw [Nat.shiftRight_eq_div_pow]
  change x.toNat / 2 ^ 255 =
    (x.toNat + x.toNat + carry.toNat) / 2 ^ 256
  have hxlt : x.toNat < 2 ^ 256 := x.val.isLt
  have hpow : 2 ^ 256 = 2 * 2 ^ 255 := by norm_num [pow_succ]
  by_cases hx : x.toNat < 2 ^ 255
  · have htotal : x.toNat + x.toNat + carry.toNat < 2 ^ 256 := by
      omega
    rw [Nat.div_eq_of_lt hx, Nat.div_eq_of_lt htotal]
  · have hxle : 2 ^ 255 ≤ x.toNat := by omega
    have htotalLe : 2 ^ 256 ≤ x.toNat + x.toNat + carry.toNat := by omega
    have htotalLt : x.toNat + x.toNat + carry.toNat < 2 * 2 ^ 256 := by omega
    have hxdiv : x.toNat / 2 ^ 255 = 1 := by
      apply Nat.div_eq_of_lt_le
      · exact hxle
      · omega
    have htotaldiv : (x.toNat + x.toNat + carry.toNat) / 2 ^ 256 = 1 := by
      apply Nat.div_eq_of_lt_le
      · exact htotalLe
      · exact htotalLt
    rw [hxdiv, htotaldiv]

set_option linter.unusedSimpArgs false in
theorem run_setup (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupPath
      (entry s dst modulus count returnDest rest) =
        some (loop s dst modulus count 0 returnDest rest) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzero' : UInt256.ofNat 0 = (0 : UInt256) := by decide
  simp [setupPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    entry, loop, BigHelpers.addProgress, doublePCs, hc6, hc7, hc8, hc9,
    hrun, hzero, hzero',
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_guard (s : State) (dst modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hcount : count < 2 ^ 256)
    (hi : i < count) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock guardPath
      (loop s dst modulus count i returnDest rest) =
        some (bodyEntry s dst modulus count i returnDest rest) := by
  have hi256 : i < 2 ^ 256 := hi.trans hcount
  have hne : ¬ i % 2 ^ 256 = count % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt hcount]
    omega
  have hneLiteral :
      ¬ i % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        count % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num at hne ⊢
    exact hne
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  simp [guardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loop, bodyEntry, doublePCs, hc9, hc10, hc11, hrun,
    UInt256.eq, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hne, hneLiteral]

set_option linter.unusedSimpArgs false in
theorem run_body (s : State) (dst modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hi : i + 1 < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock bodyPath
      (bodyEntry s dst modulus count i returnDest rest) =
        some (loop s dst modulus count (i + 1) returnDest rest) := by
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := 1) hi
  have hincLeft : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) :=
    (Challenge.EvmProof.Word.word_add_comm _ _).trans hinc
  let progress := BigHelpers.addProgress s.memory s.activeWords dst dst
    (0 - 1) i
  let off := UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)
  let x := MachineState.readWord progress.memory (dst + off).toNat
  have hcarry : progress.carry.toNat ≤ 1 := by
    exact addProgress_carry_le_one s.memory s.activeWords dst dst (0 - 1) i
  have hcarryEq := doubleCarry_eq x progress.carry hcarry
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have h255 : (255 : UInt256) = UInt256.ofNat 255 := by decide
  have h2193 : (2193 : UInt256) = UInt256.ofNat 2193 := by decide
  have h2193Nat : (2193 : UInt256).toNat = 2193 := by decide
  have hvalid : Decode.isValidJumpDest submissionBytecode
      (2193 : UInt256).toNat = true := by
    rw [h2193Nat]
    exact jump2193
  have hland : UInt256.land x (0 - UInt256.ofNat 1) = x := by
    rw [← hone]
    exact land_neg_one x
  have hmaskNat : x.toNat &&& (2 ^ 256 - 1) = x.toNat :=
    (Nat.and_two_pow_sub_one_eq_mod x.toNat 256).trans
      (Nat.mod_eq_of_lt x.val.isLt)
  have hzeroNat : (0 : UInt256).toNat = 0 := by decide
  simp (config := { maxSteps := 800000 })
    [bodyPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bodyEntry, loop, BigHelpers.addProgress, progress, off, x,
      doublePCs, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
      hcode, hrun, hinc, hincLeft, hcarryEq, hland, land_neg_one, hvalid,
      h2193, h2193Nat, jump2193,
      hone, hfive, h255, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      activeWordsAfter32_idem, activeWordsAfter32_word_idem,
      activeWordsAfter32_word_twice_eq_thrice,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      List.exchange]
  constructor
  · constructor
    · simpa [progress, off, hone] using
        (activeWordsAfter32_word_twice_eq_thrice progress.activeWords (dst + off))
    · rw [← hone]
      norm_num [hzeroNat]
      change MachineState.writeBytes progress.memory
          (Data.Bytes.natToBytesPadded
            ((progress.carry.toNat + (x.toNat + x.toNat)) % 2 ^ 256) 32)
          (dst + off).toNat =
        MachineState.writeBytes progress.memory
          (Data.Bytes.natToBytesPadded
            ((progress.carry.toNat +
              (x.toNat + (x.toNat &&& (2 ^ 256 - 1)))) % 2 ^ 256) 32)
          (dst + off).toNat
      rw [hmaskNat]
  · change UInt256.shiftRight x (UInt256.ofNat 255) =
      UInt256.lor (UInt256.lt (x + UInt256.land x (0 - UInt256.ofNat 1)) x)
        (UInt256.lt
          ((x + UInt256.land x (0 - UInt256.ofNat 1)) + progress.carry)
          (x + UInt256.land x (0 - UInt256.ofNat 1)))
    rw [hland]
    exact hcarryEq

set_option linter.unusedSimpArgs false in
theorem run_finish_guard (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock guardPath
      (loop s dst modulus count count returnDest rest) =
      some { BigHelpers.addLoop s dst dst 1 modulus count count returnDest rest with
        pc := UInt256.ofNat 170 } := by
  have hdest : (170 : UInt256) = UInt256.ofNat 170 := by decide
  have hdestNat : (170 : UInt256).toNat = 170 := by decide
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  simp [guardPath, opAt, pushAt, wfOp, loop, BigHelpers.addLoop, doublePCs,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hc9, hc10, hc11, hcode, hrun, UInt256.eq, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hdest, hdestNat, jump170]

def gasSteps_setup (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (entry s dst modulus count returnDest rest)
      (loop s dst modulus count 0 returnDest rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka setupPath hcode hfork
      (run_setup s dst modulus count returnDest rest (by omega) hrun) hrun hnp

def gasSteps_iteration (s : State) (dst modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (loop s dst modulus count i returnDest rest)
      (loop s dst modulus count (i + 1) returnDest rest) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka guardPath
        (by simpa [loop, Artifact.submissionArtifact] using hcode)
        (by simpa [loop, State.fork] using hfork)
        (run_guard s dst modulus count i returnDest rest (by omega) hcount hi hrun)
        (by simpa [loop] using hrun)
        (by simpa [loop, State.fork] using hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bodyPath
        (by simpa [bodyEntry, loop, Artifact.submissionArtifact] using hcode)
        (by simpa [bodyEntry, loop, State.fork] using hfork)
        (run_body s dst modulus count i returnDest rest (by omega) (by omega)
          hcode hrun)
        (by simpa [bodyEntry, loop] using hrun)
        (by simpa [bodyEntry, loop, State.fork] using hnp))

def gasSteps_loop (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (loop s dst modulus count 0 returnDest rest)
      (loop s dst modulus count count returnDest rest) :=
  Challenge.EvmProof.GasSteps.iterateBounded count fun i hi =>
    gasSteps_iteration s dst modulus count i returnDest rest hcap hcount hi
      hcode hfork hrun hnp

def gasSteps_toSubtract (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (loop s dst modulus count count returnDest rest)
      (BigHelpers.subtractLoop s dst dst 1 modulus count 0 returnDest rest) := by
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka guardPath
      (by simpa [loop, Artifact.submissionArtifact] using hcode)
      (by simpa [loop, State.fork] using hfork)
      (run_finish_guard s dst modulus count returnDest rest (by omega) hcode hrun)
      (by simpa [loop] using hrun)
      (by simpa [loop, State.fork] using hnp)
  have htransition := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka BigHelpers.addToSubtractPath
      (by simpa [BigHelpers.addLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [BigHelpers.addLoop, State.fork] using hfork)
      (BigHelpers.run_addToSubtract s dst dst 1 modulus count returnDest rest
        (by omega) hrun)
      (by simpa [BigHelpers.addLoop] using hrun)
      (by simpa [BigHelpers.addLoop, State.fork] using hnp)
  have hzero : (0 : UInt256) = UInt256.ofNat 0 := by decide
  simpa [BigHelpers.subtractLoop, BigHelpers.subtractLoopEntry,
    BigHelpers.subtractProgress, hzero] using hguard.trans htransition

def gasSteps_doubleMod (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (entry s dst modulus count returnDest rest)
      (BigHelpers.addReturned s dst dst 1 modulus count returnDest rest) :=
  (gasSteps_setup s dst modulus count returnDest rest hcap hcode hfork hrun hnp).trans <|
  (gasSteps_loop s dst modulus count returnDest rest hcap hcount hcode hfork hrun hnp).trans <|
  (gasSteps_toSubtract s dst modulus count returnDest rest hcap hcode hfork hrun hnp).trans <|
  (BigHelpers.gasSteps_subtractLoop s dst dst 1 modulus count returnDest rest
    hcap hcount hcode hfork hrun hnp).trans <|
  (BigHelpers.gasSteps_subtractToSelect s dst dst 1 modulus count returnDest rest
    hcap hcode hfork hrun hnp).trans <|
  (BigHelpers.gasSteps_selectLoop s dst dst 1 modulus count returnDest rest
    hcap hcount hcode hfork hrun hnp).trans <|
  BigHelpers.gasSteps_selectFinish s dst dst 1 modulus count returnDest rest hcap
    hcode hfork hrun hnp hvalid

end Challenge.Modexp.Submission.Proofs.Bytecode.BigDouble
