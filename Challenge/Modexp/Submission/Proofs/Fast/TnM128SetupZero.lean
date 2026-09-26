import Challenge.Modexp.Submission.Proofs.Fast.StagedMonpro
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandMemory
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SetupFrames
import Challenge.Modexp.Submission.Proofs.Fast.SquarePartialClear

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128Setup

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached StagedOperand

/-- Stage the first operand at 2368 (`MCOPY`) and clear the scratch word at 2048
(`PUSH0; PUSH2 2048; MSTORE`), keeping `hd` on top: pc 3441 → 3456.  The rest of the
product block is not cleared here: the square rows overwrite it before reading it
(`SquarePartialClear`, `R4SquareScratchAgreement`), and the multiply entry clears the
whole block first (`MulPreclear`). -/
def stageProgram : List Instr :=
  [.push 2 2688, .op .MLOAD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨2, by decide⟩),
   .push 2 2368, .op .MCOPY]

def clearProgram : List Instr := [.push 0 0, .push 2 2048, .op .MSTORE]

def zeroProgram : List Instr := stageProgram ++ clearProgram

/-- After `lowProgram`: `hd` above the operand pointers and the row frame. -/
def cachedSetupState (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3441
           stack := [hd, UInt256.ofNat pa, UInt256.ofNat pb,
             l1Target n, zeroTn, allOnes, MachineState.readWord mem 128, dst, ret] ++ rest
           memory := mem }

/-- After staging: `hd` above the width word (pc 3451). -/
def stagedSetupState (s : State) (mem : ByteArray) (hd : UInt256) (pb n : Nat)
    (ent dst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3451
           stack := [hd, UInt256.ofNat (32*n), UInt256.ofNat pb,
             ent, zeroTn, allOnes, MachineState.readWord mem 128, dst, ret] ++ rest
           memory := mem }

/-- After staging and clearing the scratch word: `hd` above the width word. -/
def clearedSetupState (s : State) (mem : ByteArray) (hd : UInt256) (pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3456
           stack := [hd, UInt256.ofNat (32*n), UInt256.ofNat pb,
             l1Target n, zeroTn, allOnes, MachineState.readWord mem 128, dst, ret] ++ rest
           memory := SquarePartialClear.memory mem }

theorem run_stageGen (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (ent dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hact : 88 ≤ s.activeWords.toNat) (hnpos : 0 < n) (hn : n ≤ 8) (hpa : pa+32*n ≤ 2816)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n)) :
    runInstructions stageProgram
      { s with pc := UInt256.ofNat 3441
               stack := [hd, UInt256.ofNat pa, UInt256.ofNat pb,
                 ent, zeroTn, allOnes, MachineState.readWord mem 128, dst, ret] ++ rest
               memory := mem } =
      some (stagedSetupState s (stage mem pa n) hd pb n ent dst ret rest) := by
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  have hpaN : pa % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa := Nat.mod_eq_of_lt (by omega)
  have hszN : (32*n) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 32*n := Nat.mod_eq_of_lt (by omega)
  have hactS := activeWords_fix s 2688 32 (by decide) (by omega) hact
  have hactD := activeWordsAfter_fix s.activeWords.toNat 2368 (32*n) (by omega) (by omega) hact
  have hactA := activeWordsAfter_fix s.activeWords.toNat pa (32*n) (by omega) (by omega) hact
  have h2688 : (2688 : UInt256).toNat = 2688 := by decide
  have h2368 : (2368 : UInt256).toNat = 2368 := by decide
  simp only [stagedSetupState,
    read_stage_outside mem pa n 128 (Or.inl (by decide))]
  simp [stageProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    stage, hs32, State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
    hactS, hactD, hactA, h2688, h2368,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hpaN, hszN,
    hc9, hc10, hc11, hc12, List.exchange]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat s.activeWords).symm

theorem run_clearGen (s : State) (mem : ByteArray) (hd : UInt256) (pb n : Nat)
    (ent dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions clearProgram (stagedSetupState s mem hd pb n ent dst ret rest) =
      some { stagedSetupState s (SquarePartialClear.memory mem) hd pb n ent dst ret rest with
        pc := UInt256.ofNat 3456 } := by
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  have hc11 : rest.length+11 < 1024 := by omega
  have ha := activeWords_fix s 2048 32 (by decide) (by decide) hact
  have h2048 : (2048 : UInt256).toNat = 2048 := by decide
  simp [clearProgram, stagedSetupState, SquarePartialClear.memory, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, State.activeWordsAfterUInt256, ha, h2048,
    hc9, hc10, hc11, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]
  refine ⟨by rfl, ?_⟩
  exact (SquarePartialClear.readWord_outside mem 128 (Or.inl (by decide))).symm

theorem run_zero (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hact : 88 ≤ s.activeWords.toNat) (hnpos : 0 < n) (hn : n ≤ 8) (hpa : pa+32*n ≤ 2816)
    (_hcds : s.executionEnv.calldata.size < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n)) :
    runInstructions zeroProgram (cachedSetupState s mem hd pa pb n dst ret rest) =
      some (clearedSetupState s (stage mem pa n) hd pb n dst ret rest) := by
  have h1 := run_stageGen s mem hd pa pb n (l1Target n) dst ret rest hcap hact hnpos hn hpa hs32
  have h2 := run_clearGen s (stage mem pa n) hd pb n (l1Target n) dst ret rest hcap hact
  have h := runInstructions_append_some _ _ _ _ _ h1 h2
  simpa only [zeroProgram, cachedSetupState, stagedSetupState, clearedSetupState,
    SquarePartialClear.readWord_outside _ 128 (Or.inl (by decide))] using h

/-- `cachedSetupState` with the square frame's constant row head: the square-loop riding
frame keeps the limb count (not the width word) in the setup's width slot, so the
normalized selector vanishes and the displaced head is `3562` for both widths. -/
def cachedSetupStateSq (s : State) (mem : ByteArray) (hd : UInt256) (pa pb _n : Nat)
    (dst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3441
           stack := [hd, UInt256.ofNat pa, UInt256.ofNat pb,
             UInt256.ofNat 3562, zeroTn, allOnes, MachineState.readWord mem 128, dst, ret] ++ rest
           memory := mem }

/-- `clearedSetupState` for the square frame (row head 3562). -/
def clearedSetupStateSq (s : State) (mem : ByteArray) (hd : UInt256) (pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3456
           stack := [hd, UInt256.ofNat (32*n), UInt256.ofNat pb,
             UInt256.ofNat 3562, zeroTn, allOnes, MachineState.readWord mem 128, dst, ret] ++ rest
           memory := SquarePartialClear.memory mem }

theorem run_zero_sq (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hact : 88 ≤ s.activeWords.toNat) (hnpos : 0 < n) (hn : n ≤ 8) (hpa : pa+32*n ≤ 2816)
    (_hcds : s.executionEnv.calldata.size < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n)) :
    runInstructions zeroProgram (cachedSetupStateSq s mem hd pa pb n dst ret rest) =
      some (clearedSetupStateSq s (stage mem pa n) hd pb n dst ret rest) := by
  have h1 := run_stageGen s mem hd pa pb n (UInt256.ofNat 3562) dst ret rest hcap hact hnpos hn hpa hs32
  have h2 := run_clearGen s (stage mem pa n) hd pb n (UInt256.ofNat 3562) dst ret rest hcap hact
  have h := runInstructions_append_some _ _ _ _ _ h1 h2
  simpa only [zeroProgram, cachedSetupStateSq, stagedSetupState, clearedSetupStateSq,
    SquarePartialClear.readWord_outside _ 128 (Or.inl (by decide))] using h

/-- The multiply entry's preclear trampoline (pc 5466): the kernel `setup` only clears the
scratch word at 2048, so the multiply path (whose rows are modelled on the fully cleared
block) zeroes the whole `64 + 32n` block first, exactly as the old in-setup
`CALLDATACOPY` did, then jumps to the multiply entry (pc 3383). -/
def preclearProgram : List Instr :=
  [.op .JUMPDEST, .push 2 2688, .op .MLOAD, .push 1 64, .op .ADD, .op .CALLDATASIZE,
   .push 2 2048, .op .CALLDATACOPY, .push 2 3383, .op .JUMP]

theorem run_preclear (s : State) (mem : ByteArray) (n : Nat) (st : List UInt256)
    (hcap : st.length ≤ 1010)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8)
    (hcds : s.executionEnv.calldata.size < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n))
    (hjump : Decode.isValidJumpDest s.executionEnv.code 3383 = true) :
    runInstructions preclearProgram { s with pc := UInt256.ofNat 5466, stack := st, memory := mem } =
      some { s with pc := UInt256.ofNat 3383, stack := st, memory := mpZeroed s mem n } := by
  have hc0 : st.length < 1024 := by omega
  have hc1 : st.length+1 < 1024 := by omega
  have hc2 : st.length+2 < 1024 := by omega
  have hc3 : st.length+3 < 1024 := by omega
  have hc4 : st.length+4 < 1024 := by omega
  have hsizeN : (64+32*n) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 64+32*n := Nat.mod_eq_of_lt (by omega)
  have hcdsN : s.executionEnv.calldata.size % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = s.executionEnv.calldata.size :=
    Nat.mod_eq_of_lt hcds
  have hactS := activeWords_fix s 2688 32 (by decide) (by omega) hact
  have hactC := activeWords_fix s 2048 (64+32*n) (by omega) (by omega) hact
  have hactN : s.activeWords.toNat % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = s.activeWords.toNat :=
    Nat.mod_eq_of_lt s.activeWords.val.isLt
  have h9344 : (2688 : UInt256).toNat = 2688 := by decide
  have h8192 : (2048 : UInt256).toNat = 2048 := by decide
  have h3383 : (3383 : UInt256).toNat = 3383 := by decide
  have h64 : (64 : UInt256) = UInt256.ofNat 64 := by decide
  simp (config := { maxSteps := 200000 }) [preclearProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    mpZeroed, hs32, hjump, h3383,
    State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2, hactS, hactC,
    h9344, h8192, h64, hactN,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hsizeN, hcdsN,
    hc0, hc1, hc2, hc3, hc4, List.exchange]
  decide

/-- Operand pointers and the jump to the row head (pc 4182 → `hd`):
`SWAP1; DUP3; ADD; DUP5; ADD; SWAP2; DUP5; ADD; SWAP2; DUP2; JUMP`. -/
def pointersJumpProgram : List Instr :=
  [.op (.Swap ⟨1, by decide⟩), .push 1 31, .op .NOT, .op .ADD,
   .op (.Swap ⟨1, by decide⟩), .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .ADD,
   .op (.Dup ⟨1, by decide⟩), .op .JUMP]

private theorem negative32_add_ofNat (x : Nat) (hx : 32 ≤ x)
    (hx' : x < 115792089237316195423570985008687907853269984665640564039457584007913129639936) :
    negative32 + UInt256.ofNat x = UInt256.ofNat (x - 32) := by
  have hneg : negative32 = UInt256.ofNat
      115792089237316195423570985008687907853269984665640564039457584007913129639904 := rfl
  rw [hneg, Challenge.EvmProof.Word.ofNat_add_mod]
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat]
  have h2 : (2 : Nat) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num
  rw [h2]
  have hsplit : 115792089237316195423570985008687907853269984665640564039457584007913129639904 + x =
      (x - 32) + 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    omega
  rw [hsplit, Nat.add_mod_right]

/-- From the cleared setup state the row-0 frame is built and the setup jumps to `hd`
(the row head: 4192 for the multiply, 4930 for the square). -/
theorem run_pointersJump (s : State) (mem : ByteArray) (hd : UInt256) (pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 2816) (hn : n ≤ 8)
    (htarget : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    runInstructions pointersJumpProgram (clearedSetupState s mem hd pb n dst ret rest) =
      some (outState s (SquarePartialClear.memory mem) pb n 0 hd (l1Target n) dst ret rest) := by
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hsum : UInt256.ofNat pb + UInt256.ofNat (32 * n) = UInt256.ofNat (pb + 32 * n) :=
    Challenge.EvmProof.Word.ofNat_add_mod pb (32 * n)
  have hend : negative32 + UInt256.ofNat (pb + 32 * n) = UInt256.ofNat (pb + 32 * n - 32) :=
    negative32_add_ofNat (pb + 32 * n) (by omega) (by omega)
  have hlow : negative32 + UInt256.ofNat pb = UInt256.ofNat (pb - 32) :=
    negative32_add_ofNat pb hpb (by omega)
  have hsumLow : UInt256.ofNat (pb - 32) + UInt256.ofNat (32 * n) =
      UInt256.ofNat (pb + 32 * n - 32) := by
    rw [Challenge.EvmProof.Word.ofNat_add_mod]
    congr 1
    omega
  simp only [clearedSetupState, outState,
    SquarePartialClear.readWord_outside mem 128 (Or.inl (by decide))]
  simp [pointersJumpProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    clearedSetupState, outState, ← negative32_not, hc9, hc10, hc11, hc12, htarget, hsum, hend, hlow, hsumLow,
    ptrAt_zero, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod]
  simp only [show UInt256.lnot (31 : UInt256) = negative32 by decide,
    hlow, hsumLow, and_self]

/-- `run_pointersJump` for the square frame (constant row head 3562). -/
theorem run_pointersJump_sq (s : State) (mem : ByteArray) (hd : UInt256) (pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 2816) (hn : n ≤ 8)
    (htarget : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    runInstructions pointersJumpProgram (clearedSetupStateSq s mem hd pb n dst ret rest) =
      some (outState s (SquarePartialClear.memory mem) pb n 0 hd (UInt256.ofNat 3562) dst ret rest) := by
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hsum : UInt256.ofNat pb + UInt256.ofNat (32 * n) = UInt256.ofNat (pb + 32 * n) :=
    Challenge.EvmProof.Word.ofNat_add_mod pb (32 * n)
  have hend : negative32 + UInt256.ofNat (pb + 32 * n) = UInt256.ofNat (pb + 32 * n - 32) :=
    negative32_add_ofNat (pb + 32 * n) (by omega) (by omega)
  have hlow : negative32 + UInt256.ofNat pb = UInt256.ofNat (pb - 32) :=
    negative32_add_ofNat pb hpb (by omega)
  have hsumLow : UInt256.ofNat (pb - 32) + UInt256.ofNat (32 * n) =
      UInt256.ofNat (pb + 32 * n - 32) := by
    rw [Challenge.EvmProof.Word.ofNat_add_mod]
    congr 1
    omega
  simp only [clearedSetupStateSq, outState,
    SquarePartialClear.readWord_outside mem 128 (Or.inl (by decide))]
  simp [pointersJumpProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    clearedSetupStateSq, outState, ← negative32_not, hc9, hc10, hc11, hc12, htarget, hsum, hend, hlow, hsumLow,
    ptrAt_zero, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod]
  simp only [show UInt256.lnot (31 : UInt256) = negative32 by decide,
    hlow, hsumLow, and_self]

end Challenge.Modexp.Submission.Proofs.Fast.TnM128Setup
