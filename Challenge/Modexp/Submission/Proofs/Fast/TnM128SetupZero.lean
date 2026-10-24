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

def stageProgram : List Instr :=
  [.push 2 2688, .op .MLOAD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op .ADD, .push 2 1856, .op .ADD,
   .op .MCOPY]

def clearProgram : List Instr := [.push 0 0, .push 2 2048, .op .MSTORE]

def zeroProgram : List Instr := stageProgram ++ clearProgram

def cachedSetupState (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (w5 dst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3226
           stack := [hd, UInt256.ofNat pa, UInt256.ofNat pb,
             l1Target n, w5, allOnes, MachineState.readWord mem 128, dst, ret] ++ rest
           memory := mem }

def stagedSetupState (s : State) (mem : ByteArray) (hd : UInt256) (pb n : Nat)
    (ent w5 dst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3240
           stack := [hd, UInt256.ofNat (32*n), UInt256.ofNat pb,
             ent, w5, allOnes, MachineState.readWord mem 128, dst, ret] ++ rest
           memory := mem }

def clearedSetupState (s : State) (mem : ByteArray) (hd : UInt256) (pb n : Nat)
    (w5 dst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3245
           stack := [hd, UInt256.ofNat (32*n), UInt256.ofNat pb,
             l1Target n, w5, allOnes, MachineState.readWord mem 128, dst, ret] ++ rest
           memory := SquarePartialClear.memory mem }

theorem run_stageGen (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (ent w5 dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hact : 88 ≤ s.activeWords.toNat) (hnpos : 0 < n) (hn : n ≤ 8) (hpa : pa+32*n ≤ 2816)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n)) :
    runInstructions stageProgram
      { s with pc := UInt256.ofNat 3226
               stack := [hd, UInt256.ofNat pa, UInt256.ofNat pb,
                 ent, w5, allOnes, MachineState.readWord mem 128, dst, ret] ++ rest
               memory := mem } =
      some (stagedSetupState s (stageW mem pa n) hd pb n ent w5 dst ret rest) := by
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  have hc13 : rest.length+13 < 1024 := by omega
  have hpaN : pa % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa := Nat.mod_eq_of_lt (by omega)
  have hszN : (32*n) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 32*n := Nat.mod_eq_of_lt (by omega)
  have hdst : UInt256.ofNat 1856 + (UInt256.ofNat (32*n) + UInt256.ofNat (32*n)) =
      UInt256.ofNat (1856 + 64*n) := by
    rw [Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.ofNat_add_mod]
    congr 1
    omega
  have hdstN : (1856 + 64*n) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 1856 + 64*n := Nat.mod_eq_of_lt (by omega)
  have hactS := activeWords_fix s 2688 32 (by decide) (by omega) hact
  have hactD := activeWordsAfter_fix s.activeWords.toNat (1856 + 64*n) (32*n) (by omega) (by omega) hact
  have hactA := activeWordsAfter_fix s.activeWords.toNat pa (32*n) (by omega) (by omega) hact
  have h2688 : (2688 : UInt256).toNat = 2688 := by decide
  have h1856 : (1856 : UInt256) = UInt256.ofNat 1856 := by decide
  simp only [stagedSetupState,
    read_stageW_outside mem pa n 128 (Or.inl (by omega))]
  simp [stageProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    stageW, hs32, State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
    hactS, hactD, hactA, h2688, h1856, hdst, hdstN,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hpaN, hszN,
    hc9, hc10, hc11, hc12, hc13, List.exchange]
  exact ⟨(Challenge.EvmProof.Word.word_eq_ofNat_toNat s.activeWords).symm, by decide⟩

theorem run_clearGen (s : State) (mem : ByteArray) (hd : UInt256) (pb n : Nat)
    (ent w5 dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions clearProgram (stagedSetupState s mem hd pb n ent w5 dst ret rest) =
      some { stagedSetupState s (SquarePartialClear.memory mem) hd pb n ent w5 dst ret rest with
        pc := UInt256.ofNat 3245 } := by
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
    (w5 dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hact : 88 ≤ s.activeWords.toNat) (hnpos : 0 < n) (hn : n ≤ 8) (hpa : pa+32*n ≤ 2816)
    (_hcds : s.executionEnv.calldata.size < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n)) :
    runInstructions zeroProgram (cachedSetupState s mem hd pa pb n w5 dst ret rest) =
      some (clearedSetupState s (stageW mem pa n) hd pb n w5 dst ret rest) := by
  have h1 := run_stageGen s mem hd pa pb n (l1Target n) w5 dst ret rest hcap hact hnpos hn hpa hs32
  have h2 := run_clearGen s (stageW mem pa n) hd pb n (l1Target n) w5 dst ret rest hcap hact
  have h := runInstructions_append_some _ _ _ _ _ h1 h2
  simpa only [zeroProgram, cachedSetupState, stagedSetupState, clearedSetupState,
    SquarePartialClear.readWord_outside _ 128 (Or.inl (by decide))] using h

def cachedSetupStateSq (s : State) (mem : ByteArray) (hd : UInt256) (pa pb _n : Nat)
    (w5 dst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3226
           stack := [hd, UInt256.ofNat pa, UInt256.ofNat pb,
             UInt256.ofNat 3347, w5, allOnes, MachineState.readWord mem 128, dst, ret] ++ rest
           memory := mem }

def clearedSetupStateSq (s : State) (mem : ByteArray) (hd : UInt256) (pb n : Nat)
    (w5 dst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3245
           stack := [hd, UInt256.ofNat (32*n), UInt256.ofNat pb,
             UInt256.ofNat 3347, w5, allOnes, MachineState.readWord mem 128, dst, ret] ++ rest
           memory := SquarePartialClear.memory mem }

theorem run_zero_sq (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (w5 dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hact : 88 ≤ s.activeWords.toNat) (hnpos : 0 < n) (hn : n ≤ 8) (hpa : pa+32*n ≤ 2816)
    (_hcds : s.executionEnv.calldata.size < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n)) :
    runInstructions zeroProgram (cachedSetupStateSq s mem hd pa pb n w5 dst ret rest) =
      some (clearedSetupStateSq s (stageW mem pa n) hd pb n w5 dst ret rest) := by
  have h1 := run_stageGen s mem hd pa pb n (UInt256.ofNat 3347) w5 dst ret rest hcap hact hnpos hn hpa hs32
  have h2 := run_clearGen s (stageW mem pa n) hd pb n (UInt256.ofNat 3347) w5 dst ret rest hcap hact
  have h := runInstructions_append_some _ _ _ _ _ h1 h2
  simpa only [zeroProgram, cachedSetupStateSq, stagedSetupState, clearedSetupStateSq,
    SquarePartialClear.readWord_outside _ 128 (Or.inl (by decide))] using h

def preclearProgram : List Instr :=
  [.op .JUMPDEST, .push 2 2688, .op .MLOAD, .push 1 64, .op .ADD, .op .CALLDATASIZE,
   .push 2 2048, .op .CALLDATACOPY, .push 2 3181, .op .JUMP]

theorem run_preclear (s : State) (mem : ByteArray) (n : Nat) (st : List UInt256)
    (hcap : st.length ≤ 1010)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8)
    (hcds : s.executionEnv.calldata.size < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n))
    (hjump : Decode.isValidJumpDest s.executionEnv.code 3181 = true) :
    runInstructions preclearProgram { s with pc := UInt256.ofNat 5466, stack := st, memory := mem } =
      some { s with pc := UInt256.ofNat 3181, stack := st, memory := mpZeroed s mem n } := by
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
  have h3383 : (3181 : UInt256).toNat = 3181 := by decide
  have h64 : (64 : UInt256) = UInt256.ofNat 64 := by decide
  simp (config := { maxSteps := 200000 }) [preclearProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    mpZeroed, hs32, hjump, h3383,
    State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2, hactS, hactC,
    h9344, h8192, h64, hactN,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hsizeN, hcdsN,
    hc0, hc1, hc2, hc3, hc4, List.exchange]
  decide

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

theorem run_pointersJump (s : State) (mem : ByteArray) (hd : UInt256) (pb n : Nat)
    (w5 dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 2816) (hn : n ≤ 8)
    (htarget : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    runInstructions pointersJumpProgram (clearedSetupState s mem hd pb n w5 dst ret rest) =
      some (outState s (SquarePartialClear.memory mem) pb n 0 hd (l1Target n) w5 dst ret rest) := by
  have capacity (j : Nat) (hj : j ≤ 12) : rest.length + j < 1024 := by omega
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
    clearedSetupState, outState, ← negative32_not, capacity, Nat.add_assoc, htarget, hsum, hend, hlow, hsumLow,
    ptrAt_zero, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod]
  simp only [show UInt256.lnot (31 : UInt256) = negative32 by decide,
    hlow, hsumLow, and_self]

theorem run_pointersJump_sq (s : State) (mem : ByteArray) (hd : UInt256) (pb n : Nat)
    (w5 dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 2816) (hn : n ≤ 8)
    (htarget : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    runInstructions pointersJumpProgram (clearedSetupStateSq s mem hd pb n w5 dst ret rest) =
      some (outState s (SquarePartialClear.memory mem) pb n 0 hd (UInt256.ofNat 3347) w5 dst ret rest) := by
  have capacity (j : Nat) (hj : j ≤ 12) : rest.length + j < 1024 := by omega
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
    clearedSetupStateSq, outState, ← negative32_not, capacity, Nat.add_assoc, htarget, hsum, hend, hlow, hsumLow,
    ptrAt_zero, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod]
  simp only [show UInt256.lnot (31 : UInt256) = negative32 by decide,
    hlow, hsumLow, and_self]

end Challenge.Modexp.Submission.Proofs.Fast.TnM128Setup
