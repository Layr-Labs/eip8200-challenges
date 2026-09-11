import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandMemory
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.StagedOperand

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached

/-- Stage the first operand at 8960 (`MCOPY`) and zero the scratch block (`CALLDATACOPY`
from the end of calldata), keeping `hd` on top: pc 4006 → 4026. -/
def zeroProgram : List Instr :=
  [.push 2 9344, .op .MLOAD, .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨0, by decide⟩), .push 2 8960, .op .MCOPY,
   .op (.Dup ⟨1, by decide⟩), .push 1 64, .op .ADD, .op .CALLDATASIZE,
   .push 2 8192, .op .CALLDATACOPY]

/-- After `lowProgram`: `hd` above the operand pointers and the row frame. -/
def cachedSetupState (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4006
           stack := [hd, UInt256.ofNat pa, UInt256.ofNat pb,
             l1Target n, negative32, allOnes, l2Target n, dst, ret] ++ rest
           memory := mem }

/-- After staging and zeroing: `hd` above the width word. -/
def clearedSetupState (s : State) (mem : ByteArray) (hd : UInt256) (pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4026
           stack := [hd, UInt256.ofNat (32*n), UInt256.ofNat pb,
             l1Target n, negative32, allOnes, l2Target n, dst, ret] ++ rest
           memory := mpZeroed s mem n }

theorem run_zero (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hact : 296 ≤ s.activeWords.toNat) (hnpos : 0 < n) (hn : n ≤ 8) (hpa : pa+32*n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n)) :
    runInstructions zeroProgram (cachedSetupState s mem hd pa pb n dst ret rest) =
      some (clearedSetupState s (stage mem pa n) hd pb n dst ret rest) := by
  have hc8 : rest.length+8 < 1024 := by omega
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  have hc13 : rest.length+13 < 1024 := by omega
  have hc14 : rest.length+14 < 1024 := by omega
  have hpaN : pa % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa := Nat.mod_eq_of_lt (by omega)
  have hszN : (32*n) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 32*n := Nat.mod_eq_of_lt (by omega)
  have hsizeN : (64+32*n) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 64+32*n := Nat.mod_eq_of_lt (by omega)
  have hcdsN : s.executionEnv.calldata.size % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = s.executionEnv.calldata.size :=
    Nat.mod_eq_of_lt hcds
  have hactS := activeWords_fix s 9344 32 (by decide) (by omega) hact
  have hactC := activeWords_fix s 8192 (64+32*n) (by omega) (by omega) hact
  have hactD := activeWordsAfter_fix s.activeWords.toNat 8960 (32*n) (by omega) (by omega) hact
  have hactA := activeWordsAfter_fix s.activeWords.toNat pa (32*n) (by omega) (by omega) hact
  have hactN : s.activeWords.toNat % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = s.activeWords.toNat :=
    Nat.mod_eq_of_lt s.activeWords.val.isLt
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  have h8960 : (8960 : UInt256).toNat = 8960 := by decide
  have h8192 : (8192 : UInt256).toNat = 8192 := by decide
  have h64 : (64 : UInt256) = UInt256.ofNat 64 := by decide
  simp (config := { maxSteps := 200000 }) [zeroProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    cachedSetupState, clearedSetupState, stage, mpZeroed, hs32,
    State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2, hactS, hactC, hactD, hactA,
    h9344, h8960, h8192, h64, hactN,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hpaN, hszN, hsizeN, hcdsN,
    hc8, hc9, hc10, hc11, hc12, hc13, hc14, List.exchange]

/-- Operand pointers and the jump to the row head (pc 4026 → `hd`):
`SWAP1; DUP3; ADD; DUP5; ADD; SWAP2; DUP5; ADD; SWAP2; DUP2; JUMP`. -/
def pointersJumpProgram : List Instr :=
  [.op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .ADD,
   .op (.Dup ⟨4, by decide⟩), .op .ADD, .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .ADD, .op (.Swap ⟨1, by decide⟩),
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
(the row head: 4037 for the multiply, 4710 for the square). -/
theorem run_pointersJump (s : State) (mem : ByteArray) (hd : UInt256) (pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (htarget : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    runInstructions pointersJumpProgram (clearedSetupState s mem hd pb n dst ret rest) =
      some (outState s (mpZeroed s mem n) pb n 0 hd (l1Target n) dst ret rest) := by
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
  simp [pointersJumpProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    clearedSetupState, outState, hc9, hc10, hc11, hc12, htarget, hsum, hend, hlow,
    ptrAt_zero, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod]

end Challenge.Modexp.Submission.Proofs.Fast.StagedOperand
