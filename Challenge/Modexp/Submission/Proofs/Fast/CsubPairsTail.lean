import Challenge.Modexp.Submission.Proofs.Fast.CsubPairsCore

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CsubPairsTail

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast.Csub
open Challenge.Modexp.Submission.Proofs.Fast.CsubPairsCore

def tailProgram : List Instr :=
  [Instr.op .POP, Instr.op .ISZERO, Instr.push 2 8224, Instr.op .MLOAD, Instr.op .OR,
   Instr.push 32 115792089237316195423570985008687907853269984665640564039457584007913129638848,
   Instr.op .MUL, Instr.push 2 8256, Instr.op .ADD, Instr.push 2 9344,
   Instr.op .MLOAD, Instr.op (.Swap ⟨1, by decide⟩), Instr.op .MCOPY, Instr.op .JUMP]

set_option linter.unusedSimpArgs false in
theorem run_tail (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hjump : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true)
    (hs32 : MachineState.readWord (csStep memory n (j + 1)).memory 9344 =
      UInt256.ofNat (32 * n))
    (hdstFit : pdst.toNat + 32 * n ≤ 9472)
    (hsrcFit : (csSrc memory n (j + 1)).toNat + 32 * n ≤ 9472) :
    runRaw tailProgram
      (walkState 2500 s memory n (j + 1) pdst ret rest) =
      some (csReturnedState s memory n (j + 1) pdst ret rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  have hsz : 32 * n %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * n := Nat.mod_eq_of_lt (by omega)
  have hactN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 8224 32) =
      s.activeWords := activeWords_fix s 8224 32 (by decide) (by omega) hact
  have hactS : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9344 32) =
      s.activeWords := activeWords_fix s 9344 32 (by decide) (by omega) hact
  have hactC1 : MachineState.activeWordsAfter s.activeWords.toNat pdst.toNat (32 * n) =
      s.activeWords.toNat :=
    activeWordsAfter_fix s.activeWords.toNat pdst.toNat (32 * n) (by omega) (by omega) hact
  have hactC2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (csSrc memory n (j + 1)).toNat (32 * n)) = s.activeWords :=
    activeWords_fix s _ (32 * n) (by omega) (by omega) hact
  have hsrcEq : (8256 : UInt256) +
      (115792089237316195423570985008687907853269984665640564039457584007913129638848 :
        UInt256) *
        UInt256.lor (MachineState.readWord (csStep memory n (j + 1)).memory 8224)
          (UInt256.isZero (csStep memory n (j + 1)).flag) = csSrc memory n (j + 1) := rfl
  /- The `MCOPY` source address in the distributed `toNat` normal form
  simp produces (with `lnot 1087` unreduced). -/
  have hsrcToNat : (UInt256.toNat 8256 +
      ((115792089237316195423570985008687907853269984665640564039457584007913129638848 : UInt256) *
        UInt256.lor (MachineState.readWord (csStep memory n (j + 1)).memory 8224)
          (UInt256.isZero (csStep memory n (j + 1)).flag)).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      (csSrc memory n (j + 1)).toNat := by
    have h256 : (2 ^ 256 : Nat) =
        115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      decide
    rw [← h256, ← Challenge.EvmProof.Word.word_toNat_add, hsrcEq]
  simp (config := { maxSteps := 400000 })
    [tailProgram, runRaw,
      Challenge.EvmProof.Stepper.runInstr,
      walkState, csReturnedState, hsrcEq, hsrcToNat,
      hc1, hc2, hc3, hc4, hc5, hc6, hrun, h8224, h9344, hjump, hs32,
      hsz, hactN, hactS, hactC1, hactC2,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

end Challenge.Modexp.Submission.Proofs.Fast.CsubPairsTail
