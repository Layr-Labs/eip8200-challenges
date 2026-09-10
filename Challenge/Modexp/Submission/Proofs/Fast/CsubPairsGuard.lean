import Challenge.Modexp.Submission.Proofs.Fast.CsubPairsCore

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CsubPairsGuard

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast.Csub
open Challenge.Modexp.Submission.Proofs.Fast.CsubAffineStep
open Challenge.Modexp.Submission.Proofs.Fast.CsubPairsCore

def guardProgram : List Instr :=
  [Instr.push 2 8224, Instr.op (.Dup ⟨1, by decide⟩),
   Instr.op .GT, Instr.push 2 2241, Instr.op .JUMPI]

set_option linter.unusedSimpArgs false in
theorem run_guard (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hj : j ≤ n) (hn32 : n ≤ 32)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 2241 = true) :
    runRaw guardProgram (walkState 2491 s memory n j pdst ret rest) =
      some (walkState (if j < n then 2241 else 2500) s memory n j pdst ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have h2241 : (2241 : UInt256).toNat = 2241 := by decide
  have hpt : (UInt256.ofNat (affinePt n j)).toNat = affinePt n j := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]
    exact affinePt_lt_word n j hn32 hj
  have hlt : (8224 < affinePt n j) = (j < n) := by
    apply propext
    unfold affinePt
    omega
  have hcond : (UInt256.gt (UInt256.ofNat (affinePt n j)) (8224 : UInt256)).isTrue =
      decide (j < n) := by
    simp [UInt256.gt, UInt256.lt, UInt256.isTrue, hpt, h8224, hlt]
    split <;> simp_all [UInt256.ofNat, UInt256.toNat, UInt256.size]
  by_cases hmore : j < n <;> simp (config := { maxSteps := 400000 })
    [runRaw, guardProgram, Challenge.EvmProof.Stepper.runInstr,
      walkState, hc4, hc5, hc6, hrun, h2241, hcond, hmore, hjump,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Nat.mod_eq_of_lt, List.exchange]
  all_goals decide

def pairProgram : List Instr := limbProgram ++ limbProgram ++ guardProgram

theorem run_pair (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) (hj : j + 2 ≤ n) (hn32 : n ≤ 32)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 2241 = true) :
    runRaw pairProgram (walkState 2241 s memory n j pdst ret rest) =
      some (walkState (if j + 2 < n then 2241 else 2500)
        s memory n (j + 2) pdst ret rest) := by
  have h1 := run_limb true s memory n j pdst ret rest hcap hrun hact (by omega) hn32
  have h2 := run_limb false s memory n (j + 1) pdst ret rest hcap hrun hact (by omega) hn32
  have h12 := runRaw_append limbProgram limbProgram _ _ _ h1 hrun h2
  have h3 := run_guard s memory n (j + 2) pdst ret rest hcap hrun hj hn32 hjump
  exact runRaw_append (limbProgram ++ limbProgram) guardProgram _ _ _ h12 hrun h3

theorem run_oddPeel (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 2241 = true) :
    runRaw (limbProgram ++ guardProgram) (walkState 2366 s memory n 0 pdst ret rest) =
      some (walkState 2241 s memory n 1 pdst ret rest) := by
  have h1 := run_limb false s memory n 0 pdst ret rest hcap hrun hact (by omega) hn32
  have h2 := run_guard s memory n 1 pdst ret rest hcap hrun (by omega) hn32 hjump
  have h12 := runRaw_append limbProgram guardProgram _ _ _ h1 hrun h2
  simpa [limbPC, show 1 < n by omega] using h12


end Challenge.Modexp.Submission.Proofs.Fast.CsubPairsGuard
