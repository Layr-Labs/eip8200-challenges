import Challenge.Modexp.Submission.Proofs.Fast.R4InlineBlocks
import Challenge.Modexp.Submission.Proofs.Fast.SquareRow
import Challenge.Modexp.Submission.Proofs.Fast.R4RetainedMemory
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Modexp.Submission.Proofs.Fast.R4InlineTrace
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open R4Math R4Blocks R4Runs R4Bridge R4InlineBlocks R4InlineTransport
open Challenge.EvmProof (GasSteps)
def win0 (W : W5) (tail : List UInt256) : List UInt256 := W.t3 :: W.t2 :: W.t1 :: W.t0 :: W.t4 :: tail

def win1 (W : W5) (tail : List UInt256) : List UInt256 := W.t2 :: W.t1 :: W.t0 :: W.t3 :: W.t4 :: tail

def win2 (W : W5) (tail : List UInt256) : List UInt256 := W.t1 :: W.t0 :: W.t3 :: W.t2 :: W.t4 :: tail

def win3 (W : W5) (tail : List UInt256) : List UInt256 := W.t0 :: W.t3 :: W.t2 :: W.t1 :: W.t4 :: tail
def gasSteps_sgtAt (idx pcN : Nat)
    (hidx : Artifact.submissionInstructions[idx]? = some (.op .SGT))
    (hpcI : Artifact.submissionArtifact.instructionPC idx = pcN) (hlt : pcN + 1 < 2 ^ 256)
    (s : State) (a b : UInt256) (rest : List UInt256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hcap : rest.length ≤ 1021) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps { s with pc := UInt256.ofNat pcN, stack := a :: b :: rest }
      { s with pc := UInt256.ofNat (pcN + 1), stack := UInt256.sgt a b :: rest } := by
  have hpcNat : ({ s with pc := UInt256.ofNat pcN, stack := a :: b :: rest } : State).pc.toNat =
      Artifact.submissionArtifact.instructionPC idx := by
    rw [hpcI]
    show (UInt256.ofNat pcN).toNat = pcN
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hwf : Challenge.EvmProof.Stepper.WellFormed
      ({ s with pc := UInt256.ofNat pcN, stack := a :: b :: rest } : State).fork (.op .SGT) := by
    show Challenge.EvmProof.Stepper.WellFormed s.fork (.op .SGT)
    rw [hfork]
    exact ⟨by decide, trivial, rfl⟩
  have hop := Challenge.EvmProof.Stepper.decodes_of_artifact Artifact.submissionArtifact
    { s with pc := UInt256.ofNat pcN, stack := a :: b :: rest } idx (.op .SGT) hcode hpcNat hidx hwf
  have hcap' : ({ s with pc := UInt256.ofNat pcN, stack := a :: b :: rest } : State).stack.length +
      Operation.pushArity .SGT ≤ 1024 + Operation.popArity .SGT := by
    show (a :: b :: rest).length + Operation.pushArity .SGT ≤ 1024 + Operation.popArity .SGT
    simp only [List.length_cons, Operation.pushArity, Operation.popArity]
    omega
  have h := SgtStep.gasStep_sgt hop rfl hcap' hrun hnp
  exact h.cast rfl (by rw [Challenge.EvmProof.Word.succ_ofNat_mod])

/-! Composition helpers. -/

set_option hygiene false in
/-- Connect a checked symbolic block to the remaining execution. -/
local macro "seg " blk:term:max run:term : tactic =>
  `(tactic| refine GasSteps.trans
      (SquareRow.stepsOf $blk $run rfl hcode hfork hrun hnp) ?_)

local macro "lenOK" : tactic =>
  `(tactic| ((try simp only [List.length_cons, List.length_append, win0, win1, win2, win3] at *) <;> omega))

theorem jd5158 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4621 = true :=
  Artifact.isValidJumpDest_index 3629 (by rfl)

theorem jd4903 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (4382 : UInt256).toNat = true :=
  Artifact.isValidJumpDest_index 3418 (by rfl)

theorem jd5020 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (4494 : UInt256).toNat = true :=
  Artifact.isValidJumpDest_index 3518 (by rfl)

theorem jd5108 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (4577 : UInt256).toNat = true :=
  Artifact.isValidJumpDest_index 3591 (by rfl)

theorem jd5274 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (4725 : UInt256).toNat = true :=
  Artifact.isValidJumpDest_index 3733 (by rfl)

theorem jd4248 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3999 = true :=
  Artifact.isValidJumpDest_index 3131 (by rfl)

section
variable (s : State)
  (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
  (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
  (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false)

include hcode hfork hrun hnp

def gasSteps_red0 (ret v : UInt256) (P : W5) (k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1003)
    (hjd : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true)
    (hk : k = Monpro.maxWord)
    (hminv : (n0.toNat * np.toNat + 1) % 2^256 = 0)
    (hguard : np ≠ UInt256.ofNat 1) :
    GasSteps { s with pc := UInt256.ofNat 9093,
                      stack := v :: win0 P (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) }
      { s with pc := UInt256.ofNat 9188,
               stack := win1 (red n0 n1 n2 n3 np k P v) (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) } := by
  simp only [win0, win1]
  seg block_redm_0 (run_redm_0 s ret v P.t3 P.t2 P.t1 P.t0 P.t4 k n0 n1 n2 n3 np rest (by omega) hk hminv hguard)
  seg block_reds1_0 (run_reds1_0 s _ _ ret (hcap := by lenOK) ..)
  seg block_reds2_0 (run_reds2_0 s _ _ ret (hcap := by lenOK) ..)
  seg block_reds3_0 (run_reds3_0 s _ _ ret (hcap := by lenOK) ..)
  exact SquareRow.stepsOf block_redt_0 (run_redt_0 s _ _ ret (hcap := by lenOK) (hjd := hjd) ..) rfl
    hcode hfork hrun hnp


def gasSteps_red1 (ret v : UInt256) (P : W5) (k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1003)
    (hjd : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true)
    (hk : k = Monpro.maxWord)
    (hminv : (n0.toNat * np.toNat + 1) % 2^256 = 0)
    (hguard : np ≠ UInt256.ofNat 1) :
    GasSteps { s with pc := UInt256.ofNat 9290,
                      stack := v :: win1 P (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) }
      { s with pc := UInt256.ofNat 9385,
               stack := win2 (red n0 n1 n2 n3 np k P v) (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) } := by
  simp only [win1, win2]
  seg block_redm_1 (run_redm_1 s ret v P.t3 P.t2 P.t1 P.t0 P.t4 k n0 n1 n2 n3 np rest (by omega) hk hminv hguard)
  seg block_reds1_1 (run_reds1_1 s _ _ ret (hcap := by lenOK) ..)
  seg block_reds2_1 (run_reds2_1 s _ _ ret (hcap := by lenOK) ..)
  seg block_reds3_1 (run_reds3_1 s _ _ ret (hcap := by lenOK) ..)
  exact SquareRow.stepsOf block_redt_1 (run_redt_1 s _ _ ret (hcap := by lenOK) (hjd := hjd) ..) rfl
    hcode hfork hrun hnp


def gasSteps_red2 (ret v : UInt256) (P : W5) (k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1003)
    (hjd : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true)
    (hk : k = Monpro.maxWord)
    (hminv : (n0.toNat * np.toNat + 1) % 2^256 = 0)
    (hguard : np ≠ UInt256.ofNat 1) :
    GasSteps { s with pc := UInt256.ofNat 9458,
                      stack := v :: win2 P (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) }
      { s with pc := UInt256.ofNat 9553,
               stack := win3 (red n0 n1 n2 n3 np k P v) (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) } := by
  simp only [win2, win3]
  seg block_redm_2 (run_redm_2 s ret v P.t3 P.t2 P.t1 P.t0 P.t4 k n0 n1 n2 n3 np rest (by omega) hk hminv hguard)
  seg block_reds1_2 (run_reds1_2 s _ _ ret (hcap := by lenOK) ..)
  seg block_reds2_2 (run_reds2_2 s _ _ ret (hcap := by lenOK) ..)
  seg block_reds3_2 (run_reds3_2 s _ _ ret (hcap := by lenOK) ..)
  exact SquareRow.stepsOf block_redt_2 (run_redt_2 s _ _ ret (hcap := by lenOK) (hjd := hjd) ..) rfl
    hcode hfork hrun hnp


def gasSteps_red3 (ret v : UInt256) (P : W5) (k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1003)
    (hjd : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true)
    (hk : k = Monpro.maxWord)
    (hminv : (n0.toNat * np.toNat + 1) % 2^256 = 0)
    (hguard : np ≠ UInt256.ofNat 1) :
    GasSteps { s with pc := UInt256.ofNat 9593,
                      stack := v :: win3 P (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) }
      { s with pc := UInt256.ofNat 9688,
               stack := win0 (red n0 n1 n2 n3 np k P v) (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) } := by
  simp only [win3, win0]
  seg block_redm_3 (run_redm_3 s ret v P.t3 P.t2 P.t1 P.t0 P.t4 k n0 n1 n2 n3 np rest (by omega) hk hminv hguard)
  seg block_reds1_3 (run_reds1_3 s _ _ ret (hcap := by lenOK) ..)
  seg block_reds2_3 (run_reds2_3 s _ _ ret (hcap := by lenOK) ..)
  seg block_reds3_3 (run_reds3_3 s _ _ ret (hcap := by lenOK) ..)
  exact SquareRow.stepsOf block_redt_3 (run_redt_3 s _ _ ret (hcap := by lenOK) (hjd := hjd) ..) rfl
    hcode hfork hrun hnp


def gasSteps_row0 (k n0 n1 n2 n3 np a0 a1 a2 a3 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1003) (hact : 88 ≤ s.activeWords.toNat)
    (_ha0 : MachineState.readWord s.memory 2208 = a0)
    (ha1 : MachineState.readWord s.memory 2176 = a1)
    (ha2 : MachineState.readWord s.memory 2144 = a2)
    (ha3 : MachineState.readWord s.memory 2112 = a3) :
    GasSteps { s with pc := UInt256.ofNat 9021, stack := dHi a0 k :: (a0 * a0) :: (a0 + a0) :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest }
      { s with pc := UInt256.ofNat 9093,
               stack := (⟨0⟩ : UInt256) ::
                 win0 (row0 a0 a1 a2 a3 k) (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) } := by
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4621 = true := by rw [hcode]; exact jd5158
  simp only [win0]
  seg block_r0z1_0 (run_r0z1_0 s (hcap := by lenOK) (ha1 := ha1) (hact := hact) ..)
  seg block_r0z2_0 (run_r0z2_0 s (hcap := by lenOK) (ha2 := ha2) (hact := hact) ..)
  seg block_r0z3_0 (run_r0z3_0 s (hcap := by lenOK) (ha3 := ha3) (hact := hact) ..)
  exact SquareRow.stepsOf block_r0e_0 (run_r0e_0 s (hcap := by lenOK) (hjd := hjd) ..) rfl
    hcode hfork hrun hnp

def gasSteps_row1 (P : W5) (k n0 n1 n2 n3 np a0 a1 a2 a3 : UInt256) (rest : List UInt256) (hk : k = Monpro.maxWord)
    (hcap : rest.length ≤ 1003) (hact : 88 ≤ s.activeWords.toNat)
    (ha0 : MachineState.readWord s.memory 2208 = a0)
    (ha1 : MachineState.readWord s.memory 2176 = a1)
    (ha2 : MachineState.readWord s.memory 2144 = a2)
    (ha3 : MachineState.readWord s.memory 2112 = a3) :
    GasSteps { s with pc := UInt256.ofNat 9188, stack := win1 P (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) }
      { s with pc := UInt256.ofNat 9290,
               stack := (row1 a0 a1 a2 a3 k P).2 ::
                 win1 (row1 a0 a1 a2 a3 k P).1 (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) } := by
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4621 = true := by rw [hcode]; exact jd5158
  simp only [win1]
  seg block_r1h_1 (run_r1h_1 s (hcap := by lenOK) (ha1 := ha1) (ha0 := ha0) (hact := hact) ..)
  refine GasSteps.trans (gasSteps_sgtAt 7128 9197 (by rfl) (R4InlineArtifactSuffix.pc 187 9197 rfl) (by norm_num) s _ _ _
    hcode hfork (by lenOK) hrun hnp) ?_
  seg block_r1d_1 (run_r1d_1 s (hcap := by lenOK) (hk := hk) (htb := R4Value.tb_le_one _) ..)
  seg block_r1c2_1 (run_r1c2_1 s (hcap := by lenOK) (ha2 := ha2) (hact := hact) ..)
  seg block_r1c3_1 (run_r1c3_1 s (hcap := by lenOK) (ha3 := ha3) (hact := hact) ..)
  exact SquareRow.stepsOf block_r1e_1 (run_r1e_1 s _ ((a1 + a1) + UInt256.sgt ⟨0⟩ a0) (hcap := by lenOK) (hjd := hjd) ..) rfl
    hcode hfork hrun hnp

def gasSteps_row2 (P : W5) (k n0 n1 n2 n3 np a1 a2 a3 : UInt256) (rest : List UInt256) (hk : k = Monpro.maxWord)
    (hcap : rest.length ≤ 1003) (hact : 88 ≤ s.activeWords.toNat)
    (ha1 : MachineState.readWord s.memory 2176 = a1)
    (ha2 : MachineState.readWord s.memory 2144 = a2)
    (ha3 : MachineState.readWord s.memory 2112 = a3) :
    GasSteps { s with pc := UInt256.ofNat 9385, stack := win2 P (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) }
      { s with pc := UInt256.ofNat 9458,
               stack := (row2 a1 a2 a3 k P).2 ::
                 win2 (row2 a1 a2 a3 k P).1 (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) } := by
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4621 = true := by rw [hcode]; exact jd5158
  simp only [win2]
  seg block_r2h_2 (run_r2h_2 s (hcap := by lenOK) (ha2 := ha2) (ha1 := ha1) (hact := hact) ..)
  refine GasSteps.trans (gasSteps_sgtAt 7317 9394 (by rfl) (R4InlineArtifactSuffix.pc 376 9394 rfl) (by norm_num) s _ _ _
    hcode hfork (by lenOK) hrun hnp) ?_
  seg block_r2d_2 (run_r2d_2 s (hcap := by lenOK) (hk := hk) (htb := R4Value.tb_le_one _) ..)
  seg block_r2c3_2 (run_r2c3_2 s (hcap := by lenOK) (ha3 := ha3) (hact := hact) ..)
  exact SquareRow.stepsOf block_r2e_2 (run_r2e_2 s _ ((a2 + a2) + UInt256.sgt ⟨0⟩ a1) (hcap := by lenOK) (hjd := hjd) ..) rfl
    hcode hfork hrun hnp

def gasSteps_row3 (P : W5) (k n0 n1 n2 n3 np a2 a3 : UInt256) (rest : List UInt256) (hk : k = Monpro.maxWord)
    (hcap : rest.length ≤ 1003) (hact : 88 ≤ s.activeWords.toNat)
    (ha2 : MachineState.readWord s.memory 2144 = a2)
    (ha3 : MachineState.readWord s.memory 2112 = a3) :
    GasSteps { s with pc := UInt256.ofNat 9553, stack := win3 P (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) }
      { s with pc := UInt256.ofNat 9593,
               stack := (row3 a2 a3 k P).2 ::
                 win3 (row3 a2 a3 k P).1 (k :: n0 :: n1 :: n2 :: n3 :: np :: rest) } := by
  simp only [win3]
  seg block_r3h_3 (run_r3h_3 s (hcap := by lenOK) (ha3 := ha3) (ha2 := ha2) (hact := hact) ..)
  refine GasSteps.trans (gasSteps_sgtAt 7479 9562 (by rfl) (R4InlineArtifactSuffix.pc 538 9562 rfl) (by norm_num) s _ _ _
    hcode hfork (by lenOK) hrun hnp) ?_
  seg block_r3d_3 (run_r3d_3 s (hcap := by lenOK) (hk := hk) (htb := R4Value.tb_le_one _) ..)
  exact SquareRow.stepsOf block_r3e_3 (run_r3e_3 s (hcap := by lenOK) ..) rfl hcode hfork hrun hnp


end
theorem run_entry (s : State) (rest : List UInt256) (hcap : rest.length ≤ 1022)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 8998 = true) :
    runInstructions entryProgram { s with pc := UInt256.ofNat 4280, stack := rest } =
      some { s with pc := UInt256.ofNat 8998, stack := rest } := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hpc : (8998 : UInt256).toNat = 8998 := rfl
  simp [entryProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, hc0, hc1, hpc, hjd]
  rfl

def gasSteps_entryBridge (s : State) (rest : List UInt256) (hcap : rest.length ≤ 1022)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps { s with pc := UInt256.ofNat 4280, stack := rest }
      { s with pc := UInt256.ofNat 8998, stack := rest } := by
  have hj : Decode.isValidJumpDest s.executionEnv.code 8998 = true := by rw [hcode]; exact validJump5615
  exact SquareRow.stepsOf block_entry (run_entry s rest hcap hj) rfl hcode hfork hrun hnp

def gasSteps_core (s : State) (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 990)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hk : e5 = Monpro.maxWord)
    (hminv : (e8.toNat * e11.toNat + 1) % 2^256 = 0)
    (hguard : e11 ≠ UInt256.ofNat 1) :
    GasSteps
      { s with pc := UInt256.ofNat 8998,
               stack := e8 :: e7 :: e4 :: MachineState.readWord s.memory 0 :: e11 :: e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: rest }
      { s with pc := UInt256.ofNat 9688,
               stack := win0 (r4Final s.memory e5 e8 e7 e4 e11)
                 (e5 :: e8 :: e7 :: e4 :: MachineState.readWord s.memory 0 :: e11 ::
                   e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: rest) } := by
  have hj (r : UInt256) (h : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode r.toNat = true) :
      Decode.isValidJumpDest s.executionEnv.code r.toNat = true := by rw [hcode]; exact h
  generalize ha0 : MachineState.readWord s.memory 2208 = a0
  generalize ha1 : MachineState.readWord s.memory 2176 = a1
  generalize ha2 : MachineState.readWord s.memory 2144 = a2
  generalize ha3 : MachineState.readWord s.memory 2112 = a3
  generalize hn3 : MachineState.readWord s.memory 0 = n3
  let E := e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: rest
  have hE : E.length ≤ 1003 := by simp only [E, List.length_cons]; omega
  let W1 := red e8 e7 e4 n3 e11 e5 (row0 a0 a1 a2 a3 e5) ⟨0⟩
  let R1 := row1 a0 a1 a2 a3 e5 W1
  let W2 := red e8 e7 e4 n3 e11 e5 R1.1 R1.2
  let R2 := row2 a1 a2 a3 e5 W2
  let W3 := red e8 e7 e4 n3 e11 e5 R2.1 R2.2
  let R3 := row3 a2 a3 e5 W3
  let W4 := red e8 e7 e4 n3 e11 e5 R3.1 R3.2
  have g0 := SquareRow.stepsOf block_prodiag_0
    (run_prodiag_0 s e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 n3 a0 rest (by omega) hn3 ha0 hact) rfl
    hcode hfork hrun hnp
  have g1 := gasSteps_row0 s hcode hfork hrun hnp e5 e8 e7 e4 n3 e11 a0 a1 a2 a3 E hE hact ha0 ha1 ha2 ha3
  have g2 := gasSteps_red0 s hcode hfork hrun hnp 4382 ⟨0⟩ (row0 a0 a1 a2 a3 e5) e5 e8 e7 e4 n3 e11 E hE
    (hj _ jd4903) hk hminv hguard
  have g3 := gasSteps_row1 (hk := hk) s hcode hfork hrun hnp W1 e5 e8 e7 e4 n3 e11 a0 a1 a2 a3 E hE hact ha0 ha1 ha2 ha3
  have g4 := gasSteps_red1 s hcode hfork hrun hnp 4494 R1.2 R1.1 e5 e8 e7 e4 n3 e11 E hE (hj _ jd5020) hk hminv hguard
  have g5 := gasSteps_row2 (hk := hk) s hcode hfork hrun hnp W2 e5 e8 e7 e4 n3 e11 a1 a2 a3 E hE hact ha1 ha2 ha3
  have g6 := gasSteps_red2 s hcode hfork hrun hnp 4577 R2.2 R2.1 e5 e8 e7 e4 n3 e11 E hE (hj _ jd5108) hk hminv hguard
  have g7 := gasSteps_row3 (hk := hk) s hcode hfork hrun hnp W3 e5 e8 e7 e4 n3 e11 a2 a3 E hE hact ha2 ha3
  have g8 := gasSteps_red3 s hcode hfork hrun hnp 4725 R3.2 R3.1 e5 e8 e7 e4 n3 e11 E hE (hj _ jd5274) hk hminv hguard
  refine (((((((((g0.trans g1).trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).cast rfl ?_)
  have hW : r4Final s.memory e5 e8 e7 e4 e11 = W4 := by
    simp only [r4Final, final, ha0, ha1, ha2, ha3, hn3, W4, R3, W3, R2, W2, R1, W1]
  rw [hW]

#print axioms gasSteps_core
end Challenge.Modexp.Submission.Proofs.Fast.R4InlineTrace
