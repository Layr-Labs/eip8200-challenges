import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftTrace2
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace CycleSubmission.Global.Fast.Shift.RepairFour
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Shift
open CycleSubmission.Global.Fast CycleSubmission.Global.Fast.Shift

def bodyProgram : List Instr :=
 [.op (.Dup ⟨0, by decide⟩), .op .MLOAD, .push 2 2112,
  .op (.Dup ⟨2, by decide⟩), .op .SUB, .op .MLOAD,
  .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨0, by decide⟩),
  .op (.Dup ⟨1, by decide⟩), .op .LT, .op (.Swap ⟨0, by decide⟩),
  .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Swap ⟨2, by decide⟩),
  .op (.Dup ⟨3, by decide⟩), .op .LT, .op .OR,
  .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .MSTORE]

theorem run_body (pc : Nat) (s : State) (mem : ByteArray) (p : UInt256) (n bsize esize msize k j : Nat)
    (rest : List UInt256)
    (hn32 : n ≤ 8) (hj : j < n) (hpv : p.toNat = 2112 + 32 * (n - 1 - j))
    (hcap : rest.length ≤ 1011)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    runInstructions bodyProgram
      { s with pc := UInt256.ofNat pc
               stack := p :: (addStep mem n j).flag :: UInt256.ofNat k :: rest
               memory := (addStep mem n j).memory } =
      some { s with pc := UInt256.ofNat (pc + 23)
                    stack := p :: (addStep mem n (j + 1)).flag :: UInt256.ofNat k :: rest
                    memory := (addStep mem n (j + 1)).memory } := by
  have hg3 : rest.length + 3 < 1024 := by omega
  have hg4 : rest.length + 4 < 1024 := by omega
  have hg5 : rest.length + 5 < 1024 := by omega
  have hg6 : rest.length + 6 < 1024 := by omega
  have hg7 : rest.length + 7 < 1024 := by omega
  have hg8 : rest.length + 8 < 1024 := by omega
  have hg9 : rest.length + 9 < 1024 := by omega
  have hg10 : rest.length + 10 < 1024 := by omega
  have hg11 : rest.length + 11 < 1024 := by omega
  have hg12 : rest.length + 12 < 1024 := by omega
  have hsub : (115792089237316195423570985008687907853269984665640564039457584007913129639936 + (2112 + 32 * (n - 1 - j)) - 2112) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 32 * (n - 1 - j) := by
    rw [show 115792089237316195423570985008687907853269984665640564039457584007913129639936 + (2112 + 32 * (n - 1 - j)) - 2112 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 + 32 * (n - 1 - j) by omega,
      Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (2112 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactM : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (32 * (n - 1 - j)) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 600000 })
    [bodyProgram, runInstructions,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      addStep,

      hcode, hrun, hpv, hsub, hactT, hactM,
      hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hg12,
      UInt256.gt, UInt256.lt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.ofNat_sub_ofNat, Nat.mod_eq_of_lt, List.exchange]

def cacheNat : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639904
def neg32 : UInt256 := UInt256.ofNat cacheNat
def stepProgram : List Instr := [.op (.Dup ⟨2, by decide⟩), .op .ADD]

theorem run_pointer (pc : Nat) (s : State) (mem : ByteArray) (p p' c : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1011) (hp : neg32 + p = p') :
    runInstructions stepProgram
      {s with pc := UInt256.ofNat pc, memory := mem, stack := p :: c :: neg32 :: rest} =
    some {s with pc := UInt256.ofNat (pc + 2), memory := mem, stack := p' :: c :: neg32 :: rest} := by
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  simp [stepProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    h3, h4, hp, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]

theorem ptrWord_step (base j : Nat) :
    neg32 + UInt256.ofNat (Monpro.ptrAt base j) = UInt256.ofNat (Monpro.ptrAt base (j + 1)) := by
  rw [neg32, cacheNat, Challenge.EvmProof.Word.ofNat_add_mod, Monpro.ptrAt_succ]

def limbState (pc : Nat) (s : State) (mem : ByteArray) (n j : Nat) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat pc, memory := (addStep mem n j).memory, stack := UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) j) ::
      (addStep mem n j).flag :: neg32 :: rest}

def limbProgram : List Instr := bodyProgram ++ stepProgram

theorem run_limb (pc : Nat) (s : State) (mem : ByteArray) (n j : Nat) (rest : List UInt256)
    (hn : n ≤ 8) (hj : j < n) (hcap : rest.length ≤ 1011)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    runInstructions limbProgram (limbState pc s mem n j rest) =
    some (limbState (pc + 25) s mem n (j + 1) rest) := by
  have hb := run_body pc s mem (UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) j))
    n 0 0 0 cacheNat j rest hn hj (CycleSubmission.Global.Fast.Shift.tPtr_toNat n j hn hj) hcap hact hcode hrun
  have hs := run_pointer (pc + 23) s (addStep mem n (j + 1)).memory
    (UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) j))
    (UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) (j + 1)))
    (addStep mem n (j + 1)).flag rest hcap (ptrWord_step _ _)
  simpa [limbProgram, limbState, neg32, cacheNat, Nat.add_assoc] using
    runInstructions_append_some _ _ _ _ _ hb hs

def fourProgram : List Instr :=
  ((limbProgram ++ limbProgram) ++ limbProgram) ++ limbProgram

theorem run_four (pc : Nat) (s : State) (mem : ByteArray) (n j : Nat) (rest : List UInt256)
    (hn : n ≤ 8) (hj : j + 4 ≤ n) (hcap : rest.length ≤ 1011)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    runInstructions fourProgram (limbState pc s mem n j rest) =
    some (limbState (pc + 100) s mem n (j + 4) rest) := by
  have h0 := run_limb pc s mem n j rest hn (by omega) hcap hact hcode hrun
  have h1 := run_limb (pc + 25) s mem n (j + 1) rest hn (by omega) hcap hact hcode hrun
  have h2 := run_limb (pc + 50) s mem n (j + 2) rest hn (by omega) hcap hact hcode hrun
  have h3 := run_limb (pc + 75) s mem n (j + 3) rest hn (by omega) hcap hact hcode hrun
  exact runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _
      (runInstructions_append_some _ _ _ _ _ h0 h1) h2) h3

def testProgram (target : Nat) : List Instr :=
  [.push 2 2111, .op (.Dup ⟨1, by decide⟩), .op .GT,
   .push 2 (UInt256.ofNat target), .op .JUMPI]

theorem run_test_go (pc target : Nat) (s : State) (mem : ByteArray) (p c : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1011)
    (htarget : target < 2^256)
    (hdest : Decode.isValidJumpDest s.executionEnv.code target = true)
    (hgt : 2111 < p.toNat) (hrun : s.halt = .Running) :
    runInstructions (testProgram target)
      {s with pc := UInt256.ofNat pc, memory := mem, stack := p :: c :: neg32 :: rest} =
    some {s with pc := UInt256.ofNat target, memory := mem, stack := p :: c :: neg32 :: rest} := by
  have capacity (j : Nat) (hj : j ≤ 6) : rest.length + j < 1024 := by omega
  have htmod : target % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = target := Nat.mod_eq_of_lt htarget
  simp [testProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    capacity, List.exchange, hrun, hgt, hdest, UInt256.gt, UInt256.isTrue,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    htmod, Nat.add_assoc]

theorem run_test_last (pc target : Nat) (s : State) (mem : ByteArray) (p c : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1011)
    (hle : p.toNat ≤ 2111) (hrun : s.halt = .Running) :
    runInstructions (testProgram target)
      {s with pc := UInt256.ofNat pc, memory := mem, stack := p :: c :: neg32 :: rest} =
    some {s with pc := UInt256.ofNat (pc + 9), memory := mem, stack := p :: c :: neg32 :: rest} := by
  have capacity (j : Nat) (hj : j ≤ 6) : rest.length + j < 1024 := by omega
  have hnot : ¬ 2111 < p.toNat := by omega
  simp [testProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    capacity, List.exchange, hrun, hnot, UInt256.gt, UInt256.isTrue,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]

def groupProgram (target : Nat) : List Instr :=
  ([.op .JUMPDEST] ++ fourProgram) ++ testProgram target

theorem run_head (pc : Nat) (s : State) (mem : ByteArray) (n j : Nat) (rest : List UInt256) (hcap : rest.length ≤ 1011) :
    runInstructions [.op .JUMPDEST] (limbState pc s mem n j rest) =
    some (limbState (pc + 1) s mem n j rest) := by
  simp [limbState, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod] <;> omega

theorem run_group_go (pc target : Nat) (s : State) (mem : ByteArray) (n j : Nat)
    (rest : List UInt256) (hn : n ≤ 8) (hj : j + 4 < n) (hcap : rest.length ≤ 1011)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) (htarget : target < 2^256)
    (hdest : Decode.isValidJumpDest s.executionEnv.code target = true) :
    runInstructions (groupProgram target) (limbState pc s mem n j rest) =
    some (limbState target s mem n (j + 4) rest) := by
  have hh := run_head pc s mem n j rest hcap
  have hf := run_four (pc + 1) s mem n j rest hn (by omega) hcap hact hcode hrun
  have ht := run_test_go (pc + 101) target s (addStep mem n (j + 4)).memory
    (UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) (j + 4)))
    (addStep mem n (j + 4)).flag rest hcap htarget hdest
    (CycleSubmission.Global.Fast.Shift.tPtr_gt_8255 n (j + 4) hn hj) hrun
  exact runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _ hh hf) ht

theorem run_group_last (pc target : Nat) (s : State) (mem : ByteArray) (n j : Nat)
    (rest : List UInt256) (hn : n ≤ 8) (hj : j + 4 = n) (hcap : rest.length ≤ 1011)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    runInstructions (groupProgram target) (limbState pc s mem n j rest) =
    some (limbState (pc + 110) s mem n (j + 4) rest) := by
  have hh := run_head pc s mem n j rest hcap
  have hf := run_four (pc + 1) s mem n j rest hn (by omega) hcap hact hcode hrun
  have hp : (UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) (j + 4))).toNat ≤ 2111 := by
    rw [hj, CycleSubmission.Global.Fast.Shift.tPtr_toNat_last n hn]
    decide
  have ht := run_test_last (pc + 101) target s (addStep mem n (j + 4)).memory
    (UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) (j + 4)))
    (addStep mem n (j + 4)).flag rest hcap hp hrun
  exact runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _ hh hf) ht

def loopCarrier (pc : Nat) (s : State) (mem : ByteArray) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat pc, memory := mem, stack := neg32 :: rest}
def tailProgram (target : Nat) : List Instr :=
  [.op .POP, .push 2 2080, .op .MLOAD, .op (.Dup ⟨1, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .push 2 2080, .op .MSTORE, .op .LT, .op .ISZERO,
   .push 2 (UInt256.ofNat target), .op .JUMPI]

theorem run_tail_again (pc target : Nat) (s : State) (mem : ByteArray) (n : Nat)
    (rest : List UInt256) (hn : n ≤ 8) (hcap : rest.length ≤ 1011)
    (hact : 88 ≤ s.activeWords.toNat) (hout : addOut mem n = UInt256.ofNat 0)
    (htarget : target < 2^256)
    (hdest : Decode.isValidJumpDest s.executionEnv.code target = true)
    (hrun : s.halt = .Running) :
    runInstructions (tailProgram target) (limbState pc s mem n n rest) =
    some (loopCarrier target s (addRoundMem mem n) rest) := by
  have capacity (j : Nat) (hj : j ≤ 6) : rest.length + j < 1024 := by omega
  have hTN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hptr : UInt256.ofNat (Monpro.ptrAt (2080 + 32*n) n) = UInt256.ofNat 2080 :=
    Challenge.EvmProof.Word.word_ext (by rw [CycleSubmission.Global.Fast.Shift.tPtr_toNat_last n hn]; decide)
  have hc : UInt256.isTrue (UInt256.isZero (addOut mem n)) := by rw [hout]; decide
  unfold addOut addCarry at hc
  have htmod : target % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = target := Nat.mod_eq_of_lt htarget
  simp (config := { maxSteps := 300000 })
    [tailProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
     limbState, loopCarrier, addRoundMem, addCarry, Exp.storeWord,
     capacity, hptr, hTN, hc, hdest, htmod, hrun, List.exchange,
     State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]

theorem run_tail_done (pc target : Nat) (s : State) (mem : ByteArray) (n : Nat)
    (rest : List UInt256) (hn : n ≤ 8) (hcap : rest.length ≤ 1011)
    (hact : 88 ≤ s.activeWords.toNat) (hout : addOut mem n = UInt256.ofNat 1)
    (hrun : s.halt = .Running) :
    runInstructions (tailProgram target) (limbState pc s mem n n rest) =
    some (loopCarrier (pc + 18) s (addRoundMem mem n) rest) := by
  have capacity (j : Nat) (hj : j ≤ 6) : rest.length + j < 1024 := by omega
  have hTN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hptr : UInt256.ofNat (Monpro.ptrAt (2080 + 32*n) n) = UInt256.ofNat 2080 :=
    Challenge.EvmProof.Word.word_ext (by rw [CycleSubmission.Global.Fast.Shift.tPtr_toNat_last n hn]; decide)
  have hc : ¬ UInt256.isTrue (UInt256.isZero (addOut mem n)) := by rw [hout]; decide
  unfold addOut addCarry at hc
  simp (config := { maxSteps := 300000 })
    [tailProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
     limbState, loopCarrier, addRoundMem, addCarry, Exp.storeWord,
     capacity, hptr, hTN, hc, hrun, List.exchange,
     State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]

theorem run_finish (pc : Nat) (s : State) (mem : ByteArray) (rest : List UInt256)
    (hcap : rest.length ≤ 1011) :
    runInstructions [.op .POP] (loopCarrier pc s mem rest) =
    some {s with pc := UInt256.ofNat (pc + 1), memory := mem, stack := rest} := by
  simp [loopCarrier, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod] <;> omega
end CycleSubmission.Global.Fast.Shift.RepairFour
