import Challenge.Modexp.Submission.Proofs.CycleCaller.Blocks
import Challenge.Modexp.Submission.Proofs.CycleCaller.Memory
import Challenge.Modexp.Submission.Proofs.Cycle.EntryMeaning
import Challenge.Modexp.Submission.Proofs.CRT.CRTControlBase
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace CycleSubmission.CallerPrefix
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open HistoricalSearch.CRTControl
open CycleSubmission.CallerBlocks CycleSubmission.EntryMeaning

def qWord (n : Nat) : UInt256 := UInt256.ofNat 480 - UInt256.ofNat (512+32*n-32)

def frame (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256) : Caller where
  pbi := qWord 8
  hd := UInt256.ofNat 3728
  w3 := UInt256.ofNat 480
  ent := UInt256.ofNat 3347
  m32 := UInt256.ofNat 0
  m128 := MachineState.readWord mem 128
  m64 := UInt256.ofNat 0
  m0 := UInt256.ofNat 0
  tl := UInt256.ofNat 0
  m96 := UInt256.ofNat 0
  inv := MachineState.readWord mem 2720
  tn := UInt256.ofNat 0
  aprev := UInt256.ofNat 0
  counter := UInt256.ofNat (k-1)
  ret := ret
  tail := tail

def call (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 3181
    memory := mem
    stack := [UInt256.ofNat 3728, UInt256.ofNat 2112, UInt256.ofNat 512,
      UInt256.ofNat (k-1), ret] ++ tail}

def staged (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256) : State :=
  CiosCached.outState s (CallerMemory.memory mem) 512 8 0 (UInt256.ofNat 3728)
    (UInt256.ofNat 3347) (UInt256.ofNat 0) (UInt256.ofNat 0)
    (UInt256.ofNat 0)
    ([UInt256.ofNat 0, UInt256.ofNat 0,
      MachineState.readWord mem 2720, UInt256.ofNat 0, UInt256.ofNat 0,
      UInt256.ofNat (k-1), ret] ++ tail)

def stateAt (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256)
    (pc : Nat) : State :=
  {s with
    pc := UInt256.ofNat pc
    memory := CallerMemory.memory mem
    stack := saved (frame mem k ret tail)}

theorem entry_run (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256)
    (hcap : tail.length ≤ 943) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entryProgram (staged s mem k ret tail) = some (stateAt s mem k ret tail 3743) := by
  have h16 : tail.length + 16 < 1024 := by omega
  have h17 : tail.length + 17 < 1024 := by omega
  have hactM := Csub.activeWords_fix s 192 32 (by decide) (by decide) hact
  have hz0 : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  simp [hz0, entryProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    staged, stateAt, frame, saved, CiosCached.outState, qWord,
    Monpro.ptrAt_zero, h16, h17, hactM, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    CallerMemory.readWord mem 192 (Or.inl (by decide)),
    CallerMemory.readWord mem 128 (Or.inl (by decide)), CiosCached.allOnes]

def tested (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256) : State :=
  {stateAt s mem k ret tail 3751 with
    stack := UInt256.ofNat 5334 :: UInt256.ofNat 0 :: saved (frame mem k ret tail)}

theorem test_run (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256)
    (hcap : tail.length ≤ 943) :
    runInstructions testProgram (stateAt s mem k ret tail 3743) = some (tested s mem k ret tail) := by
  have h16 : tail.length + 16 < 1024 := by omega
  have h17 : tail.length + 17 < 1024 := by omega
  have h18 : tail.length + 18 < 1024 := by omega
  have hsum : UInt256.isZero (UInt256.ofNat 128 + qWord 8) = UInt256.ofNat 0 := by decide
  simp [testProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    stateAt, tested, frame, saved, h16, h17, h18, hsum,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

/-- The guard word: zero exactly when the top 110 bits of the staged operand's leading word
are all ones. -/
def guardWord (mem : ByteArray) : UInt256 :=
  UInt256.shiftRight (UInt256.lnot (MachineState.readWord (CallerMemory.memory mem) 2368))
    (UInt256.ofNat 146)

def guarded (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256) : State :=
  {stateAt s mem k ret tail 3763 with
    stack := UInt256.ofNat 5506 :: guardWord mem :: saved (frame mem k ret tail)}

theorem guard_run (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256)
    (hcap : tail.length ≤ 943) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions guardProgram (stateAt s mem k ret tail 3752) = some (guarded s mem k ret tail) := by
  have h16 : tail.length + 16 < 1024 := by omega
  have h17 : tail.length + 17 < 1024 := by omega
  have h18 : tail.length + 18 < 1024 := by omega
  have hactM := Csub.activeWords_fix s 2368 32 (by decide) (by decide) hact
  simp [guardProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    stateAt, guarded, guardWord, frame, saved, h16, h17, h18, hactM, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem bailJump_run (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256)
    (hcap : tail.length ≤ 943)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 219 = true) :
    runInstructions bailJumpProgram (stateAt s mem k ret tail 3764) = some (stateAt s mem k ret tail 219) := by
  have h16 : tail.length + 16 < 1024 := by omega
  have h17 : tail.length + 17 < 1024 := by omega
  simp [bailJumpProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    stateAt, frame, saved, h16, h17, hvalid,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

noncomputable opaque setupTrace (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : tail.length ≤ 943) (hact : 88 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat 256)
    (_hml : MachineState.readWord mem 2752 = UInt256.ofNat 224)
    (_hw : tail[1]? = some (UInt256.ofNat 256))
    (_hn : tail[2]? = some (UInt256.ofNat 8)) :
    GasSteps (call s mem k ret tail) (staged s mem k ret tail) := by
  have hcommon := commonBlock.steps (s := call s mem k ret tail)
    (env.transfer rfl rfl) rfl (jumpDest_run _ (by
      simp only [call, List.length_append, List.length_cons, List.length_nil]; omega))
  have hsetup := setupBlock.steps
    (s := CiosCached.setupState s mem (UInt256.ofNat 3728) 2112 512 (UInt256.ofNat (k-1)) ret tail)
    (env.transfer rfl rfl) rfl
    (CycleSubmission.DeadSetup.run_entry_sq s mem (UInt256.ofNat 3728) 2112 512 8
      (UInt256.ofNat (k-1)) ret tail (by omega) hact (by decide) (by decide)
      (by decide) (by decide) (by decide) hcds hs32
      (by rw [env.code]; exact valid3728))
  exact hcommon.trans hsetup

/-- From the staged state to the guard's conditional jump at 3763. -/
noncomputable opaque toGuard (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : tail.length ≤ 943) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps (staged s mem k ret tail) (guarded s mem k ret tail) := by
  have he2 := entryBlock.steps (s := staged s mem k ret tail)
    (env.transfer rfl rfl) rfl (entry_run s mem k ret tail hcap hact)
  have ht := testBlock.steps (s := stateAt s mem k ret tail 3743)
    (env.transfer rfl rfl) rfl (test_run s mem k ret tail hcap)
  have hc : (tested s mem k ret tail).stack.length < 1024 := by
    simp only [tested, stateAt, saved, frame, List.length_cons, List.length_append, List.length_nil]; omega
  have hr := jumpi_run (tested s mem k ret tail) (UInt256.ofNat 5334)
    (UInt256.ofNat 0) (saved (frame mem k ret tail)) rfl hc
    (by rw [show (tested s mem k ret tail).executionEnv.code = Artifact.bytecode from env.code]; exact valid5334)
  have hj := branchBlock.steps (s := tested s mem k ret tail) (env.transfer rfl rfl) rfl hr
  have chosen : conditionalModel (tested s mem k ret tail) = stateAt s mem k ret tail 3752 := by
    simp only [conditionalModel, tested, stateAt, List.drop_succ_cons, List.drop_zero, List.headD_cons]
    simp
    rfl
  rw [chosen] at hj
  have hg := guardBlock.steps (s := stateAt s mem k ret tail 3752)
    (env.transfer rfl rfl) rfl (guard_run s mem k ret tail hcap hact)
  exact ((he2.trans ht).trans hj).trans hg

/-- The guard holds: the call reaches the cycle entry at 5506. -/
noncomputable opaque suffixTrace (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : tail.length ≤ 943) (hact : 88 ≤ s.activeWords.toNat)
    (hg : (guardWord mem).toNat ≠ 0) :
    GasSteps (staged s mem k ret tail) (stateAt s mem k ret tail 5506) := by
  have h1 := toGuard s mem k ret tail env hcap hact
  have hc : (guarded s mem k ret tail).stack.length < 1024 := by
    simp only [guarded, stateAt, saved, frame, List.length_cons, List.length_append, List.length_nil]; omega
  have hr := jumpi_run (guarded s mem k ret tail) (UInt256.ofNat 5506)
    (guardWord mem) (saved (frame mem k ret tail)) rfl hc
    (by rw [show (guarded s mem k ret tail).executionEnv.code = Artifact.bytecode from env.code]; exact valid5964)
  have hj := guardJumpBlock.steps (s := guarded s mem k ret tail) (env.transfer rfl rfl) rfl hr
  have chosen : conditionalModel (guarded s mem k ret tail) = stateAt s mem k ret tail 5506 := by
    simp only [conditionalModel, guarded, stateAt, List.drop_succ_cons, List.drop_zero, List.headD_cons, if_neg hg]
  rw [chosen] at hj
  exact h1.trans hj

/-- The guard fires: the call goes to the general route at 219 with the saved frame. -/
noncomputable opaque bailTrace (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : tail.length ≤ 943) (hact : 88 ≤ s.activeWords.toNat)
    (hg : (guardWord mem).toNat = 0) :
    GasSteps (staged s mem k ret tail) (stateAt s mem k ret tail 219) := by
  have h1 := toGuard s mem k ret tail env hcap hact
  have hc : (guarded s mem k ret tail).stack.length < 1024 := by
    simp only [guarded, stateAt, saved, frame, List.length_cons, List.length_append, List.length_nil]; omega
  have hr := jumpi_run (guarded s mem k ret tail) (UInt256.ofNat 5506)
    (guardWord mem) (saved (frame mem k ret tail)) rfl hc
    (by rw [show (guarded s mem k ret tail).executionEnv.code = Artifact.bytecode from env.code]; exact valid5964)
  have hj := guardJumpBlock.steps (s := guarded s mem k ret tail) (env.transfer rfl rfl) rfl hr
  have chosen : conditionalModel (guarded s mem k ret tail) = stateAt s mem k ret tail 3764 := by
    simp only [conditionalModel, guarded, stateAt, List.drop_succ_cons, List.drop_zero, List.headD_cons, hg]
    simp
    rfl
  rw [chosen] at hj
  have hx := bailJumpBlock.steps (s := stateAt s mem k ret tail 3764)
    (env.transfer rfl rfl) rfl (bailJump_run s mem k ret tail hcap
      (by rw [env.code]; exact valid219))
  exact (h1.trans hj).trans hx

noncomputable def run (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : tail.length ≤ 943) (hact : 88 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat 256)
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat 224)
    (hw : tail[1]? = some (UInt256.ofNat 256))
    (hn : tail[2]? = some (UInt256.ofNat 8))
    (hg : (guardWord mem).toNat ≠ 0) :
    GasSteps (call s mem k ret tail) (stateAt s mem k ret tail 5506) :=
  (setupTrace s mem k ret tail env hcap hact hcds hs32 hml hw hn).trans
    (suffixTrace s mem k ret tail env hcap hact hg)

noncomputable def bail (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : tail.length ≤ 943) (hact : 88 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat 256)
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat 224)
    (hw : tail[1]? = some (UInt256.ofNat 256))
    (hn : tail[2]? = some (UInt256.ofNat 8))
    (hg : (guardWord mem).toNat = 0) :
    GasSteps (call s mem k ret tail) (stateAt s mem k ret tail 219) :=
  (setupTrace s mem k ret tail env hcap hact hcds hs32 hml hw hn).trans
    (bailTrace s mem k ret tail env hcap hact hg)

set_option exponentiation.threshold 4096 in
/-- When the guard does not fire, the staged operand is at most `2^2048 - 2^1938`. -/
theorem guard_bound (mem : ByteArray) (A : Nat)
    (ha : Model.FastRepresents (CallerMemory.memory mem) 2368 8 A)
    (hg : (guardWord mem).toNat ≠ 0) : A < 2^2048 - 2^1938 := by
  have htop := Model.readWord_of_fastRepresents ha (j := 0) (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at htop
  have hsr := hg
  simp only [guardWord] at hsr
  generalize hw : MachineState.readWord (CallerMemory.memory mem) 2368 = w at htop hsr
  have hwl : w.toNat < 2^256 := w.val.isLt
  rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by decide : 146 < 256), Nat.shiftRight_eq_div_pow] at hsr
  have hlnot : (UInt256.lnot w).toNat = 2 ^ 256 - 1 - w.toNat := by
    rw [UInt256.lnot, Challenge.EvmProof.Word.word_toNat_ofNat]
    change (2 ^ 256 - 1 - w.toNat) % 2 ^ 256 = _
    exact Nat.mod_eq_of_lt (by omega)
  rw [hlnot] at hsr
  have hw2 : w.toNat < 2^256 - 2^146 := by
    by_contra hc
    apply hsr
    apply Nat.div_eq_of_lt
    omega
  have hA8 : A < Challenge.Modexp.Submission.Proofs.Limbs.radix^8 := ha.1
  have hr7 : Challenge.Modexp.Submission.Proofs.Limbs.radix^7 = 2^1792 := by
    rw [Challenge.Modexp.Submission.Proofs.Limbs.radix, ← Nat.pow_mul]
  have hr8 : Challenge.Modexp.Submission.Proofs.Limbs.radix^8 = 2^1792 * 2^256 := by
    rw [Challenge.Modexp.Submission.Proofs.Limbs.radix, ← Nat.pow_mul, ← Nat.pow_add]
  have hr : Challenge.Modexp.Submission.Proofs.Limbs.radix = 2^256 := rfl
  rw [show 8 - 1 - 0 = 7 from rfl, hr7, hr] at htop
  rw [hr8] at hA8
  have hdiv : A / 2^1792 % 2^256 = A / 2^1792 := by
    apply Nat.mod_eq_of_lt
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    rw [Nat.mul_comm]; exact hA8
  rw [hdiv] at htop
  have hq : A / 2^1792 < 2^256 - 2^146 := by rw [← htop]; exact hw2
  have hlt : A < (2^256 - 2^146) * 2^1792 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)] at hq; exact hq
  have hc : (2^256 - 2^146) * 2^1792 = (2:Nat)^2048 - 2^1938 := by norm_num
  rw [hc] at hlt
  exact hlt

end CycleSubmission.CallerPrefix
