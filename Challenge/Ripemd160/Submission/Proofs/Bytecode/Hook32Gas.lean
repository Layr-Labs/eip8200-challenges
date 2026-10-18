import Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32Route
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedHelperBooleanTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedCallTrace

set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 400000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
open Challenge.EvmProof.DataStepper
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Sites
open Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedCallTrace
open StackRoundTemplate
open YulEvmCompiler

def siteOf (located : Located) (pc : Nat)
    (hpc : submissionArtifact.instructionPC located.index = pc)
    (hsmall : pc < 2 ^ 256 := by decide) :
    LocatedSite submissionArtifact .Osaka where
  located := located
  pc := UInt256.ofNat pc
  pc_eq := by
    show (UInt256.ofNat pc).toNat = submissionArtifact.instructionPC located.index
    rw [hpc, Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsmall]

theorem contig_at (a b sz : Nat) (h : a + sz = b) (hb : a + sz < 2 ^ 256) :
    UInt256.ofNat b = UInt256.ofNat a + UInt256.ofNat sz := by
  rw [← h]
  exact (Word.ofNat_add_ofNat hb).symm

theorem pc_jumpdest {u v : State}
    (hr : DataStepper.runInstr (.op .JUMPDEST) u = some v) :
    v.pc = u.pc + UInt256.ofNat 1 := by
  simpa using runInstr_pc_extra (instruction := .op .JUMPDEST) (hform := Or.inr rfl) hr

theorem pc_push {w : Fin 33} {value : UInt256} {u v : State}
    (hr : DataStepper.runInstr (.push w value) u = some v) :
    v.pc = u.pc + UInt256.ofNat (1 + w.val) := by
  simpa using runInstr_pc_of_advances (Or.inl (StraightLine.push w value)) hr

theorem pc_eq {u v : State}
    (hr : DataStepper.runInstr (.op .EQ) u = some v) :
    v.pc = u.pc + UInt256.ofNat 1 := by
  by_cases hcap : u.stack.length < 1024
  · rw [DataStepper.runInstr, if_pos hcap] at hr
    cases hs : u.stack with
    | nil => simp [hs] at hr
    | cons a tail =>
        cases ht : tail with
        | nil => simp [hs, ht] at hr
        | cons b rest =>
            simp [hs, ht] at hr
            subst v
            rfl
  · simp [DataStepper.runInstr, if_neg hcap] at hr

theorem pc_calldataload {u v : State}
    (hr : DataStepper.runInstr (.op .CALLDATALOAD) u = some v) :
    v.pc = u.pc + UInt256.ofNat 1 := by
  by_cases hcap : u.stack.length < 1024
  · rw [DataStepper.runInstr, if_pos hcap] at hr
    cases hs : u.stack with
    | nil => simp [hs] at hr
    | cons offset rest =>
        simp [hs] at hr
        subst v
        rfl
  · simp [DataStepper.runInstr, if_neg hcap] at hr

def s5422 := siteOf loc_5422 9667 pc_5422
def s5423 := siteOf loc_5423 9668 pc_5423
def s5424 := siteOf loc_5424 9701 pc_5424
def s5425 := siteOf loc_5425 9702 pc_5425
def s5426 := siteOf loc_5426 9703 pc_5426
def s5427 := siteOf loc_5427 9704 pc_5427
def s5428 := siteOf loc_5428 9707 pc_5428
def s5429 := siteOf loc_5429 9708 pc_5429
def s5430 := siteOf loc_5430 9741 pc_5430
def s5431 := siteOf loc_5431 9742 pc_5431
def s5432 := siteOf loc_5432 9743 pc_5432
def s5433 := siteOf loc_5433 9744 pc_5433
def s5434 := siteOf loc_5434 9747 pc_5434
def s5435 := siteOf loc_5435 9748 pc_5435
def s5436 := siteOf loc_5436 9781 pc_5436
def s5437 := siteOf loc_5437 9782 pc_5437
def s5438 := siteOf loc_5438 9783 pc_5438
def s5439 := siteOf loc_5439 9784 pc_5439
def s5440 := siteOf loc_5440 9787 pc_5440
def s5441 := siteOf loc_5441 9788 pc_5441
def s5442 := siteOf loc_5442 9791 pc_5442

def cmp0Sites : List (LocatedSite submissionArtifact .Osaka) :=
  [s5422, s5423, s5424, s5425, s5426, s5427, s5428]
def cmp1Sites : List (LocatedSite submissionArtifact .Osaka) :=
  [s5429, s5430, s5431, s5432, s5433, s5434]
def cmp2Sites : List (LocatedSite submissionArtifact .Osaka) :=
  [s5435, s5436, s5437, s5438, s5439, s5440]
def missSites : List (LocatedSite submissionArtifact .Osaka) :=
  [s5441, s5442]

theorem instr_5422 : loc_5422.instruction = .op .JUMPDEST := by unfold loc_5422; rfl
theorem instr_5423 : loc_5423.instruction = .push ⟨32, by decide⟩ (UInt256.ofNat 52407983597458713726083494478729836850834839133145674611439640847371528033346) := by unfold loc_5423; rfl
theorem instr_5424 : loc_5424.instruction = .push ⟨0, by decide⟩ (UInt256.ofNat 0) := by unfold loc_5424; rfl
theorem instr_5425 : loc_5425.instruction = .op .CALLDATALOAD := by unfold loc_5425; rfl
theorem instr_5426 : loc_5426.instruction = .op .EQ := by unfold loc_5426; rfl
theorem instr_5427 : loc_5427.instruction = .push ⟨2, by decide⟩ (UInt256.ofNat 9792) := by unfold loc_5427; rfl
theorem instr_5428 : loc_5428.instruction = .op .JUMPI := by unfold loc_5428; rfl
theorem instr_5429 : loc_5429.instruction = .push ⟨32, by decide⟩ (UInt256.ofNat 67308224672597080852409368528162126009170930980447052366519322622324472729693) := by unfold loc_5429; rfl
theorem instr_5430 : loc_5430.instruction = .push ⟨0, by decide⟩ (UInt256.ofNat 0) := by unfold loc_5430; rfl
theorem instr_5431 : loc_5431.instruction = .op .CALLDATALOAD := by unfold loc_5431; rfl
theorem instr_5432 : loc_5432.instruction = .op .EQ := by unfold loc_5432; rfl
theorem instr_5433 : loc_5433.instruction = .push ⟨2, by decide⟩ (UInt256.ofNat 9820) := by unfold loc_5433; rfl
theorem instr_5434 : loc_5434.instruction = .op .JUMPI := by unfold loc_5434; rfl
theorem instr_5435 : loc_5435.instruction = .push ⟨32, by decide⟩ (UInt256.ofNat 82210225693053879566223937454697223704398777913375062608144492211390645128056) := by unfold loc_5435; rfl
theorem instr_5436 : loc_5436.instruction = .push ⟨0, by decide⟩ (UInt256.ofNat 0) := by unfold loc_5436; rfl
theorem instr_5437 : loc_5437.instruction = .op .CALLDATALOAD := by unfold loc_5437; rfl
theorem instr_5438 : loc_5438.instruction = .op .EQ := by unfold loc_5438; rfl
theorem instr_5439 : loc_5439.instruction = .push ⟨2, by decide⟩ (UInt256.ofNat 9848) := by unfold loc_5439; rfl
theorem instr_5440 : loc_5440.instruction = .op .JUMPI := by unfold loc_5440; rfl
theorem instr_5441 : loc_5441.instruction = .push ⟨2, by decide⟩ (UInt256.ofNat 497) := by unfold loc_5441; rfl
theorem instr_5442 : loc_5442.instruction = .op .JUMP := by unfold loc_5442; rfl

theorem size_5422 : loc_5422.instruction.size = 1 := by rw [instr_5422]; rfl
theorem size_5423 : loc_5423.instruction.size = 33 := by rw [instr_5423]; rfl
theorem size_5424 : loc_5424.instruction.size = 1 := by rw [instr_5424]; rfl
theorem size_5425 : loc_5425.instruction.size = 1 := by rw [instr_5425]; rfl
theorem size_5426 : loc_5426.instruction.size = 1 := by rw [instr_5426]; rfl
theorem size_5427 : loc_5427.instruction.size = 3 := by rw [instr_5427]; rfl
theorem size_5429 : loc_5429.instruction.size = 33 := by rw [instr_5429]; rfl
theorem size_5430 : loc_5430.instruction.size = 1 := by rw [instr_5430]; rfl
theorem size_5431 : loc_5431.instruction.size = 1 := by rw [instr_5431]; rfl
theorem size_5432 : loc_5432.instruction.size = 1 := by rw [instr_5432]; rfl
theorem size_5433 : loc_5433.instruction.size = 3 := by rw [instr_5433]; rfl
theorem size_5435 : loc_5435.instruction.size = 33 := by rw [instr_5435]; rfl
theorem size_5436 : loc_5436.instruction.size = 1 := by rw [instr_5436]; rfl
theorem size_5437 : loc_5437.instruction.size = 1 := by rw [instr_5437]; rfl
theorem size_5438 : loc_5438.instruction.size = 1 := by rw [instr_5438]; rfl
theorem size_5439 : loc_5439.instruction.size = 3 := by rw [instr_5439]; rfl
theorem size_5441 : loc_5441.instruction.size = 3 := by rw [instr_5441]; rfl

theorem cmp0_inst :
    cmp0Sites.map (fun site => site.located.instruction) = Hook32Route.cmp0 := by
  simp [cmp0Sites, s5422, s5423, s5424, s5425, s5426, s5427, s5428, siteOf,
    instr_5422, instr_5423, instr_5424, instr_5425, instr_5426, instr_5427, instr_5428,
    Hook32Route.cmp0, word0]

theorem cmp1_inst :
    cmp1Sites.map (fun site => site.located.instruction) = Hook32Route.cmp1 := by
  simp [cmp1Sites, s5429, s5430, s5431, s5432, s5433, s5434, siteOf,
    instr_5429, instr_5430, instr_5431, instr_5432, instr_5433, instr_5434, Hook32Route.cmp1, word1]

theorem cmp2_inst :
    cmp2Sites.map (fun site => site.located.instruction) = Hook32Route.cmp2 := by
  simp [cmp2Sites, s5435, s5436, s5437, s5438, s5439, s5440, siteOf,
    instr_5435, instr_5436, instr_5437, instr_5438, instr_5439, instr_5440, Hook32Route.cmp2, word2]

theorem miss_inst :
    missSites.map (fun site => site.located.instruction) = Hook32Route.missJump := by
  simp [missSites, s5441, s5442, siteOf, instr_5441, instr_5442, Hook32Route.missJump]

theorem cmp0_contig : Contiguous cmp0Sites := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩⟩⟩⟩
  · simp [s5422, s5423, siteOf, size_5422]; exact contig_at 9667 9668 1 rfl (by decide)
  · simp [s5423, s5424, siteOf, size_5423]; exact contig_at 9668 9701 33 rfl (by decide)
  · simp [s5424, s5425, siteOf, size_5424]; exact contig_at 9701 9702 1 rfl (by decide)
  · simp [s5425, s5426, siteOf, size_5425]; exact contig_at 9702 9703 1 rfl (by decide)
  · simp [s5426, s5427, siteOf, size_5426]; exact contig_at 9703 9704 1 rfl (by decide)
  · simp [s5427, s5428, siteOf, size_5427]; exact contig_at 9704 9707 3 rfl (by decide)
  · exact trivial

theorem cmp1_contig : Contiguous cmp1Sites := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩⟩⟩
  · simp [s5429, s5430, siteOf, size_5429]; exact contig_at 9708 9741 33 rfl (by decide)
  · simp [s5430, s5431, siteOf, size_5430]; exact contig_at 9741 9742 1 rfl (by decide)
  · simp [s5431, s5432, siteOf, size_5431]; exact contig_at 9742 9743 1 rfl (by decide)
  · simp [s5432, s5433, siteOf, size_5432]; exact contig_at 9743 9744 1 rfl (by decide)
  · simp [s5433, s5434, siteOf, size_5433]; exact contig_at 9744 9747 3 rfl (by decide)
  · exact trivial

theorem cmp2_contig : Contiguous cmp2Sites := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩⟩⟩
  · simp [s5435, s5436, siteOf, size_5435]; exact contig_at 9748 9781 33 rfl (by decide)
  · simp [s5436, s5437, siteOf, size_5436]; exact contig_at 9781 9782 1 rfl (by decide)
  · simp [s5437, s5438, siteOf, size_5437]; exact contig_at 9782 9783 1 rfl (by decide)
  · simp [s5438, s5439, siteOf, size_5438]; exact contig_at 9783 9784 1 rfl (by decide)
  · simp [s5439, s5440, siteOf, size_5439]; exact contig_at 9784 9787 3 rfl (by decide)
  · exact trivial

theorem miss_contig : Contiguous missSites := by
  refine ⟨?_, ?_⟩
  · simp [s5441, s5442, siteOf, size_5441]; exact contig_at 9788 9791 3 rfl (by decide)
  · exact trivial

theorem cast_pc {site : LocatedSite submissionArtifact .Osaka} {instruction : Instr}
    {u v : State}
    (heq : site.located.instruction = instruction)
    (hr : DataStepper.runInstr site.located.instruction u = some v)
    (hadv : DataStepper.runInstr instruction u = some v →
      v.pc = u.pc + UInt256.ofNat instruction.size) :
    v.pc = u.pc + UInt256.ofNat site.located.instruction.size := by
  subst heq
  exact hadv hr

theorem cmp0_advances (site : LocatedSite submissionArtifact .Osaka)
    (hmem : site ∈ cmp0Sites.dropLast) {u v : State}
    (hr : DataStepper.runInstr site.located.instruction u = some v) :
    v.pc = u.pc + UInt256.ofNat site.located.instruction.size := by
  simp [cmp0Sites, List.dropLast, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show s5422.located.instruction = .op .JUMPDEST from by simp [s5422, siteOf, instr_5422]] at hr ⊢
    exact pc_jumpdest hr
  · rw [show s5423.located.instruction = .push ⟨32, by decide⟩ (UInt256.ofNat 52407983597458713726083494478729836850834839133145674611439640847371528033346) from by simp [s5423, siteOf, instr_5423]] at hr ⊢
    exact pc_push hr
  · rw [show s5424.located.instruction = .push ⟨0, by decide⟩ (UInt256.ofNat 0) from by simp [s5424, siteOf, instr_5424]] at hr ⊢
    exact pc_push hr
  · rw [show s5425.located.instruction = .op .CALLDATALOAD from by simp [s5425, siteOf, instr_5425]] at hr ⊢
    exact pc_calldataload hr
  · rw [show s5426.located.instruction = .op .EQ from by simp [s5426, siteOf, instr_5426]] at hr ⊢
    exact pc_eq hr
  · rw [show s5427.located.instruction = .push ⟨2, by decide⟩ (UInt256.ofNat 9792) from by simp [s5427, siteOf, instr_5427]] at hr ⊢
    exact pc_push hr

theorem cmp1_advances (site : LocatedSite submissionArtifact .Osaka)
    (hmem : site ∈ cmp1Sites.dropLast) {u v : State}
    (hr : DataStepper.runInstr site.located.instruction u = some v) :
    v.pc = u.pc + UInt256.ofNat site.located.instruction.size := by
  simp [cmp1Sites, List.dropLast, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · rw [show s5429.located.instruction = .push ⟨32, by decide⟩ (UInt256.ofNat 67308224672597080852409368528162126009170930980447052366519322622324472729693) from by simp [s5429, siteOf, instr_5429]] at hr ⊢
    exact pc_push hr
  · rw [show s5430.located.instruction = .push ⟨0, by decide⟩ (UInt256.ofNat 0) from by simp [s5430, siteOf, instr_5430]] at hr ⊢
    exact pc_push hr
  · rw [show s5431.located.instruction = .op .CALLDATALOAD from by simp [s5431, siteOf, instr_5431]] at hr ⊢
    exact pc_calldataload hr
  · rw [show s5432.located.instruction = .op .EQ from by simp [s5432, siteOf, instr_5432]] at hr ⊢
    exact pc_eq hr
  · rw [show s5433.located.instruction = .push ⟨2, by decide⟩ (UInt256.ofNat 9820) from by simp [s5433, siteOf, instr_5433]] at hr ⊢
    exact pc_push hr

theorem cmp2_advances (site : LocatedSite submissionArtifact .Osaka)
    (hmem : site ∈ cmp2Sites.dropLast) {u v : State}
    (hr : DataStepper.runInstr site.located.instruction u = some v) :
    v.pc = u.pc + UInt256.ofNat site.located.instruction.size := by
  simp [cmp2Sites, List.dropLast, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · rw [show s5435.located.instruction = .push ⟨32, by decide⟩ (UInt256.ofNat 82210225693053879566223937454697223704398777913375062608144492211390645128056) from by simp [s5435, siteOf, instr_5435]] at hr ⊢
    exact pc_push hr
  · rw [show s5436.located.instruction = .push ⟨0, by decide⟩ (UInt256.ofNat 0) from by simp [s5436, siteOf, instr_5436]] at hr ⊢
    exact pc_push hr
  · rw [show s5437.located.instruction = .op .CALLDATALOAD from by simp [s5437, siteOf, instr_5437]] at hr ⊢
    exact pc_calldataload hr
  · rw [show s5438.located.instruction = .op .EQ from by simp [s5438, siteOf, instr_5438]] at hr ⊢
    exact pc_eq hr
  · rw [show s5439.located.instruction = .push ⟨2, by decide⟩ (UInt256.ofNat 9848) from by simp [s5439, siteOf, instr_5439]] at hr ⊢
    exact pc_push hr

theorem miss_advances (site : LocatedSite submissionArtifact .Osaka)
    (hmem : site ∈ missSites.dropLast) {u v : State}
    (hr : DataStepper.runInstr site.located.instruction u = some v) :
    v.pc = u.pc + UInt256.ofNat site.located.instruction.size := by
  simp [missSites, List.dropLast, List.mem_cons, List.not_mem_nil] at hmem
  subst hmem
  · rw [show s5441.located.instruction = .push ⟨2, by decide⟩ (UInt256.ofNat 497) from by simp [s5441, siteOf, instr_5441]] at hr ⊢
    exact pc_push hr

def gas_cmp0 (s : State) (e : Env s) (stk : List UInt256)
    (hmiss : MachineState.readWord s.executionEnv.calldata 0 ≠ word0)
    (hlen : stk.length + 3 < 1024) :
    GasSteps (atState s 9667 stk) (atState s 9708 stk) := by
  apply DataStepper.runLocatedBlock_sound submissionArtifact .Osaka (LocatedSite.path cmp0Sites)
  · simpa [atState] using e.code
  · simpa [atState] using e.fork
  · have hblock := PairedHelperBooleanTrace.runLocatedBlock_eq_raw_terminal_sites cmp0Sites Hook32Route.cmp0 cmp0_inst
      cmp0_contig (atState s 9667 stk)
      (by simp [headPC, cmp0Sites, s5422, siteOf, atState]) cmp0_advances
    rw [hblock]
    exact Hook32Route.run_cmp0 s e.run stk hmiss hlen
  · simpa [atState] using e.run
  · simpa [atState] using e.np

def gas_cmp1 (s : State) (e : Env s) (stk : List UInt256)
    (hmiss : MachineState.readWord s.executionEnv.calldata 0 ≠ word1)
    (hlen : stk.length + 3 < 1024) :
    GasSteps (atState s 9708 stk) (atState s 9748 stk) := by
  apply DataStepper.runLocatedBlock_sound submissionArtifact .Osaka (LocatedSite.path cmp1Sites)
  · simpa [atState] using e.code
  · simpa [atState] using e.fork
  · have hblock := PairedHelperBooleanTrace.runLocatedBlock_eq_raw_terminal_sites cmp1Sites Hook32Route.cmp1 cmp1_inst
      cmp1_contig (atState s 9708 stk)
      (by simp [headPC, cmp1Sites, s5429, siteOf, atState]) cmp1_advances
    rw [hblock]
    exact Hook32Route.run_cmp1 s e.run stk hmiss hlen
  · simpa [atState] using e.run
  · simpa [atState] using e.np

def gas_cmp2 (s : State) (e : Env s) (stk : List UInt256)
    (hmiss : MachineState.readWord s.executionEnv.calldata 0 ≠ word2)
    (hlen : stk.length + 3 < 1024) :
    GasSteps (atState s 9748 stk) (atState s 9788 stk) := by
  apply DataStepper.runLocatedBlock_sound submissionArtifact .Osaka (LocatedSite.path cmp2Sites)
  · simpa [atState] using e.code
  · simpa [atState] using e.fork
  · have hblock := PairedHelperBooleanTrace.runLocatedBlock_eq_raw_terminal_sites cmp2Sites Hook32Route.cmp2 cmp2_inst
      cmp2_contig (atState s 9748 stk)
      (by simp [headPC, cmp2Sites, s5435, siteOf, atState]) cmp2_advances
    rw [hblock]
    exact Hook32Route.run_cmp2 s e.run stk hmiss hlen
  · simpa [atState] using e.run
  · simpa [atState] using e.np

def gas_miss_jump (s : State) (e : Env s) (stk : List UInt256)
    (hlen : stk.length + 3 < 1024) :
    GasSteps (atState s 9788 stk) (atState s 497 stk) := by
  apply DataStepper.runLocatedBlock_sound submissionArtifact .Osaka (LocatedSite.path missSites)
  · simpa [atState] using e.code
  · simpa [atState] using e.fork
  · have hblock := PairedHelperBooleanTrace.runLocatedBlock_eq_raw_terminal_sites missSites Hook32Route.missJump miss_inst
      miss_contig (atState s 9788 stk)
      (by simp [headPC, missSites, s5441, siteOf, atState]) miss_advances
    rw [hblock]
    exact Hook32Route.run_miss_jump s e.code e.run stk (by omega)
  · simpa [atState] using e.run
  · simpa [atState] using e.np

def gas_miss (s : State) (e : Env s) (stk : List UInt256)
    (hmiss0 : MachineState.readWord s.executionEnv.calldata 0 ≠ word0)
    (hmiss1 : MachineState.readWord s.executionEnv.calldata 0 ≠ word1)
    (hmiss2 : MachineState.readWord s.executionEnv.calldata 0 ≠ word2)
    (hlen : stk.length + 3 < 1024) :
    GasSteps (atState s 9667 stk) (atState s 497 stk) :=
  (gas_cmp0 s e stk hmiss0 hlen).trans
    ((gas_cmp1 s e stk hmiss1 hlen).trans
      ((gas_cmp2 s e stk hmiss2 hlen).trans (gas_miss_jump s e stk hlen)))

def gas_from_160 (s : State) (e : Env s) (stk : List UInt256)
    (hmiss0 : MachineState.readWord s.executionEnv.calldata 0 ≠ word0)
    (hmiss1 : MachineState.readWord s.executionEnv.calldata 0 ≠ word1)
    (hmiss2 : MachineState.readWord s.executionEnv.calldata 0 ≠ word2)
    (hlen : stk.length + 3 < 1024) :
    GasSteps (atState s 160 ((1 : UInt256) :: stk)) (atState s 497 stk) :=
  (Hook32Route.gas_enter s e stk hlen).trans (gas_miss s e stk hmiss0 hmiss1 hmiss2 hlen)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32
