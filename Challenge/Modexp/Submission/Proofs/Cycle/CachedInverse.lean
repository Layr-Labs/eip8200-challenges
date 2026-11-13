import Challenge.Modexp.Submission.Proofs.Prepared.R9Shared.Complete
import Challenge.Modexp.Submission.Proofs.Cycle.SquareFrames

noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace CycleSubmission.CachedInverse
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast

def loaderProgram : List Instr :=
 [.op (.Dup ⟨15,by decide⟩),.op (.Swap ⟨10,by decide⟩),.op .POP,.push 5 768,.op .MLOAD]

def initial (s : State) (inv count : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
 {s with
   pc := UInt256.ofNat 5575
   stack := CycleSubmission.SquareMeaning.frame0 inv a b n (count :: inv :: rest)}

def loaded (s : State) (inv count : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
 {s with
   pc := UInt256.ofNat 5585
   stack := MachineState.readWord s.memory 768 ::
     (CycleSubmission.SquareMeaning.frame0 inv a b n (count :: inv :: rest)).set 10 inv}

theorem run_loader (s : State) (inv count : UInt256) (a b n : Nat → UInt256)
 (rest : List UInt256) (hcap : rest.length ≤ 959) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions loaderProgram (initial s inv count a b n rest) =
 some (loaded s inv count a b n rest) := by
 have hf := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
 have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
 simp [loaderProgram,initial,loaded,CycleSubmission.SquareMeaning.frame0,List.set,
   runInstructions,Stepper.runInstr,List.exchange,State.activeWordsAfterUInt256,hf,
   Word.literal_eq_ofNat,Word.word_toNat_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod,
   capacity,Nat.add_assoc]

def oldLoaderProgram : List Instr :=
 [.push 2 2720,.op .MLOAD,.op (.Swap ⟨10,by decide⟩),.op .POP,.push 2 768,.op .MLOAD]

theorem run_old_loader (s : State) (inv count : UInt256) (a b n : Nat → UInt256)
 (rest : List UInt256) (hcap : rest.length ≤ 959) (hact : 88 ≤ s.activeWords.toNat)
 (hread : MachineState.readWord s.memory 2720 = inv) :
 runInstructions oldLoaderProgram (initial s inv count a b n rest) =
 some (loaded s inv count a b n rest) := by
 have hf := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
 have hi := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
 have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
 simp [oldLoaderProgram,initial,loaded,CycleSubmission.SquareMeaning.frame0,List.set,
   runInstructions,Stepper.runInstr,List.exchange,State.activeWordsAfterUInt256,hf,hi,hread,
   Word.literal_eq_ofNat,Word.word_toNat_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod,
   capacity,Nat.add_assoc]

theorem replace_loader (tail : List Instr) (s : State) (inv count : UInt256)
 (a b n : Nat → UInt256) (rest : List UInt256)
 (hcap : rest.length ≤ 959) (hact : 88 ≤ s.activeWords.toNat)
 (hread : MachineState.readWord s.memory 2720 = inv) :
 runInstructions (loaderProgram ++ tail) (initial s inv count a b n rest) =
 runInstructions (oldLoaderProgram ++ tail) (initial s inv count a b n rest) := by
 rw [runInstructions_append,runInstructions_append,
   run_loader s inv count a b n rest hcap hact,
   run_old_loader s inv count a b n rest hcap hact hread]

theorem provided_prefix :
 R9InvConsumeComplete.program = oldLoaderProgram ++ R9InvConsumeComplete.program.drop 6 := by
 rfl

def squareProgram : List Instr := loaderProgram ++ R9InvConsumeComplete.program.drop 6

theorem run_square (s : State) (inv count : UInt256) (a b n : Nat → UInt256)
 (rest : List UInt256) (hcap : rest.length ≤ 958) (hact : 88 ≤ s.activeWords.toNat)
 (hmem : CycleSubmission.SquareMeaning.Memory0 s.memory inv a b n)
 (ha : ∀ i < 8, (a i).toNat < 2^240) :
 runInstructions squareProgram (initial s inv count a b n rest) =
 some {s with
   pc := UInt256.ofNat 7661
   memory := R9InvConsumeComplete.historyMemory s.memory inv a b n
   stack := CycleSubmission.SquareMeaning.frame15 inv a b n (count :: inv :: rest)} := by
 have hh := R9InvConsumeComplete.run s inv a b n (count :: inv :: rest)
   (by simp; omega) hact hmem ha
 have he := replace_loader (R9InvConsumeComplete.program.drop 6) s inv count a b n rest
   (by omega) hact hmem.at2720
 rw [← provided_prefix] at he
 change runInstructions squareProgram (initial s inv count a b n rest) =
   runInstructions R9InvConsumeComplete.program (initial s inv count a b n rest) at he
 exact he.trans hh


theorem run (s : State) (inv : UInt256) (a b n : Nat → UInt256)
 (rest : List UInt256) (hcache : rest[1]? = some inv)
 (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
 (hmem : CycleSubmission.SquareMeaning.Memory0 s.memory inv a b n)
 (ha : ∀ i < 8, (a i).toNat < 2^240) :
 runInstructions squareProgram
   {s with pc := UInt256.ofNat 5575, stack := CycleSubmission.SquareMeaning.frame0 inv a b n rest} =
 some {s with
   pc := UInt256.ofNat 7661
   memory := R9InvConsumeComplete.historyMemory s.memory inv a b n
   stack := CycleSubmission.SquareMeaning.frame15 inv a b n rest} := by
 cases rest with
 | nil => simp at hcache
 | cons count rest =>
   cases rest with
   | nil => simp at hcache
   | cons value rest =>
     have hv : value = inv := by simpa using hcache
     subst value
     exact run_square s inv count a b n rest (by simp only [List.length_cons] at hcap; omega) hact hmem ha

end CycleSubmission.CachedInverse
