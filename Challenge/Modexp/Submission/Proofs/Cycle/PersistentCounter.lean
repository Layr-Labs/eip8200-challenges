import Challenge.Modexp.Submission.Proofs.Cycle.CachedInverse
noncomputable section
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace CycleSubmission.PersistentCounter
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

def frame (inv count : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
 (SquareMeaning.frame0 inv a b n (count :: rest)).set 10 (a 5)

def program : List Instr :=
 [.push 1 1,.op (.Dup ⟨15,by decide⟩),.op .SUB,
  .op (.Swap ⟨14,by decide⟩),.push 2 5395,.op .JUMPI]

theorem run (s : State) (inv count : UInt256) (a b n : Nat → UInt256)
 (rest : List UInt256) (hcap : rest.length ≤ 959)
 (hjump : Decode.isValidJumpDest s.executionEnv.code 5395 = true) :
 runInstructions program {s with pc := UInt256.ofNat 7659, stack := frame inv count a b n rest} =
 some {s with pc := UInt256.ofNat (if count.toNat = 0 then 7668 else 5395), stack := frame inv (count-UInt256.ofNat 1) a b n rest} := by
 have capacity (j : Nat) (hj : j ≤ 20) : rest.length+j < 1024 := by omega
 by_cases hz : count.toNat = 0
 all_goals simp [program,frame,SquareMeaning.frame0,List.set,runInstructions,Stepper.runInstr,
   List.exchange,Word.literal_eq_ofNat,Word.word_toNat_ofNat,Word.succ_ofNat_mod,
   Word.ofNat_add_mod,UInt256.isTrue,hjump,hz,capacity,Nat.add_assoc]

#print axioms run

theorem square_frame (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) :
 R9InvConsumeComplete.persistentFrame15 inv a b n rest =
 (SquareMeaning.frame0 inv (WordHistory.squared inv a b n) b n rest).set 10 (WordHistory.squared inv a b n 5) := by
 rfl

def roundProgram : List Instr := CachedInverse.persistentProgram ++ program

theorem run_round (s : State) (inv count : UInt256) (a b n : Nat → UInt256)
 (rest : List UInt256) (hcap : rest.length ≤ 958) (hact : 88 ≤ s.activeWords.toNat)
 (hmem : LimbMemory.Holds s.memory inv a b n)
 (ha : ∀ i < 8, (a i).toNat < 2^240)
 (hjump : Decode.isValidJumpDest s.executionEnv.code 5395 = true) :
 runInstructions roundProgram (CachedInverse.persistentInitial s inv count a b n rest) =
 some {s with pc := UInt256.ofNat (if count.toNat = 0 then 7668 else 5395), memory := R9InvConsumeComplete.historyMemory s.memory inv a b n, stack := frame inv (count-UInt256.ofNat 1) (WordHistory.squared inv a b n) b n (inv :: rest)} := by
 have hk := CachedInverse.run_persistent s inv count a b n rest hcap hact hmem ha
 have hc := run ({s with memory := R9InvConsumeComplete.historyMemory s.memory inv a b n})
   inv count (WordHistory.squared inv a b n) b n (inv :: rest) (by simp; omega) hjump
 rw [square_frame] at hk
 exact runInstructions_append_some _ _ _ _ _ hk hc

theorem memory_output (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
 (hmem : LimbMemory.Holds mem inv a b n) :
 LimbMemory.Holds (R9InvConsumeComplete.historyMemory mem inv a b n)
   inv (WordHistory.squared inv a b n) b n := by
 constructor <;>
  simp (disch := decide) only [R9InvConsumeComplete.historyMemory,WordHistory.squared,
   Challenge.EvmProof.Memory.readWord_writeWord,
   CycleSubmission.Prepared.Arithmetic.read_disjoint,
   hmem.at768,hmem.at1344,hmem.at1376,hmem.at2720,hmem.at1568,hmem.at1600,
   hmem.at32,hmem.at64,hmem.at128,hmem.at160,hmem.at1664]

#print axioms run_round
#print axioms memory_output

end CycleSubmission.PersistentCounter
