import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
import Mathlib.Algebra.Group.Fin.Basic
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace Challenge.Modexp.Submission.Proofs.Fast.DiagonalSchedule
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel

def diagonalPrefix : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .GT,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD]

theorem diagonalPrefix_run (s : State) (pc tb x P hd w3 ent stride M : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions diagonalPrefix
      { s with pc := pc, stack := tb :: x :: P :: hd :: w3 :: ent :: stride :: M :: rest } =
    some { s with pc := advancePC 15 pc,
                  stack := UInt256.mulMod (x + tb) x M :: UInt256.gt x (x + tb) ::
                    ((x + tb) * x) :: (x + (x + tb)) :: P :: hd :: w3 :: ent :: stride :: M :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 13) : rest.length + j < 1024 := by omega
  simp [diagonalPrefix, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, capacity, Nat.add_assoc, advancePC]


theorem mul_comm_word (a b : UInt256) : a * b = b * a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val * b.val).val = (b.val * a.val).val
  rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]

theorem mulMod_comm_word (a b m : UInt256) :
    UInt256.mulMod a b m = UInt256.mulMod b a m := by
  simp [UInt256.mulMod, Nat.mul_comm]

theorem diagonalPrefix_canonical (s : State) (pc tb x P hd w3 ent stride M : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions diagonalPrefix
      { s with pc := pc, stack := tb :: x :: P :: hd :: w3 :: ent :: stride :: M :: rest } =
    some { s with pc := advancePC 15 pc,
                  stack := UInt256.mulMod x (x + tb) M :: UInt256.lt (x + tb) x ::
                    (x * (x + tb)) :: ((x + tb) + x) :: P :: hd :: w3 :: ent :: stride :: M :: rest } := by
  simpa only [mulMod_comm_word (x + tb) x M, mul_comm_word (x + tb) x,
    Challenge.EvmProof.Word.word_add_comm x (x + tb), UInt256.gt, UInt256.lt] using
    diagonalPrefix_run s pc tb x P hd w3 ent stride M rest hcap

def diagonalPrefixSub : List Instr := diagonalPrefix ++ [.op .SUB]

theorem diagonalPrefixSub_run (s : State) (pc tb x P hd w3 ent stride M : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions diagonalPrefixSub
      { s with pc := pc, stack := tb :: x :: P :: hd :: w3 :: ent :: stride :: M :: rest } =
    some { s with pc := advancePC 16 pc,
                  stack := (UInt256.mulMod x (x + tb) M - UInt256.lt (x + tb) x) ::
                    (x * (x + tb)) :: ((x + tb) + x) :: P :: hd :: w3 :: ent :: stride :: M :: rest } := by
  have h := diagonalPrefix_canonical s pc tb x P hd w3 ent stride M rest hcap
  rw [diagonalPrefixSub, runInstructions_append_some _ _ _ _ _ h]
  simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, advancePC]
  omega

end Challenge.Modexp.Submission.Proofs.Fast.DiagonalSchedule
