import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
import Challenge.EvmProof.Word

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000
namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordBitsFourCore
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

def framed (s : State) (pc : UInt256) (stack : List UInt256) : State :=
  { s with pc := pc, stack := stack }

def bodyProgram (shift : UInt256) : List Instr :=
  [.op (.Dup ⟨7, by decide⟩), .push 1 1, .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .push 1 shift, .op .SUB, .op .SHR, .op .AND,
   .op (.Dup ⟨2, by decide⟩), .op .MUL, .push 1 1, .op .ADD,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD, .op .MULMOD, .op (.Swap ⟨5, by decide⟩), .op .POP]

def stepValue (shift counter Bm1 byte acc m : UInt256) : UInt256 :=
  UInt256.mulMod (UInt256.mulMod acc acc m)
    (1 + Bm1 * UInt256.land (UInt256.shiftRight byte (shift - counter)) 1) m

def selectProgram (shift : UInt256) : List Instr := (bodyProgram shift).take 8
def factorProgram : List Instr := ((bodyProgram 0).drop 8).take 4
def productProgram : List Instr := (bodyProgram 0).drop 12

variable (s : State) (pc shift Bm1 counter byte offset outerW acc base m : UInt256)
  (rest : List UInt256)

theorem run_select (hcap : rest.length ≤ 1000) :
    runInstructions (selectProgram shift)
      (framed s pc ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest)) =
      some (framed s (pc + 10)
        ([UInt256.land (UInt256.shiftRight byte (shift-counter)) 1,m,Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest)) := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  have h13 : rest.length + 13 < 1024 := by omega
  simp [selectProgram, bodyProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, framed,
    h8, h9, h10, h11, h12, h13, List.exchange,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.literal_eq_ofNat]

theorem run_factor (bit : UInt256) (hcap : rest.length ≤ 1000) :
    runInstructions factorProgram
      (framed s pc ([bit,m,Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest)) =
      some (framed s (pc + 5)
        ([1+Bm1*bit,m,Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest)) := by
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  simp [factorProgram, bodyProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, framed,
    h10, h11, List.exchange, succ_eq_add, word_add_assoc,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.literal_eq_ofNat]

theorem run_product (factor : UInt256) (hcap : rest.length ≤ 1000) :
    runInstructions productProgram
      (framed s pc ([factor,m,Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest)) =
      some (framed s (pc + 7)
        ([Bm1,counter,byte,offset,outerW,UInt256.mulMod (UInt256.mulMod acc acc m) factor m,base,m] ++ rest)) := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  have h13 : rest.length + 13 < 1024 := by omega
  simp [productProgram, bodyProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, framed,
    h8, h9, h10, h11, h12, h13, List.exchange,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.literal_eq_ofNat]

theorem run_body (hcap : rest.length ≤ 1000) :
    runInstructions (bodyProgram shift)
      (framed s pc ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest)) =
      some (framed s (pc + 22)
        ([Bm1,counter,byte,offset,outerW,stepValue shift counter Bm1 byte acc m,base,m] ++ rest)) := by
  have ha := run_select s pc shift Bm1 counter byte offset outerW acc base m rest hcap
  have hb := run_factor s (pc+10) Bm1 counter byte offset outerW acc base m rest
    (UInt256.land (UInt256.shiftRight byte (shift-counter)) 1) hcap
  have hc := run_product s ((pc+10)+5) Bm1 counter byte offset outerW acc base m rest
    (1+Bm1*UInt256.land (UInt256.shiftRight byte (shift-counter)) 1) hcap
  have hall := runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _ ha hb) hc
  have hpc : ((pc+10)+5)+7 = pc+22 := by
    simp [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat]
  simpa only [show (selectProgram shift ++ factorProgram) ++ productProgram = bodyProgram shift from rfl,
    hpc, stepValue] using hall

/-- The one-bit loop control at pc 2400: `DUP2 PUSH1 7 GT SWAP2 PUSH1 1 ADD SWAP2
PUSH2 2377 JUMPI`. It re-enters the single body while the counter is below seven,
after incrementing the counter; on the eighth bit it falls through to the exit at
pc 2413 with the counter at eight. -/
def controlProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .push 1 7, .op .GT,
   .op (.Swap ⟨1, by decide⟩), .push 1 1, .op .ADD, .op (.Swap ⟨1, by decide⟩),
   .push 2 2377, .op .JUMPI]

theorem run_start (hcap : rest.length ≤ 1000) :
    runInstructions [.op .JUMPDEST]
      (framed s 2377 ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest)) =
      some (framed s 2378 ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest)) := by
  have h8 : rest.length + 8 < 1024 := by omega
  simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, framed, h8]
  decide

theorem gt_seven_of_lt (c : Nat) (hc : c < 7) :
    UInt256.gt (UInt256.ofNat 7) (UInt256.ofNat c) = UInt256.ofNat 1 := by
  unfold UInt256.gt
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (show c < 2 ^ 256 by omega), Nat.mod_eq_of_lt (show 7 < 2 ^ 256 by decide)]
  exact if_pos hc

theorem gt_seven_seven :
    UInt256.gt (UInt256.ofNat 7) (UInt256.ofNat 7) = UInt256.ofNat 0 := by
  decide

/-- One pass of the loop control with the counter at `c`: bits zero to six jump
back to the body head at 2377, the seventh bit falls through to the exit at 2413. -/
theorem run_control (c : Nat) (hc : c < 8) (hcap : rest.length ≤ 1000)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 2377 = true) :
    runInstructions controlProgram
      (framed s 2400 ([Bm1,UInt256.ofNat c,byte,offset,outerW,acc,base,m] ++ rest)) =
      some (framed s (if c < 7 then 2377 else 2413)
        ([Bm1,UInt256.ofNat (c+1),byte,offset,outerW,acc,base,m] ++ rest)) := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have htarget : (2377 : UInt256).toNat = 2377 := by decide
  have ht1 : UInt256.isTrue (UInt256.ofNat 1) := by decide
  have ht0 : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  by_cases h7 : c < 7
  · have hg := gt_seven_of_lt c h7
    simp [controlProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, framed,
      h8, h9, h10, List.exchange, hg, ht1, h7,
      Challenge.EvmProof.Word.word_toNat_ofNat, htarget, hjd,
      Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat]
    all_goals (try rw [Nat.add_comm])
  · have hc7 : c = 7 := by omega
    subst hc7
    simp [controlProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, framed,
      h8, h9, h10, List.exchange, gt_seven_seven, ht0,
      Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat]

end Challenge.Modexp.Submission.Proofs.Bytecode.WordBitsFourCore
