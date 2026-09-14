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

def controlProgram : List Instr :=
  [.op (.Swap ⟨0, by decide⟩), .push 1 4, .op .ADD, .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .push 1 8, .op .GT, .push 2 2505, .op .JUMPI]

/-- The four bytes after the half-byte branch. The counter slot is dead here:
the byte loop pushes a fresh zero at pc 219 and pops this slot at pc 225, so
the landing pad only has to walk the program counter to the tail. -/
def resetProgram : List Instr :=
  [.op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST]

theorem run_start (hcap : rest.length ≤ 1000) :
    runInstructions [.op .JUMPDEST]
      (framed s 2505 ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest)) =
      some (framed s 2506 ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest)) := by
  have h8 : rest.length + 8 < 1024 := by omega
  simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, framed, h8]
  decide

theorem run_control (c : Nat) (hc : c = 0 ∨ c = 4) (hcap : rest.length ≤ 1000)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 2505 = true) :
    runInstructions controlProgram
      (framed s 2594 ([Bm1,UInt256.ofNat c,byte,offset,outerW,acc,base,m] ++ rest)) =
      some (framed s (if c = 0 then 2505 else 2607)
        ([Bm1,UInt256.ofNat (c+4),byte,offset,outerW,acc,base,m] ++ rest)) := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have htarget : (2505 : UInt256).toNat = 2505 := by decide
  rcases hc with rfl | rfl <;>
    simp [controlProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr, framed,
      h8, h9, h10, List.exchange, UInt256.isTrue, UInt256.gt, UInt256.lt,
      Challenge.EvmProof.Word.word_toNat_ofNat, htarget, hjd,
      Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.literal_eq_ofNat]

theorem run_pad2607 (hcap : rest.length ≤ 1000) :
    runInstructions [.op .JUMPDEST]
      (framed s 2607 ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest)) =
      some (framed s 2608 ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest)) := by
  have h8 : rest.length + 8 < 1024 := by omega
  simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, framed, h8]
  first | done | decide

theorem run_pad2608 (hcap : rest.length ≤ 1000) :
    runInstructions [.op .JUMPDEST]
      (framed s 2608 ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest)) =
      some (framed s 2609 ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest)) := by
  have h8 : rest.length + 8 < 1024 := by omega
  simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, framed, h8]
  first | done | decide

theorem run_pad2609 (hcap : rest.length ≤ 1000) :
    runInstructions [.op .JUMPDEST]
      (framed s 2609 ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest)) =
      some (framed s 2610 ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest)) := by
  have h8 : rest.length + 8 < 1024 := by omega
  simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, framed, h8]
  first | done | decide

theorem run_pad2610 (hcap : rest.length ≤ 1000) :
    runInstructions [.op .JUMPDEST]
      (framed s 2610 ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest)) =
      some (framed s 2611 ([Bm1,counter,byte,offset,outerW,acc,base,m] ++ rest)) := by
  have h8 : rest.length + 8 < 1024 := by omega
  simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, framed, h8]
  first | done | decide

/-- The landing pad is four inert `JUMPDEST`s: the stack is untouched and the
program counter walks from the half-byte branch to the byte-loop tail. -/
theorem run_reset (hcap : rest.length ≤ 1000) :
    runInstructions resetProgram
      (framed s 2607 ([Bm1,8,byte,offset,outerW,acc,base,m] ++ rest)) =
      some (framed s 2611 ([Bm1,8,byte,offset,outerW,acc,base,m] ++ rest)) := by
  have h1 := run_pad2607 s Bm1 8 byte offset outerW acc base m rest hcap
  have h2 := run_pad2608 s Bm1 8 byte offset outerW acc base m rest hcap
  have h3 := run_pad2609 s Bm1 8 byte offset outerW acc base m rest hcap
  have h4 := run_pad2610 s Bm1 8 byte offset outerW acc base m rest hcap
  exact runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _
      (runInstructions_append_some _ _ _ _ _ h1 h2) h3) h4

end Challenge.Modexp.Submission.Proofs.Bytecode.WordBitsFourCore
