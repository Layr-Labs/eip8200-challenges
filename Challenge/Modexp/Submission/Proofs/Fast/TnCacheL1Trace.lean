import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL1
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFused
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandSnapshot
import Challenge.Modexp.Submission.Proofs.Fast.SquareModel

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-!
# The uniform first-loop block of the kernel

Every first-loop block `k = 1..7` of the sqCP1m kernel is the 37-byte
`JUMPDEST; PUSH2 (0x2300 + 32(7-k)); MLOAD; DUP9; <product>; <finish t>` (the
last block included: its load is the generic staged load with offset 0).  The
limb `a_j` is read from the staged copy at `2368 + 32(n-1-j)`, which the
`StagedOperand.Snapshot` invariant identifies with the operand limb.

The step is stated on an arbitrary MAC state `q` (memory and running carry),
producing `SquareModel.l1StepOn q bi pa n j`; the multiply rows are the instance
`q = Monpro.l1Step mem bi pa n j` (`SquareModel.l1Step_succ_eq`, by `rfl`), the
square rows use the prologue state and `SquareModel.l1Run`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheL1Trace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore StagedOperand

/-- Staged-operand load `PUSH2 (2368 + off); MLOAD; DUP9`. -/
def loadProgram (off : UInt256) : List Instr :=
  [.push 2 (UInt256.ofNat 2368 + off), .op .MLOAD, .op (.Dup ⟨8, by decide⟩)]

def l1Program (off t : UInt256) : List Instr :=
  loadProgram off ++ CiosCached.macFusedProgram t t

/-- One uniform 37-byte first-loop block, including its leading `JUMPDEST`. -/
def stepProgram (off t : UInt256) : List Instr :=
  [.op .JUMPDEST] ++ l1Program off t

/-- The first-loop frame of `CiosCachedL1.state` on an arbitrary MAC state with an
arbitrary word in the old `pa` slot (now the row head `hd`). -/
def qState (template : State) (pc : UInt256) (q : MacState)
    (bi pbi hd pbEnd flag tn destination returnPC : UInt256) (rest : List UInt256) : State :=
  { template with
    pc := pc
    stack := [q.carry, bi, pbi, hd, pbEnd, flag, tn, allOnes, destination, returnPC] ++ rest
    memory := q.memory }

theorem run_load (template : State)
    (pc off carry bi pbi hd pbEnd flag tn destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat (UInt256.ofNat 2368 + off).toNat 32) = template.activeWords) :
    runInstructions (loadProgram off)
      (framed template pc
        ([carry, bi, pbi, hd, pbEnd, flag, tn, allOnes, destination, returnPC] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 5)
      ([maxWord, MachineState.readWord template.memory (UInt256.ofNat 2368 + off).toNat,
        carry, bi, pbi, hd, pbEnd, flag, tn, allOnes, destination, returnPC] ++ rest)) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  simp only [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    show (2 : Nat)^256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 from by decide,
    Nat.reduceMod] at hactive
  simp [runInstructions, loadProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hc10, hc11, hc12, State.activeWordsAfterUInt256, hactive, allOnes_value,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

theorem snapshot_read (mem : ByteArray) (pa n j : Nat) (h : Snapshot mem pa n) (hj : j < n) :
    MachineState.readWord mem (2368 + 32 * (n - 1 - j)) =
      MachineState.readWord mem (pa + 32 * (n - 1 - j)) :=
  h (n - 1 - j) (by omega)

/-- One staged first-loop cell (without the leading `JUMPDEST`) on any MAC state. -/
theorem run_l1 (template : State) (pc : UInt256) (q : MacState)
    (bi : UInt256) (pa n j : Nat) (off t : UInt256)
    (hoff : off.toNat = 32 * (n - 1 - j))
    (ht : t.toNat = 2112 + 32 * (n - 1 - j))
    (pbi hd pbEnd flag tn destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 88 ≤ template.activeWords.toNat) (hn : n ≤ 8) (hj : j < n)
    (hsnapshot : Snapshot q.memory pa n) :
    runInstructions (l1Program off t)
      (qState template pc q bi pbi hd pbEnd flag tn destination returnPC rest) =
    some (qState template (pc + UInt256.ofNat 36) (SquareModel.l1StepOn q bi pa n j)
      bi pbi hd pbEnd flag tn destination returnPC rest) := by
  have hsaddr : (UInt256.ofNat 2368 + off).toNat = 2368 + 32*(n-1-j) := by
    rw [CiosCachedL1.base_offset_toNat 2368 off (by omega), hoff]
  have hsread : MachineState.readWord q.memory (UInt256.ofNat 2368 + off).toNat =
      MachineState.readWord q.memory (pa + 32*(n-1-j)) := by
    rw [hsaddr]
    exact snapshot_read q.memory pa n j hsnapshot hj
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (2368 + 32*(n-1-j)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (2112 + 32*(n-1-j)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  let st : State := { template with memory := q.memory }
  have hA : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat
      (UInt256.ofNat 2368 + off).toNat 32) = st.activeWords := by
    simpa only [st, hsaddr] using hactA
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat t.toNat 32) =
      st.activeWords := by simpa only [st, ht] using hactT
  have hl := run_load st pc off q.carry bi pbi hd
    pbEnd flag tn destination returnPC rest hrest hA
  rw [show MachineState.readWord st.memory (UInt256.ofNat 2368 + off).toNat =
    MachineState.readWord q.memory (pa + 32*(n-1-j)) from hsread] at hl
  have hf := CiosCachedFused.run_fused st (pc + UInt256.ofNat 5)
    (MachineState.readWord q.memory (pa + 32*(n-1-j))) bi q.carry t t
    ([pbi, hd, pbEnd, flag, tn, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT hT
  have hall := runInstructions_append_some _ _ _ _ _ hl hf
  have hpc : (pc + UInt256.ofNat 5) + UInt256.ofNat 31 =
      pc + UInt256.ofNat 36 := by
    simp [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [l1Program, st, qState, framed, SquareModel.l1StepOn, ht, hpc,
    List.cons_append, List.nil_append] using hall

/-- The whole uniform block, `JUMPDEST` included (37 bytes). -/
theorem run_step (template : State) (pc : UInt256) (q : MacState)
    (bi : UInt256) (pa n j : Nat) (off t : UInt256)
    (hoff : off.toNat = 32 * (n - 1 - j))
    (ht : t.toNat = 2112 + 32 * (n - 1 - j))
    (pbi hd pbEnd flag tn destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 88 ≤ template.activeWords.toNat) (hn : n ≤ 8) (hj : j < n)
    (hsnapshot : Snapshot q.memory pa n) :
    runInstructions (stepProgram off t)
      (qState template pc q bi pbi hd pbEnd flag tn destination returnPC rest) =
    some (qState template (pc + UInt256.ofNat 37) (SquareModel.l1StepOn q bi pa n j)
      bi pbi hd pbEnd flag tn destination returnPC rest) := by
  have hc : rest.length + 10 < 1024 := by omega
  have hjd : runInstructions [.op .JUMPDEST]
      (qState template pc q bi pbi hd pbEnd flag tn destination returnPC rest) =
      some (qState template (pc + UInt256.ofNat 1) q bi pbi hd pbEnd flag tn destination returnPC rest) := by
    simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, qState, hc, succ_eq_add]
  have hl := run_l1 template (pc + UInt256.ofNat 1) q bi pa n j off t hoff ht
    pbi hd pbEnd flag tn destination returnPC rest hrest hactive hn hj hsnapshot
  have h := runInstructions_append_some _ _ _ _ _ hjd hl
  have hpc : pc + UInt256.ofNat 1 + UInt256.ofNat 36 = pc + UInt256.ofNat 37 := by
    rw [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  rw [hpc] at h
  exact h


#print axioms run_load
#print axioms run_l1
#print axioms run_step
end Challenge.Modexp.Submission.Proofs.Fast.TnCacheL1Trace
