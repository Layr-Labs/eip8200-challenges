import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardCheck

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# One-instruction steps for the guard

Handing `simp` a whole block makes it unfold `runLocated`, evaluate
`instructionPC` over the chunked instruction list and scan the 6572-byte array
for a `JUMPDEST`.  Taking one instruction at a time, with the program counter
supplied from a named lemma, keeps all three opaque.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

/-- The machine at a program counter with a given stack. -/
def stG (input : ByteArray) (pc : Nat) (stk : List UInt256) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat pc, stack := stk }

@[simp] theorem stG_code (input : ByteArray) (pc : Nat) (stk : List UInt256) :
    (stG input pc stk).executionEnv.code = submissionBytecode := rfl

@[simp] theorem stG_stack (input : ByteArray) (pc : Nat) (stk : List UInt256) :
    (stG input pc stk).stack = stk := rfl

theorem pcFactG (input : ByteArray) (idx pc : Nat) (stk : List UInt256)
    (hpc : pc < 2 ^ 256)
    (h : Artifact.submissionArtifact.instructionPC idx = pc) :
    (stG input pc stk).pc.toNat = Artifact.submissionArtifact.instructionPC idx := by
  rw [h]
  show (UInt256.ofNat pc).toNat = pc
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hpc]

theorem runLocated_of_pcG {artifact : Challenge.EvmProof.ProgramArtifact}
    {fork : Fork} (located : Challenge.EvmProof.Stepper.Located artifact fork)
    {s : State} (h : s.pc.toNat = artifact.instructionPC located.index) :
    Challenge.EvmProof.Stepper.runLocated located s =
      Challenge.EvmProof.Stepper.runInstr located.instruction s := by
  unfold Challenge.EvmProof.Stepper.runLocated
  rw [if_pos h]

theorem runLocatedBlock_singleG {artifact : Challenge.EvmProof.ProgramArtifact}
    {fork : Fork} (l : Challenge.EvmProof.Stepper.Located artifact fork) (s : State) :
    Challenge.EvmProof.Stepper.runLocatedBlock [l] s =
      Challenge.EvmProof.Stepper.runLocated l s := by
  unfold Challenge.EvmProof.Stepper.runLocatedBlock
  cases h : Challenge.EvmProof.Stepper.runLocated l s <;> simp

theorem stepG_push (input : ByteArray) (pc w : Nat) (v : UInt256) (stk : List UInt256)
    (hlen : stk.length < 1024) (hw : w ≠ 0) (hwlt : w < 33)
    (hpc : pc + (w + 1) < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.push ⟨w, by omega⟩ v) (stG input pc stk) =
      some (stG input (pc + (w + 1)) (v :: stk)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp [stG, if_neg hw, Challenge.EvmProof.Word.ofNat_add_ofNat hpc]

theorem stepG_push0 (input : ByteArray) (pc : Nat) (stk : List UInt256)
    (hlen : stk.length < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.push ⟨0, by omega⟩ 0) (stG input pc stk) =
      some (stG input (pc + 1) (⟨0⟩ :: stk)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp [stG, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepG_calldataload (input : ByteArray) (pc : Nat) (off : UInt256)
    (rest : List UInt256) (hlen : rest.length + 1 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .CALLDATALOAD) (stG input pc (off :: rest)) =
      some (stG input (pc + 1) (MachineState.readWord input off.toNat :: rest)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stG, Challenge.Ripemd160.initialState_calldata,
    Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepG_dup1 (input : ByteArray) (pc : Nat) (a : UInt256) (rest : List UInt256)
    (hlen : rest.length + 1 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op (.Dup ⟨0, by decide⟩))
        (stG input pc (a :: rest)) =
      some (stG input (pc + 1) (a :: a :: rest)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stG_stack]
  show (match some a with
    | some value => some { stG input pc (a :: rest) with
        stack := value :: (stG input pc (a :: rest)).stack
        pc := (stG input pc (a :: rest)).pc.succ }
    | none => none) = _
  simp only [stG, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepG_xor (input : ByteArray) (pc : Nat) (a b : UInt256) (rest : List UInt256)
    (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .XOR) (stG input pc (a :: b :: rest)) =
      some (stG input (pc + 1) (UInt256.xor a b :: rest)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stG, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepG_pop (input : ByteArray) (pc : Nat) (a : UInt256) (rest : List UInt256)
    (hlen : rest.length + 1 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .POP) (stG input pc (a :: rest)) =
      some (stG input (pc + 1) rest) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stG, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepG_jumpdest (input : ByteArray) (pc : Nat) (stk : List UInt256)
    (hlen : stk.length < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .JUMPDEST) (stG input pc stk) =
      some (stG input (pc + 1) stk) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stG, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepG_jump (input : ByteArray) (pc target : Nat) (rest : List UInt256)
    (hlen : rest.length + 1 < 1024) (ht : target < 2 ^ 256)
    (hvalid : Decode.isValidJumpDest submissionBytecode target = true) :
    Challenge.EvmProof.Stepper.runInstr (.op .JUMP)
        (stG input pc (UInt256.ofNat target :: rest)) = some (stG input target rest) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stG_code, stG_stack]
  rw [show (UInt256.ofNat target).toNat = target from by
        rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt ht]]
  simp only [stG, if_pos hvalid]

theorem stepG_jumpi_taken (input : ByteArray) (pc target : Nat) (c : UInt256)
    (rest : List UInt256) (hlen : rest.length + 2 < 1024) (ht : target < 2 ^ 256)
    (hc : UInt256.isTrue c = true)
    (hvalid : Decode.isValidJumpDest submissionBytecode target = true) :
    Challenge.EvmProof.Stepper.runInstr (.op .JUMPI)
        (stG input pc (UInt256.ofNat target :: c :: rest)) =
      some (stG input target rest) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stG_stack, stG_code, hc, if_true]
  rw [show (UInt256.ofNat target).toNat = target from by
        rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt ht],
    if_pos hvalid]
  simp only [stG]

/-- One located step is one block. -/
theorem blockOf (l : Located) {s t : State}
    (hpc : s.pc.toNat = Artifact.submissionArtifact.instructionPC l.index)
    (h : Challenge.EvmProof.Stepper.runInstr l.instruction s = some t) :
    Challenge.EvmProof.Stepper.runLocatedBlock [l] s = some t := by
  rw [runLocatedBlock_singleG, runLocated_of_pcG l hpc, h]

def soundG (l : Located) {s t : State}
    (h : Challenge.EvmProof.Stepper.runLocatedBlock [l] s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) : GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    [l] hcode hfork h hrun hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
