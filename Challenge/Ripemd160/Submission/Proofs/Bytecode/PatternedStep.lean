import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# One-instruction steps for the scan

Handing `simp` a whole block makes it unfold `runLocated`, evaluate
`instructionPC` over the chunked instruction list and scan the 5305-byte array
for a `JUMPDEST`, and the two shifts in the straddle correction make it carry
both branches of `UInt256.shiftRight` through every later instruction.  Taking
one instruction at a time, with the program counter supplied from a named
lemma, keeps the artifact and the arithmetic opaque.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

/-- The machine at a program counter with a given stack. -/
def stS (input : ByteArray) (pc : Nat) (stk : List UInt256) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat pc, stack := stk }

@[simp] theorem stS_code (input : ByteArray) (pc : Nat) (stk : List UInt256) :
    (stS input pc stk).executionEnv.code = submissionBytecode := rfl

@[simp] theorem stS_stack (input : ByteArray) (pc : Nat) (stk : List UInt256) :
    (stS input pc stk).stack = stk := rfl

theorem pcFactS (input : ByteArray) (idx pc : Nat) (stk : List UInt256)
    (hpc : pc < 2 ^ 256)
    (h : Artifact.submissionArtifact.instructionPC idx = pc) :
    (stS input pc stk).pc.toNat = Artifact.submissionArtifact.instructionPC idx := by
  rw [h]
  show (UInt256.ofNat pc).toNat = pc
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hpc]

theorem runLocated_of_pcS {artifact : Challenge.EvmProof.ProgramArtifact}
    {fork : Fork} (located : Challenge.EvmProof.Stepper.Located artifact fork)
    {s : State} (h : s.pc.toNat = artifact.instructionPC located.index) :
    Challenge.EvmProof.Stepper.runLocated located s =
      Challenge.EvmProof.Stepper.runInstr located.instruction s := by
  unfold Challenge.EvmProof.Stepper.runLocated
  rw [if_pos h]

theorem runLocatedBlock_singleS {artifact : Challenge.EvmProof.ProgramArtifact}
    {fork : Fork} (l : Challenge.EvmProof.Stepper.Located artifact fork) (s : State) :
    Challenge.EvmProof.Stepper.runLocatedBlock [l] s =
      Challenge.EvmProof.Stepper.runLocated l s := by
  unfold Challenge.EvmProof.Stepper.runLocatedBlock
  cases h : Challenge.EvmProof.Stepper.runLocated l s <;> simp

/-! ### The instructions the scan uses -/

theorem stepS_jumpdest (input : ByteArray) (pc : Nat) (stk : List UInt256)
    (hlen : stk.length < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .JUMPDEST) (stS input pc stk) =
      some (stS input (pc + 1) stk) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepS_push (input : ByteArray) (pc w : Nat) (v : UInt256) (stk : List UInt256)
    (hlen : stk.length < 1024) (hw : w ≠ 0) (hwlt : w < 33)
    (hpc : pc + (w + 1) < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.push ⟨w, by omega⟩ v) (stS input pc stk) =
      some (stS input (pc + (w + 1)) (v :: stk)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp [stS, if_neg hw, Challenge.EvmProof.Word.ofNat_add_ofNat hpc]

theorem stepS_push0 (input : ByteArray) (pc : Nat) (stk : List UInt256)
    (hlen : stk.length < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.push ⟨0, by omega⟩ 0) (stS input pc stk) =
      some (stS input (pc + 1) ((⟨0⟩ : UInt256) :: stk)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp [stS, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepS_pop (input : ByteArray) (pc : Nat) (a : UInt256) (rest : List UInt256)
    (hlen : rest.length + 1 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .POP) (stS input pc (a :: rest)) =
      some (stS input (pc + 1) rest) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepS_dup (input : ByteArray) (pc n : Nat) (hn : n < 16) (stk : List UInt256)
    (v : UInt256) (hget : stk[n]? = some v)
    (hlen : stk.length < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op (.Dup ⟨n, hn⟩)) (stS input pc stk) =
      some (stS input (pc + 1) (v :: stk)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS_stack, hget]
  simp only [stS, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepS_swap (input : ByteArray) (pc n : Nat) (hn : n < 16)
    (stk out : List UInt256) (hex : stk.exchange 0 (n + 1) = some out)
    (hlen : stk.length < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op (.Swap ⟨n, hn⟩)) (stS input pc stk) =
      some (stS input (pc + 1) out) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS_stack, hex]
  simp only [stS, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepS_calldataload (input : ByteArray) (pc : Nat) (off : UInt256)
    (rest : List UInt256) (hlen : rest.length + 1 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .CALLDATALOAD)
        (stS input pc (off :: rest)) =
      some (stS input (pc + 1) (MachineState.readWord input off.toNat :: rest)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS, Challenge.Ripemd160.initialState_calldata,
    Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepS_add (input : ByteArray) (pc : Nat) (a b : UInt256) (rest : List UInt256)
    (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .ADD) (stS input pc (a :: b :: rest)) =
      some (stS input (pc + 1) ((a + b) :: rest)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepS_mul (input : ByteArray) (pc : Nat) (a b : UInt256) (rest : List UInt256)
    (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .MUL) (stS input pc (a :: b :: rest)) =
      some (stS input (pc + 1) ((a * b) :: rest)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepS_sub (input : ByteArray) (pc : Nat) (a b : UInt256) (rest : List UInt256)
    (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .SUB) (stS input pc (a :: b :: rest)) =
      some (stS input (pc + 1) ((a - b) :: rest)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepS_and (input : ByteArray) (pc : Nat) (a b : UInt256) (rest : List UInt256)
    (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .AND) (stS input pc (a :: b :: rest)) =
      some (stS input (pc + 1) (UInt256.land a b :: rest)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepS_or (input : ByteArray) (pc : Nat) (a b : UInt256) (rest : List UInt256)
    (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .OR) (stS input pc (a :: b :: rest)) =
      some (stS input (pc + 1) (UInt256.lor a b :: rest)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepS_xor (input : ByteArray) (pc : Nat) (a b : UInt256) (rest : List UInt256)
    (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .XOR) (stS input pc (a :: b :: rest)) =
      some (stS input (pc + 1) (UInt256.xor a b :: rest)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepS_gt (input : ByteArray) (pc : Nat) (a b : UInt256) (rest : List UInt256)
    (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .GT) (stS input pc (a :: b :: rest)) =
      some (stS input (pc + 1) (UInt256.gt a b :: rest)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepS_eq (input : ByteArray) (pc : Nat) (a b : UInt256) (rest : List UInt256)
    (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .EQ) (stS input pc (a :: b :: rest)) =
      some (stS input (pc + 1) (UInt256.eq a b :: rest)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepS_shr (input : ByteArray) (pc : Nat) (shift value : UInt256)
    (rest : List UInt256) (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .SHR)
        (stS input pc (shift :: value :: rest)) =
      some (stS input (pc + 1) (UInt256.shiftRight value shift :: rest)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepS_shl (input : ByteArray) (pc : Nat) (shift value : UInt256)
    (rest : List UInt256) (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .SHL)
        (stS input pc (shift :: value :: rest)) =
      some (stS input (pc + 1) (UInt256.shiftLeft value shift :: rest)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepS_jump (input : ByteArray) (pc target : Nat) (d : UInt256)
    (rest : List UInt256) (hlen : rest.length + 1 < 1024) (ht : target < 2 ^ 256)
    (hd : d = UInt256.ofNat target)
    (hvalid : Decode.isValidJumpDest submissionBytecode target = true) :
    Challenge.EvmProof.Stepper.runInstr (.op .JUMP) (stS input pc (d :: rest)) =
      some (stS input target rest) := by
  subst hd
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS_code, stS_stack]
  rw [show (UInt256.ofNat target).toNat = target from by
        rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt ht]]
  simp only [stS, if_pos hvalid]

theorem stepS_jumpi_taken (input : ByteArray) (pc target : Nat) (d c : UInt256)
    (rest : List UInt256) (hlen : rest.length + 2 < 1024) (ht : target < 2 ^ 256)
    (hd : d = UInt256.ofNat target) (hc : UInt256.isTrue c)
    (hvalid : Decode.isValidJumpDest submissionBytecode target = true) :
    Challenge.EvmProof.Stepper.runInstr (.op .JUMPI) (stS input pc (d :: c :: rest)) =
      some (stS input target rest) := by
  subst hd
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS_code, stS_stack]
  rw [if_pos hc, show (UInt256.ofNat target).toNat = target from by
        rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt ht],
    if_pos hvalid]
  simp only [stS]

theorem stepS_jumpi_fall (input : ByteArray) (pc : Nat) (d c : UInt256)
    (rest : List UInt256) (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256)
    (hc : ¬ UInt256.isTrue c) :
    Challenge.EvmProof.Stepper.runInstr (.op .JUMPI) (stS input pc (d :: c :: rest)) =
      some (stS input (pc + 1) rest) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stS_stack]
  rw [if_neg hc]
  simp only [stS, Challenge.EvmProof.Word.succ_ofNat hpc]

/-- One located step is one block. -/
theorem blockOfS (l : Located) {s t : State}
    (hpc : s.pc.toNat = Artifact.submissionArtifact.instructionPC l.index)
    (h : Challenge.EvmProof.Stepper.runInstr l.instruction s = some t) :
    Challenge.EvmProof.Stepper.runLocatedBlock [l] s = some t := by
  rw [runLocatedBlock_singleS, runLocated_of_pcS l hpc, h]

def soundS (l : Located) {s t : State}
    (h : Challenge.EvmProof.Stepper.runLocatedBlock [l] s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) : GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    [l] hcode hfork h hrun hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
