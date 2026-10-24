import Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
import Challenge.EvmProof.Meter
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# One-instruction steps for the unrolled exponent-bit block

Handing `simp` a whole copy makes it unfold `runLocated` and evaluate
`instructionPC` over the chunked instruction list.  Taking one instruction at a
time, with the program counter supplied from a named lemma and the frame below
the copy left as an opaque list, keeps the artifact out of every goal.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordStep

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located := Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) : Located :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) : Located :=
  ⟨index, .push width value, hget, hwf⟩

/-- The machine of `s` at a program counter with a given stack. -/
def stW (s : State) (pc : Nat) (stk : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc, stack := stk }

@[simp] theorem stW_code (s : State) (pc : Nat) (stk : List UInt256) :
    (stW s pc stk).executionEnv.code = s.executionEnv.code := rfl

@[simp] theorem stW_stack (s : State) (pc : Nat) (stk : List UInt256) :
    (stW s pc stk).stack = stk := rfl

/-- What `runLocatedBlock_sound` needs of the frame the copies run in. -/
structure Frame (s : State) : Prop where
  code : s.executionEnv.code = Artifact.submissionArtifact.code
  fork : s.fork = .Osaka
  halt : s.halt = .Running
  np : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false

theorem pcFactW (s : State) (idx pc : Nat) (stk : List UInt256)
    (hpc : pc < 2 ^ 256)
    (h : Artifact.submissionArtifact.instructionPC idx = pc) :
    (stW s pc stk).pc.toNat = Artifact.submissionArtifact.instructionPC idx := by
  rw [h]
  show (UInt256.ofNat pc).toNat = pc
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hpc]

theorem runLocated_of_pcW {artifact : Challenge.EvmProof.ProgramArtifact}
    {fork : Fork} (located : Challenge.EvmProof.Stepper.Located artifact fork)
    {s : State} (h : s.pc.toNat = artifact.instructionPC located.index) :
    Challenge.EvmProof.Stepper.runLocated located s =
      Challenge.EvmProof.Stepper.runInstr located.instruction s := by
  unfold Challenge.EvmProof.Stepper.runLocated
  rw [if_pos h]

theorem runLocatedBlock_singleW {artifact : Challenge.EvmProof.ProgramArtifact}
    {fork : Fork} (l : Challenge.EvmProof.Stepper.Located artifact fork) (s : State) :
    Challenge.EvmProof.Stepper.runLocatedBlock [l] s =
      Challenge.EvmProof.Stepper.runLocated l s := by
  unfold Challenge.EvmProof.Stepper.runLocatedBlock
  cases h : Challenge.EvmProof.Stepper.runLocated l s <;> simp

/-! ### The instructions the block uses -/

theorem stepW_jumpdest (s : State) (pc : Nat) (stk : List UInt256)
    (hlen : stk.length < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .JUMPDEST) (stW s pc stk) =
      some (stW s (pc + 1) stk) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stW, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepW_push (s : State) (pc w : Nat) (v : UInt256) (stk : List UInt256)
    (hlen : stk.length < 1024) (hw : w ≠ 0) (hwlt : w < 33)
    (hpc : pc + (w + 1) < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.push ⟨w, by omega⟩ v) (stW s pc stk) =
      some (stW s (pc + (w + 1)) (v :: stk)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp [stW, if_neg hw, Challenge.EvmProof.Word.ofNat_add_ofNat hpc]

theorem stepW_push0 (s : State) (pc : Nat) (stk : List UInt256)
    (hlen : stk.length < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.push ⟨0, by omega⟩ 0) (stW s pc stk) =
      some (stW s (pc + 1) ((⟨0⟩ : UInt256) :: stk)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp [stW, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepW_pop (s : State) (pc : Nat) (a : UInt256) (rest : List UInt256)
    (hlen : rest.length + 1 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .POP) (stW s pc (a :: rest)) =
      some (stW s (pc + 1) rest) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stW, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepW_dup (s : State) (pc n : Nat) (hn : n < 16) (stk : List UInt256)
    (v : UInt256) (hget : stk[n]? = some v)
    (hlen : stk.length < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op (.Dup ⟨n, hn⟩)) (stW s pc stk) =
      some (stW s (pc + 1) (v :: stk)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stW_stack, hget]
  simp only [stW, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepW_swap (s : State) (pc n : Nat) (hn : n < 16)
    (stk out : List UInt256) (hex : stk.exchange 0 (n + 1) = some out)
    (hlen : stk.length < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op (.Swap ⟨n, hn⟩)) (stW s pc stk) =
      some (stW s (pc + 1) out) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stW_stack, hex]
  simp only [stW, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepW_add (s : State) (pc : Nat) (a b : UInt256) (rest : List UInt256)
    (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .ADD) (stW s pc (a :: b :: rest)) =
      some (stW s (pc + 1) ((a + b) :: rest)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stW, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepW_mul (s : State) (pc : Nat) (a b : UInt256) (rest : List UInt256)
    (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .MUL) (stW s pc (a :: b :: rest)) =
      some (stW s (pc + 1) ((a * b) :: rest)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stW, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepW_sub (s : State) (pc : Nat) (a b : UInt256) (rest : List UInt256)
    (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .SUB) (stW s pc (a :: b :: rest)) =
      some (stW s (pc + 1) ((a - b) :: rest)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stW, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepW_and (s : State) (pc : Nat) (a b : UInt256) (rest : List UInt256)
    (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .AND) (stW s pc (a :: b :: rest)) =
      some (stW s (pc + 1) (UInt256.land a b :: rest)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stW, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepW_xor (s : State) (pc : Nat) (a b : UInt256) (rest : List UInt256)
    (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .XOR) (stW s pc (a :: b :: rest)) =
      some (stW s (pc + 1) (UInt256.xor a b :: rest)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stW, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepW_shr (s : State) (pc : Nat) (shift value : UInt256)
    (rest : List UInt256) (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .SHR)
        (stW s pc (shift :: value :: rest)) =
      some (stW s (pc + 1) (UInt256.shiftRight value shift :: rest)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stW, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepW_mulmod (s : State) (pc : Nat) (a b n : UInt256)
    (rest : List UInt256) (hlen : rest.length + 3 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .MULMOD)
        (stW s pc (a :: b :: n :: rest)) =
      some (stW s (pc + 1) (UInt256.mulMod a b n :: rest)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stW, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem stepW_jump (s : State) (pc target : Nat) (d : UInt256)
    (rest : List UInt256) (hlen : rest.length + 1 < 1024) (ht : target < 2 ^ 256)
    (hd : d = UInt256.ofNat target)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code target = true) :
    Challenge.EvmProof.Stepper.runInstr (.op .JUMP) (stW s pc (d :: rest)) =
      some (stW s target rest) := by
  subst hd
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [stW_code, stW_stack]
  rw [show (UInt256.ofNat target).toNat = target from by
        rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt ht]]
  simp only [stW, if_pos hvalid]

/-- One located step is one block. -/
theorem blockOfW (l : Located) {a t : State}
    (hpc : a.pc.toNat = Artifact.submissionArtifact.instructionPC l.index)
    (h : Challenge.EvmProof.Stepper.runInstr l.instruction a = some t) :
    Challenge.EvmProof.Stepper.runLocatedBlock [l] a = some t := by
  rw [runLocatedBlock_singleW, runLocated_of_pcW l hpc, h]

def soundW {s : State} (hs : Frame s) (l : Located) {pc : Nat} {stk : List UInt256}
    {t : State} (h : Challenge.EvmProof.Stepper.runLocatedBlock [l] (stW s pc stk)
      = some t) : GasSteps (stW s pc stk) t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    [l] hs.code hs.fork h hs.halt hs.np

/-- The static cost of a one-instruction block, for the copy-free opcodes the
block uses. -/
theorem blockCostW
    {artifact : Challenge.EvmProof.ProgramArtifact} {fork : Fork}
    (path : List (Challenge.EvmProof.Stepper.Located artifact fork)) {s t : State}
    (work : Nat)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = fork)
    (hfree : ∀ located ∈ path,
      Challenge.EvmProof.Meter.CopyFree located.instruction)
    (hcost : Challenge.EvmProof.Meter.runLocatedBlockStaticCost path = work)
    (hactive : s.activeWords = t.activeWords) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost path s = work := by
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    path work hresult hfork hfree hcost
  rw [hactive] at hmeter
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
