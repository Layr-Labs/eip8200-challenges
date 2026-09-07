import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Word
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# The entry trampolines

Instruction 0 jumps to the guard at pc 0x1489, and the guard's fall-through
walks a chain of `JUMPDEST; PUSH2; JUMP` blocks down to the program body at
pc 0x3ef.  Every step is taken one instruction at a time with its program
counter supplied from a named lemma, so nothing here ever asks `simp` to
normalize the artifact's byte array or its chunked instruction list.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

/-- The machine at a program counter with a given stack. -/
def st (input : ByteArray) (pc : Nat) (stk : List UInt256) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat pc, stack := stk }

def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

theorem atPC_eq_st (input : ByteArray) (pc : Nat) : atPC input pc = st input pc [] := rfl

def mainStart (input : ByteArray) : State := atPC input 0x28a

@[simp] private theorem st_code (input : ByteArray) (pc : Nat) (stk : List UInt256) :
    (st input pc stk).executionEnv.code = submissionBytecode := rfl

@[simp] private theorem st_stack (input : ByteArray) (pc : Nat) (stk : List UInt256) :
    (st input pc stk).stack = stk := rfl

theorem pcToNat (input : ByteArray) (n : Nat) (stk : List UInt256)
    (h : n < 2 ^ 256) : (st input n stk).pc.toNat = n := by
  show (UInt256.ofNat n).toNat = n
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt h]

theorem pcFact (input : ByteArray) (idx pc : Nat) (stk : List UInt256)
    (hpc : pc < 2 ^ 256)
    (h : Artifact.submissionArtifact.instructionPC idx = pc) :
    (st input pc stk).pc.toNat = Artifact.submissionArtifact.instructionPC idx := by
  rw [pcToNat input _ _ hpc, h]

/-- Take one located step once its program counter is known. -/
theorem runLocated_of_pc {artifact : Challenge.EvmProof.ProgramArtifact}
    {fork : Fork} (located : Challenge.EvmProof.Stepper.Located artifact fork)
    {s : State} (h : s.pc.toNat = artifact.instructionPC located.index) :
    Challenge.EvmProof.Stepper.runLocated located s =
      Challenge.EvmProof.Stepper.runInstr located.instruction s := by
  unfold Challenge.EvmProof.Stepper.runLocated
  rw [if_pos h]

theorem runLocatedBlock_single {artifact : Challenge.EvmProof.ProgramArtifact}
    {fork : Fork} (l : Challenge.EvmProof.Stepper.Located artifact fork)
    (s : State) :
    Challenge.EvmProof.Stepper.runLocatedBlock [l] s =
      Challenge.EvmProof.Stepper.runLocated l s := by
  unfold Challenge.EvmProof.Stepper.runLocatedBlock
  cases h : Challenge.EvmProof.Stepper.runLocated l s <;> simp

theorem runInstr_jumpdest (input : ByteArray) (pc : Nat) (stk : List UInt256)
    (hlen : stk.length < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr (.op .JUMPDEST) (st input pc stk) =
      some (st input (pc + 1) stk) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [st, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem runInstr_push (input : ByteArray) (pc w v : Nat) (stk : List UInt256)
    (hlen : stk.length < 1024) (hw : w ≠ 0) (hwlt : w < 33)
    (hpc : pc + (w + 1) < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runInstr
        (.push ⟨w, by omega⟩ (UInt256.ofNat v)) (st input pc stk) =
      some (st input (pc + (w + 1)) (UInt256.ofNat v :: stk)) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [st, if_neg hw, Challenge.EvmProof.Word.ofNat_add_ofNat hpc]

theorem runInstr_jump (input : ByteArray) (pc target : Nat) (rest : List UInt256)
    (hlen : rest.length + 1 < 1024) (ht : target < 2 ^ 256)
    (hvalid : Decode.isValidJumpDest submissionBytecode target = true) :
    Challenge.EvmProof.Stepper.runInstr (.op .JUMP)
        (st input pc (UInt256.ofNat target :: rest)) =
      some (st input target rest) := by
  unfold Challenge.EvmProof.Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [st_code, st_stack]
  rw [show (UInt256.ofNat target).toNat = target from by
        rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt ht]]
  simp only [st, if_pos hvalid]

def sound (path : List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka)) {s t : State}
    (h : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    path hcode hfork h hrun hnp


/-! Program counters and jump destinations, named once each. -/

@[simp] theorem pc0 : Artifact.submissionArtifact.instructionPC 0 = 0x0 := by rfl
@[simp] theorem pc1 : Artifact.submissionArtifact.instructionPC 1 = 0x3 := by rfl
@[simp] theorem pc20 : Artifact.submissionArtifact.instructionPC 3 = 0x5 := by rfl
@[simp] theorem pc21 : Artifact.submissionArtifact.instructionPC 4 = 0x6 := by rfl
@[simp] theorem pc22 : Artifact.submissionArtifact.instructionPC 5 = 0x9 := by rfl
@[simp] theorem pc35 : Artifact.submissionArtifact.instructionPC 16 = 0x16 := by rfl
@[simp] theorem pc36 : Artifact.submissionArtifact.instructionPC 17 = 0x17 := by rfl
@[simp] theorem pc37 : Artifact.submissionArtifact.instructionPC 18 = 0x1a := by rfl
@[simp] theorem pc52 : Artifact.submissionArtifact.instructionPC 20 = 0x1c := by rfl
@[simp] theorem pc53 : Artifact.submissionArtifact.instructionPC 21 = 0x1d := by rfl
@[simp] theorem pc54 : Artifact.submissionArtifact.instructionPC 22 = 0x20 := by rfl
@[simp] theorem pc67 : Artifact.submissionArtifact.instructionPC 24 = 0x22 := by rfl
@[simp] theorem pc68 : Artifact.submissionArtifact.instructionPC 25 = 0x23 := by rfl
@[simp] theorem pc69 : Artifact.submissionArtifact.instructionPC 26 = 0x26 := by rfl
@[simp] theorem pc83 : Artifact.submissionArtifact.instructionPC 40 = 0x3b := by rfl
@[simp] theorem pc84 : Artifact.submissionArtifact.instructionPC 41 = 0x3c := by rfl
@[simp] theorem pc85 : Artifact.submissionArtifact.instructionPC 42 = 0x3f := by rfl
@[simp] theorem pc105 : Artifact.submissionArtifact.instructionPC 44 = 0x41 := by rfl
@[simp] theorem pc106 : Artifact.submissionArtifact.instructionPC 45 = 0x42 := by rfl
@[simp] theorem pc107 : Artifact.submissionArtifact.instructionPC 46 = 0x45 := by rfl
@[simp] theorem pc205 : Artifact.submissionArtifact.instructionPC 48 = 0x47 := by rfl
@[simp] theorem pc206 : Artifact.submissionArtifact.instructionPC 49 = 0x48 := by rfl
@[simp] theorem pc207 : Artifact.submissionArtifact.instructionPC 50 = 0x4b := by rfl
@[simp] theorem pc313 : Artifact.submissionArtifact.instructionPC 52 = 0x4d := by rfl
@[simp] theorem pc314 : Artifact.submissionArtifact.instructionPC 53 = 0x4e := by rfl
@[simp] theorem pc315 : Artifact.submissionArtifact.instructionPC 54 = 0x51 := by rfl
@[simp] theorem pc346 : Artifact.submissionArtifact.instructionPC 85 = 0x76 := by rfl
@[simp] theorem pc347 : Artifact.submissionArtifact.instructionPC 86 = 0x77 := by rfl
@[simp] theorem pc348 : Artifact.submissionArtifact.instructionPC 87 = 0x7a := by rfl
@[simp] theorem pc410 : Artifact.submissionArtifact.instructionPC 149 = 0xcc := by rfl
@[simp] theorem pc411 : Artifact.submissionArtifact.instructionPC 150 = 0xcd := by rfl
@[simp] theorem pc412 : Artifact.submissionArtifact.instructionPC 151 = 0xd0 := by rfl
@[simp] theorem pc448 : Artifact.submissionArtifact.instructionPC 187 = 0x103 := by rfl
@[simp] theorem pc449 : Artifact.submissionArtifact.instructionPC 188 = 0x104 := by rfl
@[simp] theorem pc450 : Artifact.submissionArtifact.instructionPC 189 = 0x107 := by rfl
@[simp] theorem pc647 : Artifact.submissionArtifact.instructionPC 386 = 0x25c := by rfl
@[simp] theorem pc648 : Artifact.submissionArtifact.instructionPC 387 = 0x25d := by rfl
@[simp] theorem pc649 : Artifact.submissionArtifact.instructionPC 388 = 0x260 := by rfl
@[simp] theorem pc682 : Artifact.submissionArtifact.instructionPC 421 = 0x289 := by rfl

theorem jumpDest_12ce : Decode.isValidJumpDest submissionBytecode 0x1311 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 2500 (by rfl)
theorem jumpDest_2e : Decode.isValidJumpDest submissionBytecode 0x16 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 16 (by rfl)
theorem jumpDest_46 : Decode.isValidJumpDest submissionBytecode 0x1c = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 20 (by rfl)
theorem jumpDest_5a : Decode.isValidJumpDest submissionBytecode 0x22 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 24 (by rfl)
theorem jumpDest_73 : Decode.isValidJumpDest submissionBytecode 0x3b = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 40 (by rfl)
theorem jumpDest_8e : Decode.isValidJumpDest submissionBytecode 0x41 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 44 (by rfl)
theorem jumpDest_10f : Decode.isValidJumpDest submissionBytecode 0x47 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 48 (by rfl)
theorem jumpDest_1b2 : Decode.isValidJumpDest submissionBytecode 0x4d = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 52 (by rfl)
theorem jumpDest_1db : Decode.isValidJumpDest submissionBytecode 0x76 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 85 (by rfl)
theorem jumpDest_231 : Decode.isValidJumpDest submissionBytecode 0xcc = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 149 (by rfl)
theorem jumpDest_268 : Decode.isValidJumpDest submissionBytecode 0x103 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 187 (by rfl)
theorem jumpDest_3c1 : Decode.isValidJumpDest submissionBytecode 0x25c = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 386 (by rfl)
theorem jumpDest_3ee : Decode.isValidJumpDest submissionBytecode 0x289 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 421 (by rfl)

def loc0 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨0, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1311), by rfl, by decide⟩

theorem step0 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc0]
      (st input 0x0 []) = some (st input 0x3 [UInt256.ofNat 0x1311]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc0 (pcFact input 0 0x0 [] (by norm_num) pc0)]
  exact runInstr_push input 0 2 0x1311 [] (by simp) (by decide) (by decide) (by norm_num)

def loc1 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨1, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step1 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc1]
      (st input 0x3 [UInt256.ofNat 0x1311]) = some (st input 0x1311 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc1 (pcFact input 1 0x3 [UInt256.ofNat 0x1311] (by norm_num) pc1)]
  exact runInstr_jump input 3 0x1311 [] (by simp) (by norm_num) jumpDest_12ce

def gasSteps_start (input : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0) (atPC input 0x1311) := by
  rw [atPC_eq_st]
  exact
  (sound [loc0] (step0 input)).trans <|
    sound [loc1] (step1 input)

def loc20 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨3, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step20 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc20]
      (st input 0x5 []) = some (st input 0x6 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc20 (pcFact input 3 0x5 [] (by norm_num) pc20)]
  exact runInstr_jumpdest input 5 [] (by simp) (by norm_num)

def loc21 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨4, .push ⟨2, by decide⟩ (UInt256.ofNat 0x16), by rfl, by decide⟩

theorem step21 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc21]
      (st input 0x6 []) = some (st input 0x9 [UInt256.ofNat 0x16]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc21 (pcFact input 4 0x6 [] (by norm_num) pc21)]
  exact runInstr_push input 6 2 0x16 [] (by simp) (by decide) (by decide) (by norm_num)

def loc22 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨5, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step22 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc22]
      (st input 0x9 [UInt256.ofNat 0x16]) = some (st input 0x16 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc22 (pcFact input 5 0x9 [UInt256.ofNat 0x16] (by norm_num) pc22)]
  exact runInstr_jump input 9 0x16 [] (by simp) (by norm_num) jumpDest_2e

def gasSteps_1b (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x5) (atPC input 0x16) := by
  rw [atPC_eq_st]
  exact
  (sound [loc20] (step20 input)).trans <|
    (sound [loc21] (step21 input)).trans <|
    sound [loc22] (step22 input)

def loc35 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨16, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step35 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc35]
      (st input 0x16 []) = some (st input 0x17 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc35 (pcFact input 16 0x16 [] (by norm_num) pc35)]
  exact runInstr_jumpdest input 22 [] (by simp) (by norm_num)

def loc36 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨17, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1c), by rfl, by decide⟩

theorem step36 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc36]
      (st input 0x17 []) = some (st input 0x1a [UInt256.ofNat 0x1c]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc36 (pcFact input 17 0x17 [] (by norm_num) pc36)]
  exact runInstr_push input 23 2 0x1c [] (by simp) (by decide) (by decide) (by norm_num)

def loc37 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨18, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step37 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc37]
      (st input 0x1a [UInt256.ofNat 0x1c]) = some (st input 0x1c []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc37 (pcFact input 18 0x1a [UInt256.ofNat 0x1c] (by norm_num) pc37)]
  exact runInstr_jump input 26 0x1c [] (by simp) (by norm_num) jumpDest_46

def gasSteps_2e (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x16) (atPC input 0x1c) := by
  rw [atPC_eq_st]
  exact
  (sound [loc35] (step35 input)).trans <|
    (sound [loc36] (step36 input)).trans <|
    sound [loc37] (step37 input)

def loc52 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨20, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step52 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc52]
      (st input 0x1c []) = some (st input 0x1d []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc52 (pcFact input 20 0x1c [] (by norm_num) pc52)]
  exact runInstr_jumpdest input 28 [] (by simp) (by norm_num)

def loc53 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨21, .push ⟨2, by decide⟩ (UInt256.ofNat 0x22), by rfl, by decide⟩

theorem step53 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc53]
      (st input 0x1d []) = some (st input 0x20 [UInt256.ofNat 0x22]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc53 (pcFact input 21 0x1d [] (by norm_num) pc53)]
  exact runInstr_push input 29 2 0x22 [] (by simp) (by decide) (by decide) (by norm_num)

def loc54 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨22, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step54 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc54]
      (st input 0x20 [UInt256.ofNat 0x22]) = some (st input 0x22 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc54 (pcFact input 22 0x20 [UInt256.ofNat 0x22] (by norm_num) pc54)]
  exact runInstr_jump input 32 0x22 [] (by simp) (by norm_num) jumpDest_5a

def gasSteps_46 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x1c) (atPC input 0x22) := by
  rw [atPC_eq_st]
  exact
  (sound [loc52] (step52 input)).trans <|
    (sound [loc53] (step53 input)).trans <|
    sound [loc54] (step54 input)

def loc67 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨24, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step67 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc67]
      (st input 0x22 []) = some (st input 0x23 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc67 (pcFact input 24 0x22 [] (by norm_num) pc67)]
  exact runInstr_jumpdest input 34 [] (by simp) (by norm_num)

def loc68 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨25, .push ⟨2, by decide⟩ (UInt256.ofNat 0x3b), by rfl, by decide⟩

theorem step68 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc68]
      (st input 0x23 []) = some (st input 0x26 [UInt256.ofNat 0x3b]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc68 (pcFact input 25 0x23 [] (by norm_num) pc68)]
  exact runInstr_push input 35 2 0x3b [] (by simp) (by decide) (by decide) (by norm_num)

def loc69 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨26, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step69 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc69]
      (st input 0x26 [UInt256.ofNat 0x3b]) = some (st input 0x3b []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc69 (pcFact input 26 0x26 [UInt256.ofNat 0x3b] (by norm_num) pc69)]
  exact runInstr_jump input 38 0x3b [] (by simp) (by norm_num) jumpDest_73

def gasSteps_5a (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x22) (atPC input 0x3b) := by
  rw [atPC_eq_st]
  exact
  (sound [loc67] (step67 input)).trans <|
    (sound [loc68] (step68 input)).trans <|
    sound [loc69] (step69 input)

def loc83 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨40, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step83 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc83]
      (st input 0x3b []) = some (st input 0x3c []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc83 (pcFact input 40 0x3b [] (by norm_num) pc83)]
  exact runInstr_jumpdest input 59 [] (by simp) (by norm_num)

def loc84 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨41, .push ⟨2, by decide⟩ (UInt256.ofNat 0x41), by rfl, by decide⟩

theorem step84 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc84]
      (st input 0x3c []) = some (st input 0x3f [UInt256.ofNat 0x41]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc84 (pcFact input 41 0x3c [] (by norm_num) pc84)]
  exact runInstr_push input 60 2 0x41 [] (by simp) (by decide) (by decide) (by norm_num)

def loc85 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨42, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step85 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc85]
      (st input 0x3f [UInt256.ofNat 0x41]) = some (st input 0x41 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc85 (pcFact input 42 0x3f [UInt256.ofNat 0x41] (by norm_num) pc85)]
  exact runInstr_jump input 63 0x41 [] (by simp) (by norm_num) jumpDest_8e

def gasSteps_73 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x3b) (atPC input 0x41) := by
  rw [atPC_eq_st]
  exact
  (sound [loc83] (step83 input)).trans <|
    (sound [loc84] (step84 input)).trans <|
    sound [loc85] (step85 input)

def loc105 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨44, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step105 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc105]
      (st input 0x41 []) = some (st input 0x42 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc105 (pcFact input 44 0x41 [] (by norm_num) pc105)]
  exact runInstr_jumpdest input 65 [] (by simp) (by norm_num)

def loc106 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨45, .push ⟨2, by decide⟩ (UInt256.ofNat 0x47), by rfl, by decide⟩

theorem step106 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc106]
      (st input 0x42 []) = some (st input 0x45 [UInt256.ofNat 0x47]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc106 (pcFact input 45 0x42 [] (by norm_num) pc106)]
  exact runInstr_push input 66 2 0x47 [] (by simp) (by decide) (by decide) (by norm_num)

def loc107 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨46, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step107 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc107]
      (st input 0x45 [UInt256.ofNat 0x47]) = some (st input 0x47 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc107 (pcFact input 46 0x45 [UInt256.ofNat 0x47] (by norm_num) pc107)]
  exact runInstr_jump input 69 0x47 [] (by simp) (by norm_num) jumpDest_10f

def gasSteps_8e (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x41) (atPC input 0x47) := by
  rw [atPC_eq_st]
  exact
  (sound [loc105] (step105 input)).trans <|
    (sound [loc106] (step106 input)).trans <|
    sound [loc107] (step107 input)

def loc205 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨48, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step205 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc205]
      (st input 0x47 []) = some (st input 0x48 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc205 (pcFact input 48 0x47 [] (by norm_num) pc205)]
  exact runInstr_jumpdest input 71 [] (by simp) (by norm_num)

def loc206 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨49, .push ⟨2, by decide⟩ (UInt256.ofNat 0x4d), by rfl, by decide⟩

theorem step206 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc206]
      (st input 0x48 []) = some (st input 0x4b [UInt256.ofNat 0x4d]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc206 (pcFact input 49 0x48 [] (by norm_num) pc206)]
  exact runInstr_push input 72 2 0x4d [] (by simp) (by decide) (by decide) (by norm_num)

def loc207 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨50, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step207 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc207]
      (st input 0x4b [UInt256.ofNat 0x4d]) = some (st input 0x4d []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc207 (pcFact input 50 0x4b [UInt256.ofNat 0x4d] (by norm_num) pc207)]
  exact runInstr_jump input 75 0x4d [] (by simp) (by norm_num) jumpDest_1b2

def gasSteps_10f (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x47) (atPC input 0x4d) := by
  rw [atPC_eq_st]
  exact
  (sound [loc205] (step205 input)).trans <|
    (sound [loc206] (step206 input)).trans <|
    sound [loc207] (step207 input)

def loc313 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨52, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step313 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc313]
      (st input 0x4d []) = some (st input 0x4e []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc313 (pcFact input 52 0x4d [] (by norm_num) pc313)]
  exact runInstr_jumpdest input 77 [] (by simp) (by norm_num)

def loc314 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨53, .push ⟨2, by decide⟩ (UInt256.ofNat 0x76), by rfl, by decide⟩

theorem step314 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc314]
      (st input 0x4e []) = some (st input 0x51 [UInt256.ofNat 0x76]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc314 (pcFact input 53 0x4e [] (by norm_num) pc314)]
  exact runInstr_push input 78 2 0x76 [] (by simp) (by decide) (by decide) (by norm_num)

def loc315 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨54, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step315 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc315]
      (st input 0x51 [UInt256.ofNat 0x76]) = some (st input 0x76 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc315 (pcFact input 54 0x51 [UInt256.ofNat 0x76] (by norm_num) pc315)]
  exact runInstr_jump input 81 0x76 [] (by simp) (by norm_num) jumpDest_1db

def gasSteps_1b2 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x4d) (atPC input 0x76) := by
  rw [atPC_eq_st]
  exact
  (sound [loc313] (step313 input)).trans <|
    (sound [loc314] (step314 input)).trans <|
    sound [loc315] (step315 input)

def loc346 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨85, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step346 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc346]
      (st input 0x76 []) = some (st input 0x77 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc346 (pcFact input 85 0x76 [] (by norm_num) pc346)]
  exact runInstr_jumpdest input 118 [] (by simp) (by norm_num)

def loc347 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨86, .push ⟨2, by decide⟩ (UInt256.ofNat 0xcc), by rfl, by decide⟩

theorem step347 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc347]
      (st input 0x77 []) = some (st input 0x7a [UInt256.ofNat 0xcc]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc347 (pcFact input 86 0x77 [] (by norm_num) pc347)]
  exact runInstr_push input 119 2 0xcc [] (by simp) (by decide) (by decide) (by norm_num)

def loc348 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨87, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step348 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc348]
      (st input 0x7a [UInt256.ofNat 0xcc]) = some (st input 0xcc []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc348 (pcFact input 87 0x7a [UInt256.ofNat 0xcc] (by norm_num) pc348)]
  exact runInstr_jump input 122 0xcc [] (by simp) (by norm_num) jumpDest_231

def gasSteps_1db (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x76) (atPC input 0xcc) := by
  rw [atPC_eq_st]
  exact
  (sound [loc346] (step346 input)).trans <|
    (sound [loc347] (step347 input)).trans <|
    sound [loc348] (step348 input)

def loc410 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨149, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step410 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc410]
      (st input 0xcc []) = some (st input 0xcd []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc410 (pcFact input 149 0xcc [] (by norm_num) pc410)]
  exact runInstr_jumpdest input 204 [] (by simp) (by norm_num)

def loc411 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨150, .push ⟨2, by decide⟩ (UInt256.ofNat 0x103), by rfl, by decide⟩

theorem step411 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc411]
      (st input 0xcd []) = some (st input 0xd0 [UInt256.ofNat 0x103]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc411 (pcFact input 150 0xcd [] (by norm_num) pc411)]
  exact runInstr_push input 205 2 0x103 [] (by simp) (by decide) (by decide) (by norm_num)

def loc412 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨151, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step412 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc412]
      (st input 0xd0 [UInt256.ofNat 0x103]) = some (st input 0x103 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc412 (pcFact input 151 0xd0 [UInt256.ofNat 0x103] (by norm_num) pc412)]
  exact runInstr_jump input 208 0x103 [] (by simp) (by norm_num) jumpDest_268

def gasSteps_231 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0xcc) (atPC input 0x103) := by
  rw [atPC_eq_st]
  exact
  (sound [loc410] (step410 input)).trans <|
    (sound [loc411] (step411 input)).trans <|
    sound [loc412] (step412 input)

def loc448 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨187, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step448 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc448]
      (st input 0x103 []) = some (st input 0x104 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc448 (pcFact input 187 0x103 [] (by norm_num) pc448)]
  exact runInstr_jumpdest input 259 [] (by simp) (by norm_num)

def loc449 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨188, .push ⟨2, by decide⟩ (UInt256.ofNat 0x25c), by rfl, by decide⟩

theorem step449 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc449]
      (st input 0x104 []) = some (st input 0x107 [UInt256.ofNat 0x25c]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc449 (pcFact input 188 0x104 [] (by norm_num) pc449)]
  exact runInstr_push input 260 2 0x25c [] (by simp) (by decide) (by decide) (by norm_num)

def loc450 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨189, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step450 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc450]
      (st input 0x107 [UInt256.ofNat 0x25c]) = some (st input 0x25c []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc450 (pcFact input 189 0x107 [UInt256.ofNat 0x25c] (by norm_num) pc450)]
  exact runInstr_jump input 263 0x25c [] (by simp) (by norm_num) jumpDest_3c1

def gasSteps_268 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x103) (atPC input 0x25c) := by
  rw [atPC_eq_st]
  exact
  (sound [loc448] (step448 input)).trans <|
    (sound [loc449] (step449 input)).trans <|
    sound [loc450] (step450 input)

def loc647 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨386, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step647 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc647]
      (st input 0x25c []) = some (st input 0x25d []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc647 (pcFact input 386 0x25c [] (by norm_num) pc647)]
  exact runInstr_jumpdest input 604 [] (by simp) (by norm_num)

def loc648 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨387, .push ⟨2, by decide⟩ (UInt256.ofNat 0x289), by rfl, by decide⟩

theorem step648 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc648]
      (st input 0x25d []) = some (st input 0x260 [UInt256.ofNat 0x289]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc648 (pcFact input 387 0x25d [] (by norm_num) pc648)]
  exact runInstr_push input 605 2 0x289 [] (by simp) (by decide) (by decide) (by norm_num)

def loc649 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨388, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step649 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc649]
      (st input 0x260 [UInt256.ofNat 0x289]) = some (st input 0x289 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc649 (pcFact input 388 0x260 [UInt256.ofNat 0x289] (by norm_num) pc649)]
  exact runInstr_jump input 608 0x289 [] (by simp) (by norm_num) jumpDest_3ee

def gasSteps_3c1 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x25c) (atPC input 0x289) := by
  rw [atPC_eq_st]
  exact
  (sound [loc647] (step647 input)).trans <|
    (sound [loc648] (step648 input)).trans <|
    sound [loc649] (step649 input)

def loc682 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨421, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step682 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc682]
      (st input 0x289 []) = some (st input 0x28a []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc682 (pcFact input 421 0x289 [] (by norm_num) pc682)]
  exact runInstr_jumpdest input 649 [] (by simp) (by norm_num)

def gasSteps_3ee (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x289) (mainStart input) := by
  rw [atPC_eq_st]
  exact
  sound [loc682] (step682 input)

def gasSteps_entry (input : ByteArray)
    (entryPrefix : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (atPC input 0x289)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (mainStart input) :=
  entryPrefix.trans (gasSteps_3ee input)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution
