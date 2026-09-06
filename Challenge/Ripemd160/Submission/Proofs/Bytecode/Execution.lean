import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Word
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# The entry trampolines

Instruction 0 jumps to the guard at pc 0x12ce, and the guard's fall-through
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

def mainStart (input : ByteArray) : State := atPC input 0x03ef

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
@[simp] theorem pc20 : Artifact.submissionArtifact.instructionPC 20 = 0x1b := by rfl
@[simp] theorem pc21 : Artifact.submissionArtifact.instructionPC 21 = 0x1c := by rfl
@[simp] theorem pc22 : Artifact.submissionArtifact.instructionPC 22 = 0x1f := by rfl
@[simp] theorem pc35 : Artifact.submissionArtifact.instructionPC 35 = 0x2e := by rfl
@[simp] theorem pc36 : Artifact.submissionArtifact.instructionPC 36 = 0x2f := by rfl
@[simp] theorem pc37 : Artifact.submissionArtifact.instructionPC 37 = 0x32 := by rfl
@[simp] theorem pc52 : Artifact.submissionArtifact.instructionPC 52 = 0x46 := by rfl
@[simp] theorem pc53 : Artifact.submissionArtifact.instructionPC 53 = 0x47 := by rfl
@[simp] theorem pc54 : Artifact.submissionArtifact.instructionPC 54 = 0x4a := by rfl
@[simp] theorem pc67 : Artifact.submissionArtifact.instructionPC 67 = 0x5a := by rfl
@[simp] theorem pc68 : Artifact.submissionArtifact.instructionPC 68 = 0x5b := by rfl
@[simp] theorem pc69 : Artifact.submissionArtifact.instructionPC 69 = 0x5e := by rfl
@[simp] theorem pc83 : Artifact.submissionArtifact.instructionPC 83 = 0x73 := by rfl
@[simp] theorem pc84 : Artifact.submissionArtifact.instructionPC 84 = 0x74 := by rfl
@[simp] theorem pc85 : Artifact.submissionArtifact.instructionPC 85 = 0x77 := by rfl
@[simp] theorem pc105 : Artifact.submissionArtifact.instructionPC 105 = 0x8e := by rfl
@[simp] theorem pc106 : Artifact.submissionArtifact.instructionPC 106 = 0x8f := by rfl
@[simp] theorem pc107 : Artifact.submissionArtifact.instructionPC 107 = 0x92 := by rfl
@[simp] theorem pc205 : Artifact.submissionArtifact.instructionPC 205 = 0x10f := by rfl
@[simp] theorem pc206 : Artifact.submissionArtifact.instructionPC 206 = 0x110 := by rfl
@[simp] theorem pc207 : Artifact.submissionArtifact.instructionPC 207 = 0x113 := by rfl
@[simp] theorem pc313 : Artifact.submissionArtifact.instructionPC 313 = 0x1b2 := by rfl
@[simp] theorem pc314 : Artifact.submissionArtifact.instructionPC 314 = 0x1b3 := by rfl
@[simp] theorem pc315 : Artifact.submissionArtifact.instructionPC 315 = 0x1b6 := by rfl
@[simp] theorem pc346 : Artifact.submissionArtifact.instructionPC 346 = 0x1db := by rfl
@[simp] theorem pc347 : Artifact.submissionArtifact.instructionPC 347 = 0x1dc := by rfl
@[simp] theorem pc348 : Artifact.submissionArtifact.instructionPC 348 = 0x1df := by rfl
@[simp] theorem pc410 : Artifact.submissionArtifact.instructionPC 410 = 0x231 := by rfl
@[simp] theorem pc411 : Artifact.submissionArtifact.instructionPC 411 = 0x232 := by rfl
@[simp] theorem pc412 : Artifact.submissionArtifact.instructionPC 412 = 0x235 := by rfl
@[simp] theorem pc448 : Artifact.submissionArtifact.instructionPC 448 = 0x268 := by rfl
@[simp] theorem pc449 : Artifact.submissionArtifact.instructionPC 449 = 0x269 := by rfl
@[simp] theorem pc450 : Artifact.submissionArtifact.instructionPC 450 = 0x26c := by rfl
@[simp] theorem pc647 : Artifact.submissionArtifact.instructionPC 647 = 0x3c1 := by rfl
@[simp] theorem pc648 : Artifact.submissionArtifact.instructionPC 648 = 0x3c2 := by rfl
@[simp] theorem pc649 : Artifact.submissionArtifact.instructionPC 649 = 0x3c5 := by rfl
@[simp] theorem pc682 : Artifact.submissionArtifact.instructionPC 682 = 0x3ee := by rfl

theorem jumpDest_12ce : Decode.isValidJumpDest submissionBytecode 0x12ce = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 2813 (by rfl)
theorem jumpDest_2e : Decode.isValidJumpDest submissionBytecode 0x2e = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 35 (by rfl)
theorem jumpDest_46 : Decode.isValidJumpDest submissionBytecode 0x46 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 52 (by rfl)
theorem jumpDest_5a : Decode.isValidJumpDest submissionBytecode 0x5a = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 67 (by rfl)
theorem jumpDest_73 : Decode.isValidJumpDest submissionBytecode 0x73 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 83 (by rfl)
theorem jumpDest_8e : Decode.isValidJumpDest submissionBytecode 0x8e = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 105 (by rfl)
theorem jumpDest_10f : Decode.isValidJumpDest submissionBytecode 0x10f = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 205 (by rfl)
theorem jumpDest_1b2 : Decode.isValidJumpDest submissionBytecode 0x1b2 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 313 (by rfl)
theorem jumpDest_1db : Decode.isValidJumpDest submissionBytecode 0x1db = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 346 (by rfl)
theorem jumpDest_231 : Decode.isValidJumpDest submissionBytecode 0x231 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 410 (by rfl)
theorem jumpDest_268 : Decode.isValidJumpDest submissionBytecode 0x268 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 448 (by rfl)
theorem jumpDest_3c1 : Decode.isValidJumpDest submissionBytecode 0x3c1 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 647 (by rfl)
theorem jumpDest_3ee : Decode.isValidJumpDest submissionBytecode 0x3ee = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 682 (by rfl)

def loc0 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨0, .push ⟨2, by decide⟩ (UInt256.ofNat 0x12ce), by rfl, by decide⟩

theorem step0 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc0]
      (st input 0x0 []) = some (st input 0x3 [UInt256.ofNat 0x12ce]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc0 (pcFact input 0 0x0 [] (by norm_num) pc0)]
  exact runInstr_push input 0 2 0x12ce [] (by simp) (by decide) (by decide) (by norm_num)

def loc1 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨1, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step1 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc1]
      (st input 0x3 [UInt256.ofNat 0x12ce]) = some (st input 0x12ce []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc1 (pcFact input 1 0x3 [UInt256.ofNat 0x12ce] (by norm_num) pc1)]
  exact runInstr_jump input 3 0x12ce [] (by simp) (by norm_num) jumpDest_12ce

def gasSteps_start (input : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0) (atPC input 0x12ce) := by
  rw [atPC_eq_st]
  exact
  (sound [loc0] (step0 input)).trans <|
    sound [loc1] (step1 input)

def loc20 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨20, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step20 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc20]
      (st input 0x1b []) = some (st input 0x1c []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc20 (pcFact input 20 0x1b [] (by norm_num) pc20)]
  exact runInstr_jumpdest input 27 [] (by simp) (by norm_num)

def loc21 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨21, .push ⟨2, by decide⟩ (UInt256.ofNat 0x2e), by rfl, by decide⟩

theorem step21 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc21]
      (st input 0x1c []) = some (st input 0x1f [UInt256.ofNat 0x2e]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc21 (pcFact input 21 0x1c [] (by norm_num) pc21)]
  exact runInstr_push input 28 2 0x2e [] (by simp) (by decide) (by decide) (by norm_num)

def loc22 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨22, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step22 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc22]
      (st input 0x1f [UInt256.ofNat 0x2e]) = some (st input 0x2e []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc22 (pcFact input 22 0x1f [UInt256.ofNat 0x2e] (by norm_num) pc22)]
  exact runInstr_jump input 31 0x2e [] (by simp) (by norm_num) jumpDest_2e

def gasSteps_1b (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x1b) (atPC input 0x2e) := by
  rw [atPC_eq_st]
  exact
  (sound [loc20] (step20 input)).trans <|
    (sound [loc21] (step21 input)).trans <|
    sound [loc22] (step22 input)

def loc35 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨35, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step35 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc35]
      (st input 0x2e []) = some (st input 0x2f []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc35 (pcFact input 35 0x2e [] (by norm_num) pc35)]
  exact runInstr_jumpdest input 46 [] (by simp) (by norm_num)

def loc36 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨36, .push ⟨2, by decide⟩ (UInt256.ofNat 0x46), by rfl, by decide⟩

theorem step36 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc36]
      (st input 0x2f []) = some (st input 0x32 [UInt256.ofNat 0x46]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc36 (pcFact input 36 0x2f [] (by norm_num) pc36)]
  exact runInstr_push input 47 2 0x46 [] (by simp) (by decide) (by decide) (by norm_num)

def loc37 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨37, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step37 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc37]
      (st input 0x32 [UInt256.ofNat 0x46]) = some (st input 0x46 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc37 (pcFact input 37 0x32 [UInt256.ofNat 0x46] (by norm_num) pc37)]
  exact runInstr_jump input 50 0x46 [] (by simp) (by norm_num) jumpDest_46

def gasSteps_2e (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x2e) (atPC input 0x46) := by
  rw [atPC_eq_st]
  exact
  (sound [loc35] (step35 input)).trans <|
    (sound [loc36] (step36 input)).trans <|
    sound [loc37] (step37 input)

def loc52 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨52, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step52 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc52]
      (st input 0x46 []) = some (st input 0x47 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc52 (pcFact input 52 0x46 [] (by norm_num) pc52)]
  exact runInstr_jumpdest input 70 [] (by simp) (by norm_num)

def loc53 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨53, .push ⟨2, by decide⟩ (UInt256.ofNat 0x5a), by rfl, by decide⟩

theorem step53 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc53]
      (st input 0x47 []) = some (st input 0x4a [UInt256.ofNat 0x5a]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc53 (pcFact input 53 0x47 [] (by norm_num) pc53)]
  exact runInstr_push input 71 2 0x5a [] (by simp) (by decide) (by decide) (by norm_num)

def loc54 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨54, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step54 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc54]
      (st input 0x4a [UInt256.ofNat 0x5a]) = some (st input 0x5a []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc54 (pcFact input 54 0x4a [UInt256.ofNat 0x5a] (by norm_num) pc54)]
  exact runInstr_jump input 74 0x5a [] (by simp) (by norm_num) jumpDest_5a

def gasSteps_46 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x46) (atPC input 0x5a) := by
  rw [atPC_eq_st]
  exact
  (sound [loc52] (step52 input)).trans <|
    (sound [loc53] (step53 input)).trans <|
    sound [loc54] (step54 input)

def loc67 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨67, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step67 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc67]
      (st input 0x5a []) = some (st input 0x5b []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc67 (pcFact input 67 0x5a [] (by norm_num) pc67)]
  exact runInstr_jumpdest input 90 [] (by simp) (by norm_num)

def loc68 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨68, .push ⟨2, by decide⟩ (UInt256.ofNat 0x73), by rfl, by decide⟩

theorem step68 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc68]
      (st input 0x5b []) = some (st input 0x5e [UInt256.ofNat 0x73]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc68 (pcFact input 68 0x5b [] (by norm_num) pc68)]
  exact runInstr_push input 91 2 0x73 [] (by simp) (by decide) (by decide) (by norm_num)

def loc69 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨69, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step69 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc69]
      (st input 0x5e [UInt256.ofNat 0x73]) = some (st input 0x73 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc69 (pcFact input 69 0x5e [UInt256.ofNat 0x73] (by norm_num) pc69)]
  exact runInstr_jump input 94 0x73 [] (by simp) (by norm_num) jumpDest_73

def gasSteps_5a (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x5a) (atPC input 0x73) := by
  rw [atPC_eq_st]
  exact
  (sound [loc67] (step67 input)).trans <|
    (sound [loc68] (step68 input)).trans <|
    sound [loc69] (step69 input)

def loc83 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨83, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step83 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc83]
      (st input 0x73 []) = some (st input 0x74 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc83 (pcFact input 83 0x73 [] (by norm_num) pc83)]
  exact runInstr_jumpdest input 115 [] (by simp) (by norm_num)

def loc84 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨84, .push ⟨2, by decide⟩ (UInt256.ofNat 0x8e), by rfl, by decide⟩

theorem step84 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc84]
      (st input 0x74 []) = some (st input 0x77 [UInt256.ofNat 0x8e]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc84 (pcFact input 84 0x74 [] (by norm_num) pc84)]
  exact runInstr_push input 116 2 0x8e [] (by simp) (by decide) (by decide) (by norm_num)

def loc85 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨85, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step85 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc85]
      (st input 0x77 [UInt256.ofNat 0x8e]) = some (st input 0x8e []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc85 (pcFact input 85 0x77 [UInt256.ofNat 0x8e] (by norm_num) pc85)]
  exact runInstr_jump input 119 0x8e [] (by simp) (by norm_num) jumpDest_8e

def gasSteps_73 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x73) (atPC input 0x8e) := by
  rw [atPC_eq_st]
  exact
  (sound [loc83] (step83 input)).trans <|
    (sound [loc84] (step84 input)).trans <|
    sound [loc85] (step85 input)

def loc105 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨105, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step105 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc105]
      (st input 0x8e []) = some (st input 0x8f []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc105 (pcFact input 105 0x8e [] (by norm_num) pc105)]
  exact runInstr_jumpdest input 142 [] (by simp) (by norm_num)

def loc106 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨106, .push ⟨2, by decide⟩ (UInt256.ofNat 0x10f), by rfl, by decide⟩

theorem step106 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc106]
      (st input 0x8f []) = some (st input 0x92 [UInt256.ofNat 0x10f]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc106 (pcFact input 106 0x8f [] (by norm_num) pc106)]
  exact runInstr_push input 143 2 0x10f [] (by simp) (by decide) (by decide) (by norm_num)

def loc107 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨107, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step107 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc107]
      (st input 0x92 [UInt256.ofNat 0x10f]) = some (st input 0x10f []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc107 (pcFact input 107 0x92 [UInt256.ofNat 0x10f] (by norm_num) pc107)]
  exact runInstr_jump input 146 0x10f [] (by simp) (by norm_num) jumpDest_10f

def gasSteps_8e (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x8e) (atPC input 0x10f) := by
  rw [atPC_eq_st]
  exact
  (sound [loc105] (step105 input)).trans <|
    (sound [loc106] (step106 input)).trans <|
    sound [loc107] (step107 input)

def loc205 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨205, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step205 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc205]
      (st input 0x10f []) = some (st input 0x110 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc205 (pcFact input 205 0x10f [] (by norm_num) pc205)]
  exact runInstr_jumpdest input 271 [] (by simp) (by norm_num)

def loc206 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨206, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1b2), by rfl, by decide⟩

theorem step206 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc206]
      (st input 0x110 []) = some (st input 0x113 [UInt256.ofNat 0x1b2]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc206 (pcFact input 206 0x110 [] (by norm_num) pc206)]
  exact runInstr_push input 272 2 0x1b2 [] (by simp) (by decide) (by decide) (by norm_num)

def loc207 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨207, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step207 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc207]
      (st input 0x113 [UInt256.ofNat 0x1b2]) = some (st input 0x1b2 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc207 (pcFact input 207 0x113 [UInt256.ofNat 0x1b2] (by norm_num) pc207)]
  exact runInstr_jump input 275 0x1b2 [] (by simp) (by norm_num) jumpDest_1b2

def gasSteps_10f (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x10f) (atPC input 0x1b2) := by
  rw [atPC_eq_st]
  exact
  (sound [loc205] (step205 input)).trans <|
    (sound [loc206] (step206 input)).trans <|
    sound [loc207] (step207 input)

def loc313 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨313, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step313 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc313]
      (st input 0x1b2 []) = some (st input 0x1b3 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc313 (pcFact input 313 0x1b2 [] (by norm_num) pc313)]
  exact runInstr_jumpdest input 434 [] (by simp) (by norm_num)

def loc314 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨314, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1db), by rfl, by decide⟩

theorem step314 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc314]
      (st input 0x1b3 []) = some (st input 0x1b6 [UInt256.ofNat 0x1db]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc314 (pcFact input 314 0x1b3 [] (by norm_num) pc314)]
  exact runInstr_push input 435 2 0x1db [] (by simp) (by decide) (by decide) (by norm_num)

def loc315 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨315, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step315 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc315]
      (st input 0x1b6 [UInt256.ofNat 0x1db]) = some (st input 0x1db []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc315 (pcFact input 315 0x1b6 [UInt256.ofNat 0x1db] (by norm_num) pc315)]
  exact runInstr_jump input 438 0x1db [] (by simp) (by norm_num) jumpDest_1db

def gasSteps_1b2 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x1b2) (atPC input 0x1db) := by
  rw [atPC_eq_st]
  exact
  (sound [loc313] (step313 input)).trans <|
    (sound [loc314] (step314 input)).trans <|
    sound [loc315] (step315 input)

def loc346 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨346, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step346 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc346]
      (st input 0x1db []) = some (st input 0x1dc []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc346 (pcFact input 346 0x1db [] (by norm_num) pc346)]
  exact runInstr_jumpdest input 475 [] (by simp) (by norm_num)

def loc347 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨347, .push ⟨2, by decide⟩ (UInt256.ofNat 0x231), by rfl, by decide⟩

theorem step347 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc347]
      (st input 0x1dc []) = some (st input 0x1df [UInt256.ofNat 0x231]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc347 (pcFact input 347 0x1dc [] (by norm_num) pc347)]
  exact runInstr_push input 476 2 0x231 [] (by simp) (by decide) (by decide) (by norm_num)

def loc348 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨348, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step348 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc348]
      (st input 0x1df [UInt256.ofNat 0x231]) = some (st input 0x231 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc348 (pcFact input 348 0x1df [UInt256.ofNat 0x231] (by norm_num) pc348)]
  exact runInstr_jump input 479 0x231 [] (by simp) (by norm_num) jumpDest_231

def gasSteps_1db (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x1db) (atPC input 0x231) := by
  rw [atPC_eq_st]
  exact
  (sound [loc346] (step346 input)).trans <|
    (sound [loc347] (step347 input)).trans <|
    sound [loc348] (step348 input)

def loc410 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨410, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step410 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc410]
      (st input 0x231 []) = some (st input 0x232 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc410 (pcFact input 410 0x231 [] (by norm_num) pc410)]
  exact runInstr_jumpdest input 561 [] (by simp) (by norm_num)

def loc411 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨411, .push ⟨2, by decide⟩ (UInt256.ofNat 0x268), by rfl, by decide⟩

theorem step411 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc411]
      (st input 0x232 []) = some (st input 0x235 [UInt256.ofNat 0x268]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc411 (pcFact input 411 0x232 [] (by norm_num) pc411)]
  exact runInstr_push input 562 2 0x268 [] (by simp) (by decide) (by decide) (by norm_num)

def loc412 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨412, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step412 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc412]
      (st input 0x235 [UInt256.ofNat 0x268]) = some (st input 0x268 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc412 (pcFact input 412 0x235 [UInt256.ofNat 0x268] (by norm_num) pc412)]
  exact runInstr_jump input 565 0x268 [] (by simp) (by norm_num) jumpDest_268

def gasSteps_231 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x231) (atPC input 0x268) := by
  rw [atPC_eq_st]
  exact
  (sound [loc410] (step410 input)).trans <|
    (sound [loc411] (step411 input)).trans <|
    sound [loc412] (step412 input)

def loc448 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨448, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step448 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc448]
      (st input 0x268 []) = some (st input 0x269 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc448 (pcFact input 448 0x268 [] (by norm_num) pc448)]
  exact runInstr_jumpdest input 616 [] (by simp) (by norm_num)

def loc449 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨449, .push ⟨2, by decide⟩ (UInt256.ofNat 0x3c1), by rfl, by decide⟩

theorem step449 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc449]
      (st input 0x269 []) = some (st input 0x26c [UInt256.ofNat 0x3c1]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc449 (pcFact input 449 0x269 [] (by norm_num) pc449)]
  exact runInstr_push input 617 2 0x3c1 [] (by simp) (by decide) (by decide) (by norm_num)

def loc450 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨450, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step450 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc450]
      (st input 0x26c [UInt256.ofNat 0x3c1]) = some (st input 0x3c1 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc450 (pcFact input 450 0x26c [UInt256.ofNat 0x3c1] (by norm_num) pc450)]
  exact runInstr_jump input 620 0x3c1 [] (by simp) (by norm_num) jumpDest_3c1

def gasSteps_268 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x268) (atPC input 0x3c1) := by
  rw [atPC_eq_st]
  exact
  (sound [loc448] (step448 input)).trans <|
    (sound [loc449] (step449 input)).trans <|
    sound [loc450] (step450 input)

def loc647 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨647, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step647 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc647]
      (st input 0x3c1 []) = some (st input 0x3c2 []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc647 (pcFact input 647 0x3c1 [] (by norm_num) pc647)]
  exact runInstr_jumpdest input 961 [] (by simp) (by norm_num)

def loc648 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨648, .push ⟨2, by decide⟩ (UInt256.ofNat 0x3ee), by rfl, by decide⟩

theorem step648 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc648]
      (st input 0x3c2 []) = some (st input 0x3c5 [UInt256.ofNat 0x3ee]) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc648 (pcFact input 648 0x3c2 [] (by norm_num) pc648)]
  exact runInstr_push input 962 2 0x3ee [] (by simp) (by decide) (by decide) (by norm_num)

def loc649 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨649, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩

theorem step649 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc649]
      (st input 0x3c5 [UInt256.ofNat 0x3ee]) = some (st input 0x3ee []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc649 (pcFact input 649 0x3c5 [UInt256.ofNat 0x3ee] (by norm_num) pc649)]
  exact runInstr_jump input 965 0x3ee [] (by simp) (by norm_num) jumpDest_3ee

def gasSteps_3c1 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x3c1) (atPC input 0x3ee) := by
  rw [atPC_eq_st]
  exact
  (sound [loc647] (step647 input)).trans <|
    (sound [loc648] (step648 input)).trans <|
    sound [loc649] (step649 input)

def loc682 :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨682, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩

theorem step682 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock [loc682]
      (st input 0x3ee []) = some (st input 0x3ef []) := by
  rw [runLocatedBlock_single,
    runLocated_of_pc loc682 (pcFact input 682 0x3ee [] (by norm_num) pc682)]
  exact runInstr_jumpdest input 1006 [] (by simp) (by norm_num)

def gasSteps_3ee (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x3ee) (mainStart input) := by
  rw [atPC_eq_st]
  exact
  sound [loc682] (step682 input)

def gasSteps_entry (input : ByteArray)
    (entryPrefix : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (atPC input 0x3ee)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (mainStart input) :=
  entryPrefix.trans (gasSteps_3ee input)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution
