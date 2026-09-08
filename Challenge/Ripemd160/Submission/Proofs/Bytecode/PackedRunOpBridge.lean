import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
import Challenge.EvmProof.Stepper

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# Stack projection for the packed operation model

`PackedStep0.runOp` intentionally forgets gas, the program counter, decoding,
and memory expansion.  A sound bridge therefore cannot identify its result
with a whole EVM state.  This file starts with the smallest useful leaf: a
concrete `MLOAD` step agrees with the model after projecting the concrete state
to its stack and unchanged memory bytes.

The stack-capacity premise is real.  `Stepper.runInstr` rejects every opcode
when the incoming stack already has 1024 entries, while `runOp` has no such
check.  The memory accessor is also pinned to the exact EVM address conversion:
`MachineState.readWord s.memory address.toNat`.

`MLOAD` may increase `activeWords`; this theorem does not erase that fact by
asserting state equality.  It records the exact concrete post-state separately
below, so later gas proofs can account for memory expansion.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRunOpBridge

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

/-- The memory interpretation used by the packed model at one concrete state. -/
def memoryWord (s : State) (address : UInt256) : UInt256 :=
  MachineState.readWord s.memory address.toNat

/-! ## Exact opcode encoding

`Op.push v` does not remember how many immediate bytes encoded `v`.  The
shape relation therefore keeps a positive width for ordinary `PUSH`; the
fork-specific wrapper additionally requires `Stepper.WellFormed`, which in
particular proves `v.toNat < 256 ^ width.val`.  `PUSH0` is a separate exact
shape.  `DUP` and `SWAP` translate the model's one-based depth to the EVM
operation's zero-based `Fin 16` index.
-/

inductive EncodesShape :
    Op → YulEvmCompiler.Instr → Prop where
  | push0 : EncodesShape Op.push0 (.push ⟨0, by decide⟩ 0)
  | push (width : Fin 33) (value : UInt256) (positive : 0 < width.val) :
      EncodesShape (.push value) (.push width value)
  | mload : EncodesShape Op.mload (.op .MLOAD)
  | dup (index : Fin 16) :
      EncodesShape (.dup (index.val + 1)) (.op (.Dup ⟨index⟩))
  | swap (index : Fin 16) :
      EncodesShape (.swap (index.val + 1)) (.op (.Swap ⟨index⟩))
  | pop : EncodesShape Op.pop (.op .POP)
  | land : EncodesShape Op.and (.op .AND)
  | lor : EncodesShape Op.or (.op .OR)
  | xor : EncodesShape Op.xor (.op .XOR)
  | add : EncodesShape Op.add (.op .ADD)
  | mul : EncodesShape Op.mul (.op .MUL)
  | shr : EncodesShape Op.shr (.op .SHR)

/-- A semantic opcode shape together with the exact fork-specific decoder
side conditions.  For `PUSH`, `wellFormed` contains both representability in
the chosen width and opcode availability in the fork. -/
structure EncodesOp (fork : Fork) (op : Op)
    (instruction : YulEvmCompiler.Instr) : Prop where
  shape : EncodesShape op instruction
  wellFormed : Stepper.WellFormed fork instruction

/-- Ordinary `PUSH` witnesses expose the immediate-width representability
condition rather than treating two encodings of the same word as identical. -/
theorem EncodesOp.push_fits {fork : Fork} {width : Fin 33}
    {value : UInt256}
    (encoding : EncodesOp fork (.push value) (.push width value)) :
    value.toNat < 256 ^ width.val :=
  encoding.wellFormed.1

/-- The state projection represented by `runOp`. -/
def stackMemory (s : State) : List UInt256 × ByteArray :=
  (s.stack, s.memory)

/-! ## One-instruction projection leaves -/

theorem runInstr_push0_stack_memory (s : State)
    (hcap : s.stack.length < 1024) :
    (Stepper.runInstr (.push ⟨0, by decide⟩ 0) s).map stackMemory =
      (runOp (memoryWord s) Op.push0 s.stack).map
        (fun stack => (stack, s.memory)) := by
  have hzero : ({ val := 0 } : UInt256) = (0 : UInt256) := by
    exact congrArg UInt256.mk (Fin.ext (by rfl))
  simp [Stepper.runInstr, runOp, stackMemory, hcap, hzero]

theorem runInstr_push_stack_memory (s : State) (width : Fin 33)
    (value : UInt256) (hwidth : 0 < width.val)
    (hcap : s.stack.length < 1024) :
    (Stepper.runInstr (.push width value) s).map stackMemory =
      (runOp (memoryWord s) (.push value) s.stack).map
        (fun stack => (stack, s.memory)) := by
  simp [Stepper.runInstr, runOp, stackMemory, hcap,
    Nat.ne_of_gt hwidth]

/-- Falsifiable `MLOAD` leaf: after projecting away PC and active-word
bookkeeping, concrete execution produces exactly the abstract stack and leaves
the memory bytes unchanged.  The equality fails if `memoryWord` uses a
different address conversion or if memory mutation is hidden in the model. -/
theorem runInstr_mload_stack_memory (s : State)
    (hcap : s.stack.length < 1024) :
    (Stepper.runInstr (.op .MLOAD) s).map stackMemory =
      (runOp (memoryWord s) Op.mload s.stack).map
        (fun stack => (stack, s.memory)) := by
  unfold Stepper.runInstr runOp memoryWord stackMemory
  rw [if_pos hcap]
  cases s.stack <;> rfl

/-- The information deliberately omitted by `runOp`: on a nonempty stack,
concrete `MLOAD` advances PC and updates the active-memory extent. -/
theorem runInstr_mload_exact (s : State) (offset : UInt256)
    (rest : List UInt256) (hstack : s.stack = offset :: rest)
    (hcap : s.stack.length < 1024) :
    Stepper.runInstr (.op .MLOAD) s = some { s with
      stack := memoryWord s offset :: rest
      pc := s.pc.succ
      activeWords := s.activeWordsAfterUInt256 offset.toNat 32 } := by
  unfold Stepper.runInstr memoryWord
  rw [if_pos hcap, hstack]

theorem runInstr_dup_stack_memory (s : State) (index : Fin 16)
    (hcap : s.stack.length < 1024) :
    (Stepper.runInstr (.op (.Dup ⟨index⟩)) s).map stackMemory =
      (runOp (memoryWord s) (.dup (index.val + 1)) s.stack).map
        (fun stack => (stack, s.memory)) := by
  unfold Stepper.runInstr runOp
  rw [if_pos hcap]
  simp only [Nat.add_sub_cancel]
  cases hget : s.stack[index.val]? <;> simp [stackMemory]

theorem runInstr_swap_stack_memory (s : State) (index : Fin 16)
    (hcap : s.stack.length < 1024) :
    (Stepper.runInstr (.op (.Swap ⟨index⟩)) s).map stackMemory =
      (runOp (memoryWord s) (.swap (index.val + 1)) s.stack).map
        (fun stack => (stack, s.memory)) := by
  unfold Stepper.runInstr runOp stackMemory
  rw [if_pos hcap]
  cases s.stack with
  | nil => rfl
  | cons top rest =>
      cases hget : rest[index.val]? <;> simp [List.exchange, hget]

theorem runInstr_pop_stack_memory (s : State)
    (hcap : s.stack.length < 1024) :
    (Stepper.runInstr (.op .POP) s).map stackMemory =
      (runOp (memoryWord s) Op.pop s.stack).map
        (fun stack => (stack, s.memory)) := by
  unfold Stepper.runInstr runOp stackMemory
  rw [if_pos hcap]
  cases s.stack <;> rfl

theorem runInstr_and_stack_memory (s : State)
    (hcap : s.stack.length < 1024) :
    (Stepper.runInstr (.op .AND) s).map stackMemory =
      (runOp (memoryWord s) Op.and s.stack).map
        (fun stack => (stack, s.memory)) := by
  unfold Stepper.runInstr runOp stackMemory
  rw [if_pos hcap]
  cases s.stack with
  | nil => rfl
  | cons x rest => cases rest <;> rfl

theorem runInstr_or_stack_memory (s : State)
    (hcap : s.stack.length < 1024) :
    (Stepper.runInstr (.op .OR) s).map stackMemory =
      (runOp (memoryWord s) Op.or s.stack).map
        (fun stack => (stack, s.memory)) := by
  unfold Stepper.runInstr runOp stackMemory
  rw [if_pos hcap]
  cases s.stack with
  | nil => rfl
  | cons x rest => cases rest <;> rfl

theorem runInstr_xor_stack_memory (s : State)
    (hcap : s.stack.length < 1024) :
    (Stepper.runInstr (.op .XOR) s).map stackMemory =
      (runOp (memoryWord s) Op.xor s.stack).map
        (fun stack => (stack, s.memory)) := by
  unfold Stepper.runInstr runOp stackMemory
  rw [if_pos hcap]
  cases s.stack with
  | nil => rfl
  | cons x rest => cases rest <;> rfl

theorem runInstr_add_stack_memory (s : State)
    (hcap : s.stack.length < 1024) :
    (Stepper.runInstr (.op .ADD) s).map stackMemory =
      (runOp (memoryWord s) Op.add s.stack).map
        (fun stack => (stack, s.memory)) := by
  unfold Stepper.runInstr runOp stackMemory
  rw [if_pos hcap]
  cases s.stack with
  | nil => rfl
  | cons x rest => cases rest <;> rfl

theorem runInstr_mul_stack_memory (s : State)
    (hcap : s.stack.length < 1024) :
    (Stepper.runInstr (.op .MUL) s).map stackMemory =
      (runOp (memoryWord s) Op.mul s.stack).map
        (fun stack => (stack, s.memory)) := by
  unfold Stepper.runInstr runOp stackMemory
  rw [if_pos hcap]
  cases s.stack with
  | nil => rfl
  | cons x rest => cases rest <;> rfl

theorem runInstr_shr_stack_memory (s : State)
    (hcap : s.stack.length < 1024) :
    (Stepper.runInstr (.op .SHR) s).map stackMemory =
      (runOp (memoryWord s) Op.shr s.stack).map
        (fun stack => (stack, s.memory)) := by
  unfold Stepper.runInstr runOp stackMemory
  rw [if_pos hcap]
  cases s.stack with
  | nil => rfl
  | cons x rest => cases rest <;> rfl

/-- Uniform stack/memory projection for the complete `PackedStep0.Op` subset.
The `WellFormed` field is not needed to reduce `runInstr`, but is retained in
the premise so the same witness can be used by `runLocated_sound`. -/
theorem runInstr_stack_memory_of_encoding (s : State)
    {op : Op} {instruction : YulEvmCompiler.Instr}
    (encoding : EncodesOp s.fork op instruction)
    (hcap : s.stack.length < 1024) :
    (Stepper.runInstr instruction s).map stackMemory =
      (runOp (memoryWord s) op s.stack).map
        (fun stack => (stack, s.memory)) := by
  cases encoding.shape with
  | push0 => exact runInstr_push0_stack_memory s hcap
  | push width value positive =>
      exact runInstr_push_stack_memory s width value positive hcap
  | mload => exact runInstr_mload_stack_memory s hcap
  | dup index => exact runInstr_dup_stack_memory s index hcap
  | swap index => exact runInstr_swap_stack_memory s index hcap
  | pop => exact runInstr_pop_stack_memory s hcap
  | land => exact runInstr_and_stack_memory s hcap
  | lor => exact runInstr_or_stack_memory s hcap
  | xor => exact runInstr_xor_stack_memory s hcap
  | add => exact runInstr_add_stack_memory s hcap
  | mul => exact runInstr_mul_stack_memory s hcap
  | shr => exact runInstr_shr_stack_memory s hcap

/-! ## Ordered composition

`EncodedRun` records an actual successful `Stepper.runInstr` chain.  Its two
lists are built in lockstep, so no permutation or dropped opcode is possible.
Every prefix carries its own stack-cap premise and its own fork-specific
`EncodesOp` witness.  Underflow and invalid DUP/SWAP depth remain observable:
they make the `step` field impossible rather than becoming extra assumptions
about the abstract result.

This relation still deliberately stops below artifact execution.  A future
located-path bridge must additionally prove the PC at each instruction,
decoder/code equality, running status, and no-precompile condition before
using `Stepper.runLocated_sound` for gas-parametric EVM execution.
-/

inductive EncodedRun :
    List Op → List YulEvmCompiler.Instr → State → State → Prop where
  | nil (s : State) : EncodedRun [] [] s s
  | cons {op : Op} {instruction : YulEvmCompiler.Instr}
      {ops : List Op} {instructions : List YulEvmCompiler.Instr}
      {s next t : State}
      (encoding : EncodesOp s.fork op instruction)
      (stackCap : s.stack.length < 1024)
      (step : Stepper.runInstr instruction s = some next)
      (tail : EncodedRun ops instructions next t) :
      EncodedRun (op :: ops) (instruction :: instructions) s t

theorem EncodedRun.lengths {ops : List Op}
    {instructions : List YulEvmCompiler.Instr} {s t : State}
    (run : EncodedRun ops instructions s t) :
    ops.length = instructions.length := by
  induction run with
  | nil => rfl
  | cons _ _ _ _ ih => simp [ih]

/-- A successful concrete instruction step determines the corresponding
abstract result and proves that this opcode subset did not mutate memory. -/
theorem runOp_of_runInstr {s next : State} {op : Op}
    {instruction : YulEvmCompiler.Instr}
    (encoding : EncodesOp s.fork op instruction)
    (hcap : s.stack.length < 1024)
    (hstep : Stepper.runInstr instruction s = some next) :
    runOp (memoryWord s) op s.stack = some next.stack ∧
      next.memory = s.memory := by
  have hprojection := runInstr_stack_memory_of_encoding s encoding hcap
  rw [hstep] at hprojection
  cases hrunOp : runOp (memoryWord s) op s.stack with
  | none => simp [hrunOp] at hprojection
  | some stack =>
      have hpairs : (next.stack, next.memory) = (stack, s.memory) := by
        simpa [hrunOp, stackMemory] using hprojection
      have hstack : next.stack = stack := congrArg Prod.fst hpairs
      have hmemory : next.memory = s.memory := congrArg Prod.snd hpairs
      exact ⟨congrArg some hstack.symm, hmemory⟩

/-- Reverse use of the same projection theorem: abstract success plus an exact
encoding and the concrete stack cap construct a successful stepper state.
This does not assume a concrete execution witness. -/
theorem runInstr_of_runOp {s : State} {op : Op}
    {instruction : YulEvmCompiler.Instr} {out : List UInt256}
    (encoding : EncodesOp s.fork op instruction)
    (hcap : s.stack.length < 1024)
    (hrunOp : runOp (memoryWord s) op s.stack = some out) :
    ∃ next, Stepper.runInstr instruction s = some next ∧
      next.stack = out ∧ next.memory = s.memory := by
  have hprojection := runInstr_stack_memory_of_encoding s encoding hcap
  cases hstep : Stepper.runInstr instruction s with
  | none => simp [hstep, hrunOp] at hprojection
  | some next =>
      have hpairs : (next.stack, next.memory) = (out, s.memory) := by
        simpa [hstep, hrunOp, stackMemory] using hprojection
      exact ⟨next, rfl, congrArg Prod.fst hpairs,
        congrArg Prod.snd hpairs⟩

/-! `EncodedPlan` contains no concrete-success premise.  At a prefix it gives
only the exact encoding and cap; its tail must be valid for whichever unique
next state `runInstr_of_runOp` constructs.  This makes it usable to turn an
already-computed abstract `runOps` trace into an `EncodedRun` without assuming
the desired concrete chain.
-/

def EncodedPlan :
    List Op → List YulEvmCompiler.Instr → State → Prop
  | [], [], _ => True
  | op :: ops, instruction :: instructions, s =>
      EncodesOp s.fork op instruction ∧
        s.stack.length < 1024 ∧
        ∀ next, Stepper.runInstr instruction s = some next →
          EncodedPlan ops instructions next
  | _, _, _ => False

/-- Program-counter update performed by the permitted straight-line subset. -/
def instructionNextPC : YulEvmCompiler.Instr → UInt256 → UInt256
  | .push width _, pc =>
      if width.val = 0 then pc.succ
      else pc + UInt256.ofNat (width.val + 1)
  | .op _, pc => pc.succ

/-- Permitted packed instructions preserve the halt state.  This supplies the
intermediate `Running` facts required by `runLocatedBlock`, rather than adding
them as fields of the located plan. -/
theorem runInstr_halt_of_encoding {s next : State} {op : Op}
    {instruction : YulEvmCompiler.Instr}
    (encoding : EncodesOp s.fork op instruction)
    (hcap : s.stack.length < 1024)
    (hstep : Stepper.runInstr instruction s = some next) :
    next.halt = s.halt := by
  cases encoding.shape <;>
    unfold Stepper.runInstr at hstep <;>
    rw [if_pos hcap] at hstep
  all_goals
    repeat' first | split at hstep | simp_all
  all_goals (subst next; rfl)

/-- The same subset has no control-flow instruction: its concrete PC update is
exactly the instruction-width update above.  Located-path construction can use
this to discharge the next prefix's PC fact from artifact adjacency. -/
theorem runInstr_pc_of_encoding {s next : State} {op : Op}
    {instruction : YulEvmCompiler.Instr}
    (encoding : EncodesOp s.fork op instruction)
    (hcap : s.stack.length < 1024)
    (hstep : Stepper.runInstr instruction s = some next) :
    next.pc = instructionNextPC instruction s.pc := by
  cases encoding.shape <;>
    unfold Stepper.runInstr at hstep <;>
    rw [if_pos hcap] at hstep
  all_goals
    repeat' first | split at hstep | simp_all
  all_goals (subst next; simp [instructionNextPC, *])

/-- The abstract evaluator itself never grows a successful stack by more than
one slot.  Keeping this leaf independent of concrete state avoids unfolding
the large EVM stepper merely to count list constructors. -/
theorem runOp_stack_length_le_succ {memAt : UInt256 → UInt256} {op : Op}
    {stack out : List UInt256} (hrun : runOp memAt op stack = some out) :
    out.length ≤ stack.length + 1 := by
  cases op with
  | push0 =>
      simp only [runOp, Option.some.injEq] at hrun
      subst out
      simp
  | push value =>
      simp only [runOp, Option.some.injEq] at hrun
      subst out
      simp
  | mload =>
      cases stack with
      | nil => simp [runOp] at hrun
      | cons address rest =>
          simp only [runOp, Option.some.injEq] at hrun
          subst out
          simp
  | dup index =>
      cases hget : stack[index - 1]? with
      | none => simp [runOp, hget] at hrun
      | some value =>
          simp only [runOp, hget, Option.map_some, Option.some.injEq] at hrun
          subst out
          simp
  | swap index =>
      cases stack with
      | nil => simp [runOp] at hrun
      | cons top rest =>
          cases hget : rest[index - 1]? with
          | none => simp [runOp, hget] at hrun
          | some value =>
              simp only [runOp, hget, Option.map_some, Option.some.injEq] at hrun
              subst out
              simp
  | pop =>
      cases stack with
      | nil => simp [runOp] at hrun
      | cons top rest =>
          simp only [runOp, Option.some.injEq] at hrun
          subst out
          simp only [List.length_cons]
          omega
  | and | or | xor | add | mul | shr =>
      cases stack with
      | nil => simp [runOp] at hrun
      | cons first rest =>
          cases rest with
          | nil => simp [runOp] at hrun
          | cons second tail =>
              simp only [runOp, Option.some.injEq] at hrun
              subst out
              simp

/-- Every successful instruction in the packed subset grows the stack by at
most one slot.  This is intentionally a coarse bound: it is independent of
the opcode's exact pop count and therefore composes using only the remaining
operation count. -/
theorem runInstr_stack_length_le_succ {s next : State} {op : Op}
    {instruction : YulEvmCompiler.Instr}
    (encoding : EncodesOp s.fork op instruction)
    (hcap : s.stack.length < 1024)
    (hstep : Stepper.runInstr instruction s = some next) :
    next.stack.length ≤ s.stack.length + 1 := by
  exact runOp_stack_length_le_succ
    (runOp_of_runInstr encoding hcap hstep).1

/-- Compositional stack/memory theorem for an ordered encoded sequence.
It says exactly what `runOps` models and nothing about gas, decoding, or the
final PC. -/
theorem runOps_stack_memory_of_encodedRun {ops : List Op}
    {instructions : List YulEvmCompiler.Instr} {s t : State}
    (run : EncodedRun ops instructions s t) :
    runOps (memoryWord s) ops s.stack = some t.stack ∧
      t.memory = s.memory := by
  induction run with
  | nil state => exact ⟨rfl, rfl⟩
  | @cons op instruction ops instructions state next target
      encoding stackCap step tail ih =>
      have hhead := runOp_of_runInstr encoding stackCap step
      have hmemoryWord : memoryWord next = memoryWord state := by
        funext address
        simp [memoryWord, hhead.2]
      constructor
      · change (runOp (memoryWord state) op state.stack).bind
          (runOps (memoryWord state) ops) = some target.stack
        rw [hhead.1]
        simp only [Option.bind_some]
        rw [← hmemoryWord, ih.1]
      · exact ih.2.trans hhead.2

/-- An abstract successful trace plus a non-circular prefix safety plan
constructs the ordered concrete stepper chain.  The final stack and memory
facts are derived along with that chain. -/
theorem encodedRun_of_runOps {ops : List Op}
    {instructions : List YulEvmCompiler.Instr} {s : State}
    {out : List UInt256}
    (plan : EncodedPlan ops instructions s)
    (hrun : runOps (memoryWord s) ops s.stack = some out) :
    ∃ t, EncodedRun ops instructions s t ∧
      t.stack = out ∧ t.memory = s.memory := by
  induction ops generalizing instructions s out with
  | nil =>
      cases instructions with
      | nil =>
          simp only [runOps] at hrun
          injection hrun with hstack
          exact ⟨s, EncodedRun.nil s, hstack, rfl⟩
      | cons instruction instructions =>
          simp [EncodedPlan] at plan
  | cons op ops ih =>
      cases instructions with
      | nil => simp [EncodedPlan] at plan
      | cons instruction instructions =>
          change EncodesOp s.fork op instruction ∧
            s.stack.length < 1024 ∧
            ∀ next, Stepper.runInstr instruction s = some next →
              EncodedPlan ops instructions next at plan
          rcases plan with ⟨encoding, hcap, htailPlan⟩
          change (runOp (memoryWord s) op s.stack).bind
            (runOps (memoryWord s) ops) = some out at hrun
          cases hhead : runOp (memoryWord s) op s.stack with
          | none => simp [hhead] at hrun
          | some middleStack =>
              have htailAbstract :
                  runOps (memoryWord s) ops middleStack = some out := by
                simpa [hhead] using hrun
              obtain ⟨next, hstep, hstack, hmemory⟩ :=
                runInstr_of_runOp encoding hcap hhead
              have hmemoryWord : memoryWord next = memoryWord s := by
                funext address
                simp [memoryWord, hmemory]
              have htailAbstract' :
                  runOps (memoryWord next) ops next.stack = some out := by
                simpa [hmemoryWord, hstack] using htailAbstract
              obtain ⟨target, htailRun, hout, htailMemory⟩ :=
                ih (htailPlan next hstep) htailAbstract'
              exact ⟨target,
                EncodedRun.cons encoding hcap hstep htailRun,
                hout, htailMemory.trans hmemory⟩

/-! ## Located EVM execution

The located plan contains only facts not recoverable from abstract execution:
the opcode shape, the concrete stack cap, and the artifact PC at each prefix.
`Located.wellFormed` supplies decoder validity.  The tail is conditional on the
unique concrete next state, just as for `EncodedPlan`; it does not assume that
the concrete step succeeds.
-/

def LocatedPlan {artifact : ProgramArtifact} {fork : Fork} :
    List Op → List (Stepper.Located artifact fork) → State → Prop
  | [], [], _ => True
  | op :: ops, located :: path, s =>
      EncodesShape op located.instruction ∧
        s.stack.length < 1024 ∧
        s.pc.toNat = artifact.instructionPC located.index ∧
        ∀ next, Stepper.runInstr located.instruction s = some next →
          LocatedPlan ops path next
  | _, _, _ => False

/-- Artifact-level adjacency for the straight-line subset.  Stating the edge
through `UInt256.toNat` makes PC wraparound an explicit failed obligation,
rather than silently identifying natural byte offsets modulo `2^256`. -/
def PCAdjacent {artifact : ProgramArtifact} {fork : Fork}
    (here next : Stepper.Located artifact fork) : Prop :=
  ∀ pc : UInt256,
    pc.toNat = artifact.instructionPC here.index →
      (instructionNextPC here.instruction pc).toNat =
        artifact.instructionPC next.index

/-- A lockstep list of abstract operations and located artifact instructions.
The recursive constructor carries exactly one adjacency/no-wrap certificate
for each neighboring pair. -/
inductive StraightLineLocated {artifact : ProgramArtifact} {fork : Fork} :
    List Op → List (Stepper.Located artifact fork) → Prop where
  | nil : StraightLineLocated [] []
  | single {op : Op} {located : Stepper.Located artifact fork}
      (shape : EncodesShape op located.instruction) :
      StraightLineLocated [op] [located]
  | cons {op nextOp : Op} {ops : List Op}
      {located nextLocated : Stepper.Located artifact fork}
      {path : List (Stepper.Located artifact fork)}
      (shape : EncodesShape op located.instruction)
      (adjacent : PCAdjacent located nextLocated)
      (tail : StraightLineLocated (nextOp :: ops) (nextLocated :: path)) :
      StraightLineLocated (op :: nextOp :: ops)
        (located :: nextLocated :: path)

/-! ## Artifact-site construction

`StackSiteBuilder.ofSlice` proves that a `GenericRoundSite` is an exact slice
of a concrete artifact and records its instruction-boundary PCs.  The two
relations below retain the missing lockstep fact: every instruction in that
slice encodes the corresponding packed operation.  They contain no evaluator
or desired-state premise.
-/

/-- Pointwise opcode-shape agreement for an emitted operation sequence and an
instruction template. -/
inductive EncodesSequence :
    List Op → List YulEvmCompiler.Instr → Prop where
  | nil : EncodesSequence [] []
  | cons {op : Op} {instruction : YulEvmCompiler.Instr}
      {ops : List Op} {instructions : List YulEvmCompiler.Instr}
      (shape : EncodesShape op instruction)
      (tail : EncodesSequence ops instructions) :
      EncodesSequence (op :: ops) (instruction :: instructions)

/-- The same lockstep relation after the concrete artifact lookup has been
packaged into `LocatedSite` records. -/
inductive EncodesSites {artifact : ProgramArtifact} {fork : Fork} :
    List Op → List (LocatedSite artifact fork) → Prop where
  | nil : EncodesSites [] []
  | cons {op : Op} {site : LocatedSite artifact fork}
      {ops : List Op} {sites : List (LocatedSite artifact fork)}
      (shape : EncodesShape op site.located.instruction)
      (tail : EncodesSites ops sites) :
      EncodesSites (op :: ops) (site :: sites)

/-- Mapping away the site metadata preserves the exact operation/instruction
alignment; this is the only transport needed from a template equality. -/
theorem encodesSites_of_sequence {artifact : ProgramArtifact} {fork : Fork}
    {ops : List Op} {sites : List (LocatedSite artifact fork)}
    (sequence : EncodesSequence ops
      (sites.map (fun site => site.located.instruction))) :
    EncodesSites ops sites := by
  induction sites generalizing ops with
  | nil =>
      cases ops with
      | nil => exact .nil
      | cons op ops => cases sequence
  | cons site sites ih =>
      cases ops with
      | nil => cases sequence
      | cons op ops =>
          cases sequence with
          | cons shape tail => exact .cons shape (ih tail)

/-- For every permitted shape, the bridge's PC update is exactly the encoded
instruction size.  This theorem is word-level, so a later `toNat` equality
still has to discharge non-wrapping from the artifact PC certificate. -/
theorem instructionNextPC_eq_add_size {op : Op}
    {instruction : YulEvmCompiler.Instr}
    (shape : EncodesShape op instruction) (pc : UInt256) :
    instructionNextPC instruction pc =
      pc + UInt256.ofNat instruction.size := by
  cases shape with
  | push width value positive =>
      have hwidth : width.val ≠ 0 := Nat.ne_of_gt positive
      simp only [instructionNextPC, hwidth, if_false,
        YulEvmCompiler.Instr.size_push]
      rw [Nat.add_comm width.val 1]
  | push0 | mload | dup | swap | pop | land | lor | xor | add | mul | shr =>
      change pc.add (UInt256.ofNat 1) = pc.add (UInt256.ofNat 1)
      rfl

/-- One `Contiguous` edge supplies the explicit no-wrap `PCAdjacent` fact.
Both endpoint PCs remain tied to the concrete artifact's `instructionPC`
table through their `LocatedSite.pc_eq` fields. -/
theorem pcAdjacent_of_contiguous {artifact : ProgramArtifact} {fork : Fork}
    {op : Op} {here next : LocatedSite artifact fork}
    (shape : EncodesShape op here.located.instruction)
    (edge : next.pc = here.pc +
      UInt256.ofNat here.located.instruction.size) :
    PCAdjacent here.located next.located := by
  intro pc hpc
  have hpceq : pc = here.pc :=
    Challenge.EvmProof.Word.word_ext (hpc.trans here.pc_eq.symm)
  subst pc
  rw [instructionNextPC_eq_add_size shape, ← edge]
  exact next.pc_eq

/-- Convert exact artifact sites plus pointwise opcode shapes into the
straight-line located path consumed by `roundsCertificate`. -/
theorem straightLineLocated_of_sites {artifact : ProgramArtifact}
    {fork : Fork} {ops : List Op}
    {sites : List (LocatedSite artifact fork)}
    (encoding : EncodesSites ops sites)
    (contiguous : Contiguous sites) :
    StraightLineLocated ops (LocatedSite.path sites) := by
  induction encoding with
  | nil => exact .nil
  | @cons op site ops sites shape tail ih =>
      cases tail with
      | nil => exact .single shape
      | @cons nextOp nextSite nextOps nextSites nextShape nextTail =>
          exact .cons shape
            (pcAdjacent_of_contiguous shape contiguous.1)
            (ih contiguous.2)

/-- Reusable constructor from a concrete artifact slice.  The site object
supplies exact instruction lookup and contiguous PCs; the caller proves only
that its emitted operation list encodes the template in order. -/
theorem straightLineLocated_of_genericRoundSite
    {artifact : ProgramArtifact} {fork : Fork}
    {ops : List Op} {template : List YulEvmCompiler.Instr}
    (site : GenericRoundSite artifact fork template)
    (encoding : EncodesSequence ops template) :
    StraightLineLocated ops site.path := by
  have mapped : EncodesSequence ops
      (site.sites.map (fun item => item.located.instruction)) := by
    rw [site.instruction_eq]
    exact encoding
  exact straightLineLocated_of_sites
    (encodesSites_of_sequence mapped) site.contiguous

/-- The initial PC obligation for a possibly empty located path. -/
def PathStarts {artifact : ProgramArtifact} {fork : Fork}
    (path : List (Stepper.Located artifact fork)) (s : State) : Prop :=
  match path with
  | [] => True
  | located :: _ => s.pc.toNat = artifact.instructionPC located.index

/-- Construct all per-prefix `LocatedPlan` capacity and PC facts from a
lockstep straight-line path and one coarse stack bound.  The conditional tail
is proved for the concrete state produced by any successful head step; no
concrete-success witness or desired intermediate state is assumed. -/
theorem locatedPlan_of_straightLine {artifact : ProgramArtifact} {fork : Fork}
    {ops : List Op} {path : List (Stepper.Located artifact fork)} {s : State}
    (sequence : StraightLineLocated ops path)
    (hbudget : s.stack.length + ops.length < 1024)
    (hstart : PathStarts path s)
    (hfork : s.fork = fork) :
    LocatedPlan ops path s := by
  induction sequence generalizing s with
  | nil => trivial
  | @single op located shape =>
      have hcap : s.stack.length < 1024 := by
        simp only [List.length_cons, List.length_nil] at hbudget
        omega
      have hpc : s.pc.toNat = artifact.instructionPC located.index := by
        simpa [PathStarts] using hstart
      change EncodesShape op located.instruction ∧
        s.stack.length < 1024 ∧
        s.pc.toNat = artifact.instructionPC located.index ∧
        ∀ next, Stepper.runInstr located.instruction s = some next → True
      exact ⟨shape, hcap, hpc, by intros; trivial⟩
  | @cons op nextOp ops located nextLocated path shape adjacent tail ih =>
      have hcap : s.stack.length < 1024 := by
        simp only [List.length_cons] at hbudget
        omega
      have hpc : s.pc.toNat = artifact.instructionPC located.index := by
        simpa [PathStarts] using hstart
      change EncodesShape op located.instruction ∧
        s.stack.length < 1024 ∧
        s.pc.toNat = artifact.instructionPC located.index ∧
        ∀ next, Stepper.runInstr located.instruction s = some next →
          LocatedPlan (nextOp :: ops) (nextLocated :: path) next
      refine ⟨shape, hcap, hpc, ?_⟩
      intro next hstep
      let encoding : EncodesOp s.fork op located.instruction := {
        shape := shape
        wellFormed := by simpa [hfork] using located.wellFormed }
      have hgrowth := runInstr_stack_length_le_succ encoding hcap hstep
      have htailBudget : next.stack.length + (nextOp :: ops).length < 1024 := by
        simp only [List.length_cons] at hbudget ⊢
        omega
      have htailStart : PathStarts (nextLocated :: path) next := by
        simp only [PathStarts]
        rw [runInstr_pc_of_encoding encoding hcap hstep]
        exact adjacent s.pc hpc
      have henv := Stepper.runInstr_executionEnv hstep
      have hnextFork : next.fork = fork := by
        change next.executionEnv.fork = fork
        rw [henv]
        exact hfork
      exact ih htailBudget htailStart hnextFork

/-- Construct an executable located block from the abstract packed trace.
Running status and fork preservation are derived at every recursive step. -/
theorem runLocatedBlock_of_runOps {artifact : ProgramArtifact} {fork : Fork}
    {ops : List Op} {path : List (Stepper.Located artifact fork)}
    {s : State} {out : List UInt256}
    (plan : LocatedPlan ops path s)
    (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (habstract : runOps (memoryWord s) ops s.stack = some out) :
    ∃ t, Stepper.runLocatedBlock path s = some t ∧
      t.stack = out ∧ t.memory = s.memory := by
  induction ops generalizing path s out with
  | nil =>
      cases path with
      | nil =>
          simp only [runOps] at habstract
          injection habstract with hstack
          exact ⟨s, rfl, hstack, rfl⟩
      | cons located path => simp [LocatedPlan] at plan
  | cons op ops ih =>
      cases path with
      | nil => simp [LocatedPlan] at plan
      | cons located path =>
          change EncodesShape op located.instruction ∧
            s.stack.length < 1024 ∧
            s.pc.toNat = artifact.instructionPC located.index ∧
            ∀ next,
              Stepper.runInstr located.instruction s = some next →
                LocatedPlan ops path next at plan
          rcases plan with ⟨shape, hcap, hpc, htailPlan⟩
          let encoding : EncodesOp s.fork op located.instruction := {
            shape := shape
            wellFormed := by simpa [hfork] using located.wellFormed }
          change (runOp (memoryWord s) op s.stack).bind
            (runOps (memoryWord s) ops) = some out at habstract
          cases hhead : runOp (memoryWord s) op s.stack with
          | none => simp [hhead] at habstract
          | some middleStack =>
              have htailAbstract :
                  runOps (memoryWord s) ops middleStack = some out := by
                simpa [hhead] using habstract
              obtain ⟨next, hstep, hstack, hmemory⟩ :=
                runInstr_of_runOp encoding hcap hhead
              have hlocated : Stepper.runLocated located s = some next := by
                unfold Stepper.runLocated
                rw [if_pos hpc]
                exact hstep
              have hnextRun : next.halt = .Running := by
                rw [runInstr_halt_of_encoding encoding hcap hstep, hrun]
              have henv := Stepper.runInstr_executionEnv hstep
              have hnextFork : next.fork = fork := by
                change next.executionEnv.fork = fork
                rw [henv]
                exact hfork
              have hmemoryWord : memoryWord next = memoryWord s := by
                funext address
                simp [memoryWord, hmemory]
              have htailAbstract' :
                  runOps (memoryWord next) ops next.stack = some out := by
                simpa [hmemoryWord, hstack] using htailAbstract
              obtain ⟨target, htailBlock, hout, htailMemory⟩ :=
                ih (htailPlan next hstep) hnextFork hnextRun htailAbstract'
              have hheadBlock :
                  Stepper.runLocatedBlock [located] s = some next := by
                simp [Stepper.runLocatedBlock, hlocated]
              have hwhole := Stepper.runLocatedBlock_append
                [located] path s next target hheadBlock hnextRun htailBlock
              exact ⟨target, by simpa using hwhole,
                hout, htailMemory.trans hmemory⟩

/-- Actual gas-parametric EVM certificate for a planned packed straight-line
sequence.  Code/fork/running/no-precompile remain explicit because they are
semantic premises, while decoder well-formedness is carried by each `Located`.
-/
theorem gasSteps_of_runOps {artifact : ProgramArtifact} {fork : Fork}
    {ops : List Op} {path : List (Stepper.Located artifact fork)}
    {s : State} {out : List UInt256}
    (plan : LocatedPlan ops path s)
    (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (habstract : runOps (memoryWord s) ops s.stack = some out) :
    ∃ t, Stepper.runLocatedBlock path s = some t ∧
      ∃ _trace : GasSteps s t, t.stack = out ∧ t.memory = s.memory := by
  obtain ⟨t, hblock, hstack, hmemory⟩ :=
    runLocatedBlock_of_runOps plan hfork hrun habstract
  exact ⟨t, hblock,
    ⟨Stepper.runLocatedBlock_sound artifact fork path hcode hfork hblock hrun hnp,
      hstack, hmemory⟩⟩

/-- Reusable round certificate with no manually supplied per-prefix plan.
One initial PC fact, artifact adjacency/no-wrap, and the coarse stack budget
generate the full located execution plan before lifting to `GasSteps`. -/
theorem roundsCertificate {artifact : ProgramArtifact} {fork : Fork}
    {ops : List Op} {path : List (Stepper.Located artifact fork)}
    {s : State} {out : List UInt256}
    (sequence : StraightLineLocated ops path)
    (hbudget : s.stack.length + ops.length < 1024)
    (hstart : PathStarts path s)
    (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (habstract : runOps (memoryWord s) ops s.stack = some out) :
    ∃ t, Stepper.runLocatedBlock path s = some t ∧
      ∃ _trace : GasSteps s t, t.stack = out ∧ t.memory = s.memory := by
  exact gasSteps_of_runOps
    (locatedPlan_of_straightLine sequence hbudget hstart hfork)
    hcode hfork hrun hnp habstract

#print axioms runInstr_mload_stack_memory
#print axioms runInstr_mload_exact
#print axioms runInstr_stack_memory_of_encoding
#print axioms runOps_stack_memory_of_encodedRun
#print axioms runInstr_of_runOp
#print axioms encodedRun_of_runOps
#print axioms runInstr_halt_of_encoding
#print axioms runInstr_pc_of_encoding
#print axioms gasSteps_of_runOps
#print axioms runInstr_stack_length_le_succ
#print axioms runOp_stack_length_le_succ
#print axioms locatedPlan_of_straightLine
#print axioms roundsCertificate

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRunOpBridge
