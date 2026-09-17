import Challenge.Modexp.Submission.LocalPatch.StaticDomain
import Challenge.EvmProof.Word
import EvmSemantics.EVM.BigStep

set_option warningAsError true

/-!
# Actual-step closure of a certified static PC domain

This module connects the decoder-level `StaticDomain.Certificate` to the real
pinned `EVM.Step` relation. It is independent of candidate/reference state
transport and gas refinement.

The live source invariant is top-level and same-frame:

* the active frame is running;
* `callStack = []`;
* the active environment contains the certified code;
* the active fork is Osaka;
* the current natural PC belongs to the certified finite domain.

Same-frame preservation is a conclusion for a running target, not a premise.
Terminal targets are classified separately.
-/

namespace Challenge.Modexp.Submission.LocalPatch.StaticExecution

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.LocalPatch.StaticDomain

/-- A completed top-level frame. -/
def TerminalTop (s : State) : Prop :=
  s.halt ≠ .Running ∧ s.callStack = []

/-- A live state in one fixed top-level execution environment and finite PC
certificate. -/
def RunningInDomain {code : ByteArray} (cert : Certificate code)
    (env : ExecutionEnv) (s : State) : Prop :=
  s.halt = .Running ∧
    s.callStack = [] ∧
    s.executionEnv = env ∧
    s.pc.toNat ∈ cert.pcs

/-- Endpoint invariant propagated along an actual finite EVM execution. -/
def InDomain {code : ByteArray} (cert : Certificate code)
    (env : ExecutionEnv) (s : State) : Prop :=
  TerminalTop s ∨ RunningInDomain cert env s

private theorem transportSafe_available_osaka (op : Operation)
    (hsafe : transportSafe op = true) :
    op.availableInFork .Osaka = true := by
  cases op with
  | StopArith op => cases op <;> rfl
  | CompBit op => cases op <;> decide
  | Keccak op => simp [transportSafe] at hsafe
  | Env op =>
      cases op <;>
        simp [transportSafe, Operation.availableInFork] at hsafe ⊢
  | Block op => simp [transportSafe] at hsafe
  | StackMemFlow op =>
      cases op <;>
        simp [transportSafe, Operation.availableInFork] at hsafe ⊢;
        decide
  | Push op =>
      by_cases hzero : op.width.val = 0
      · simp [Operation.availableInFork, hzero]
        decide
      · simp [Operation.availableInFork, hzero]
  | Dup op => rfl
  | Swap op => rfl
  | DupN op => simp [transportSafe] at hsafe
  | SwapN op => simp [transportSafe] at hsafe
  | Exchange op => simp [transportSafe] at hsafe
  | Log op =>
      cases op with
      | mk topics => simp [transportSafe] at hsafe
  | System op =>
      cases op <;>
        simp [transportSafe, Operation.availableInFork] at hsafe ⊢

private theorem state_decoded_of_raw_osaka {code : ByteArray} {s : State}
    {op : Operation} {imm : Option (UInt256 × Nat)}
    (hcode : s.executionEnv.code = code)
    (hfork : s.fork = .Osaka)
    (hraw : Decode.decodeAt code s.pc.toNat = some (op, imm))
    (hsafe : transportSafe op = true) :
    s.decoded = some (op, imm) := by
  unfold State.decoded
  rw [hcode, hraw, hfork]
  simp [transportSafe_available_osaka op hsafe]

private theorem raw_of_decodedOp
    {code : ByteArray} {s : State}
    {current expected : Operation} {imm : Option (UInt256 × Nat)}
    (hraw : Decode.decodeAt code s.pc.toNat = some (current, imm))
    (hcurrent : s.decodedOp = some current)
    (hexpected : s.decodedOp = some expected) :
    Decode.decodeAt code s.pc.toNat = some (expected, imm) := by
  have hop : current = expected :=
    Option.some.inj (hcurrent.symm.trans hexpected)
  simpa [hop] using hraw

private theorem raw_of_decoded
    {code : ByteArray} {s : State}
    {current expected : Operation}
    {imm expectedImm : Option (UInt256 × Nat)}
    (hraw : Decode.decodeAt code s.pc.toNat = some (current, imm))
    (hcurrent : s.decoded = some (current, imm))
    (hexpected : s.decoded = some (expected, expectedImm)) :
    Decode.decodeAt code s.pc.toNat = some (expected, expectedImm) := by
  have hpair : (current, imm) = (expected, expectedImm) :=
    Option.some.inj (hcurrent.symm.trans hexpected)
  cases hpair
  exact hraw

private theorem unsafe_decodedOp
    {s : State} {current bad : Operation}
    {imm : Option (UInt256 × Nat)}
    (hdecoded : s.decoded = some (current, imm))
    (hsafe : transportSafe current = true)
    (hbad : s.decodedOp = some bad)
    (hunsafe : transportSafe bad = false) : False := by
  have hcurrent : s.decodedOp = some current :=
    State.decoded_to_op hdecoded
  have hop : current = bad :=
    Option.some.inj (hcurrent.symm.trans hbad)
  subst bad
  simp_all

private theorem next_facts_of_site {code : ByteArray} {pc : Nat}
    {op : Operation} {imm : Option (UInt256 × Nat)}
    (hdecode : Decode.decodeAt code pc = some (op, imm))
    (hflow : flowKind op = .next ∨ flowKind op = .jumpi)
    (hsite : siteCheck code pc = true) :
    execNext code pc = scanNext code pc ∧ execNext code pc < code.size := by
  rw [siteCheck, hdecode] at hsite
  simp only [Bool.and_eq_true] at hsite
  have hrest := hsite.2
  rcases hflow with hflow | hflow <;> simp only [hflow] at hrest
  all_goals
    simp only [Bool.and_eq_true] at hrest
    exact ⟨beq_iff_eq.mp hrest.1, of_decide_eq_true hrest.2⟩

private theorem succ_toNat_noWrap (pc : UInt256)
    (h : pc.toNat + 1 < 2 ^ 256) :
    pc.succ.toNat = pc.toNat + 1 := by
  change (pc + UInt256.ofNat 1).toNat = pc.toNat + 1
  rw [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  norm_num
  exact h

private theorem add_ofNat_toNat_noWrap (pc : UInt256) (n : Nat)
    (h : pc.toNat + n < 2 ^ 256) :
    (pc + UInt256.ofNat n).toNat = pc.toNat + n := by
  have hn : n < 2 ^ 256 := by omega
  rw [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt h]

private theorem decodeAt_push_width {code : ByteArray} {pc : Nat}
    {k : Fin 33} {data : UInt256} {immWidth : Nat}
    (hdecode : Decode.decodeAt code pc =
      some (.Push ⟨k, k.isLt⟩, some (data, immWidth))) :
    immWidth = k.val := by
  unfold Decode.decodeAt at hdecode
  split at hdecode
  · cases hopcode : Decode.opcodeOf code[pc] with
    | none => simp_all
    | some op =>
        cases op <;> simp_all
        rename_i push
        rcases hdecode with ⟨hpush, _, hwidth⟩
        cases hpush
        exact hwidth.symm
  · simp at hdecode

private theorem successor_succ_of_decodedOp
    {code : ByteArray} (cert : Certificate code)
    (hsize : code.size < 2 ^ 256)
    {s : State} {current expected : Operation}
    {imm : Option (UInt256 × Nat)}
    (hpc : s.pc.toNat ∈ cert.pcs)
    (hraw : Decode.decodeAt code s.pc.toNat = some (current, imm))
    (hcurrent : s.decodedOp = some current)
    (hexpected : s.decodedOp = some expected)
    (hflow : flowKind expected = .next)
    (hwidth : execWidth expected = 1) :
    StaticSuccessor code s.pc.toNat s.pc.succ.toNat := by
  have hdecode := raw_of_decodedOp hraw hcurrent hexpected
  obtain ⟨_, hlt⟩ := next_facts_of_site hdecode (Or.inl hflow)
    (cert.safe hpc)
  have hexec : execNext code s.pc.toNat = s.pc.toNat + 1 := by
    simp [execNext, hdecode, hwidth]
  have hlt' : s.pc.toNat + 1 < code.size := by
    rw [← hexec]
    exact hlt
  have hnowrap : s.pc.toNat + 1 < 2 ^ 256 :=
    lt_trans hlt' hsize
  have hsucc := succ_toNat_noWrap s.pc hnowrap
  unfold StaticSuccessor
  simp only [hdecode]
  rw [hflow]
  exact hsucc.trans hexec.symm

private theorem successor_succ_jumpi
    {code : ByteArray} (cert : Certificate code)
    (hsize : code.size < 2 ^ 256)
    {s : State} {current : Operation}
    {imm : Option (UInt256 × Nat)}
    (hpc : s.pc.toNat ∈ cert.pcs)
    (hraw : Decode.decodeAt code s.pc.toNat = some (current, imm))
    (hcurrent : s.decodedOp = some current)
    (hjumpi : s.decodedOp = some .JUMPI) :
    StaticSuccessor code s.pc.toNat s.pc.succ.toNat := by
  have hdecode := raw_of_decodedOp hraw hcurrent hjumpi
  have hflow : flowKind (.JUMPI : Operation) = .jumpi := rfl
  obtain ⟨_, hlt⟩ := next_facts_of_site hdecode (Or.inr hflow)
    (cert.safe hpc)
  have hexec : execNext code s.pc.toNat = s.pc.toNat + 1 := by
    simp [execNext, hdecode, execWidth]
  have hlt' : s.pc.toNat + 1 < code.size := by
    rw [← hexec]
    exact hlt
  have hnowrap : s.pc.toNat + 1 < 2 ^ 256 :=
    lt_trans hlt' hsize
  have hsucc := succ_toNat_noWrap s.pc hnowrap
  unfold StaticSuccessor
  simp only [hdecode, flowKind]
  exact Or.inl (hsucc.trans hexec.symm)

private theorem successor_push
    {code : ByteArray} (cert : Certificate code)
    (hsize : code.size < 2 ^ 256)
    {s : State} {current : Operation}
    {imm : Option (UInt256 × Nat)}
    {k : Fin 33} {data : UInt256} {immWidth : Nat}
    (hpc : s.pc.toNat ∈ cert.pcs)
    (hraw : Decode.decodeAt code s.pc.toNat = some (current, imm))
    (hcurrent : s.decoded = some (current, imm))
    (hpush : s.decoded =
      some (.Push ⟨k, k.isLt⟩, some (data, immWidth))) :
    StaticSuccessor code s.pc.toNat
      (s.pc + UInt256.ofNat (immWidth + 1)).toNat := by
  have hdecode := raw_of_decoded hraw hcurrent hpush
  have hwidth := decodeAt_push_width hdecode
  have hflow : flowKind (.Push ⟨k, k.isLt⟩ : Operation) = .next := rfl
  obtain ⟨_, hlt⟩ := next_facts_of_site hdecode (Or.inl hflow)
    (cert.safe hpc)
  have hexec : execNext code s.pc.toNat =
      s.pc.toNat + (immWidth + 1) := by
    simp [execNext, hdecode, execWidth, hwidth]
    omega
  have hlt' : s.pc.toNat + (immWidth + 1) < code.size := by
    rw [← hexec]
    exact hlt
  have hnowrap : s.pc.toNat + (immWidth + 1) < 2 ^ 256 :=
    lt_trans hlt' hsize
  have hpcNat := add_ofNat_toNat_noWrap s.pc (immWidth + 1) hnowrap
  unfold StaticSuccessor
  simp only [hdecode, flowKind]
  exact hpcNat.trans hexec.symm

private theorem successor_jump
    {code : ByteArray} {s : State}
    {current : Operation} {imm : Option (UInt256 × Nat)}
    {dest : UInt256}
    (hraw : Decode.decodeAt code s.pc.toNat = some (current, imm))
    (hcurrent : s.decodedOp = some current)
    (hjump : s.decodedOp = some .JUMP)
    (hcode : s.executionEnv.code = code)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code dest.toNat = true) :
    StaticSuccessor code s.pc.toNat dest.toNat := by
  have hdecode := raw_of_decodedOp hraw hcurrent hjump
  have hvalid' : Decode.isValidJumpDest code dest.toNat = true := by
    simpa [hcode] using hvalid
  unfold StaticSuccessor
  simp only [hdecode, flowKind]
  exact hvalid'

private theorem successor_jumpi_taken
    {code : ByteArray} {s : State}
    {current : Operation} {imm : Option (UInt256 × Nat)}
    {dest : UInt256}
    (hraw : Decode.decodeAt code s.pc.toNat = some (current, imm))
    (hcurrent : s.decodedOp = some current)
    (hjumpi : s.decodedOp = some .JUMPI)
    (hcode : s.executionEnv.code = code)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code dest.toNat = true) :
    StaticSuccessor code s.pc.toNat dest.toNat := by
  have hdecode := raw_of_decodedOp hraw hcurrent hjumpi
  have hvalid' : Decode.isValidJumpDest code dest.toNat = true := by
    simpa [hcode] using hvalid
  unfold StaticSuccessor
  simp only [hdecode, flowKind]
  exact Or.inr hvalid'

private theorem running_succ_result
    {code : ByteArray} (cert : Certificate code)
    (hsize : code.size < 2 ^ 256)
    {s t : State} {current expected : Operation}
    {imm : Option (UInt256 × Nat)}
    (hpc : s.pc.toNat ∈ cert.pcs)
    (hraw : Decode.decodeAt code s.pc.toNat = some (current, imm))
    (hdecoded : s.decoded = some (current, imm))
    (hexpected : s.decodedOp = some expected)
    (hflow : flowKind expected = .next)
    (hwidth : execWidth expected = 1)
    (hsEmpty : s.callStack = [])
    (hcall : t.callStack = s.callStack)
    (henv : t.executionEnv = s.executionEnv)
    (hnext : t.pc = s.pc.succ) :
    t.callStack = [] ∧
      t.executionEnv = s.executionEnv ∧
      StaticSuccessor code s.pc.toNat t.pc.toNat := by
  refine ⟨hcall.trans hsEmpty, henv, ?_⟩
  rw [hnext]
  exact successor_succ_of_decodedOp cert hsize hpc hraw
    (State.decoded_to_op hdecoded) hexpected hflow hwidth

private theorem running_push_result
    {code : ByteArray} (cert : Certificate code)
    (hsize : code.size < 2 ^ 256)
    {s t : State} {current : Operation}
    {imm : Option (UInt256 × Nat)}
    {k : Fin 33} {data : UInt256} {immWidth : Nat}
    (hpc : s.pc.toNat ∈ cert.pcs)
    (hraw : Decode.decodeAt code s.pc.toNat = some (current, imm))
    (hdecoded : s.decoded = some (current, imm))
    (hpush : s.decoded =
      some (.Push ⟨k, k.isLt⟩, some (data, immWidth)))
    (hsEmpty : s.callStack = [])
    (hcall : t.callStack = s.callStack)
    (henv : t.executionEnv = s.executionEnv)
    (hnext : t.pc = s.pc + UInt256.ofNat (immWidth + 1)) :
    t.callStack = [] ∧
      t.executionEnv = s.executionEnv ∧
      StaticSuccessor code s.pc.toNat t.pc.toNat := by
  refine ⟨hcall.trans hsEmpty, henv, ?_⟩
  rw [hnext]
  exact successor_push cert hsize hpc hraw hdecoded hpush

private theorem stepRunning_terminal_callStack_empty
    {s t : State} {current : Operation}
    {imm : Option (UInt256 × Nat)}
    (hrun : StepRunning s t)
    (hsRunning : s.halt = .Running)
    (hsEmpty : s.callStack = [])
    (htTerminal : t.halt ≠ .Running)
    (hdecoded : s.decoded = some (current, imm))
    (hsafe : transportSafe current = true) :
    t.callStack = [] := by
  cases hrun
  case call =>
      have hbad : s.decodedOp = some .CALL := by assumption
      exact (unsafe_decodedOp hdecoded hsafe hbad rfl).elim
  case callcode =>
      have hbad : s.decodedOp = some .CALLCODE := by assumption
      exact (unsafe_decodedOp hdecoded hsafe hbad rfl).elim
  case delegatecall =>
      have hbad : s.decodedOp = some .DELEGATECALL := by assumption
      exact (unsafe_decodedOp hdecoded hsafe hbad rfl).elim
  case staticcall =>
      have hbad : s.decodedOp = some .STATICCALL := by assumption
      exact (unsafe_decodedOp hdecoded hsafe hbad rfl).elim
  case create =>
      have hbad : s.decodedOp = some .CREATE := by assumption
      exact (unsafe_decodedOp hdecoded hsafe hbad rfl).elim
  case create2 =>
      have hbad : s.decodedOp = some .CREATE2 := by assumption
      exact (unsafe_decodedOp hdecoded hsafe hbad rfl).elim
  case selfDestruct =>
      have hbad : s.decodedOp = some .SELFDESTRUCT := by assumption
      exact (unsafe_decodedOp hdecoded hsafe hbad rfl).elim
  all_goals simp_all

private theorem stepRunning_running_outcome
    {code : ByteArray} (cert : Certificate code)
    (hsize : code.size < 2 ^ 256)
    {s t : State}
    (hrun : StepRunning s t)
    (htRunning : t.halt = .Running)
    (hsEmpty : s.callStack = [])
    (hcode : s.executionEnv.code = code)
    (hfork : s.fork = .Osaka)
    (hpc : s.pc.toNat ∈ cert.pcs) :
    t.callStack = [] ∧
      t.executionEnv = s.executionEnv ∧
      StaticSuccessor code s.pc.toNat t.pc.toNat := by
  obtain ⟨op, imm, hraw, hsafe⟩ := cert.decodedSafe hpc
  have hsDecoded :=
    state_decoded_of_raw_osaka hcode hfork hraw hsafe
  cases hrun
  case add =>
      have hOp : s.decodedOp = some .ADD := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case mul =>
      have hOp : s.decodedOp = some .MUL := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case sub =>
      have hOp : s.decodedOp = some .SUB := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case div =>
      have hOp : s.decodedOp = some .DIV := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case sdiv =>
      have hOp : s.decodedOp = some .SDIV := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case mod =>
      have hOp : s.decodedOp = some .MOD := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case smod =>
      have hOp : s.decodedOp = some .SMOD := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case addmod =>
      have hOp : s.decodedOp = some .ADDMOD := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case mulmod =>
      have hOp : s.decodedOp = some .MULMOD := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case exp =>
      have hOp : s.decodedOp = some .EXP := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case signextend =>
      have hOp : s.decodedOp = some .SIGNEXTEND := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case lt =>
      have hOp : s.decodedOp = some .LT := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case gt =>
      have hOp : s.decodedOp = some .GT := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case slt =>
      have hOp : s.decodedOp = some .SLT := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case sgt =>
      have hOp : s.decodedOp = some .SGT := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case eq =>
      have hOp : s.decodedOp = some .EQ := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case iszero =>
      have hOp : s.decodedOp = some .ISZERO := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case «and» =>
      have hOp : s.decodedOp = some .AND := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case «or» =>
      have hOp : s.decodedOp = some .OR := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case xor_ =>
      have hOp : s.decodedOp = some .XOR := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case «not» =>
      have hOp : s.decodedOp = some .NOT := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case clz =>
      have hOp : s.decodedOp = some .CLZ := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case byte_ =>
      have hOp : s.decodedOp = some .BYTE := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case shl =>
      have hOp : s.decodedOp = some .SHL := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case shr =>
      have hOp : s.decodedOp = some .SHR := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case sar =>
      have hOp : s.decodedOp = some .SAR := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case calldataload =>
      have hOp : s.decodedOp = some .CALLDATALOAD := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case calldatasize =>
      have hOp : s.decodedOp = some .CALLDATASIZE := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case calldatacopy =>
      have hOp : s.decodedOp = some .CALLDATACOPY := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case pop =>
      have hOp : s.decodedOp = some .POP := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case push0 =>
      have hOp : s.decodedOp = some (.Push ⟨0, by decide⟩) := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case mload =>
      have hOp : s.decodedOp = some .MLOAD := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case mstore =>
      have hOp : s.decodedOp = some .MSTORE := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case mstore8 =>
      have hOp : s.decodedOp = some .MSTORE8 := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case msize =>
      have hOp : s.decodedOp = some .MSIZE := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case mcopy =>
      have hOp : s.decodedOp = some .MCOPY := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case jumpdest =>
      have hOp : s.decodedOp = some .JUMPDEST := by assumption
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case dup =>
      obtain ⟨n, hOp⟩ :
          ∃ n : Fin 16, s.decodedOp = some (.Dup ⟨n⟩) := by
        exact ⟨_, by assumption⟩
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case swap =>
      obtain ⟨n, hOp⟩ :
          ∃ n : Fin 16, s.decodedOp = some (.Swap ⟨n⟩) := by
        exact ⟨_, by assumption⟩
      exact running_succ_result cert hsize hpc hraw hsDecoded hOp
        rfl rfl hsEmpty rfl rfl rfl
  case pushN =>
      exact running_push_result cert hsize hpc hraw hsDecoded
        (by assumption) hsEmpty rfl rfl rfl
  case jump =>
      have hOp : s.decodedOp = some .JUMP := by assumption
      refine ⟨hsEmpty, rfl, ?_⟩
      exact successor_jump hraw (State.decoded_to_op hsDecoded) hOp hcode
        (by assumption)
  case jumpi_taken =>
      have hOp : s.decodedOp = some .JUMPI := by assumption
      refine ⟨hsEmpty, rfl, ?_⟩
      exact successor_jumpi_taken hraw (State.decoded_to_op hsDecoded) hOp
        hcode (by assumption)
  case jumpi_notTaken =>
      have hOp : s.decodedOp = some .JUMPI := by assumption
      refine ⟨hsEmpty, rfl, ?_⟩
      exact successor_succ_jumpi cert hsize hpc hraw
        (State.decoded_to_op hsDecoded) hOp
  case keccak256 =>
      have hBad : s.decodedOp = some .KECCAK256 := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case address =>
      have hBad : s.decodedOp = some .ADDRESS := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case balance =>
      have hBad : s.decodedOp = some .BALANCE := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case origin =>
      have hBad : s.decodedOp = some .ORIGIN := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case caller =>
      have hBad : s.decodedOp = some .CALLER := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case callvalue =>
      have hBad : s.decodedOp = some .CALLVALUE := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case codesize =>
      have hBad : s.decodedOp = some .CODESIZE := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case codecopy =>
      have hBad : s.decodedOp = some .CODECOPY := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case gasprice =>
      have hBad : s.decodedOp = some .GASPRICE := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case extcodesize =>
      have hBad : s.decodedOp = some .EXTCODESIZE := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case extcodecopy =>
      have hBad : s.decodedOp = some .EXTCODECOPY := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case returndatasize =>
      have hBad : s.decodedOp = some .RETURNDATASIZE := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case returndatacopy =>
      have hBad : s.decodedOp = some .RETURNDATACOPY := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case extcodehash =>
      have hBad : s.decodedOp = some .EXTCODEHASH := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case blockhash =>
      have hBad : s.decodedOp = some .BLOCKHASH := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case coinbase =>
      have hBad : s.decodedOp = some .COINBASE := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case timestamp =>
      have hBad : s.decodedOp = some .TIMESTAMP := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case number =>
      have hBad : s.decodedOp = some .NUMBER := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case prevrandao =>
      have hBad : s.decodedOp = some .PREVRANDAO := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case gaslimit =>
      have hBad : s.decodedOp = some .GASLIMIT := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case chainid =>
      have hBad : s.decodedOp = some .CHAINID := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case selfbalance =>
      have hBad : s.decodedOp = some .SELFBALANCE := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case basefee =>
      have hBad : s.decodedOp = some .BASEFEE := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case blobhash =>
      have hBad : s.decodedOp = some .BLOBHASH := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case blobhash_oob =>
      have hBad : s.decodedOp = some .BLOBHASH := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case blobbasefee =>
      have hBad : s.decodedOp = some .BLOBBASEFEE := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case sload =>
      have hBad : s.decodedOp = some .SLOAD := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case sstore =>
      have hBad : s.decodedOp = some .SSTORE := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case tload =>
      have hBad : s.decodedOp = some .TLOAD := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case tstore =>
      have hBad : s.decodedOp = some .TSTORE := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case pc =>
      have hBad : s.decodedOp = some .PC := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case gas =>
      have hBad : s.decodedOp = some .GAS := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case revert =>
      have hBad : s.decodedOp = some .REVERT := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case callStatic =>
      have hBad : s.decodedOp = some .CALL := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case call =>
      have hBad : s.decodedOp = some .CALL := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case callFail =>
      have hBad : s.decodedOp = some .CALL := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case callcode =>
      have hBad : s.decodedOp = some .CALLCODE := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case callcodeFail =>
      have hBad : s.decodedOp = some .CALLCODE := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case delegatecall =>
      have hBad : s.decodedOp = some .DELEGATECALL := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case delegatecallFail =>
      have hBad : s.decodedOp = some .DELEGATECALL := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case staticcall =>
      have hBad : s.decodedOp = some .STATICCALL := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case staticcallFail =>
      have hBad : s.decodedOp = some .STATICCALL := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case createStatic =>
      have hBad : s.decodedOp = some .CREATE := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case createFail =>
      have hBad : s.decodedOp = some .CREATE := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case createCollision =>
      have hBad : s.decodedOp = some .CREATE := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case create =>
      have hBad : s.decodedOp = some .CREATE := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case create2Static =>
      have hBad : s.decodedOp = some .CREATE2 := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case create2Fail =>
      have hBad : s.decodedOp = some .CREATE2 := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case create2Collision =>
      have hBad : s.decodedOp = some .CREATE2 := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case create2 =>
      have hBad : s.decodedOp = some .CREATE2 := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case selfDestructStatic =>
      have hBad : s.decodedOp = some .SELFDESTRUCT := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case selfDestruct =>
      have hBad : s.decodedOp = some .SELFDESTRUCT := by assumption
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case log =>
      obtain ⟨n, hBad⟩ :
          ∃ n : Fin 5, s.decodedOp = some (.Log ⟨n⟩) := by
        exact ⟨_, by assumption⟩
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case dupN =>
      obtain ⟨n, hBad⟩ :
          ∃ n : Fin 256, s.decodedOp = some (.DupN ⟨n⟩) := by
        exact ⟨_, by assumption⟩
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case swapN =>
      obtain ⟨n, hBad⟩ :
          ∃ n : Fin 256, s.decodedOp = some (.SwapN ⟨n⟩) := by
        exact ⟨_, by assumption⟩
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case exchange =>
      obtain ⟨b, hBad⟩ :
          ∃ b : Fin 256, s.decodedOp = some (.Exchange ⟨b⟩) := by
        exact ⟨_, by assumption⟩
      exact (unsafe_decodedOp hsDecoded hsafe hBad rfl).elim
  case stop =>
      simp at htRunning
  case return_ =>
      simp at htRunning
  case decodeFailure =>
      simp at htRunning
  case invalidOpcode =>
      simp at htRunning
  case outOfGas =>
      simp at htRunning
  case initCodeSizeOog =>
      simp at htRunning
  case stackUnderflow =>
      simp at htRunning
  case stackOverflow =>
      simp at htRunning
  case staticModeViolation =>
      simp at htRunning
  case jumpBadDest =>
      simp at htRunning
  case jumpiBadDest =>
      simp at htRunning
  case returndatacopyOob =>
      simp at htRunning

/-- A real EVM step from a live certified top-level state is either terminal,
or is a same-frame running transition whose natural PC is a certified static
successor. Same-frame preservation is a conclusion, not a premise. -/
theorem step_outcome
    {code : ByteArray} (cert : Certificate code)
    (hsize : code.size < 2 ^ 256)
    {s t : State}
    (hstep : Step s t)
    (hsRunning : s.halt = .Running)
    (hsEmpty : s.callStack = [])
    (hcode : s.executionEnv.code = code)
    (hfork : s.fork = .Osaka)
    (hpc : s.pc.toNat ∈ cert.pcs) :
    TerminalTop t ∨
      (t.halt = .Running ∧
        t.callStack = [] ∧
        t.executionEnv = s.executionEnv ∧
        StaticSuccessor code s.pc.toNat t.pc.toNat) := by
  cases hstep with
  | running _ _ hrun =>
      by_cases htRunning : t.halt = .Running
      · right
        refine ⟨htRunning, ?_⟩
        exact stepRunning_running_outcome cert hsize hrun htRunning
          hsEmpty hcode hfork hpc
      · left
        obtain ⟨op, imm, hraw, hsafe⟩ := cert.decodedSafe hpc
        have hsDecoded :=
          state_decoded_of_raw_osaka hcode hfork hraw hsafe
        exact ⟨htRunning,
          stepRunning_terminal_callStack_empty hrun hsRunning hsEmpty
            htRunning hsDecoded hsafe⟩
  | precompileSuccess =>
      left
      exact ⟨by simp, hsEmpty⟩
  | precompileOog =>
      left
      exact ⟨by simp, hsEmpty⟩
  | returning hreturn =>
      cases hreturn <;> simp_all

/-- Closure of the endpoint invariant under one actual EVM step. -/
theorem inDomain_step
    {code : ByteArray} (cert : Certificate code)
    (hsize : code.size < 2 ^ 256)
    {env : ExecutionEnv}
    (henvCode : env.code = code)
    (henvFork : env.fork = .Osaka)
    {s t : State}
    (hinv : InDomain cert env s)
    (hstep : Step s t) :
    InDomain cert env t := by
  rcases hinv with hterminal | hrunning
  · exact False.elim (Step.not_from_done hstep hterminal.1 hterminal.2)
  · rcases hrunning with ⟨hsRunning, hsEmpty, hsEnv, hpc⟩
    have hcode : s.executionEnv.code = code := by
      rw [hsEnv]
      exact henvCode
    have hfork : s.fork = .Osaka := by
      change s.executionEnv.fork = .Osaka
      rw [hsEnv]
      exact henvFork
    rcases step_outcome cert hsize hstep hsRunning hsEmpty hcode hfork hpc with
      hterminal | ⟨htRunning, htEmpty, htEnv, hsucc⟩
    · exact Or.inl hterminal
    · refine Or.inr ⟨htRunning, htEmpty, ?_,
        Certificate.successor_mem cert hpc hsucc⟩
      exact htEnv.trans hsEnv

/-- Closure along any finite actual execution. -/
theorem inDomain_steps
    {code : ByteArray} (cert : Certificate code)
    (hsize : code.size < 2 ^ 256)
    {env : ExecutionEnv}
    (henvCode : env.code = code)
    (henvFork : env.fork = .Osaka)
    {s t : State}
    (hinv : InDomain cert env s)
    (hsteps : Steps s t) :
    InDomain cert env t := by
  revert hinv
  induction hsteps with
  | refl =>
      intro hinv
      exact hinv
  | trans hstep htail ih =>
      intro hinv
      apply ih
      exact inDomain_step cert hsize henvCode henvFork hinv hstep

/-- Every live endpoint in the propagated domain has a genuinely available
Osaka decode in the supported opcode subset. -/
theorem decoded_of_runningInDomain
    {code : ByteArray} (cert : Certificate code)
    {env : ExecutionEnv}
    (henvCode : env.code = code)
    (henvFork : env.fork = .Osaka)
    {s : State}
    (hrunning : RunningInDomain cert env s) :
    ∃ op imm,
      s.decoded = some (op, imm) ∧ transportSafe op = true := by
  rcases hrunning with ⟨_, _, hsEnv, hpc⟩
  obtain ⟨op, imm, hraw, hsafe⟩ := cert.decodedSafe hpc
  have hcode : s.executionEnv.code = code := by
    rw [hsEnv]
    exact henvCode
  have hfork : s.fork = .Osaka := by
    change s.executionEnv.fork = .Osaka
    rw [hsEnv]
    exact henvFork
  exact ⟨op, imm, state_decoded_of_raw_osaka hcode hfork hraw hsafe, hsafe⟩

end Challenge.Modexp.Submission.LocalPatch.StaticExecution
