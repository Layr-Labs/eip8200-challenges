import EvmSemantics.EVM.Decode

set_option warningAsError true

/-!
# Static decoder/control-flow domain

This module is independent of any concrete submission.  A `ScanPath` is an
explicit finite certificate for the exact boundary walk used by
`Decode.isValidJumpDest`: advance by one opcode byte plus PUSH payload width.

`StaticSuccessor` is a decoder-level overapproximation.  Dynamic JUMP and taken
JUMPI may choose any globally valid target; ordinary instructions use the
pinned decoder's real PC width, including two-byte EIP-8024 operations.
No gas or machine-state relation appears here.
-/

namespace Challenge.Modexp.Submission.LocalPatch.StaticDomain

open EvmSemantics
open EvmSemantics.EVM

inductive FlowKind where
  | halt | jump | jumpi | next
  deriving DecidableEq

def flowKind : Operation → FlowKind
  | .STOP | .RETURN | .REVERT | .INVALID | .SELFDESTRUCT => .halt
  | .JUMP => .jump
  | .JUMPI => .jumpi
  | _ => .next

/-- Exact instruction width used by successful same-frame execution. -/
def execWidth : Operation → Nat
  | .Push p => 1 + p.width.val
  | .DupN _ | .SwapN _ | .Exchange _ => 2
  | _ => 1

def execNext (code : ByteArray) (pc : Nat) : Nat :=
  match Decode.decodeAt code pc with
  | some (op, _) => pc + execWidth op
  | none => pc + 1

/-- Boundary successor used by the pinned JUMPDEST scanner.  EIP-8024
immediates are deliberately *not* skipped here. -/
def scanNext (code : ByteArray) (pc : Nat) : Nat :=
  pc + 1 + Decode.pushDataSize code pc

/-- Exact finite boundary walk from `start` through `pcs`, stopping at `stop`. -/
def ScanPath (code : ByteArray) : Nat → List Nat → Nat → Prop
  | start, [], stop => start = stop
  | start, pc :: pcs, stop =>
      start = pc ∧ pc < code.size ∧
        ScanPath code (scanNext code pc) pcs stop

namespace ScanPath

theorem append {code : ByteArray} {start middle stop : Nat}
    {left right : List Nat}
    (hleft : ScanPath code start left middle)
    (hright : ScanPath code middle right stop) :
    ScanPath code start (left ++ right) stop := by
  induction left generalizing start with
  | nil =>
      simp only [ScanPath] at hleft
      subst middle
      simpa using hright
  | cons pc left ih =>
      simp only [ScanPath] at hleft ⊢
      rcases hleft with ⟨hstart, hlt, htail⟩
      exact ⟨hstart, hlt, ih htail⟩

/-- The next scanner boundary is present unless it is the terminal `stop`. -/
theorem next_mem {code : ByteArray} {start stop pc : Nat}
    {pcs : List Nat} (hpath : ScanPath code start pcs stop)
    (hpc : pc ∈ pcs) (hnext : scanNext code pc < stop) :
    scanNext code pc ∈ pcs := by
  induction pcs generalizing start with
  | nil => simp at hpc
  | cons head tail ih =>
      simp only [ScanPath] at hpath
      rcases hpath with ⟨hstart, hhead, htail⟩
      subst start
      simp only [List.mem_cons] at hpc ⊢
      rcases hpc with rfl | hpc
      · cases tail with
        | nil =>
            simp only [ScanPath] at htail
            exfalso
            omega
        | cons next rest =>
            simp only [ScanPath] at htail
            exact Or.inr (by
              simp only [List.mem_cons]
              exact Or.inl htail.1)
      · exact Or.inr (ih htail hpc)

private theorem validFrom_mem {code : ByteArray} {target : Nat} :
    ∀ {start stop fuel : Nat} {pcs : List Nat},
      ScanPath code start pcs stop → code.size ≤ stop →
      Decode.validJumpDestFrom code target start fuel = true →
      target ∈ pcs := by
  intro start stop fuel pcs hpath hstop hvalid
  induction pcs generalizing start fuel with
  | nil =>
      simp only [ScanPath] at hpath
      subst start
      cases fuel with
      | zero => simp [Decode.validJumpDestFrom] at hvalid
      | succ fuel =>
          by_cases heq : stop = target
          · subst target
            have hnot : ¬stop < code.size := by omega
            simp [Decode.validJumpDestFrom, hnot] at hvalid
          · have hge : stop ≥ code.size := hstop
            simp [Decode.validJumpDestFrom, heq, hge] at hvalid
  | cons pc pcs ih =>
      simp only [ScanPath] at hpath
      rcases hpath with ⟨hstart, hpclt, htail⟩
      subst start
      cases fuel with
      | zero => simp [Decode.validJumpDestFrom] at hvalid
      | succ fuel =>
          by_cases heq : pc = target
          · subst target
            simp
          · rw [Decode.validJumpDestFrom, if_neg heq] at hvalid
            by_cases hstopHere : pc > target ∨ pc ≥ code.size
            · simp [hstopHere] at hvalid
            · rw [if_neg hstopHere] at hvalid
              exact List.mem_cons_of_mem _
                (ih htail (by simpa [scanNext] using hvalid))

/-- Every globally valid JUMP/JUMPI target occurs in a complete scan path. -/
theorem validJumpDest_mem {code : ByteArray} {pcs : List Nat} {target : Nat}
    (hpath : ScanPath code 0 pcs code.size)
    (hvalid : Decode.isValidJumpDest code target = true) :
    target ∈ pcs := by
  unfold Decode.isValidJumpDest at hvalid
  exact validFrom_mem hpath (Nat.le_refl _) hvalid

end ScanPath

/-- Deliberately narrow operation domain for the fd95 transport proof.
It excludes every code/account observer, GAS, calls/creates, storage/transient
storage, logs, block/environment observers, and EIP-8024 operation. -/
def transportSafe : Operation → Bool
  | .StopArith _ => true
  | .CompBit _ => true
  | .Env op =>
      match op with
      | .CALLDATALOAD | .CALLDATASIZE | .CALLDATACOPY => true
      | _ => false
  | .StackMemFlow op =>
      match op with
      | .POP | .MLOAD | .MSTORE | .MSTORE8
      | .JUMP | .JUMPI | .JUMPDEST | .MSIZE | .MCOPY => true
      | _ => false
  | .Push _ | .Dup _ | .Swap _ => true
  | .System op =>
      match op with
      | .RETURN => true
      | _ => false
  | _ => false

/-- A local site is safe when it decodes to the narrow domain and every
fallthrough agrees with both the execution width and scanner boundary width. -/
def siteCheck (code : ByteArray) (pc : Nat) : Bool :=
  match Decode.decodeAt code pc with
  | none => false
  | some (op, _) =>
      transportSafe op &&
        match flowKind op with
        | .halt | .jump => true
        | .jumpi | .next =>
            (execNext code pc == scanNext code pc) &&
              decide (execNext code pc < code.size)

def sitesCheck (code : ByteArray) (pcs : List Nat) : Bool :=
  pcs.all (siteCheck code)

theorem site_of_sitesCheck {code : ByteArray} {pcs : List Nat} {pc : Nat}
    (hall : sitesCheck code pcs = true) (hpc : pc ∈ pcs) :
    siteCheck code pc = true :=
  (List.all_eq_true.mp hall) pc hpc

theorem decode_safe_of_site {code : ByteArray} {pc : Nat}
    (hsite : siteCheck code pc = true) :
    ∃ op imm, Decode.decodeAt code pc = some (op, imm) ∧
      transportSafe op = true := by
  cases hdecode : Decode.decodeAt code pc with
  | none => simp [siteCheck, hdecode] at hsite
  | some decoded =>
      rcases decoded with ⟨op, imm⟩
      rw [siteCheck, hdecode] at hsite
      simp only [Bool.and_eq_true] at hsite
      exact ⟨op, imm, rfl, hsite.1⟩

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

/-- Decoder-level overapproximation of the next PC for successful normal
execution.  It is intentionally separate from gas/state transport. -/
def StaticSuccessor (code : ByteArray) (pc next : Nat) : Prop :=
  match Decode.decodeAt code pc with
  | none => False
  | some (op, _) =>
      match flowKind op with
      | .halt => False
      | .jump => Decode.isValidJumpDest code next = true
      | .jumpi => next = execNext code pc ∨
          Decode.isValidJumpDest code next = true
      | .next => next = execNext code pc

/-- Finite static-domain certificate.  The fields are local byte/decode facts,
not an execution-equivalence assumption. -/
structure Certificate (code : ByteArray) where
  pcs : List Nat
  path : ScanPath code 0 pcs code.size
  entry : 0 ∈ pcs
  safe : ∀ {pc}, pc ∈ pcs → siteCheck code pc = true

namespace Certificate

theorem decodedSafe {code : ByteArray} (cert : Certificate code)
    {pc : Nat} (hpc : pc ∈ cert.pcs) :
    ∃ op imm, Decode.decodeAt code pc = some (op, imm) ∧
      transportSafe op = true :=
  decode_safe_of_site (cert.safe hpc)

/-- Static decoder/JUMP closure. -/
theorem successor_mem {code : ByteArray} (cert : Certificate code)
    {pc next : Nat} (hpc : pc ∈ cert.pcs)
    (hsucc : StaticSuccessor code pc next) :
    next ∈ cert.pcs := by
  obtain ⟨op, imm, hdecode, hsafe⟩ := cert.decodedSafe hpc
  rw [StaticSuccessor, hdecode] at hsucc
  cases hflow : flowKind op with
  | halt => simp [hflow] at hsucc
  | jump =>
      have hjump : Decode.isValidJumpDest code next = true := by
        simpa only [hflow] using hsucc
      exact ScanPath.validJumpDest_mem cert.path hjump
  | jumpi =>
      have hsucc' : next = execNext code pc ∨
          Decode.isValidJumpDest code next = true := by
        simpa only [hflow] using hsucc
      rcases hsucc' with hnext | hjump
      · subst next
        obtain ⟨heq, hlt⟩ := next_facts_of_site hdecode
          (Or.inr hflow) (cert.safe hpc)
        have hscan : scanNext code pc < code.size := by
          simpa only [← heq] using hlt
        rw [heq]
        exact ScanPath.next_mem cert.path hpc hscan
      · exact ScanPath.validJumpDest_mem cert.path hjump
  | next =>
      have hnext : next = execNext code pc := by
        simpa only [hflow] using hsucc
      subst next
      obtain ⟨heq, hlt⟩ := next_facts_of_site hdecode
        (Or.inl hflow) (cert.safe hpc)
      have hscan : scanNext code pc < code.size := by
        simpa only [← heq] using hlt
      rw [heq]
      exact ScanPath.next_mem cert.path hpc hscan

inductive Reachable (code : ByteArray) : Nat → Prop
  | entry : Reachable code 0
  | step {pc next} : Reachable code pc →
      StaticSuccessor code pc next → Reachable code next

/-- Every decoder-level PC reachable from zero lies in the certified domain. -/
theorem reachable_mem {code : ByteArray} (cert : Certificate code)
    {pc : Nat} (hreach : Reachable code pc) : pc ∈ cert.pcs := by
  induction hreach with
  | entry => exact cert.entry
  | step _ hsucc ih => exact cert.successor_mem ih hsucc

end Certificate

end Challenge.Modexp.Submission.LocalPatch.StaticDomain
