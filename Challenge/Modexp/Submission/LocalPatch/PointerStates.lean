import Challenge.Modexp.Submission.LocalPatch.TransportMacro
import Challenge.EvmProof.Word

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.LocalPatch.PointerSub32
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Transport

def entryPC : Nat := 2539
def exitPC : Nat := 2545
def Interior (pc : Nat) : Prop := entryPC < pc ∧ pc < exitPC
instance (pc : Nat) : Decidable (Interior pc) := inferInstanceAs
  (Decidable (entryPC < pc ∧ pc < exitPC))
def Exterior (pc : Nat) : Prop := pc < entryPC ∨ exitPC ≤ pc
instance (pc : Nat) : Decidable (Exterior pc) := inferInstanceAs
  (Decidable (pc < entryPC ∨ exitPC ≤ pc))

def negative32 : UInt256 := UInt256.lnot (UInt256.ofNat 31)

theorem negative32_add (p : UInt256) :
    negative32 + p = p - UInt256.ofNat 32 := by
  have hn : (UInt256.lnot (UInt256.ofNat 31)).val =
      -(UInt256.ofNat 32).val := by decide
  apply Challenge.EvmProof.Word.word_ext
  change (((UInt256.lnot (UInt256.ofNat 31)).val + p.val).val) =
    ((p.val - (UInt256.ofNat 32).val).val)
  rw [hn, Fin.val_add, Fin.val_sub]
  have hneg : (-(UInt256.ofNat 32).val).val =
      UInt256.size - (UInt256.ofNat 32).val.val := by decide
  rw [hneg]

/-- Actual old endpoints. The source gas is not erased. -/
def pre (a : State) (p : UInt256) (tail : List UInt256) : Nat → State
  | 0 => a
  | 1 =>
      { a with
          pc := UInt256.ofNat 2540
          stack := p :: p :: tail
          gasAvailable := a.gasAvailable - 3 }
  | 2 =>
      { a with
          pc := UInt256.ofNat 2542
          stack := UInt256.ofNat 31 :: p :: p :: tail
          gasAvailable := a.gasAvailable - 6 }
  | 3 =>
      { a with
          pc := UInt256.ofNat 2543
          stack := negative32 :: p :: p :: tail
          gasAvailable := a.gasAvailable - 9 }
  | 4 =>
      { a with
          pc := UInt256.ofNat 2544
          stack := (negative32 + p) :: p :: tail
          gasAvailable := a.gasAvailable - 12 }
  | _ =>
      { a with
          pc := UInt256.ofNat 2545
          stack := p :: (negative32 + p) :: tail
          gasAvailable := a.gasAvailable - 15 }

/-- Prefix one proves only its own peak. Prefix two proves the full old peak.
No capacity fact is extracted from a sufficient trace. -/
def Capacity (j : Nat) (tail : List UInt256) : Prop :=
  if j = 1 then tail.length + 1 < 1024 else tail.length + 2 < 1024

@[simp] theorem pre_env (a : State) (p : UInt256) (tail : List UInt256) (j : Nat) :
    (pre a p tail j).executionEnv = a.executionEnv := by
  cases j with
  | zero => simp [pre]
  | succ j => cases j with
    | zero => simp [pre]
    | succ j => cases j with
      | zero => simp [pre]
      | succ j => cases j with
        | zero => simp [pre]
        | succ j => cases j <;> simp [pre]

@[simp] theorem pre_halt (a : State) (p : UInt256) (tail : List UInt256) (j : Nat) :
    (pre a p tail j).halt = a.halt := by
  cases j with
  | zero => simp [pre]
  | succ j => cases j with
    | zero => simp [pre]
    | succ j => cases j with
      | zero => simp [pre]
      | succ j => cases j with
        | zero => simp [pre]
        | succ j => cases j <;> simp [pre]

/-- Only fixed code facts; neither record assumes a transition. -/
structure OldCode (code : ByteArray) : Prop where
  d0 : Decode.decodeAt code 2539 = some (.Dup ⟨0, by decide⟩, none)
  d1 : Decode.decodeAt code 2540 = some (.Push ⟨1, by decide⟩,
    some (UInt256.ofNat 31, 1))
  d2 : Decode.decodeAt code 2542 = some (.NOT, none)
  d3 : Decode.decodeAt code 2543 = some (.ADD, none)
  d4 : Decode.decodeAt code 2544 = some (.Swap ⟨0, by decide⟩, none)

structure NewCode (code : ByteArray) : Prop where
  d0 : Decode.decodeAt code 2539 = some (.Push ⟨2, by decide⟩,
    some (UInt256.ofNat 32, 2))
  d1 : Decode.decodeAt code 2542 = some (.Dup ⟨1, by decide⟩, none)
  d2 : Decode.decodeAt code 2543 = some (.SUB, none)
  d3 : Decode.decodeAt code 2544 = some (.Swap ⟨0, by decide⟩, none)

theorem decoded_at {code : ByteArray} {s : State} {pc : Nat}
    {op : Operation} {imm : Option (UInt256 × Nat)}
    (hc : s.executionEnv.code = code) (hf : s.fork = .Osaka)
    (hp : s.pc.toNat = pc) (hd : Decode.decodeAt code pc = some (op, imm))
    (ha : op.availableInFork .Osaka = true) : s.decoded = some (op, imm) := by
  simp [State.decoded, hc, hp, hd, hf, ha]

theorem decodedOp_at {code : ByteArray} {s : State} {pc : Nat}
    {op : Operation} {imm : Option (UInt256 × Nat)}
    (hc : s.executionEnv.code = code) (hf : s.fork = .Osaka)
    (hp : s.pc.toNat = pc) (hd : Decode.decodeAt code pc = some (op, imm))
    (ha : op.availableInFork .Osaka = true) : s.decodedOp = some op := by
  exact congrArg (fun d => d.map Prod.fst) (decoded_at hc hf hp hd ha)

end Challenge.Modexp.Submission.LocalPatch.PointerSub32
