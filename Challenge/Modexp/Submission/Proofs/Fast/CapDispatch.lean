import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFrames

set_option warningAsError true
set_option linter.unusedSimpArgs false

/-!
# Normalized ladder dispatch

The ladder entry is a computed jump `base + distance * [bit 7 of s32]`.  The old
artifact carried the distance as a multiplier on the masked bit itself
(`PUSH1 0x80 AND PUSH1 0x0e MUL PUSH2 base ADD`), which forces the distance to be a
multiple of 128.  Normalizing the mask with `ISZERO ISZERO` first turns the
selector into a plain 0/1, so any distance fits in a `PUSH2` literal.

Everything here is generic in the entry program counter, the base and the
distance; the concrete values of a relocated artifact are supplied at the call
site.  `selectBit` is deliberately *not* proved equal to `isFour` for widths
outside `{4, 8}`: `32 * n` has bit 7 set for `n = 4,5,6,7`, so a width-generic
bridge would be false.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CapDispatch

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.CiosCached

/-- The normalized four-limb selector: `1` when bit 7 of `x` is set, else `0`. -/
def selectBit (x : UInt256) : UInt256 :=
  UInt256.isZero (UInt256.isZero (UInt256.land (UInt256.ofNat 128) x))

@[simp] theorem selectBit_128 : selectBit (UInt256.ofNat 128) = UInt256.ofNat 1 := by decide

@[simp] theorem selectBit_256 : selectBit (UInt256.ofNat 256) = UInt256.ofNat 0 := by decide

/-- On the two admissible widths the normalized selector is the old `isFour`. -/
theorem selectBit_s32 (n : Nat) (hn : n = 4 ∨ n = 8) :
    selectBit (UInt256.ofNat (32 * n)) = isFour n := by
  rcases hn with rfl | rfl <;> decide

theorem mul_selectBit_128 (dist : UInt256) :
    dist * selectBit (UInt256.ofNat 128) = dist := by
  rw [selectBit_128]
  apply Challenge.EvmProof.Word.word_ext
  rw [Monpro.word_toNat_mul, show (UInt256.ofNat 1).toNat = 1 from by decide,
    Nat.mul_one, Nat.mod_eq_of_lt (Monpro.word_lt_size dist)]

theorem mul_selectBit_256 (dist : UInt256) :
    dist * selectBit (UInt256.ofNat 256) = UInt256.ofNat 0 := by
  rw [selectBit_256]
  apply Challenge.EvmProof.Word.word_ext
  rw [Monpro.word_toNat_mul, show (UInt256.ofNat 0).toNat = 0 from by decide,
    Nat.mul_zero, Nat.zero_mod]

/-- The computed target, for an arbitrary base and distance. -/
def target (base dist x : UInt256) : UInt256 := base + dist * selectBit x

theorem target_four (base dist : UInt256) :
    target base dist (UInt256.ofNat 128) = base + dist := by
  rw [target, mul_selectBit_128]

theorem word_add_zero (a : UInt256) : a + UInt256.ofNat 0 = a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_add,
    show (UInt256.ofNat 0).toNat = 0 from by decide,
    Nat.add_zero, Nat.mod_eq_of_lt (Monpro.word_lt_size a)]

theorem target_eight (base dist : UInt256) :
    target base dist (UInt256.ofNat 256) = base := by
  rw [target, mul_selectBit_256, word_add_zero]

/-- Jump validity of the computed target.  Both reachable destinations are
supplied as hypotheses; nothing else is admitted. -/
theorem target_isValidJumpDest (code : ByteArray) (base dist : UInt256) (n : Nat)
    (hn : n = 4 ∨ n = 8)
    (hfour : Decode.isValidJumpDest code (base + dist).toNat = true)
    (height : Decode.isValidJumpDest code base.toNat = true) :
    Decode.isValidJumpDest code (target base dist (UInt256.ofNat (32 * n))).toNat = true := by
  rcases hn with rfl | rfl
  · rw [show (32 * 4 : Nat) = 128 from rfl, target_four]
    exact hfour
  · rw [show (32 * 8 : Nat) = 256 from rfl, target_eight]
    exact height

/-! ## The two dispatch programs

`targetProgram` is the site that consumes the width word already on top of the
stack; `targetProgramDup` is the site that reaches it with a `DUP`.  Both are
thirteen and fourteen bytes respectively, and both are stated at an arbitrary
entry program counter.
-/

def targetProgram (dist base : UInt256) : List Instr :=
  [.push 1 128, .op .AND, .op .ISZERO, .op .ISZERO,
   .push 2 dist, .op .MUL, .push 2 base, .op .ADD]

def targetProgramDup (k : Operation.DupOp) (dist base : UInt256) : List Instr :=
  [.push 1 128, .op (.Dup k), .op .AND, .op .ISZERO, .op .ISZERO,
   .push 2 dist, .op .MUL, .push 2 base, .op .ADD]

theorem land_comm' (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_land, Nat.and_comm]

/-- The direct site: the width word is on top and is consumed. -/
theorem run_target (s : State) (pc : UInt256) (dist base x : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions (targetProgram dist base)
      { s with pc := pc, stack := x :: rest } =
    some { s with pc := advancePC 13 pc, stack := target base dist x :: rest } := by
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  have hp3 : UInt256.ofNat 3 = UInt256.ofNat 1 + (UInt256.ofNat 1 + UInt256.ofNat 1) := by decide
  simp [targetProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    target, selectBit, h1, h2, h3, land_comm', Nat.add_assoc,
    Challenge.EvmProof.Word.literal_eq_ofNat, advancePC, succ_eq_add, hp2, hp3,
    word_add_assoc]

/-- The `DUP11` site, on the fusion frame's sixteen-slot stack.  The width word
`tl` sits at depth nine, so `PUSH1 0x80 DUP11` lifts it. -/
theorem run_targetDup (s : State) (pc : UInt256) (dist base : UInt256)
    (a b c ent neg mask ent2 inv m0 tl m96 m64 m32 aprev dst : UInt256)
    (rest : List UInt256) (hcap : rest.length <= 1005) :
    runInstructions (targetProgramDup ⟨10, by decide⟩ dist base)
      { s with pc := pc, stack := [a,b,c,ent,neg,mask,ent2,inv,m0,tl,m96,m64,m32,aprev,dst] ++ rest } =
    some { s with pc := advancePC 14 pc, stack := target base dist tl :: [a,b,c,ent,neg,mask,ent2,inv,m0,tl,m96,m64,m32,aprev,dst] ++ rest } := by
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  have h17 : rest.length + 17 < 1024 := by omega
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  have hp3 : UInt256.ofNat 3 = UInt256.ofNat 1 + (UInt256.ofNat 1 + UInt256.ofNat 1) := by decide
  simp [targetProgramDup, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    target, selectBit, h15, h16, h17, land_comm', Nat.add_assoc, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, advancePC, succ_eq_add, hp2, hp3,
    word_add_assoc]

#print axioms run_target
#print axioms run_targetDup
#print axioms target_isValidJumpDest
#print axioms selectBit_s32

end Challenge.Modexp.Submission.Proofs.Fast.CapDispatch
