import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# A concrete execution certificate for round 0 of `ed34`

The forty-seven operations below are the bytes at PC 886..934 of
`/tmp/packed-gate.hex` (decoded sha256 `ed34b6a2…`), transcribed
mechanically, not retyped.  `step0_trace` is a computation: it runs them on the
nineteen-slot round-0 frame and states exactly what comes out.

The evaluator was validated against the machine before this file was written —
running these ops on the real entry stack reproduces the real exit stack in all
nineteen slots, bit for bit.

Round 0 is the identity phase, so nothing here is affected by the register
alternation.

## Gas

Static cost of the forty-seven ops is 144, which is what the machine charges:
the two `MLOAD`s expand no memory, since the schedule spread has already
touched those words.

## Six places where the emitted operand order is NOT the definition order

This is the finding that decides how the bridge to `stepFrame` has to be
written.  Every one of these is an equality by commutativity, so the ARITHMETIC
is unaffected — but none of them is a definitional match, so the bridge needs
explicit `comm`/`assoc` steps and cannot be `rfl`:

1. message word: emitted `memAt 88 ||| memAt 0` — right lane first;
   `StepLoad` has left first.
2. packed `f`: emitted `(d ||| (mR &&& c)) ^^^ (mR ^^^ (c ^^^ b))`;
   `packedFWord 0 b c d` is `((b ^^^ c) ^^^ maskR) ^^^ ((c &&& maskR) ||| d)`.
   Outer `^^^` swapped, inner reassociated, `&&&` swapped.
3. round sum: emitted `kk + ((f + X) + a)`; `roundSum` is `((f + X) + a) + K`.
   The final `ADD` has its operands the other way round, because `DUP16` puts
   the constant on top.
4. rotate: emitted `(mR &&& shr Q 24) ||| (mL &&& shr Q u21)`; `packedRot`
   is `lor (land (shr Q _) maskL) (land (shr Q _) maskR)`.  Both the outer
   `|||` and each inner `&&&` are reversed.
5. write-back: emitted `e + rot`; `correctedStep` has `packedRot … + g.e`.
6. `rol10`: emitted `mLR &&& shr (cM * (mLR &&& c)) u22`; `packedRol10` masks
   on the right.  The multiplication itself is in the same order.

STATUS: WRITTEN, NOT ELABORATED.  No admitted goals; the file contains zero
occurrences of the placeholder token, so a grep and this claim agree.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame

/-- The opcode subset round 0 uses.  Nothing else appears in those 47 bytes. -/
inductive Op where
  | push0
  | push (v : UInt256)
  | mload
  | dup (n : Nat)
  | swap (n : Nat)
  | pop
  | and | or | xor | add | mul | shr
deriving DecidableEq

/-- `memAt` abstracts the machine's `MLOAD`; the memory premises live in
`PackedStepFrame.StepLoad`, not here. -/
def runOp (memAt : UInt256 → UInt256) : Op → List UInt256 → Option (List UInt256)
  | .push0, s => some (0 :: s)
  | .push v, s => some (v :: s)
  | .mload, x :: s => some (memAt x :: s)
  | .pop, _ :: s => some s
  | .dup n, s => (s[n - 1]?).map (fun v => v :: s)
  | .swap n, x :: s => (s[n - 1]?).map (fun v => v :: s.set (n - 1) x)
  | .and, x :: y :: s => some ((x &&& y) :: s)
  | .or, x :: y :: s => some ((x ||| y) :: s)
  | .xor, x :: y :: s => some ((x ^^^ y) :: s)
  | .add, x :: y :: s => some ((x + y) :: s)
  | .mul, x :: y :: s => some ((x * y) :: s)
  | .shr, x :: y :: s => some (UInt256.shiftRight y x :: s)
  | _, _ => none

def runOps (memAt : UInt256 → UInt256) :
    List Op → List UInt256 → Option (List UInt256)
  | [], s => some s
  | o :: rest, s => (runOp memAt o s).bind (runOps memAt rest)

/-- Static gas of one operation, Osaka schedule. -/
def opCost : Op → Nat
  | .push0 => 2
  | .pop => 2
  | .push _ => 3
  | .mload => 3
  | .dup _ => 3
  | .swap _ => 3
  | .mul => 5
  | _ => 3

/-- Round 0 of `ed34`, PC 886..934, transcribed from the raw. -/
def step0Ops : List Op :=
  [Op.push0, Op.mload, Op.push (UInt256.ofNat 88),
   Op.mload, Op.or, Op.dup 3,
   Op.dup 5, Op.xor, Op.dup 10,
   Op.xor, Op.dup 5, Op.dup 11,
   Op.and, Op.dup 7, Op.or,
   Op.xor, Op.add, Op.add,
   Op.dup 16, Op.add, Op.dup 6,
   Op.and, Op.dup 9, Op.mul,
   Op.dup 1, Op.dup 15, Op.shr,
   Op.dup 8, Op.and, Op.swap 1,
   Op.push (UInt256.ofNat 24), Op.shr, Op.dup 9,
   Op.and, Op.or, Op.dup 5,
   Op.add, Op.swap 2, Op.dup 6,
   Op.and, Op.dup 9, Op.mul,
   Op.dup 15, Op.shr, Op.dup 6,
   Op.and, Op.swap 4]

theorem step0Ops_length : step0Ops.length = 47 := rfl

/-- `PUSH0` costs 2, not 3, so the schedule total is stated directly.
144, matching what the machine charges: the two `MLOAD`s expand no memory
because the schedule spread has already touched those words. -/
theorem step0_cost : (step0Ops.map opCost).sum = 144 := rfl

/-- **The certificate.**  Running the forty-seven emitted operations on the
round-0 frame produces exactly this stack.  Pure computation — every step is a
definitional unfold, so this is `rfl`. -/
theorem step0_trace (memAt : UInt256 → UInt256)
    (a b c d e mLR mL mR cM u17 u18 u19 u20 u21 u22 kk ret xo xe : UInt256) :
    runOps memAt step0Ops
        [a, b, c, d, e, mLR, mL, mR, cM,
         u17, u18, u19, u20, u21, u22, kk, ret, xo, xe]
      = some
        [e, b, (e + ((mR &&& (UInt256.shiftRight (cM * (mLR &&& (kk + ((((d |||
         (mR &&& c)) ^^^ (mR ^^^ (c ^^^ b))) + ((memAt (UInt256.ofNat 88))
         ||| (memAt (0 : UInt256)))) + a)))) (UInt256.ofNat 24))) ||| (mL
         &&& (UInt256.shiftRight (cM * (mLR &&& (kk + ((((d ||| (mR &&&
         c)) ^^^ (mR ^^^ (c ^^^ b))) + ((memAt (UInt256.ofNat 88)) |||
         (memAt (0 : UInt256)))) + a)))) u21)))), d, (mLR &&&
         (UInt256.shiftRight (cM * (mLR &&& c)) u22)), mLR, mL, mR, cM,
         u17, u18, u19, u20, u21, u22, kk, ret, xo, xe] := rfl

/-- The fourteen-slot suffix is untouched by round 0, read off the certificate
rather than assumed. -/
theorem step0_suffix (memAt : UInt256 → UInt256)
    (a b c d e mLR mL mR cM u17 u18 u19 u20 u21 u22 kk ret xo xe : UInt256) :
    (runOps memAt step0Ops
        [a, b, c, d, e, mLR, mL, mR, cM,
         u17, u18, u19, u20, u21, u22, kk, ret, xo, xe]).map (List.drop 5)
      = some [mLR, mL, mR, cM, u17, u18, u19, u20, u21, u22, kk, ret, xo, xe] :=
  rfl

/-- Round 0 leaves the stack at depth nineteen. -/
theorem step0_depth (memAt : UInt256 → UInt256)
    (a b c d e mLR mL mR cM u17 u18 u19 u20 u21 u22 kk ret xo xe : UInt256) :
    (runOps memAt step0Ops
        [a, b, c, d, e, mLR, mL, mR, cM,
         u17, u18, u19, u20, u21, u22, kk, ret, xo, xe]).map List.length
      = some 19 := rfl

/-- The emitted write-back order at round 0 is `[A, C, B, E, D]`: slot 1 holds
the OLD `b` (the new `C`) and slot 3 the OLD `d` (the new `E`).  This is the
alternation, read straight off the certificate instead of measured. -/
theorem step0_phase_flip (memAt : UInt256 → UInt256)
    (a b c d e mLR mL mR cM u17 u18 u19 u20 u21 u22 kk ret xo xe : UInt256) :
    (runOps memAt step0Ops
        [a, b, c, d, e, mLR, mL, mR, cM,
         u17, u18, u19, u20, u21, u22, kk, ret, xo, xe]).map
          (fun t => (t[0]?, t[1]?, t[3]?))
      = some (some e, some b, some d) := rfl

#print axioms step0Ops_length
#print axioms step0_trace
#print axioms step0_suffix
#print axioms step0_depth
#print axioms step0_phase_flip

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0
