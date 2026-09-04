import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSwapLemmas
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScratchLow
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduleActiveWords

set_option warningAsError true
set_option maxRecDepth 30000

/-!
# Q4M quad-round common states and the machine-shaped round model

`qRound` mirrors the exact `UInt256` expressions produced by the stepper on the
generated quad templates (operand order included).  The semantic bridge to
`ScratchLow.rawRound` lives in `QuadRoundModel`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
export Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSwapLemmas
  (exchange_swap1 exchange_swap2 exchange_swap3 exchange_swap4 exchange_swap5
   exchange_swap6 exchange_swap7 exchange_swap8 exchange_swap9 exchange_swap10
   exchange_swap11 exchange_swap12)

/-- Boolean form exactly as the stepper evaluates the generated DUP sequences; these are
definitionally `StackRound.stackF j` for `j ∈ {0, 1, 3}` and its unmasked body for `j ∈ {2, 4}`. -/
def qf (j : Nat) (b c d : UInt256) : UInt256 :=
  match j with
  | 0 => UInt256.xor (UInt256.xor b c) d
  | 1 => UInt256.xor (UInt256.land (UInt256.xor c d) b) d
  | 2 => UInt256.xor (UInt256.lor b (UInt256.lnot c)) d
  | 3 => UInt256.xor (UInt256.land (UInt256.xor b c) d) c
  | _ => UInt256.xor b (UInt256.lor c (UInt256.lnot d))

/-- The unmasked sum in stepper operand order; form 0 has no constant add. -/
def qSum (j : Nat) (f a word constant : UInt256) : UInt256 :=
  match j with
  | 0 => a + (f + word)
  | _ => constant + (a + (f + word))

/-- One quad-helper round: `M` is the rotation multiplier `(2^32 + 1) <<< r`. -/
def qRound (x : EvmWorking) (j : Nat) (word M constant : UInt256) : EvmWorking :=
  { a := x.e
    b := UInt256.land mask
      (x.e + UInt256.shiftRight
        (UInt256.land mask (qSum j (qf j x.b x.c x.d) x.a word constant) * M)
        (UInt256.ofNat 32))
    c := x.b
    d := UInt256.shiftRight (foldM * x.c) (UInt256.ofNat 22)
    e := x.d }

/-- Four rounds reading `p0`, `p1`, `p2`, `p3` in order. -/
def quadWorking (s : State) (x : EvmWorking) (j : Nat)
    (p0 p1 p2 p3 M0 M1 M2 M3 constant : UInt256) : EvmWorking :=
  qRound
    (qRound
      (qRound
        (qRound x j (MachineState.readWord s.memory p0.toNat) M0 constant)
        j (MachineState.readWord s.memory p1.toNat) M1 constant)
      j (MachineState.readWord s.memory p2.toNat) M2 constant)
    j (MachineState.readWord s.memory p3.toNat) M3 constant

/-- Wrapper pushes, bottom to top: `M3 p3 M2 p2 M1 p1 M0 ret p0 helper`. -/
def quadCallPushes (returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 : UInt256)
    (w0 w1 w2 w3 : Fin 33) : List Instr :=
  [.push w3 M3, push2 p3, .push w2 M2, push2 p2, .push w1 M1, push2 p1,
    .push w0 M0, push2 returnPC, push2 p0, push2 helperPC]

def quadCallPushed (s : State) (pc returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 : UInt256)
    (working : EvmWorking) (rest : List UInt256) : State :=
  { s with
    pc := pc
    stack := [helperPC, p0, returnPC, M0, p1, M1, p2, M2, p3, M3] ++
      roundWords working ++ rest }

def quadHelperEntry (s : State) (startPC p0 p1 p2 p3 returnPC M0 M1 M2 M3 : UInt256)
    (working : EvmWorking) (rest : List UInt256) : State :=
  { s with
    pc := startPC
    stack := [p0, returnPC, M0, p1, M1, p2, M2, p3, M3] ++ roundWords working ++ rest }

def quadAfterHelperBeforeJump (s : State) (endPC returnPC : UInt256)
    (working : EvmWorking) (rest : List UInt256) : State :=
  { s with
    pc := endPC
    stack := returnPC :: roundWords working ++ rest }

theorem runInstrSeq_singleton (i : Instr) (s next : State)
    (hstep : Stepper.runInstr i s = some next) :
    runInstrSeq [i] s = some next := by
  rw [runInstrSeq, hstep]

theorem runInstrSeq_cons_cons (i r : Instr) (rs : List Instr) (s next : State)
    (hstep : Stepper.runInstr i s = some next) (hrun : next.halt = .Running) :
    runInstrSeq (i :: r :: rs) s = runInstrSeq (r :: rs) next := by
  rw [runInstrSeq, hstep]
  simp only [hrun]

theorem runInstrSeq_append {xs ys : List Instr} {s t u : State}
    (hxs : runInstrSeq xs s = some t) (hys : runInstrSeq ys t = some u)
    (hrun : t.halt = .Running) :
    runInstrSeq (xs ++ ys) s = some u := by
  induction xs generalizing s with
  | nil =>
      have hst : s = t := by
        simpa [runInstrSeq] using hxs
      subst hst
      simpa using hys
  | cons instruction tail ih =>
      cases hstep : Stepper.runInstr instruction s with
      | none =>
          cases tail with
          | nil =>
              rw [runInstrSeq, hstep] at hxs
              simp at hxs
          | cons i2 tail' =>
              rw [runInstrSeq, hstep] at hxs
              simp at hxs
      | some next =>
          cases tail with
          | nil =>
              have hnext : next = t := by
                rw [runInstrSeq_singleton instruction s next hstep] at hxs
                exact Option.some.inj hxs
              subst hnext
              cases ys with
              | nil =>
                  have hnu : next = u := by
                    simpa [runInstrSeq] using hys
                  subst hnu
                  simpa using runInstrSeq_singleton instruction s next hstep
              | cons y ys' =>
                  rw [List.singleton_append,
                    runInstrSeq_cons_cons instruction y ys' s next hstep hrun]
                  exact hys
          | cons i2 tail' =>
              have hhalt : next.halt = .Running := by
                cases h : next.halt with
                | Running => rfl
                | Success =>
                    rw [runInstrSeq, hstep] at hxs
                    simp [h] at hxs
                | Returned =>
                    rw [runInstrSeq, hstep] at hxs
                    simp [h] at hxs
                | Reverted =>
                    rw [runInstrSeq, hstep] at hxs
                    simp [h] at hxs
                | Exception e =>
                    rw [runInstrSeq, hstep] at hxs
                    simp [h] at hxs
              have hrest : runInstrSeq (i2 :: tail') next = some t := by
                rw [runInstrSeq_cons_cons instruction i2 tail' s next hstep hhalt] at hxs
                exact hxs
              rw [List.cons_append]
              exact (runInstrSeq_cons_cons instruction i2 (tail' ++ ys) s next hstep
                hhalt).trans (ih hrest)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
