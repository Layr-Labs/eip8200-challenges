import Challenge.Modexp.Submission.Proofs.Fast.CsubModel
import Challenge.Modexp.Submission.Proofs.Fast.CsubAffineStep

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Theory A affine CSUB execution at the raw-instruction level

This module proves the exact state transition of the new one-pointer CSUB
body against the unchanged pure model `Csub.csStep`, without depending on
any whole-program artifact binding.

Ownership boundary (structural lane owns the rest): `Bytes.lean`,
`Proofs/Bytecode/Artifact.lean`, `Proofs/Fast/Defs.lean` (PC/jumpdest
tables) and `Proofs/Fast/Paths/*` (located blocks) are **not** touched here.
Once the structural lane delivers the new located blocks, the transition
lemmas below lift through `runLocatedBlock` by discharging, per
instruction, the program-counter side goals (parent's `fastPC` tables) and
reusing the same `simp` fact sets; the hard content — stack evolution,
memory writes, and the two-comparison borrow recurrence — is settled here.

Exact bytes under proof (new CSUB window `[2304, 2474)`, 190 bytes,
identical outside the window to the frozen baseline; raw-SHA256
`2b74ddba…`, see the native evidence record):

```text
entry [2304,2317): JUMPDEST; PUSH8 9440; MLOAD; PUSH0; SWAP1
loop  [2317,2451): JUMPDEST; DUP1; MLOAD
                   PUSH32 (W-8256); DUP3; ADD; MLOAD
                   DUP2; DUP2; GT; SWAP2; SUB
                   DUP4; DUP2; SUB; SWAP1; DUP5; GT
                   SWAP1; SWAP2; OR; SWAP3; POP
                   PUSH32 (W-1088); DUP3; ADD; MSTORE
                   PUSH32 (W-32); ADD
                   PUSH2 8224; DUP2; GT; PUSH2 2317; JUMPI
exit  2451:        POP
tail  [2452,2474): unchanged common return tail (structural lane)
```

Loop-state shape (both arrivals at pc 2317 — fall-through from entry with
borrow `0`, loopback with the propagated borrow — carry the same shape):

```text
[pt, borrow, dst, ret] ++ rest,  pt = 8224 + 32*n - 32*j
```

`CsubAffineStep.affineLoopState` is reused as the state predicate, so there
is exactly one definition of the affine state.  The borrow recurrence is
the retained two-comparison form `bout = [t<m] ∨ [d1<b]`; no wrapped
`(m+b)` shortcut is used anywhere below.

Proof shape: the load prefix is closed in two pieces (T-load, M-load) and
the remainder likewise (taken / not-taken guard), composed with
`runRaw_append`.  Each `simp` therefore covers at most one
memory-touching segment, with address normalization facts stated against
the simproc-normalized literal modulus.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CsubAffineRun

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Csub
open Challenge.Modexp.Submission.Proofs.Fast.CsubAffineStep

/-- Raw-instruction fold with exactly `runLocatedBlock`'s control shape
(single-instruction case included), minus the program-counter certificate
check that the structural lane supplies per index. -/
def runRaw : List Instr → State → Option State
  | [], s => some s
  | i :: rest, s =>
      match Challenge.EvmProof.Stepper.runInstr i s with
      | none => none
      | some next =>
          match rest with
          | [] => some next
          | _ :: _ =>
              match next.halt with
              | .Running => runRaw rest next
              | _ => none

/-- Composition for `runRaw`, mirroring `runLocatedBlock_append`: the only
proofs the structural lane needs for reassembling segments. -/
theorem runRaw_append (left right : List Instr) (s t u : State)
    (hleft : runRaw left s = some t)
    (hrunning : t.halt = .Running)
    (hright : runRaw right t = some u) :
    runRaw (left ++ right) s = some u := by
  induction left generalizing s with
  | nil =>
      simp [runRaw] at hleft
      subst t
      exact hright
  | cons i rest ih =>
      cases rest with
      | nil =>
          cases hnext : Challenge.EvmProof.Stepper.runInstr i s with
          | none => simp [runRaw, hnext] at hleft
          | some next =>
              simp [runRaw, hnext] at hleft
              subst next
              cases right with
              | nil => simpa [runRaw, hnext] using hright
              | cons j tail =>
                  simpa [runRaw, hnext, hrunning] using hright
      | cons j tail =>
          cases hnext : Challenge.EvmProof.Stepper.runInstr i s with
          | none => simp [runRaw, hnext] at hleft
          | some next =>
              cases hhalt : next.halt with
              | Running =>
                  have hrest : runRaw (j :: tail) next = some t := by
                    simpa [runRaw, hnext, hhalt] using hleft
                  have happ := ih next hrest
                  simpa [runRaw, hnext, hhalt] using happ
              | Success => simp [runRaw, hnext, hhalt] at hleft
              | Returned => simp [runRaw, hnext, hhalt] at hleft
              | Reverted => simp [runRaw, hnext, hhalt] at hleft
              | Exception error => simp [runRaw, hnext, hhalt] at hleft

/-- New CSUB entry `[2304, 2317)`: `JUMPDEST; PUSH8 9440; MLOAD; PUSH0;
SWAP1`.  Reads only word 9440 (never 9408). -/
def affineEntry : List Instr :=
  [Instr.op .JUMPDEST,
   Instr.push 8 9440,
   Instr.op .MLOAD,
   Instr.push 0 0,
   Instr.op (.Swap ⟨0, by decide⟩)]

/-- Load prefix, T half `[2317, 2320)`: `JUMPDEST; DUP1; MLOAD`. -/
def affineLoadT : List Instr :=
  [Instr.op .JUMPDEST,
   Instr.op (.Dup ⟨0, by decide⟩),
   Instr.op .MLOAD]

/-- Load prefix, M half `[2320, 2356)`: `PUSH32 (W-8256); DUP3; ADD;
MLOAD`. -/
def affineLoadM : List Instr :=
  [Instr.push 32
     115792089237316195423570985008687907853269984665640564039457584007913129631680,
   Instr.op (.Dup ⟨2, by decide⟩),
   Instr.op .ADD,
   Instr.op .MLOAD]

/-- Full 7-instruction load prefix `[2317, 2356)`, by concatenation. -/
def affineLoad : List Instr := affineLoadT ++ affineLoadM

/-- Remaining 27 loop-body instructions `[2356, 2451)`: borrow recurrence,
store, pointer advance, guard. -/
def affineRest : List Instr :=
  [Instr.op (.Dup ⟨1, by decide⟩),
   Instr.op (.Dup ⟨1, by decide⟩),
   Instr.op .GT,
   Instr.op (.Swap ⟨1, by decide⟩),
   Instr.op .SUB,
   Instr.op (.Dup ⟨3, by decide⟩),
   Instr.op (.Dup ⟨1, by decide⟩),
   Instr.op .SUB,
   Instr.op (.Swap ⟨0, by decide⟩),
   Instr.op (.Dup ⟨4, by decide⟩),
   Instr.op .GT,
   Instr.op (.Swap ⟨0, by decide⟩),
   Instr.op (.Swap ⟨1, by decide⟩),
   Instr.op .OR,
   Instr.op (.Swap ⟨2, by decide⟩),
   Instr.op .POP,
   Instr.push 32
     115792089237316195423570985008687907853269984665640564039457584007913129638848,
   Instr.op (.Dup ⟨2, by decide⟩),
   Instr.op .ADD,
   Instr.op .MSTORE,
   Instr.push 32
     115792089237316195423570985008687907853269984665640564039457584007913129639904,
   Instr.op .ADD,
   Instr.push 2 8224,
   Instr.op (.Dup ⟨1, by decide⟩),
   Instr.op .GT,
   Instr.push 2 2317,
   Instr.op .JUMPI]

/-- New CSUB loop body `[2317, 2451)`: 34 instructions ending in
`PUSH2 2317; JUMPI`. -/
def affineLoopBody : List Instr := affineLoad ++ affineRest

/-- Loop-exit trace: body plus the stale-pointer `POP` at 2451. -/
def affineLoopExit : List Instr :=
  affineLoopBody ++ [Instr.op .POP]

theorem affineEntry_length : affineEntry.length = 5 := by rfl

theorem affineLoadT_length : affineLoadT.length = 3 := by rfl

theorem affineLoadM_length : affineLoadM.length = 4 := by rfl

theorem affineLoad_length : affineLoad.length = 7 := by rfl

theorem affineRest_length : affineRest.length = 27 := by rfl

theorem affineLoopBody_length : affineLoopBody.length = 34 := by rfl

theorem affineLoopExit_length : affineLoopExit.length = 35 := by rfl

/-- Intermediate state at pc 2320 with stack `[t, pt, borrow, dst, ret]`. -/
def affineLoadedTState (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2320
           stack := [MachineState.readWord (csStep memory n j).memory
                       (8256 + 32 * (n - 1 - j)),
                     UInt256.ofNat (affinePt n j),
                     (csStep memory n j).flag, pdst, ret] ++ rest
           memory := (csStep memory n j).memory }

/-- Intermediate state at pc 2356 with stack `[m, t, pt, borrow, dst,
ret]`. -/
def affineLoadedState (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2356
           stack := [MachineState.readWord (csStep memory n j).memory
                       (32 * (n - 1 - j)),
                     MachineState.readWord (csStep memory n j).memory
                       (8256 + 32 * (n - 1 - j)),
                     UInt256.ofNat (affinePt n j),
                     (csStep memory n j).flag, pdst, ret] ++ rest
           memory := (csStep memory n j).memory }

/-- Post-guard exit state at pc 2451 with stack `[pt, borrow, dst, ret]`. -/
def affineGuardExitState (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2451
           stack := [UInt256.ofNat (affinePt n (j + 1)),
                     (csStep memory n (j + 1)).flag, pdst, ret] ++ rest
           memory := (csStep memory n (j + 1)).memory }

/-- Handoff state at pc 2452 with stack `[borrow, dst, ret]`: what the
unchanged common return tail consumes. -/
def affineTailPreState (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2452
           stack := [(csStep memory n j).flag, pdst, ret] ++ rest
           memory := (csStep memory n j).memory }

set_option linter.unusedSimpArgs false in
/-- Entry execution: `[pdst, ret]` at 2304 becomes the affine loop state
with `j = 0` (borrow `0`, `pt = 8224 + 32 * n`). -/
theorem run_affineEntry (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32)
    (htl : MachineState.readWord memory 9440 = UInt256.ofNat (8224 + 32 * n)) :
    runRaw affineEntry (csEntryState s memory pdst ret rest) =
      some (affineLoopState s memory n 0 pdst ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have h9440 : ((9440 : UInt256)).toNat = 9440 := by decide
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hpt0 : affinePt n 0 = 8224 + 32 * n := by unfold affinePt; omega
  have hactA : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9440 32) =
      s.activeWords := activeWords_fix s 9440 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [runRaw, affineEntry, Challenge.EvmProof.Stepper.runInstr,
      csEntryState, affineLoopState, affinePt, csStep,
      hc2, hc3, hc4, hrun, h9440, hzero, hpt0, htl, hactA,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
/-- T-load execution: `[pt, borrow, dst, ret]` at 2317 becomes
`[t, pt, borrow, dst, ret]` at 2320. -/
theorem run_affineLoadT (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j < n) (hn32 : n ≤ 32) :
    runRaw affineLoadT (affineLoopState s memory n j pdst ret rest) =
      some (affineLoadedTState s memory n j pdst ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have h256 : (2 ^ 256 : Nat) =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    decide
  have hta : affinePt n j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 1 - j) := by
    have hlt : affinePt n j <
        115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      rw [← h256]; exact affinePt_lt_word n j hn32 (by omega)
    rw [Nat.mod_eq_of_lt hlt, affinePt_eq_taddr n j hj]
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [runRaw, affineLoadT, Challenge.EvmProof.Stepper.runInstr,
      affineLoopState, affineLoadedTState,
      hc4, hc5, hrun, hta, hactT,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
/-- M-load execution: `[t, pt, borrow, dst, ret]` at 2320 becomes
`[m, t, pt, borrow, dst, ret]` at 2356. -/
theorem run_affineLoadM (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j < n) (hn32 : n ≤ 32) :
    runRaw affineLoadM (affineLoadedTState s memory n j pdst ret rest) =
      some (affineLoadedState s memory n j pdst ret rest) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hmodM : (affinePt n j + UInt256.toNat
      115792089237316195423570985008687907853269984665640564039457584007913129631680) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * (n - 1 - j) := by
    have hC : UInt256.toNat
        115792089237316195423570985008687907853269984665640564039457584007913129631680 =
        115792089237316195423570985008687907853269984665640564039457584007913129631680 := by
      decide
    have h1 := affinePt_eq_taddr n j hj
    have hR : 8256 +
        115792089237316195423570985008687907853269984665640564039457584007913129631680 =
        115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      decide
    rw [hC]; omega
  have hactM : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [runRaw, affineLoadM, Challenge.EvmProof.Stepper.runInstr,
      affineLoadedTState, affineLoadedState,
      hc5, hc6, hc7, hrun, hmodM, hactM,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

/-- Full load prefix by composition of the two halves. -/
theorem run_affineLoad (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j < n) (hn32 : n ≤ 32) :
    runRaw affineLoad (affineLoopState s memory n j pdst ret rest) =
      some (affineLoadedState s memory n j pdst ret rest) := by
  have h1 := run_affineLoadT s memory n j pdst ret rest hcap hrun hact hj hn32
  have h2 := run_affineLoadM s memory n j pdst ret rest hcap hrun hact hj hn32
  have hhalt : (affineLoadedTState s memory n j pdst ret rest).halt =
      .Running := hrun
  exact runRaw_append affineLoadT affineLoadM _ _ _ h1 hhalt h2

set_option linter.unusedSimpArgs false in
/-- Remainder execution, guard taken (`j + 1 < n`): `[m, t, pt, borrow,
dst, ret]` at 2356 becomes the next affine loop state at 2317, with memory
and borrow exactly `csStep (j + 1)`. -/
theorem run_affineRestBody (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j + 1 < n) (hn32 : n ≤ 32)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 2317 = true) :
    runRaw affineRest (affineLoadedState s memory n j pdst ret rest) =
      some (affineLoopState s memory n (j + 1) pdst ret rest) := by
  have hjn : j < n := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hmodD : (affinePt n j + UInt256.toNat
      115792089237316195423570985008687907853269984665640564039457584007913129638848) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      7168 + 32 * (n - 1 - j) := by
    have hC : UInt256.toNat
        115792089237316195423570985008687907853269984665640564039457584007913129638848 =
        115792089237316195423570985008687907853269984665640564039457584007913129638848 := by
      decide
    have h1 := affinePt_eq_taddr n j hjn
    have hR : 8256 +
        115792089237316195423570985008687907853269984665640564039457584007913129638848 =
        115792089237316195423570985008687907853269984665640564039457584007913129639936 +
          7168 := by
      decide
    rw [hC]; omega
  have hmodN : (UInt256.toNat
      115792089237316195423570985008687907853269984665640564039457584007913129639904 +
      affinePt n j) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      affinePt n (j + 1) := by
    have hC : UInt256.toNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 =
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
      decide
    have h1 := affinePt_eq_taddr n j hjn
    have hS := affinePt_succ n j (by omega)
    have hR :
        115792089237316195423570985008687907853269984665640564039457584007913129639904 +
          8256 =
        115792089237316195423570985008687907853269984665640564039457584007913129639936 +
          8224 := by
      decide
    rw [hC]; omega
  have h8224 : ((8224 : UInt256)).toNat = 8224 := by decide
  have h2337 : ((2317 : UInt256)) = UInt256.ofNat 2317 := by decide
  have hdest : ((2317 : UInt256)).toNat = 2317 := by decide
  have hgt : affinePt n (j + 1) > 8224 :=
    (affinePt_guard n j (by omega)).mpr hj
  have h256 : (2 ^ 256 : Nat) =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    decide
  have hgtM : 8224 < affinePt n (j + 1) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    have hlt : affinePt n (j + 1) <
        115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      rw [← h256]; exact affinePt_lt_word n (j + 1) hn32 (by omega)
    rw [Nat.mod_eq_of_lt hlt]; omega
  have hnext : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
        UInt256) + UInt256.ofNat (affinePt n j) =
      UInt256.ofNat (affinePt n (j + 1)) :=
    affine_add_next_word_left n j (by omega) hn32
  have hactD : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (7168 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [runRaw, affineRest, Challenge.EvmProof.Stepper.runInstr,
      affineLoadedState, affineLoopState, csStep, hnext,
      hc4, hc5, hc6, hc7, hc8, hrun,
      hmodD, hmodN, h8224, h2337, hdest, hgt, hgtM, hjump, hactD,
      State.activeWordsAfterUInt256,
      UInt256.gt, UInt256.lt, UInt256.isTrue,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
/-- Remainder execution, guard not taken (`j + 1 = n`): `[m, t, pt,
borrow, dst, ret]` at 2356 reaches the post-guard exit state at 2451. -/
theorem run_affineRestExit (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j + 1 = n) (hn32 : n ≤ 32) :
    runRaw affineRest (affineLoadedState s memory n j pdst ret rest) =
      some (affineGuardExitState s memory n j pdst ret rest) := by
  have hjn : j < n := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hmodD : (affinePt n j + UInt256.toNat
      115792089237316195423570985008687907853269984665640564039457584007913129638848) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      7168 + 32 * (n - 1 - j) := by
    have hC : UInt256.toNat
        115792089237316195423570985008687907853269984665640564039457584007913129638848 =
        115792089237316195423570985008687907853269984665640564039457584007913129638848 := by
      decide
    have h1 := affinePt_eq_taddr n j hjn
    have hR : 8256 +
        115792089237316195423570985008687907853269984665640564039457584007913129638848 =
        115792089237316195423570985008687907853269984665640564039457584007913129639936 +
          7168 := by
      decide
    rw [hC]; omega
  have hmodN : (UInt256.toNat
      115792089237316195423570985008687907853269984665640564039457584007913129639904 +
      affinePt n j) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      affinePt n (j + 1) := by
    have hC : UInt256.toNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 =
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
      decide
    have h1 := affinePt_eq_taddr n j hjn
    have hS := affinePt_succ n j (by omega)
    have hR :
        115792089237316195423570985008687907853269984665640564039457584007913129639904 +
          8256 =
        115792089237316195423570985008687907853269984665640564039457584007913129639936 +
          8224 := by
      decide
    rw [hC]; omega
  have h8224 : ((8224 : UInt256)).toNat = 8224 := by decide
  have hexit : affinePt n (j + 1) = 8224 := by unfold affinePt; omega
  have hnge : ¬ affinePt n (j + 1) > 8224 := by omega
  have hnext : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
        UInt256) + UInt256.ofNat (affinePt n j) =
      UInt256.ofNat (affinePt n (j + 1)) :=
    affine_add_next_word_left n j (by omega) hn32
  have hactD : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (7168 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [runRaw, affineRest, Challenge.EvmProof.Stepper.runInstr,
      affineLoadedState, affineGuardExitState, csStep, hnext,
      hc4, hc5, hc6, hc7, hc8, hrun,
      hmodD, hmodN, h8224, hexit, hnge, hactD,
      State.activeWordsAfterUInt256,
      UInt256.gt, UInt256.lt, UInt256.isTrue,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
/-- Stale-pointer pop at 2451: `[pt, borrow, dst, ret]` becomes
`[borrow, dst, ret]` at 2452. -/
theorem run_affinePop (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running) :
    runRaw [Instr.op .POP] (affineGuardExitState s memory n j pdst ret rest) =
      some (affineTailPreState s memory n (j + 1) pdst ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  simp (config := { maxSteps := 400000 })
    [runRaw, Challenge.EvmProof.Stepper.runInstr,
      affineGuardExitState, affineTailPreState,
      hc4, hrun,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

/-- Whole loop-body execution (`j + 1 < n`, JUMPI taken) by composition. -/
theorem run_affineLoopBody (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j + 1 < n) (hn32 : n ≤ 32)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 2317 = true) :
    runRaw affineLoopBody (affineLoopState s memory n j pdst ret rest) =
      some (affineLoopState s memory n (j + 1) pdst ret rest) := by
  have hjn : j < n := by omega
  have h1 := run_affineLoad s memory n j pdst ret rest hcap hrun hact hjn hn32
  have h2 := run_affineRestBody s memory n j pdst ret rest hcap hrun hact hj hn32
    hjump
  have hhalt : (affineLoadedState s memory n j pdst ret rest).halt =
      .Running := hrun
  exact runRaw_append affineLoad affineRest _ _ _ h1 hhalt h2

/-- Whole loop-exit execution (`j + 1 = n`) by composition. -/
theorem run_affineLoopExit (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j + 1 = n) (hn32 : n ≤ 32) :
    runRaw affineLoopExit (affineLoopState s memory n j pdst ret rest) =
      some (affineTailPreState s memory n (j + 1) pdst ret rest) := by
  have hjn : j < n := by omega
  have h1 := run_affineLoad s memory n j pdst ret rest hcap hrun hact hjn hn32
  have h2 := run_affineRestExit s memory n j pdst ret rest hcap hrun hact hj hn32
  have h3 := run_affinePop s memory n j pdst ret rest hcap hrun
  have hhalt1 : (affineLoadedState s memory n j pdst ret rest).halt =
      .Running := hrun
  have h12 := runRaw_append affineLoad affineRest _ _ _ h1 hhalt1 h2
  have hhalt2 : (affineGuardExitState s memory n j pdst ret rest).halt =
      .Running := hrun
  have h123 := runRaw_append (affineLoad ++ affineRest) [Instr.op .POP] _ _ _
    h12 hhalt2 h3
  simpa [affineLoopBody, affineLoopExit] using h123

end Challenge.Modexp.Submission.Proofs.Fast.CsubAffineRun
