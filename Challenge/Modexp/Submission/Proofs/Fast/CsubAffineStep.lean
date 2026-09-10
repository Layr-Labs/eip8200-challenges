import Challenge.Modexp.Submission.Proofs.Fast.CsubModel

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Theory A affine CSUB step (one live pointer)

Single-pointer reconstruction of the `CSUB` limb addresses, preserving the
public `Csub.gasSteps_csub` contract, `csEntryState`, `csReturnedState`,
and `csStep`/`csResultMemory`.

Reference: `research/REPORT.md` section 3 and
`research/one_pointer_pc_stable.fragment.txt` (last byte is a test sentinel,
not part of the solver).

New loop state (internal only):

```text
[pt, borrow, dst, ret] ++ rest
pt = 8224 + 32*n - 32*j
```

Entry schedule `[2282, 2311)`: `JUMPDEST; PUSH24 9440; MLOAD; PUSH0; SWAP1`
turns `[pdst, ret]` into `[pt, 0, dst, ret]` with `pt = 8224 + 32*n`,
falling through into the loop head at 2311.  Both arrivals at 2311
(fall-through with borrow `0`, loopback with the propagated borrow) carry
the same `[pt, borrow, dst, ret]` stack shape, so `affineLoopState` is
well-formed as the single loop invariant.

Old `csStep` memory/borrow recurrence is unchanged.  At step `j` (with `j < n`):

```text
t_addr = pt               = 8256 + 32*(n-1-j)
m_addr = pt - 8256        = 32*(n-1-j)
s_addr = pt - 1088        = 7168 + 32*(n-1-j)
d1 = t - m; d2 = d1 - borrow
newBorrow = [t < m] OR [d1 < borrow]
```

No wrapped `m + borrow` shortcut is used.  The EVM schedule under proof is:

```text
DUP1; MLOAD
PUSH32 (W-8256); DUP3; ADD; MLOAD
DUP2; DUP2; GT; SWAP2; SUB
DUP4; DUP2; SUB; SWAP1; DUP5; GT
SWAP1; SWAP2; OR; SWAP3; POP
PUSH32 (W-1088); DUP3; ADD; MSTORE
PUSH32 (W-32); ADD
PUSH2 8224; DUP2; GT; PUSH2 loop; JUMPI
POP
```

followed by the unchanged common return tail at `[2446, 2468)`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CsubAffineStep

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Csub

/-- The single live pointer at step `j`: the `t`-limb address itself. -/
def affinePt (n j : Nat) : Nat :=
  8224 + 32 * n - 32 * j

/-- Proposed affine loop state: `[pt, borrow, dst, ret]`, same `csStep`
memory/borrow as the current three-pointer invariant. -/
def affineLoopState (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2311
           stack := [UInt256.ofNat (affinePt n j),
                     (csStep memory n j).flag, pdst, ret] ++ rest
           memory := (csStep memory n j).memory }

/-- `pt` is exactly the current `t`-limb address. -/
theorem affinePt_eq_taddr (n j : Nat) (hj : j < n) :
    affinePt n j = 8256 + 32 * (n - 1 - j) := by
  unfold affinePt
  omega

/-- `pt - 8256` is exactly the current modulus-limb address. -/
theorem affinePt_sub_mod (n j : Nat) (hj : j < n) :
    affinePt n j - 8256 = 32 * (n - 1 - j) := by
  have h := affinePt_eq_taddr n j hj
  omega

/-- `pt - 1088` is exactly the current scratch-limb address. -/
theorem affinePt_sub_scratch (n j : Nat) (hj : j < n) :
    affinePt n j - 1088 = 7168 + 32 * (n - 1 - j) := by
  have h := affinePt_eq_taddr n j hj
  omega

/-- One downward step decreases `pt` by one limb. -/
theorem affinePt_succ (n j : Nat) (hj : j + 1 ≤ n) :
    affinePt n (j + 1) = affinePt n j - 32 := by
  unfold affinePt
  omega

/-- Loop-exit guard in pointer form: after the step, `pt = 8224` iff done. -/
theorem affinePt_guard (n j : Nat) (hj : j + 1 ≤ n) :
    (affinePt n (j + 1) > 8224) ↔ (j + 1 < n) := by
  unfold affinePt
  omega

/-- The raw affine arithmetic/store step lands exactly on `csStep (j+1)`.

Reads use `pt`, `pt - 8256`; the store uses `pt - 1088`; the borrow uses the
retained two-comparison recurrence.  This is the pure-model half of one new
loop iteration; the EVM `Located` execution binding comes next and must reuse
this statement rather than any old three-pointer execution fact. -/
theorem affine_step_eq_csStep (memory : ByteArray) (n j : Nat) (hj : j < n) :
    let prev := csStep memory n j
    let t := MachineState.readWord prev.memory (affinePt n j)
    let md := MachineState.readWord prev.memory (affinePt n j - 8256)
    let d1 := t - md
    let d2 := d1 - prev.flag
    let bout := UInt256.lor (UInt256.lt t md) (UInt256.lt d1 prev.flag)
    csStep memory n (j + 1) =
      { memory := MachineState.writeBytes prev.memory
          (Data.Bytes.natToBytesPadded d2.toNat 32) (affinePt n j - 1088)
        flag := bout } := by
  simp only
  have ht : affinePt n j = 8256 + 32 * (n - 1 - j) :=
    affinePt_eq_taddr n j hj
  have hm : affinePt n j - 8256 = 32 * (n - 1 - j) :=
    affinePt_sub_mod n j hj
  have hd : affinePt n j - 1088 = 7168 + 32 * (n - 1 - j) :=
    affinePt_sub_scratch n j hj
  simp only [csStep]
  rw [hm, hd, ht]

/-- `pt` always fits in one EVM word for the supported limb counts. -/
theorem affinePt_lt_word (n j : Nat) (hn32 : n ≤ 32) (hj : j ≤ n) :
    affinePt n j < 2 ^ 256 := by
  have hW : 9248 < 2 ^ 256 := by norm_num
  unfold affinePt
  omega

/-- EVM `PUSH32 (W-8256); ADD` on `pt` yields the modulus address. -/
theorem affine_add_mod_word (n j : Nat) (hj : j < n) (hn32 : n ≤ 32) :
    UInt256.ofNat (affinePt n j) +
        (115792089237316195423570985008687907853269984665640564039457584007913129631680 :
          UInt256) =
      UInt256.ofNat (32 * (n - 1 - j)) := by
  have hC : (115792089237316195423570985008687907853269984665640564039457584007913129631680 :
      UInt256).toNat =
      115792089237316195423570985008687907853269984665640564039457584007913129631680 := by
    decide
  have hCeq : 115792089237316195423570985008687907853269984665640564039457584007913129631680 =
      2 ^ 256 - 8256 := by
    norm_num
  have hPt : affinePt n j < 2 ^ 256 := affinePt_lt_word n j hn32 (by omega)
  have hT : 32 * (n - 1 - j) < 2 ^ 256 := by
    have hW : 1024 < 2 ^ 256 := by norm_num
    omega
  have h1 : affinePt n j = 8256 + 32 * (n - 1 - j) :=
    affinePt_eq_taddr n j hj
  have hEq : affinePt n j +
      115792089237316195423570985008687907853269984665640564039457584007913129631680 =
      2 ^ 256 + 32 * (n - 1 - j) := by
    omega
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_add, hC,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hPt,
    Nat.mod_eq_of_lt hT, hEq, Nat.add_mod, Nat.mod_self, Nat.zero_add,
    Nat.mod_mod, Nat.mod_eq_of_lt hT]

/-- EVM `PUSH32 (W-1088); ADD` on `pt` yields the scratch address. -/
theorem affine_add_scratch_word (n j : Nat) (hj : j < n) (hn32 : n ≤ 32) :
    UInt256.ofNat (affinePt n j) +
        (115792089237316195423570985008687907853269984665640564039457584007913129638848 :
          UInt256) =
      UInt256.ofNat (7168 + 32 * (n - 1 - j)) := by
  have hC : (115792089237316195423570985008687907853269984665640564039457584007913129638848 :
      UInt256).toNat =
      115792089237316195423570985008687907853269984665640564039457584007913129638848 := by
    decide
  have hCeq : 115792089237316195423570985008687907853269984665640564039457584007913129638848 =
      2 ^ 256 - 1088 := by
    norm_num
  have hPt : affinePt n j < 2 ^ 256 := affinePt_lt_word n j hn32 (by omega)
  have hT : 7168 + 32 * (n - 1 - j) < 2 ^ 256 := by
    have hW : 8192 < 2 ^ 256 := by norm_num
    omega
  have h1 : affinePt n j = 8256 + 32 * (n - 1 - j) :=
    affinePt_eq_taddr n j hj
  have hEq : affinePt n j +
      115792089237316195423570985008687907853269984665640564039457584007913129638848 =
      2 ^ 256 + (7168 + 32 * (n - 1 - j)) := by
    omega
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_add, hC,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hPt,
    Nat.mod_eq_of_lt hT, hEq, Nat.add_mod, Nat.mod_self, Nat.zero_add,
    Nat.mod_mod, Nat.mod_eq_of_lt hT]

/-- EVM `PUSH32 (W-32); ADD` advances `pt` by one downward limb. -/
theorem affine_add_next_word (n j : Nat) (hj : j + 1 ≤ n) (hn32 : n ≤ 32) :
    UInt256.ofNat (affinePt n j) +
        (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
          UInt256) =
      UInt256.ofNat (affinePt n (j + 1)) := by
  have hC : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
      UInt256).toNat =
      115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have hCeq : 115792089237316195423570985008687907853269984665640564039457584007913129639904 =
      2 ^ 256 - 32 := by
    norm_num
  have hPt : affinePt n j < 2 ^ 256 := affinePt_lt_word n j hn32 (by omega)
  have hN : affinePt n (j + 1) < 2 ^ 256 := affinePt_lt_word n (j + 1) hn32 hj
  have hStep : affinePt n (j + 1) = affinePt n j - 32 := affinePt_succ n j hj
  have hGe : 32 ≤ affinePt n j := by
    unfold affinePt
    omega
  have hEq : affinePt n j +
      115792089237316195423570985008687907853269984665640564039457584007913129639904 =
      2 ^ 256 + affinePt n (j + 1) := by
    omega
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_add, hC,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hPt,
    Nat.mod_eq_of_lt hN, hEq, Nat.add_mod, Nat.mod_self, Nat.zero_add,
    Nat.mod_mod, Nat.mod_eq_of_lt hN]

/-- EVM `PUSH32 (W-32); ADD` with the constant on top (guard position:
`[C32, pt, ...]`) advances `pt` by one downward limb. -/
theorem affine_add_next_word_left (n j : Nat) (hj : j + 1 ≤ n)
    (hn32 : n ≤ 32) :
    (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
        UInt256) + UInt256.ofNat (affinePt n j) =
      UInt256.ofNat (affinePt n (j + 1)) := by
  have hC : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
      UInt256).toNat =
      115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
    decide
  have hPt : affinePt n j < 2 ^ 256 := affinePt_lt_word n j hn32 (by omega)
  have hN : affinePt n (j + 1) < 2 ^ 256 := affinePt_lt_word n (j + 1) hn32 hj
  have hStep : affinePt n (j + 1) = affinePt n j - 32 := affinePt_succ n j hj
  have hGe : 32 ≤ affinePt n j := by
    unfold affinePt
    omega
  have hEq : 115792089237316195423570985008687907853269984665640564039457584007913129639904 +
      affinePt n j =
      2 ^ 256 + affinePt n (j + 1) := by
    omega
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_add, hC,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hPt,
    Nat.mod_eq_of_lt hN, hEq, Nat.add_mod, Nat.mod_self, Nat.zero_add,
    Nat.mod_mod, Nat.mod_eq_of_lt hN]

/-- Pure affine iteration, mirroring `csStep` but addressing through `pt`. -/
def affineIter (memory : ByteArray) (n : Nat) : Nat → LimbState
  | 0 => ⟨memory, UInt256.ofNat 0⟩
  | j + 1 =>
      let prev := affineIter memory n j
      let t := MachineState.readWord prev.memory (affinePt n j)
      let md := MachineState.readWord prev.memory (affinePt n j - 8256)
      let d1 := t - md
      let d2 := d1 - prev.flag
      { memory := MachineState.writeBytes prev.memory
          (Data.Bytes.natToBytesPadded d2.toNat 32) (affinePt n j - 1088)
        flag := UInt256.lor (UInt256.lt t md) (UInt256.lt d1 prev.flag) }

/-- The affine iteration reproduces `csStep` on every supported prefix. -/
theorem affineIter_eq_csStep (memory : ByteArray) (n : Nat)
    (_hn32 : n ≤ 32) : ∀ j, j ≤ n →
      affineIter memory n j = csStep memory n j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      have hj' : j < n := by omega
      have hjle : j ≤ n := by omega
      have hprev := ih hjle
      have ht : affinePt n j = 8256 + 32 * (n - 1 - j) :=
        affinePt_eq_taddr n j hj'
      have hm : affinePt n j - 8256 = 32 * (n - 1 - j) :=
        affinePt_sub_mod n j hj'
      have hd : affinePt n j - 1088 = 7168 + 32 * (n - 1 - j) :=
        affinePt_sub_scratch n j hj'
      simp only [affineIter, hprev]
      simp only [csStep]
      rw [hm, hd, ht]

end Challenge.Modexp.Submission.Proofs.Fast.CsubAffineStep
