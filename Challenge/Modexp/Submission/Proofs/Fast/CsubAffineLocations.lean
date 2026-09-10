import YulEvmCompiler.Instr
import Challenge.Modexp.Submission.Proofs.Fast.CsubAffineRun
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P12
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P13

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Theory A affine CSUB located bindings (home module)

This module owns the new CSUB located entry/body/exit/tail bindings and
their `runRaw` → `Located` bridge.

What is verified **now** (no whole-program artifact needed):

* `csubWindowBytes`: the exact 190-byte new CSUB window `[2304, 2474)`.
* `csubWindowInstrs`: the same window as instructions
  (`affineEntry ++ affineLoopExit ++ affineTailInstrs`, 54 instructions).
* `csubWindow_assembles`: the instruction lists assemble to the exact
  bytes (`by decide`).  The structural lane cross-checks its regenerated
  artifact window against this theorem: their disassembly must reproduce
  `csubWindowInstrs` in order.

What activates on the structural transfer (new `Artifact.lean` with the
candidate instruction list;PENDING section below spells out the exact
code): four `Located` block definitions over indices `1668..1721`
(entry `1668..1672`, loop `1673..1706`, tail `1707..1721`), the four
`runLocatedBlock` transition lemmas (same `simp` recipes as
`CsubAffineRun`, plus per-index program-counter facts from the new
`fastPC` tables and the new loop-dest jumpdest fact at pc 2317), and the
bridge corollaries identifying each `runLocatedBlock` with its `runRaw`
segment by transitivity through the shared affine end states.

Tail contract: `csTailState` (pc 2469, three pointers) is superseded by
`affineTailPreState` (pc 2452, `[borrow, dst, ret]` only).  The tail block
reuses the old tail `MCOPY` reasoning with the old three-`POP` prefix
dropped (single stale-`pt` `POP` at 2451 instead); the endpoint
`csReturnedState` is unchanged.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CsubAffineLocations

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Csub
open Challenge.Modexp.Submission.Proofs.Fast.CsubAffineStep
open Challenge.Modexp.Submission.Proofs.Fast.CsubAffineRun

/-- Exact new CSUB window bytes `[2304, 2474)` (190 bytes; identical
outside the window to the frozen baseline). -/
def csubWindowBytes : ByteArray := ByteArray.mk #[
  0x5b, 0x67, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x24, 0xe0, 0x51, 0x5f, 0x90, 0x5b, 0x80, 0x51, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xdf, 0xc0, 0x82, 0x01, 0x51, 0x81, 0x81, 0x11, 0x91, 0x03, 0x83, 0x81, 0x03, 0x90, 0x84, 0x11, 0x90, 0x91, 0x17, 0x92, 0x50, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfb, 0xc0, 0x82, 0x01, 0x52, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xe0, 0x01, 0x61, 0x20, 0x20, 0x81, 0x11, 0x61, 0x09, 0x0d, 0x57, 0x50, 0x15, 0x61, 0x20, 0x20, 0x51, 0x17, 0x61, 0x04, 0x3f, 0x19, 0x02, 0x61, 0x20, 0x40, 0x01, 0x61, 0x24, 0x80, 0x51, 0x91, 0x5e, 0x56]

/-- Unchanged common return tail `[2452, 2474)` as instructions (14). -/
def affineTailInstrs : List Instr :=
  [Instr.op .ISZERO,
   Instr.push 2 8224,
   Instr.op .MLOAD,
   Instr.op .OR,
   Instr.push 2 1087,
   Instr.op .NOT,
   Instr.op .MUL,
   Instr.push 2 8256,
   Instr.op .ADD,
   Instr.push 2 9344,
   Instr.op .MLOAD,
   Instr.op (.Swap ⟨1, by decide⟩),
   Instr.op .MCOPY,
   Instr.op .JUMP]

/-- Whole new window as instructions (54). -/
def csubWindowInstrs : List Instr :=
  affineEntry ++ affineLoopExit ++ affineTailInstrs

theorem csubWindowBytes_size : csubWindowBytes.size = 170 := by rfl

theorem affineTailInstrs_length : affineTailInstrs.length = 14 := by rfl

theorem csubWindowInstrs_length : csubWindowInstrs.length = 54 := by rfl

/-- The proven instruction lists assemble to the exact native-passing
bytes.  Structural lane: the regenerated artifact's disassembly of
`[2304, 2474)` must reproduce `csubWindowInstrs` in order. -/
theorem csubWindow_assembles :
    YulEvmCompiler.assemble csubWindowInstrs = csubWindowBytes := by
  decide

/-! ## Located entry transition (active)

`blk1667` (`Paths.P12`, indices `1668..1672`) runs the new 5-instruction
entry against the exact artifact: same `simp` recipe as
`CsubAffineRun.run_affineEntry`, plus the per-index program-counter facts
from `fastPC17`. -/

set_option linter.unusedSimpArgs false in
theorem run_csubEntryLocated (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32)
    (htl : MachineState.readWord memory 9440 = UInt256.ofNat (8224 + 32 * n)) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1667
      (csEntryState s memory pdst ret rest) =
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
    [blk1667, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      csEntryState, affineLoopState, affinePt, csStep, fastPC17,
      hc2, hc3, hc4, hrun, h9440, hzero, hpt0, htl, hactA,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

/-! ## Located loop body via the raw seam (active)

`blk1683` (`Paths.P13`, indices `1673..1706`) is the new 34-instruction
loop body.  The located proof reuses the exact `CsubAffineRun` seam —
T-load (first 3), M-load (next 4), rest (remaining 27) — with the same
fact sets plus per-index program-counter facts, composed with
`runLocatedBlock_append`.  Taken (`j + 1 < n`) it reaches the next
affine loop state. -/

set_option linter.unusedSimpArgs false in
theorem run_csubLoadTLocated (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j < n) (hn32 : n ≤ 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock (blk1683.take 3)
      (affineLoopState s memory n j pdst ret rest) =
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
    [blk1683, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      affineLoopState, affineLoadedTState, fastPC17,
      hc4, hc5, hrun, hta, hactT,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_csubLoadMLocated (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j < n) (hn32 : n ≤ 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock ((blk1683.drop 3).take 4)
      (affineLoadedTState s memory n j pdst ret rest) =
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
    [blk1683, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      affineLoadedTState, affineLoadedState, fastPC17,
      hc5, hc6, hc7, hrun, hmodM, hactM,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_csubRestBodyLocated (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j + 1 < n) (hn32 : n ≤ 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock (blk1683.drop 7)
      (affineLoadedState s memory n j pdst ret rest) =
      some (affineLoopState s memory n (j + 1) pdst ret rest) := by
  have hjn : j < n := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have h256 : (2 ^ 256 : Nat) =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    decide
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
  have hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2317 = true :=
    jumpDest2666
  have hactD : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (7168 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [blk1683, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      affineLoadedState, affineLoopState, csStep, fastPC17, fastPC18,
      hc4, hc5, hc6, hc7, hc8, hrun, hcode,
      hmodD, hmodN, h8224, h2337, hdest, hgt, hgtM, hjump, hnext, hactD,
      State.activeWordsAfterUInt256,
      UInt256.gt, UInt256.lt, UInt256.isTrue,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

/-- Whole loop-body execution (`j + 1 < n`, JUMPI taken) by composition of
the three located parts. -/
theorem run_csubLoopBodyLocated (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j + 1 < n) (hn32 : n ≤ 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1683
      (affineLoopState s memory n j pdst ret rest) =
      some (affineLoopState s memory n (j + 1) pdst ret rest) := by
  have hjn : j < n := by omega
  have h1 := run_csubLoadTLocated s memory n j pdst ret rest hcap hrun hact hjn hn32
  have hhaltT : (affineLoadedTState s memory n j pdst ret rest).halt =
      .Running := hrun
  have h2 := run_csubLoadMLocated s memory n j pdst ret rest hcap hrun hact hjn hn32
  have hhaltL : (affineLoadedState s memory n j pdst ret rest).halt =
      .Running := hrun
  have h3 := run_csubRestBodyLocated s memory n j pdst ret rest hcap hrun hcode
    hact hj hn32
  have h12 := Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _ h1
    hhaltT h2
  have h123 := Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _ h12
    hhaltL h3
  have hsplit : (blk1683.take 3 ++ (blk1683.drop 3).take 4) ++ blk1683.drop 7 =
      blk1683 := by
    simp [blk1683]
  rwa [hsplit] at h123

/-! ## Located loop exit and tail (active)

Not taken (`j + 1 = n`), the same `blk1683` reaches the post-guard exit
state at pc 2451 (recipe: `run_affineRestExit` facts on the `drop 7`
rest, same load prefix as the taken case).  `blk1724` (`Paths.P13`,
indices `1707..1721`) then runs the stale-pointer `POP` plus the common
return tail to `csReturnedState` (recipe: old `run_csTail` facts minus
the three pointer `POP`s). -/

set_option linter.unusedSimpArgs false in
theorem run_csubRestExitLocated (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j + 1 = n) (hn32 : n ≤ 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock (blk1683.drop 7)
      (affineLoadedState s memory n j pdst ret rest) =
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
    [blk1683, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      affineLoadedState, affineGuardExitState, csStep, fastPC17, fastPC18,
      hc4, hc5, hc6, hc7, hc8, hrun,
      hmodD, hmodN, h8224, hexit, hnge, hnext, hactD,
      State.activeWordsAfterUInt256,
      UInt256.gt, UInt256.lt, UInt256.isTrue,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

/-- Whole loop-exit execution (`j + 1 = n`) by composition of the same
load prefix with the not-taken rest. -/
theorem run_csubLoopExitLocated (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j + 1 = n) (hn32 : n ≤ 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1683
      (affineLoopState s memory n j pdst ret rest) =
      some (affineGuardExitState s memory n j pdst ret rest) := by
  have hjn : j < n := by omega
  have h1 := run_csubLoadTLocated s memory n j pdst ret rest hcap hrun hact hjn hn32
  have hhaltT : (affineLoadedTState s memory n j pdst ret rest).halt =
      .Running := hrun
  have h2 := run_csubLoadMLocated s memory n j pdst ret rest hcap hrun hact hjn hn32
  have hhaltL : (affineLoadedState s memory n j pdst ret rest).halt =
      .Running := hrun
  have h3 := run_csubRestExitLocated s memory n j pdst ret rest hcap hrun hact
    hj hn32
  have h12 := Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _ h1
    hhaltT h2
  have h123 := Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _ h12
    hhaltL h3
  have hsplit : (blk1683.take 3 ++ (blk1683.drop 3).take 4) ++ blk1683.drop 7 =
      blk1683 := by
    simp [blk1683]
  rwa [hsplit] at h123

set_option linter.unusedSimpArgs false in
theorem run_csubTailLocated (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hs32 : MachineState.readWord (csStep memory n (j + 1)).memory 9344 =
      UInt256.ofNat (32 * n))
    (hdstFit : pdst.toNat + 32 * n ≤ 9472)
    (hsrcFit : (csSrc memory n (j + 1)).toNat + 32 * n ≤ 9472) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1724
      (affineGuardExitState s memory n j pdst ret rest) =
      some (csReturnedState s memory n (j + 1) pdst ret rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  have hsz : 32 * n %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * n := Nat.mod_eq_of_lt (by omega)
  have hactN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 8224 32) =
      s.activeWords := activeWords_fix s 8224 32 (by decide) (by omega) hact
  have hactS : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9344 32) =
      s.activeWords := activeWords_fix s 9344 32 (by decide) (by omega) hact
  have hactC1 : MachineState.activeWordsAfter s.activeWords.toNat pdst.toNat (32 * n) =
      s.activeWords.toNat :=
    activeWordsAfter_fix s.activeWords.toNat pdst.toNat (32 * n) (by omega) (by omega) hact
  have hactC2 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (csSrc memory n (j + 1)).toNat (32 * n)) = s.activeWords :=
    activeWords_fix s _ (32 * n) (by omega) (by omega) hact
  have hsrcEq : (8256 : UInt256) +
      (115792089237316195423570985008687907853269984665640564039457584007913129638848 :
        UInt256) *
        UInt256.lor (MachineState.readWord (csStep memory n (j + 1)).memory 8224)
          (UInt256.isZero (csStep memory n (j + 1)).flag) = csSrc memory n (j + 1) := rfl
  /- The `MCOPY` source address in the distributed `toNat` normal form
  simp produces (with `lnot 1087` unreduced). -/
  have hsrcToNat : (UInt256.toNat 8256 +
      (UInt256.lnot 1087 *
        UInt256.lor (MachineState.readWord (csStep memory n (j + 1)).memory 8224)
          (UInt256.isZero (csStep memory n (j + 1)).flag)).toNat) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      (csSrc memory n (j + 1)).toNat := by
    have hC : UInt256.lnot 1087 =
        (115792089237316195423570985008687907853269984665640564039457584007913129638848 :
          UInt256) := by
      decide
    have h256 : (2 ^ 256 : Nat) =
        115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      decide
    rw [hC, ← h256, ← Challenge.EvmProof.Word.word_toNat_add, hsrcEq]
  simp (config := { maxSteps := 400000 })
    [blk1724, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      affineGuardExitState, csReturnedState, hsrcEq, hsrcToNat, fastPC18, fastPC19,
      hc1, hc2, hc3, hc4, hc5, hc6, hrun, hcode, h8224, h9344, hjump, hs32,
      hsz, hactN, hactS, hactC1, hactC2,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

/-! REMAINING activation (entry + loop-body located above; blocks now live
in `Paths.P12`/`Paths.P13` under their historic names `blk1667`/`blk1683` /
`blk1724` with new contents — do not paste duplicates here):

1. Paste the four block definitions below into this module (replacing this
   comment), with `open Challenge.Modexp.Submission.Proofs.Bytecode` and
   the `Located Artifact.submissionArtifact .Osaka` list type used by
   `Paths/*`.  Expected indices (prefix `< 1668` unchanged; window
   `1667 + 54 = 1721`; post-window shifted `-20`):

```lean
def blkAffineEntry : List (Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1660 .JUMPDEST,
   pushAt 1661 8 9440,
   opAt 1662 .MLOAD,
   pushAt 1663 0 0,
   opAt 1664 (.Swap ⟨0, by decide⟩)]

def blkAffineLoop : List (Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1665 .JUMPDEST,
   opAt 1666 (.Dup ⟨0, by decide⟩),
   opAt 1667 .MLOAD,
   pushAt 1668 32 115792089237316195423570985008687907853269984665640564039457584007913129631680,
   opAt 1669 (.Dup ⟨2, by decide⟩),
   opAt 1670 .ADD,
   opAt 1671 .MLOAD,
   opAt 1672 (.Dup ⟨1, by decide⟩),
   opAt 1673 (.Dup ⟨1, by decide⟩),
   opAt 1674 .GT,
   opAt 1675 (.Swap ⟨1, by decide⟩),
   opAt 1676 .SUB,
   opAt 1677 (.Dup ⟨3, by decide⟩),
   opAt 1678 (.Dup ⟨1, by decide⟩),
   opAt 1679 .SUB,
   opAt 1680 (.Swap ⟨0, by decide⟩),
   opAt 1681 (.Dup ⟨4, by decide⟩),
   opAt 1682 .GT,
   opAt 1683 (.Swap ⟨0, by decide⟩),
   opAt 1684 (.Swap ⟨1, by decide⟩),
   opAt 1685 .OR,
   opAt 1686 (.Swap ⟨2, by decide⟩),
   opAt 1687 .POP,
   pushAt 1688 32 115792089237316195423570985008687907853269984665640564039457584007913129638848,
   opAt 1689 (.Dup ⟨2, by decide⟩),
   opAt 1690 .ADD,
   opAt 1691 .MSTORE,
   pushAt 1692 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1693 .ADD,
   pushAt 1694 2 8224,
   opAt 1695 (.Dup ⟨1, by decide⟩),
   opAt 1696 .GT,
   pushAt 1697 2 2317,
   opAt 1698 .JUMPI]

def blkAffineTail : List (Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1699 .POP,
   opAt 1700 .ISZERO,
   pushAt 1701 2 8224,
   opAt 1702 .MLOAD,
   opAt 1703 .OR,
   pushAt 1704 2 1087, opAt 1705 .NOT,
   opAt 1706 .MUL,
   pushAt 1707 2 8256,
   opAt 1708 .ADD,
   pushAt 1709 2 9344,
   opAt 1710 .MLOAD,
   opAt 1711 (.Swap ⟨1, by decide⟩),
   opAt 1712 .MCOPY,
   opAt 1713 .JUMP]
```

2. Prove the four `runLocatedBlock` transitions with the `CsubAffineRun`
   `simp` recipes (same fact sets; add per-index program-counter facts
   from the new tables and the new pc-2317 jumpdest fact for the loopback):
   - `run_affineEntryLocated`: `blkAffineEntry` from `csEntryState` to
     `affineLoopState j = 0` (recipe: `run_affineEntry`).
   - `run_affineLoopBodyLocated`: `blkAffineLoop` from `affineLoopState j`
     to `affineLoopState (j+1)` for `j + 1 < n` (recipe:
     `run_affineLoad` + `run_affineRestBody` facts combined, as in the
     monolithic attempt; or two blocks split at 1679 mirroring
     `affineLoad`/`affineRest` and composed with `runLocatedBlock_append`).
   - `run_affineLoopExitLocated`: `blkAffineLoop` then `POP` (1707) from
     `affineLoopState j` to `affineTailPreState (j+1)` for `j + 1 = n`
     (recipes: `run_affineRestExit`, `run_affinePop`).
   - `run_affineTailLocated`: `blkAffineTail` from `affineTailPreState` to
     `csReturnedState` (recipe: old `run_csTail` simp minus the three
     pointer `POP`s and pointer facts; keep `hsrcEq`, `hs32`, `hdstFit`,
     `hsrcFit`, `MCOPY`/active-words facts; endpoint `csReturnedState`
     unchanged).

3. Bridge corollaries (one line each by transitivity through the shared
   affine end states, e.g.):
   `runLocatedBlock blkAffineLoop s = runRaw affineLoopBody s`
   by `rw [run_affineLoopBodyLocated ..., run_affineLoopBody ...]`.

4. In `Csub.lean`: delete the stale three-pointer `csLoopState`,
   `csTailState`, `run_csEntry`, `run_csLoopBody`, `run_csLoopExit`,
   `run_csTail` block and reassemble `gasSteps_csub` (statement and all
   premises, including unused `hml`, unchanged) from new
   entry/iteration/loop/exit/tail `GasSteps` wrappers following the
   existing `iterateBounded` + `trans` composition pattern.
-/

end Challenge.Modexp.Submission.Proofs.Fast.CsubAffineLocations
