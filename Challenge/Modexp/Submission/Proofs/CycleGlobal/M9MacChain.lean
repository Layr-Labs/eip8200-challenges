import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.ShiftJumpTargets
import Challenge.Modexp.Submission.Proofs.CycleGlobal.M9MacBlocks
import Challenge.Modexp.Submission.Proofs.Fast.M9MacRun

noncomputable section
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 40000

/-!
# M9: gas traces of the straight MAC chain

* `gasSteps_block b`  : one block on any MAC state (the `KernelChain.gasSteps_l1Step` shape).
* `gasSteps_run m b`   : blocks `b..7` (`b + m = 8`) from the start of block `b` to the exit at pc 3168,
                         producing `SquareModel.l1Run q bi 1280 n j m` (the `gasSteps_l1Run` recursion).
* `gasSteps_exit`      : `JUMPDEST JUMPDEST JUMPDEST`, pc 3168 → 3171 (the unchanged top-limb fixup).
* `gasSteps_chain n`   : the whole section for `n = 4 ∨ n = 8` from the entry `JUMPDEST` (2899 for eight
                         limbs, 3032 for four) to pc 3171, with `Monpro.l1Step um q 1280 n n`.
* `gasSteps_entry n`   : E6 from pc 2895 with `[q, 2^256-1] ++ rest` to the entry `JUMPDEST`, through the
                         scratch slot `rest[1]`.
* `gasSteps_macChain n`: `gasSteps_entry` then `gasSteps_chain`.

`rest` carries the loop counter, the seventeen riding slots and the outer frame.  The riding
hypotheses: `hslot` fixes the `-N` limb slots `rest[8-i] = readWord um (1280 + 32(7-i))`
(`Shift.entrySlots` discharges them definitionally), and `hread` maintains that the running
memory still agrees with `um` below `0x840` — the blocks only ever write the `t` area.

`1280` is `Shift.NEG` (`Proofs/Fast/ShiftModel.lean`, `def NEG : Nat := 1280`, `rfl`); it is written as a
literal so that this module does not import `ShiftModel` (whose closure is `Exp`).

## Assumed from the tree (unchanged by the port), beyond `M9MacBlocks` and `M9MacRun`
* `CycleSubmission.Artifact.bytecodeSize : CycleSubmission.Artifact.bytecode.size = 5165` (`Submission/Bytecode.lean`).
* `Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding.Environment` and `Block.steps`.
* `Challenge.EvmProof.GasSteps` with `.refl`, `.trans`, `.cast`.
* `Challenge.Modexp.Submission.Proofs.Fast.SquareModel.l1Run`, `l1Run_succ`, `l1Step_eq_l1Run`
  (`l1Step mem bi pa n j = l1Run ⟨mem, UInt256.ofNat 0⟩ bi pa n 0 j`); `Monpro.l1Step`.
-/

namespace CycleSubmission.Global.Fast.M9Mac
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission.Global.Fast
open Challenge.Modexp.Submission.Proofs.Fast.M9Mac


open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached

def environment (s : State)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment CycleSubmission.Artifact.artifact .Osaka s :=
  ⟨by change CycleSubmission.Artifact.bytecode.size < 2^256
      rw [CycleSubmission.Artifact.bytecodeSize]; decide,
    hcode, hfork, hrun, hnp⟩

/-- Start pc of block `b` (`b = 8`: the exit `JUMPDEST JUMPDEST JUMPDEST`).  Blocks 0 and 4 start on their `JUMPDEST`. -/
def startPC : Nat → Nat
  | 0 => 2787
  | 1 => 2805
  | 2 => 2837
  | 3 => 2869
  | 4 => 2901
  | 5 => 2933
  | 6 => 2966
  | 7 => 2998
  | _ => 3034

/-- Entry pc of the section for width `n`: block 0 for eight limbs, block 4 (`2946 + 116`) for four. -/
def entryPC : Nat → Nat
  | 4 => 2901
  | _ => 2785

/-! ## One block -/

/-- Block `b` (`b < 8`) performs limb step `j = b + n - 8` of width `n` on any MAC state.

Blocks 0–6 reproduce their `-N` limb from the riding slot `rest[8-b]`, which `hslot` fixes to
the `um` word at `1280 + 32(7-b)` and `hread` to the running memory's word (the blocks only
write the `t` area, so the two agree throughout); block 7 `MLOAD`s its limb.  Block 0 alone
runs the `PUSH0` schedule, so it alone needs its incoming carry to be zero; `hcarry` is vacuous
for every other `b`. -/
def gasSteps_block (b : Nat) (hb : b < 8) (s : State) (m : MacState) (bi : UInt256)
    (n j : Nat) (rest : List UInt256) (hrest : rest.length ≤ 1014) (hlong : 9 ≤ rest.length)
    (um : ByteArray)
    (hread : b < 7 → MachineState.readWord m.memory (1280 + 32 * (7 - b)) =
      MachineState.readWord um (1280 + 32 * (7 - b)))
    (hslot : b < 7 → rest[8 - b]? =
      some (MachineState.readWord um (1280 + 32 * (7 - b))))
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjb : j + 8 = b + n)
    (hcarry : b = 0 → m.carry = UInt256.ofNat 0)
    (htop : b = 0 → MachineState.readWord m.memory 2336 = UInt256.ofNat 0)
    (hb1 : 1 ≤ b) :
    Challenge.EvmProof.GasSteps
      (chainState s (UInt256.ofNat (startPC b)) m bi rest)
      (chainState s (UInt256.ofNat (startPC (b + 1))) (SquareModel.l1StepOn m bi 1280 n j) bi rest) := by
  interval_cases b
  · have hsj : n - 1 - j = 7 - 1 := by omega
    have hs := hslot (by omega)
    have hr := hread (by omega)
    rw [← hr, ← hsj] at hs
    have hx : rest[(10 : Fin 16).val - 3]? =
        some (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) := hs
    have h := run_ride s (UInt256.ofNat 2805) m bi n j 2304 10
      (by rw [show n - 1 - j = 6 from by omega]; decide)
      (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) rfl
      rest hrest (by decide) (by decide) (by omega) hx hact hn (by omega)
    simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
    show Challenge.EvmProof.GasSteps (chainState s (UInt256.ofNat 2805) m bi rest)
      (chainState s (UInt256.ofNat 2837) (SquareModel.l1StepOn m bi 1280 n j) bi rest)
    exact block1.steps (environment (chainState s (UInt256.ofNat 2805) m bi rest)
      hcode hfork hrun hnp) rfl h
  · have hsj : n - 1 - j = 7 - 2 := by omega
    have hs := hslot (by omega)
    have hr := hread (by omega)
    rw [← hr, ← hsj] at hs
    have hx : rest[(9 : Fin 16).val - 3]? =
        some (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) := hs
    have h := run_ride s (UInt256.ofNat 2837) m bi n j 2272 9
      (by rw [show n - 1 - j = 5 from by omega]; decide)
      (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) rfl
      rest hrest (by decide) (by decide) (by omega) hx hact hn (by omega)
    simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
    show Challenge.EvmProof.GasSteps (chainState s (UInt256.ofNat 2837) m bi rest)
      (chainState s (UInt256.ofNat 2869) (SquareModel.l1StepOn m bi 1280 n j) bi rest)
    exact block2.steps (environment (chainState s (UInt256.ofNat 2837) m bi rest)
      hcode hfork hrun hnp) rfl h
  · have hsj : n - 1 - j = 7 - 3 := by omega
    have hs := hslot (by omega)
    have hr := hread (by omega)
    rw [← hr, ← hsj] at hs
    have hx : rest[(8 : Fin 16).val - 3]? =
        some (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) := hs
    have h := run_ride s (UInt256.ofNat 2869) m bi n j 2240 8
      (by rw [show n - 1 - j = 4 from by omega]; decide)
      (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) rfl
      rest hrest (by decide) (by decide) (by omega) hx hact hn (by omega)
    simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
    show Challenge.EvmProof.GasSteps (chainState s (UInt256.ofNat 2869) m bi rest)
      (chainState s (UInt256.ofNat 2901) (SquareModel.l1StepOn m bi 1280 n j) bi rest)
    exact block3.steps (environment (chainState s (UInt256.ofNat 2869) m bi rest)
      hcode hfork hrun hnp) rfl h
  · have hsj : n - 1 - j = 7 - 4 := by omega
    have hs := hslot (by omega)
    have hr := hread (by omega)
    rw [← hr, ← hsj] at hs
    have hx : rest[(7 : Fin 16).val - 3]? =
        some (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) := hs
    have h := run_ride s (UInt256.ofNat 2901) m bi n j 2208 7
      (by rw [show n - 1 - j = 3 from by omega]; decide)
      (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) rfl
      rest hrest (by decide) (by decide) (by omega) hx hact hn (by omega)
    simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
    show Challenge.EvmProof.GasSteps (chainState s (UInt256.ofNat 2901) m bi rest)
      (chainState s (UInt256.ofNat 2933) (SquareModel.l1StepOn m bi 1280 n j) bi rest)
    exact block4.steps (environment (chainState s (UInt256.ofNat 2901) m bi rest)
      hcode hfork hrun hnp) rfl h
  · have hsj : n - 1 - j = 7 - 5 := by omega
    have hs := hslot (by omega)
    have hr := hread (by omega)
    rw [← hr, ← hsj] at hs
    have hx : rest[(6 : Fin 16).val - 3]? =
        some (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) := hs
    have h := run_ride_head s (UInt256.ofNat 2933) m bi n j 2176 6
      (by rw [show n - 1 - j = 2 from by omega]; decide)
      (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) rfl
      rest hrest (by decide) (by decide) (by omega) hx hact hn (by omega)
    simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
    show Challenge.EvmProof.GasSteps (chainState s (UInt256.ofNat 2933) m bi rest)
      (chainState s (UInt256.ofNat 2966) (SquareModel.l1StepOn m bi 1280 n j) bi rest)
    exact block5.steps (environment (chainState s (UInt256.ofNat 2933) m bi rest)
      hcode hfork hrun hnp) rfl h
  · have hsj : n - 1 - j = 7 - 6 := by omega
    have hs := hslot (by omega)
    have hr := hread (by omega)
    rw [← hr, ← hsj] at hs
    have hx : rest[(5 : Fin 16).val - 3]? =
        some (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) := hs
    have h := run_ride s (UInt256.ofNat 2966) m bi n j 2144 5
      (by rw [show n - 1 - j = 1 from by omega]; decide)
      (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) rfl
      rest hrest (by decide) (by decide) (by omega) hx hact hn (by omega)
    simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
    show Challenge.EvmProof.GasSteps (chainState s (UInt256.ofNat 2966) m bi rest)
      (chainState s (UInt256.ofNat 2998) (SquareModel.l1StepOn m bi 1280 n j) bi rest)
    exact block6.steps (environment (chainState s (UInt256.ofNat 2966) m bi rest)
      hcode hfork hrun hnp) rfl h
  · have h := run_block s (UInt256.ofNat 2998) m bi 1280 n j 1280 2112
      (by rw [show n - 1 - j = 0 from by omega]; decide)
      (by rw [show n - 1 - j = 0 from by omega]; decide)
      rest hrest hact (by omega) hn (by omega)
    simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
    show Challenge.EvmProof.GasSteps (chainState s (UInt256.ofNat 2998) m bi rest)
      (chainState s (UInt256.ofNat 3034) (SquareModel.l1StepOn m bi 1280 n j) bi rest)
    exact block7.steps (environment (chainState s (UInt256.ofNat 2998) m bi rest)
      hcode hfork hrun hnp) rfl h

/-! ## The chain -/

/-- Peel the first step off a run. -/
theorem l1Run_succ_left (q : MacState) (bi : UInt256) (pa n j : Nat) :
    ∀ m, SquareModel.l1Run q bi pa n j (m + 1) =
      SquareModel.l1Run (SquareModel.l1StepOn q bi pa n j) bi pa n (j + 1) m
  | 0 => rfl
  | m + 1 => by
      rw [SquareModel.l1Run_succ, l1Run_succ_left q bi pa n j m, SquareModel.l1Run_succ]
      congr 1
      omega

/-- Blocks `b..7` (`b + m = 8`) from the start of block `b` to the exit at pc 3168. -/
def gasSteps_run : (m b : Nat) → b + m = 8 →
    (s : State) → (q : MacState) → (bi : UInt256) → (n j : Nat) → (rest : List UInt256) →
    (um : ByteArray) → rest.length ≤ 1014 → 9 ≤ rest.length →
    (∀ i : Nat, i < 7 → rest[8 - i]? =
      some (MachineState.readWord um (1280 + 32 * (7 - i)))) →
    (∀ i : Nat, i < 7 → MachineState.readWord q.memory (1280 + 32 * (7 - i)) =
      MachineState.readWord um (1280 + 32 * (7 - i))) →
    s.halt = .Running →
    s.executionEnv.code = CycleSubmission.Artifact.bytecode →
    s.fork = .Osaka →
    Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false →
    88 ≤ s.activeWords.toNat → n ≤ 8 → j + 8 = b + n →
    (b = 0 → q.carry = UInt256.ofNat 0) →
    (b = 0 → MachineState.readWord q.memory 2336 = UInt256.ofNat 0) →
    1 ≤ b →
    Challenge.EvmProof.GasSteps
      (chainState s (UInt256.ofNat (startPC b)) q bi rest)
      (chainState s (UInt256.ofNat 3034) (SquareModel.l1Run q bi 1280 n j m) bi rest)
  | 0, b, hbm, s, q, bi, n, j, rest, um, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
      obtain rfl : b = 8 := by omega
      exact Challenge.EvmProof.GasSteps.refl _
  | m + 1, b, hbm, s, q, bi, n, j, rest, um, hrest, hlong, hslot, hread, hrun, hcode, hfork,
      hnp, hact, hn, hjb, hcarry, htop, hb1 => by
      have h1 := gasSteps_block b (by omega) s q bi n j rest hrest hlong um
        (fun hb => hread b hb) (fun hb => hslot b hb)
        hrun hcode hfork hnp hact hn hjb hcarry htop hb1
      have hread' : ∀ i : Nat, i < 7 →
          MachineState.readWord (SquareModel.l1StepOn q bi 1280 n j).memory (1280 + 32 * (7 - i)) =
          MachineState.readWord um (1280 + 32 * (7 - i)) := by
        intro i hi
        rw [l1StepOn_readWord_below q bi 1280 n j (1280 + 32 * (7 - i)) (by omega)]
        exact hread i hi
      have h2 := gasSteps_run m (b + 1) (by omega) s (SquareModel.l1StepOn q bi 1280 n j) bi
        n (j + 1) rest um hrest hlong hslot hread' hrun hcode hfork hnp hact hn (by omega)
        (fun h => absurd h (by omega)) (fun h => absurd h (by omega)) (by omega)
      rw [← l1Run_succ_left] at h2
      exact h1.trans h2

/-- Start pc of the four-limb private copies of blocks 5..7 (`8`: the private middle block). -/
def startPCC : Nat → Nat
  | 5 => 10845
  | 6 => 10877
  | 7 => 10909
  | _ => 10945

/-- `gasSteps_block` for the private copies of blocks 5..7. -/
def gasSteps_blockC (b : Nat) (hb : b < 8) (hb5 : 5 ≤ b) (s : State) (m : MacState) (bi : UInt256)
    (n j : Nat) (rest : List UInt256) (hrest : rest.length ≤ 1014) (hlong : 9 ≤ rest.length)
    (um : ByteArray)
    (hread : b < 7 → MachineState.readWord m.memory (1280 + 32 * (7 - b)) =
      MachineState.readWord um (1280 + 32 * (7 - b)))
    (hslot : b < 7 → rest[8 - b]? =
      some (MachineState.readWord um (1280 + 32 * (7 - b))))
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjb : j + 8 = b + n)
    (hcarry : b = 0 → m.carry = UInt256.ofNat 0)
    (htop : b = 0 → MachineState.readWord m.memory 2336 = UInt256.ofNat 0)
    (hb1 : 1 ≤ b) :
    Challenge.EvmProof.GasSteps
      (chainState s (UInt256.ofNat (startPCC b)) m bi rest)
      (chainState s (UInt256.ofNat (startPCC (b + 1))) (SquareModel.l1StepOn m bi 1280 n j) bi rest) := by
  interval_cases b
  · have hsj : n - 1 - j = 7 - 5 := by omega
    have hs := hslot (by omega)
    have hr := hread (by omega)
    rw [← hr, ← hsj] at hs
    have hx : rest[(6 : Fin 16).val - 3]? =
        some (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) := hs
    have h := run_ride s (UInt256.ofNat 10845) m bi n j 2176 6
      (by rw [show n - 1 - j = 2 from by omega]; decide)
      (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) rfl
      rest hrest (by decide) (by decide) (by omega) hx hact hn (by omega)
    simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
    show Challenge.EvmProof.GasSteps (chainState s (UInt256.ofNat 10845) m bi rest)
      (chainState s (UInt256.ofNat 10877) (SquareModel.l1StepOn m bi 1280 n j) bi rest)
    exact block5c.steps (environment (chainState s (UInt256.ofNat 10845) m bi rest)
      hcode hfork hrun hnp) rfl h
  · have hsj : n - 1 - j = 7 - 6 := by omega
    have hs := hslot (by omega)
    have hr := hread (by omega)
    rw [← hr, ← hsj] at hs
    have hx : rest[(5 : Fin 16).val - 3]? =
        some (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) := hs
    have h := run_ride s (UInt256.ofNat 10877) m bi n j 2144 5
      (by rw [show n - 1 - j = 1 from by omega]; decide)
      (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) rfl
      rest hrest (by decide) (by decide) (by omega) hx hact hn (by omega)
    simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
    show Challenge.EvmProof.GasSteps (chainState s (UInt256.ofNat 10877) m bi rest)
      (chainState s (UInt256.ofNat 10909) (SquareModel.l1StepOn m bi 1280 n j) bi rest)
    exact block6c.steps (environment (chainState s (UInt256.ofNat 10877) m bi rest)
      hcode hfork hrun hnp) rfl h
  · have h := run_block s (UInt256.ofNat 10909) m bi 1280 n j 1280 2112
      (by rw [show n - 1 - j = 0 from by omega]; decide)
      (by rw [show n - 1 - j = 0 from by omega]; decide)
      rest hrest hact (by omega) hn (by omega)
    simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
    show Challenge.EvmProof.GasSteps (chainState s (UInt256.ofNat 10909) m bi rest)
      (chainState s (UInt256.ofNat 10945) (SquareModel.l1StepOn m bi 1280 n j) bi rest)
    exact block7c.steps (environment (chainState s (UInt256.ofNat 10909) m bi rest)
      hcode hfork hrun hnp) rfl h

def gasSteps_runC : (m b : Nat) → b + m = 8 →
    (s : State) → (q : MacState) → (bi : UInt256) → (n j : Nat) → (rest : List UInt256) →
    (um : ByteArray) → rest.length ≤ 1014 → 9 ≤ rest.length →
    (∀ i : Nat, i < 7 → rest[8 - i]? =
      some (MachineState.readWord um (1280 + 32 * (7 - i)))) →
    (∀ i : Nat, i < 7 → MachineState.readWord q.memory (1280 + 32 * (7 - i)) =
      MachineState.readWord um (1280 + 32 * (7 - i))) →
    s.halt = .Running →
    s.executionEnv.code = CycleSubmission.Artifact.bytecode →
    s.fork = .Osaka →
    Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false →
    88 ≤ s.activeWords.toNat → n ≤ 8 → j + 8 = b + n →
    (b = 0 → q.carry = UInt256.ofNat 0) →
    (b = 0 → MachineState.readWord q.memory 2336 = UInt256.ofNat 0) →
    1 ≤ b → 5 ≤ b →
    Challenge.EvmProof.GasSteps
      (chainState s (UInt256.ofNat (startPCC b)) q bi rest)
      (chainState s (UInt256.ofNat 10945) (SquareModel.l1Run q bi 1280 n j m) bi rest)
  | 0, b, hbm, s, q, bi, n, j, rest, um, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
      obtain rfl : b = 8 := by omega
      exact Challenge.EvmProof.GasSteps.refl _
  | m + 1, b, hbm, s, q, bi, n, j, rest, um, hrest, hlong, hslot, hread, hrun, hcode, hfork,
      hnp, hact, hn, hjb, hcarry, htop, hb1, hb5 => by
      have h1 := gasSteps_blockC b (by omega) hb5 s q bi n j rest hrest hlong um
        (fun hb => hread b hb) (fun hb => hslot b hb)
        hrun hcode hfork hnp hact hn hjb hcarry htop hb1
      have hread' : ∀ i : Nat, i < 7 →
          MachineState.readWord (SquareModel.l1StepOn q bi 1280 n j).memory (1280 + 32 * (7 - i)) =
          MachineState.readWord um (1280 + 32 * (7 - i)) := by
        intro i hi
        rw [l1StepOn_readWord_below q bi 1280 n j (1280 + 32 * (7 - i)) (by omega)]
        exact hread i hi
      have h2 := gasSteps_runC m (b + 1) (by omega) s (SquareModel.l1StepOn q bi 1280 n j) bi
        n (j + 1) rest um hrest hlong hslot hread' hrun hcode hfork hnp hact hn (by omega)
        (fun h => absurd h (by omega)) (fun h => absurd h (by omega)) (by omega) (by omega)
      rw [← l1Run_succ_left] at h2
      exact h1.trans h2


/-- `JUMPDEST JUMPDEST JUMPDEST` at pc 3168, falling into pc 3171 with the chain frame untouched. -/
def gasSteps_exit (s : State) (q : MacState) (bi : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1014) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (chainState s (UInt256.ofNat 3034) q bi rest)
      (chainState s (UInt256.ofNat 3034) q bi rest) :=
  exitBlock.steps (environment (chainState s (UInt256.ofNat 3034) q bi rest) hcode hfork hrun hnp) rfl
    (run_exit s (UInt256.ofNat 3034) q bi rest hrest)

/-- The section entry pc of the width: the eight-limb loop head falls straight into block 0's
first product at 2787; the four-limb loop head ends in its own zero-carry first product at 10827. -/
def sectionPC (n : Nat) : Nat := if n = 4 then 10827 else 2787

/-- The section exit: the middle block of the width (the four-limb copy at 10945). -/
def sectionEndPC (n : Nat) : Nat := if n = 4 then 10945 else 3034

/-- Block 0 entered from the loop head without a carry on the stack (pc 2787 to 2805). -/
def gasSteps_block0 (s : State) (um : ByteArray) (q : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1014) (hlong : 9 ≤ rest.length)
    (hslot : ∀ i : Nat, i < 7 → rest[8 - i]? =
      some (MachineState.readWord um (1280 + 32 * (7 - i))))
    (htop : MachineState.readWord um 2336 = UInt256.ofNat 0)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.GasSteps
      (setupState s (UInt256.ofNat 2787) um q (maxWord :: rest))
      (chainState s (UInt256.ofNat 2805) (SquareModel.l1StepOn ⟨um, UInt256.ofNat 0⟩ q 1280 8 0) q rest) := by
  have hs := hslot 0 (by omega)
  have hx : rest[(10 : Fin 16).val - 2]? =
      some (MachineState.readWord (⟨um, UInt256.ofNat 0⟩ : MacState).memory (1280 + 32 * (8 - 1 - 0))) := hs
  have h := run_ride_top_np s (UInt256.ofNat 2787) ⟨um, UInt256.ofNat 0⟩ q 8 0 2336 10
      (by decide) (MachineState.readWord um (1280 + 32 * (8 - 1 - 0))) rfl
      rest hrest (by decide) (by omega) hx (by decide) hact (by decide) (by decide) rfl
      (by simpa using htop)
  simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
  exact block0.steps (environment (setupState s (UInt256.ofNat 2787) um q (maxWord :: rest))
    hcode hfork hrun hnp) rfl h

/-- The four-limb loop head's own first product (limb 3, `t` top 2208, zero carry; pc 10827) and
falls into its private copies of blocks 5..7 (pc 10845). -/
def gasSteps_zero4 (s : State) (um : ByteArray) (q : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1014) (hlong : 9 ≤ rest.length)
    (hslot : ∀ i : Nat, i < 7 → rest[8 - i]? =
      some (MachineState.readWord um (1280 + 32 * (7 - i))))
    (htop : MachineState.readWord um 2208 = UInt256.ofNat 0)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.GasSteps
      (setupState s (UInt256.ofNat 10827) um q (maxWord :: rest))
      (chainState s (UInt256.ofNat 10845) (SquareModel.l1StepOn ⟨um, UInt256.ofNat 0⟩ q 1280 4 0) q rest) := by
  have hs := hslot 4 (by omega)
  have hx : rest[(6 : Fin 16).val - 2]? =
      some (MachineState.readWord (⟨um, UInt256.ofNat 0⟩ : MacState).memory (1280 + 32 * (4 - 1 - 0))) := hs
  have h := run_ride_top_np s (UInt256.ofNat 10827) ⟨um, UInt256.ofNat 0⟩ q 4 0 2208 6
      (by decide) (MachineState.readWord um (1280 + 32 * (4 - 1 - 0))) rfl
      rest hrest (by decide) (by omega) hx (by decide) hact (by decide) (by decide) rfl
      (by simpa using htop)
  simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
  exact zero4Block.steps (environment (setupState s (UInt256.ofNat 10827) um q (maxWord :: rest))
    hcode hfork hrun hnp) rfl h

/-- **The section.**  For `n = 4 ∨ n = 8`, from the section entry (`sectionPC n`) with the frame
`[q, 2^256-1] ++ rest` over `um` to pc 3034 with `[carry, q, 2^256-1] ++ rest`, where memory and
carry are `Monpro.l1Step um q 1280 n n`. -/
def gasSteps_macChain (n : Nat) (hn : n = 4 ∨ n = 8) (s : State) (um : ByteArray) (q : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1014) (hlong : 9 ≤ rest.length)
    (hslot : ∀ i : Nat, i < 7 → rest[8 - i]? =
      some (MachineState.readWord um (1280 + 32 * (7 - i))))
    (htop : n = 8 → MachineState.readWord um 2336 = UInt256.ofNat 0)
    (htop4 : n = 4 → MachineState.readWord um 2208 = UInt256.ofNat 0)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.GasSteps
      (setupState s (UInt256.ofNat (sectionPC n)) um q (maxWord :: rest))
      (chainState s (UInt256.ofNat (sectionEndPC n)) (l1Step um q 1280 n n) q rest) :=
  if h4 : n = 4 then by
    subst h4
    have hz := gasSteps_zero4 s um q rest hrest hlong hslot (htop4 rfl) hrun hcode hfork hnp hact
    have hread : ∀ i : Nat, i < 7 →
        MachineState.readWord (SquareModel.l1StepOn ⟨um, UInt256.ofNat 0⟩ q 1280 4 0).memory
          (1280 + 32 * (7 - i)) = MachineState.readWord um (1280 + 32 * (7 - i)) := by
      intro i hi
      rw [l1StepOn_readWord_below ⟨um, UInt256.ofNat 0⟩ q 1280 4 0 (1280 + 32 * (7 - i)) (by omega)]
    have hr := gasSteps_runC 3 5 rfl s (SquareModel.l1StepOn ⟨um, UInt256.ofNat 0⟩ q 1280 4 0) q 4 (0 + 1)
      rest um hrest hlong hslot hread hrun hcode hfork hnp hact (by decide) rfl
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (by decide) (by decide)
    rw [← l1Run_succ_left] at hr
    have hE : sectionEndPC 4 = 10945 := rfl
    rw [hE]
    exact (hz.trans hr).cast rfl (by rw [SquareModel.l1Step_eq_l1Run])
  else by
    have h8 : n = 8 := by omega
    subst h8
    have hb0 := gasSteps_block0 s um q rest hrest hlong hslot (htop rfl) hrun hcode hfork hnp hact
    have hread : ∀ i : Nat, i < 7 →
        MachineState.readWord (SquareModel.l1StepOn ⟨um, UInt256.ofNat 0⟩ q 1280 8 0).memory
          (1280 + 32 * (7 - i)) = MachineState.readWord um (1280 + 32 * (7 - i)) := by
      intro i hi
      rw [l1StepOn_readWord_below ⟨um, UInt256.ofNat 0⟩ q 1280 8 0 (1280 + 32 * (7 - i)) (by omega)]
    have hr := gasSteps_run 7 1 rfl s (SquareModel.l1StepOn ⟨um, UInt256.ofNat 0⟩ q 1280 8 0) q 8 (0 + 1)
      rest um hrest hlong hslot hread hrun hcode hfork hnp hact (by decide) rfl
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (by decide)
    rw [← l1Run_succ_left] at hr
    have hE : sectionEndPC 8 = 3034 := rfl
    rw [hE]
    exact ((hb0.trans hr).trans (gasSteps_exit s _ q rest hrest hrun hcode hfork hnp)).cast rfl
      (by rw [SquareModel.l1Step_eq_l1Run])

end CycleSubmission.Global.Fast.M9Mac
