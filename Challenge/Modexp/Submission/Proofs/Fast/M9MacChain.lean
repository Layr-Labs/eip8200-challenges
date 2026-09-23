import Challenge.Modexp.Submission.Proofs.Fast.M9MacBlocks
import Challenge.Modexp.Submission.Proofs.Fast.M9MacRun

set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 40000

/-!
# M9: gas traces of the straight MAC chain

* `gasSteps_block b`  : one block on any MAC state (the `KernelChain.gasSteps_l1Step` shape).
* `gasSteps_run m b`   : blocks `b..7` (`b + m = 8`) from the start of block `b` to the exit at pc 3168,
                         producing `SquareModel.l1Run q bi 1280 n j m` (the `gasSteps_l1Run` recursion).
* `gasSteps_exit`      : `SWAP1 SWAP2 POP`, pc 3168 → 3171 (the unchanged top-limb fixup).
* `gasSteps_chain n`   : the whole section for `n = 4 ∨ n = 8` from the entry `JUMPDEST` (2899 for eight
                         limbs, 3032 for four) to pc 3171, with `Monpro.l1Step um q 1280 n n`.
* `gasSteps_entry n`   : E6 from pc 2893 with `[q] ++ rest` to the entry `JUMPDEST`, through the
                         scratch slot `rest[1]`.
* `gasSteps_macChain n`: `gasSteps_entry` then `gasSteps_chain`.

`rest` carries the loop counter, the seventeen riding slots and the outer frame.  The riding
hypotheses: `hslot` fixes the `-N` limb slots `rest[8-i] = readWord um (1280 + 32(7-i))`
(`Shift.entrySlots` discharges them definitionally), and `hread` maintains that the running
memory still agrees with `um` below `0x840` — the blocks only ever write the `t` area.

`1280` is `Shift.NEG` (`Proofs/Fast/ShiftModel.lean`, `def NEG : Nat := 1280`, `rfl`); it is written as a
literal so that this module does not import `ShiftModel` (whose closure is `Exp`).

## Assumed from the tree (unchanged by the port), beyond `M9MacBlocks` and `M9MacRun`
* `Challenge.Modexp.submissionBytecode_size : submissionBytecode.size = 5165` (`Submission/Bytecode.lean`).
* `Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding.Environment` and `Block.steps`.
* `Challenge.EvmProof.GasSteps` with `.refl`, `.trans`, `.cast`.
* `Challenge.Modexp.Submission.Proofs.Fast.SquareModel.l1Run`, `l1Run_succ`, `l1Step_eq_l1Run`
  (`l1Step mem bi pa n j = l1Run ⟨mem, UInt256.ofNat 0⟩ bi pa n 0 j`); `Monpro.l1Step`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.M9Mac

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256
      rw [Challenge.Modexp.submissionBytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩

/-- Start pc of block `b` (`b = 8`: the exit `SWAP1 SWAP2 POP`).  Blocks 0 and 4 start on their `JUMPDEST`. -/
def startPC : Nat → Nat
  | 0 => 2899
  | 1 => 2933
  | 2 => 2966
  | 3 => 2999
  | 4 => 3032
  | 5 => 3066
  | 6 => 3099
  | 7 => 3132
  | _ => 3168

/-- Entry pc of the section for width `n`: block 0 for eight limbs, block 4 (`2899 + 133`) for four. -/
def entryPC : Nat → Nat
  | 4 => 3032
  | _ => 2899

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
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hjb : j + 8 = b + n)
    (hcarry : b = 0 → m.carry = UInt256.ofNat 0) :
    Challenge.EvmProof.GasSteps
      (chainState s (UInt256.ofNat (startPC b)) m bi rest)
      (chainState s (UInt256.ofNat (startPC (b + 1))) (SquareModel.l1StepOn m bi 1280 n j) bi rest) := by
  interval_cases b
  · have hsj : n - 1 - j = 7 - 0 := by omega
    have hs := hslot (by omega)
    have hr := hread (by omega)
    rw [← hr, ← hsj] at hs
    have hx : rest[(11 : Fin 16).val - 3]? =
        some (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) := hs
    have hd3b : 3 ≤ (11 : Fin 16).val := by decide
    have hinb : (11 : Fin 16).val < 3 + rest.length := by omega
    have hjb2 : j < n := by omega
    have h := run_ride_zero_head s (UInt256.ofNat 2899) m bi n j 2336 11
      (by rw [show n - 1 - j = 7 from by omega]; decide)
      (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) rfl
      rest hrest hd3b hinb hx hact hn hjb2 (hcarry rfl)
    simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
    show Challenge.EvmProof.GasSteps (chainState s (UInt256.ofNat 2899) m bi rest)
      (chainState s (UInt256.ofNat 2933) (SquareModel.l1StepOn m bi 1280 n j) bi rest)
    exact block0.steps (environment (chainState s (UInt256.ofNat 2899) m bi rest)
      hcode hfork hrun hnp) rfl h
  · have hsj : n - 1 - j = 7 - 1 := by omega
    have hs := hslot (by omega)
    have hr := hread (by omega)
    rw [← hr, ← hsj] at hs
    have hx : rest[(10 : Fin 16).val - 3]? =
        some (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) := hs
    have h := run_ride s (UInt256.ofNat 2933) m bi n j 2304 10
      (by rw [show n - 1 - j = 6 from by omega]; decide)
      (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) rfl
      rest hrest (by decide) (by omega) hx hact hn (by omega)
    simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
    show Challenge.EvmProof.GasSteps (chainState s (UInt256.ofNat 2933) m bi rest)
      (chainState s (UInt256.ofNat 2966) (SquareModel.l1StepOn m bi 1280 n j) bi rest)
    exact block1.steps (environment (chainState s (UInt256.ofNat 2933) m bi rest)
      hcode hfork hrun hnp) rfl h
  · have hsj : n - 1 - j = 7 - 2 := by omega
    have hs := hslot (by omega)
    have hr := hread (by omega)
    rw [← hr, ← hsj] at hs
    have hx : rest[(9 : Fin 16).val - 3]? =
        some (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) := hs
    have h := run_ride s (UInt256.ofNat 2966) m bi n j 2272 9
      (by rw [show n - 1 - j = 5 from by omega]; decide)
      (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) rfl
      rest hrest (by decide) (by omega) hx hact hn (by omega)
    simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
    show Challenge.EvmProof.GasSteps (chainState s (UInt256.ofNat 2966) m bi rest)
      (chainState s (UInt256.ofNat 2999) (SquareModel.l1StepOn m bi 1280 n j) bi rest)
    exact block2.steps (environment (chainState s (UInt256.ofNat 2966) m bi rest)
      hcode hfork hrun hnp) rfl h
  · have hsj : n - 1 - j = 7 - 3 := by omega
    have hs := hslot (by omega)
    have hr := hread (by omega)
    rw [← hr, ← hsj] at hs
    have hx : rest[(8 : Fin 16).val - 3]? =
        some (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) := hs
    have h := run_ride s (UInt256.ofNat 2999) m bi n j 2240 8
      (by rw [show n - 1 - j = 4 from by omega]; decide)
      (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) rfl
      rest hrest (by decide) (by omega) hx hact hn (by omega)
    simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
    show Challenge.EvmProof.GasSteps (chainState s (UInt256.ofNat 2999) m bi rest)
      (chainState s (UInt256.ofNat 3032) (SquareModel.l1StepOn m bi 1280 n j) bi rest)
    exact block3.steps (environment (chainState s (UInt256.ofNat 2999) m bi rest)
      hcode hfork hrun hnp) rfl h
  · have hsj : n - 1 - j = 7 - 4 := by omega
    have hs := hslot (by omega)
    have hr := hread (by omega)
    rw [← hr, ← hsj] at hs
    have hx : rest[(7 : Fin 16).val - 3]? =
        some (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) := hs
    have h := run_ride_head s (UInt256.ofNat 3032) m bi n j 2208 7
      (by rw [show n - 1 - j = 3 from by omega]; decide)
      (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) rfl
      rest hrest (by decide) (by omega) hx hact hn (by omega)
    simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
    show Challenge.EvmProof.GasSteps (chainState s (UInt256.ofNat 3032) m bi rest)
      (chainState s (UInt256.ofNat 3066) (SquareModel.l1StepOn m bi 1280 n j) bi rest)
    exact block4.steps (environment (chainState s (UInt256.ofNat 3032) m bi rest)
      hcode hfork hrun hnp) rfl h
  · have hsj : n - 1 - j = 7 - 5 := by omega
    have hs := hslot (by omega)
    have hr := hread (by omega)
    rw [← hr, ← hsj] at hs
    have hx : rest[(6 : Fin 16).val - 3]? =
        some (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) := hs
    have h := run_ride s (UInt256.ofNat 3066) m bi n j 2176 6
      (by rw [show n - 1 - j = 2 from by omega]; decide)
      (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) rfl
      rest hrest (by decide) (by omega) hx hact hn (by omega)
    simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
    show Challenge.EvmProof.GasSteps (chainState s (UInt256.ofNat 3066) m bi rest)
      (chainState s (UInt256.ofNat 3099) (SquareModel.l1StepOn m bi 1280 n j) bi rest)
    exact block5.steps (environment (chainState s (UInt256.ofNat 3066) m bi rest)
      hcode hfork hrun hnp) rfl h
  · have hsj : n - 1 - j = 7 - 6 := by omega
    have hs := hslot (by omega)
    have hr := hread (by omega)
    rw [← hr, ← hsj] at hs
    have hx : rest[(5 : Fin 16).val - 3]? =
        some (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) := hs
    have h := run_ride s (UInt256.ofNat 3099) m bi n j 2144 5
      (by rw [show n - 1 - j = 1 from by omega]; decide)
      (MachineState.readWord m.memory (1280 + 32 * (n - 1 - j))) rfl
      rest hrest (by decide) (by omega) hx hact hn (by omega)
    simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
    show Challenge.EvmProof.GasSteps (chainState s (UInt256.ofNat 3099) m bi rest)
      (chainState s (UInt256.ofNat 3132) (SquareModel.l1StepOn m bi 1280 n j) bi rest)
    exact block6.steps (environment (chainState s (UInt256.ofNat 3099) m bi rest)
      hcode hfork hrun hnp) rfl h
  · have h := run_block s (UInt256.ofNat 3132) m bi 1280 n j 1280 2112
      (by rw [show n - 1 - j = 0 from by omega]; decide)
      (by rw [show n - 1 - j = 0 from by omega]; decide)
      rest hrest hact (by omega) hn (by omega)
    simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
    show Challenge.EvmProof.GasSteps (chainState s (UInt256.ofNat 3132) m bi rest)
      (chainState s (UInt256.ofNat 3168) (SquareModel.l1StepOn m bi 1280 n j) bi rest)
    exact block7.steps (environment (chainState s (UInt256.ofNat 3132) m bi rest)
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
    s.executionEnv.code = Challenge.Modexp.submissionBytecode →
    s.fork = .Osaka →
    Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false →
    88 ≤ s.activeWords.toNat → n ≤ 8 → j + 8 = b + n →
    (b = 0 → q.carry = UInt256.ofNat 0) →
    Challenge.EvmProof.GasSteps
      (chainState s (UInt256.ofNat (startPC b)) q bi rest)
      (chainState s (UInt256.ofNat 3168) (SquareModel.l1Run q bi 1280 n j m) bi rest)
  | 0, b, hbm, s, q, bi, n, j, rest, um, _, _, _, _, _, _, _, _, _, _, _, _ => by
      obtain rfl : b = 8 := by omega
      exact Challenge.EvmProof.GasSteps.refl _
  | m + 1, b, hbm, s, q, bi, n, j, rest, um, hrest, hlong, hslot, hread, hrun, hcode, hfork,
      hnp, hact, hn, hjb, hcarry => by
      have h1 := gasSteps_block b (by omega) s q bi n j rest hrest hlong um
        (fun hb => hread b hb) (fun hb => hslot b hb)
        hrun hcode hfork hnp hact hn hjb hcarry
      have hread' : ∀ i : Nat, i < 7 →
          MachineState.readWord (SquareModel.l1StepOn q bi 1280 n j).memory (1280 + 32 * (7 - i)) =
          MachineState.readWord um (1280 + 32 * (7 - i)) := by
        intro i hi
        rw [l1StepOn_readWord_below q bi 1280 n j (1280 + 32 * (7 - i)) (by omega)]
        exact hread i hi
      have h2 := gasSteps_run m (b + 1) (by omega) s (SquareModel.l1StepOn q bi 1280 n j) bi
        n (j + 1) rest um hrest hlong hslot hread' hrun hcode hfork hnp hact hn (by omega)
        (fun h => absurd h (by omega))
      rw [← l1Run_succ_left] at h2
      exact h1.trans h2

/-- `SWAP1 SWAP2 POP` at pc 3168, falling into pc 3171. -/
def gasSteps_exit (s : State) (q : MacState) (bi : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1014) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (chainState s (UInt256.ofNat 3168) q bi rest)
      (exitState s (UInt256.ofNat 3171) q bi rest) :=
  exitBlock.steps (environment (chainState s (UInt256.ofNat 3168) q bi rest) hcode hfork hrun hnp) rfl
    (by simpa only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] using
      run_exit s (UInt256.ofNat 3168) q bi rest hrest)

/-- **The section.**  For `n = 4 ∨ n = 8`, from the entry `JUMPDEST` (`entryPC n`) with the frame
`[0, q, 2^256-1] ++ rest` over `um` to pc 3171 with `[carry, q] ++ rest`, where memory and carry are
`Monpro.l1Step um q 1280 n n`. -/
def gasSteps_chain (n : Nat) (hn : n = 4 ∨ n = 8) (s : State) (um : ByteArray) (q : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1014) (hlong : 9 ≤ rest.length)
    (hslot : ∀ i : Nat, i < 7 → rest[8 - i]? =
      some (MachineState.readWord um (1280 + 32 * (7 - i))))
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.GasSteps
      (chainState s (UInt256.ofNat (entryPC n)) ⟨um, UInt256.ofNat 0⟩ q rest)
      (exitState s (UInt256.ofNat 3171) (l1Step um q 1280 n n) q rest) :=
  if h4 : n = 4 then by
    subst h4
    exact ((gasSteps_run 4 4 rfl s ⟨um, UInt256.ofNat 0⟩ q 4 0 rest um hrest hlong hslot
        (fun _ _ => rfl)
        hrun hcode hfork hnp hact (by decide) rfl (fun _ => rfl)).trans
      (gasSteps_exit s _ q rest hrest hrun hcode hfork hnp)).cast rfl
      (by rw [SquareModel.l1Step_eq_l1Run])
  else by
    have h8 : n = 8 := by omega
    subst h8
    exact ((gasSteps_run 8 0 rfl s ⟨um, UInt256.ofNat 0⟩ q 8 0 rest um hrest hlong hslot
        (fun _ _ => rfl)
        hrun hcode hfork hnp hact (by decide) rfl (fun _ => rfl)).trans
      (gasSteps_exit s _ q rest hrest hrun hcode hfork hnp)).cast rfl
      (by rw [SquareModel.l1Step_eq_l1Run])

/-! ## The E6 entry -/

/-- Both entries are jump destinations. -/
theorem jumpDest_entry (n : Nat) (hn : n = 4 ∨ n = 8) :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (entryPC n) = true := by
  rcases hn with rfl | rfl
  · exact jumpDest3032
  · exact jumpDest2899

/-- E6 at pc 2893: `[q] ++ rest` over `um` to the chain frame at the entry parked in the
scratch slot `rest[1]`. -/
def gasSteps_entry (n : Nat) (hn : n = 4 ∨ n = 8) (s : State) (um : ByteArray) (q : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1014) (hlong : 9 ≤ rest.length)
    (hslot0 : rest[1]? = some (UInt256.ofNat (entryPC n)))
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (setupState s (UInt256.ofNat 2893) um q rest)
      (chainState s (UInt256.ofNat (entryPC n)) ⟨um, UInt256.ofNat 0⟩ q rest) :=
  entryBlock.steps (environment (setupState s (UInt256.ofNat 2893) um q rest) hcode hfork hrun hnp) rfl
    (run_entry s (UInt256.ofNat 2893) um q rest (entryPC n) hrest (by omega) hslot0
      (by rcases hn with rfl | rfl <;> decide)
      (by rw [hcode]; exact jumpDest_entry n hn))

/-- E6 followed by the section: pc 2893 with `[q] ++ rest` over `um` to pc 3171 with
`[carry, q] ++ rest` over `l1Step um q 1280 n n`. -/
def gasSteps_macChain (n : Nat) (hn : n = 4 ∨ n = 8) (s : State) (um : ByteArray) (q : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1014) (hlong : 9 ≤ rest.length)
    (hslot : ∀ i : Nat, i < 7 → rest[8 - i]? =
      some (MachineState.readWord um (1280 + 32 * (7 - i))))
    (hslot0 : rest[1]? = some (UInt256.ofNat (entryPC n)))
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.GasSteps
      (setupState s (UInt256.ofNat 2893) um q rest)
      (exitState s (UInt256.ofNat 3171) (l1Step um q 1280 n n) q rest) :=
  (gasSteps_entry n hn s um q rest hrest hlong hslot0 hrun hcode hfork hnp).trans
    (gasSteps_chain n hn s um q rest hrest hlong hslot hrun hcode hfork hnp hact)

end Challenge.Modexp.Submission.Proofs.Fast.M9Mac

#print axioms Challenge.Modexp.Submission.Proofs.Fast.M9Mac.gasSteps_block
#print axioms Challenge.Modexp.Submission.Proofs.Fast.M9Mac.gasSteps_run
#print axioms Challenge.Modexp.Submission.Proofs.Fast.M9Mac.gasSteps_exit
#print axioms Challenge.Modexp.Submission.Proofs.Fast.M9Mac.gasSteps_chain
#print axioms Challenge.Modexp.Submission.Proofs.Fast.M9Mac.gasSteps_entry
#print axioms Challenge.Modexp.Submission.Proofs.Fast.M9Mac.gasSteps_macChain
