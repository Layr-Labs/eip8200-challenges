import Challenge.Modexp.Submission.Proofs.Fast.SquarePrepared
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowGas
import Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
import Challenge.Modexp.Submission.Proofs.Fast.CarryControl

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareEntry
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore SquareInit StagedOperand SquarePrepared

theorem guard_iff (mem : ByteArray) (pa pb n : Nat) (hn : n ≤ 32)
    (hpa : pa < 2^256) (hpb : pb < 2^256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n)) :
    UInt256.isTrue (SquareSelect.guard mem (UInt256.ofNat pa) (UInt256.ofNat pb)) ↔ n = 8 ∧ pa = pb := by
  have he : 256 = 32*n ↔ n = 8 := by omega
  simp only [SquareSelect.guard, hs32, UInt256.eq, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hpa, Nat.mod_eq_of_lt hpb, Nat.mod_eq_of_lt (show 32*n < 2^256 by omega)]
  change UInt256.isTrue (UInt256.land (if 256=32*n then UInt256.ofNat 1 else UInt256.ofNat 0)
    (if pb=pa then UInt256.ofNat 1 else UInt256.ofNat 0)) ↔ _
  simp only [he]
  by_cases hn8 : n=8 <;> by_cases hp : pa=pb <;>
    simp [hn8, hp, Eq.comm, UInt256.land, UInt256.isTrue, UInt256.toNat, Fin.land] <;> decide

def args (mem : ByteArray) (pa n : Nat) (dst ret : UInt256) (rest : List UInt256) : List UInt256 :=
  MachineState.readWord mem 9440 :: MachineState.readWord mem 96 :: MachineState.readWord mem 64 ::
    MachineState.readWord mem 32 :: MachineState.readWord mem (pa+32*n-32) :: dst :: ret :: rest

def out (s : State) (mem : ByteArray) (pa pb n : Nat) (dst ret : UInt256) (rest : List UInt256) : State :=
  outState s (mpZeroed s (before mem pa pb n) n) pa pb n 0
    (MachineState.readWord mem 9376) (MachineState.readWord mem (32*n-32)) (args mem pa n dst ret rest)

def gasSteps_header (s : State) (mem : ByteArray) (pa pb n : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hn : n=4 ∨ n=8) (hpa : 32 ≤ pa) (hpafit : pa+32*n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbfit : pb+32*n ≤ 8192)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32*n-32))
    (env : Environment Artifact.submissionArtifact .Osaka s) :
    Challenge.EvmProof.GasSteps (Cios2Dispatch.dispatchState s mem pa pb dst ret rest)
      {out s mem pa pb n dst ret rest with pc := UInt256.ofNat 4160} := by
  have hn8 : n ≤ 8 := by rcases hn with rfl | rfl <;> decide
  have hn2 : 2 ≤ n := by rcases hn with rfl | rfl <;> decide
  have hdispatch : Challenge.EvmProof.GasSteps (Cios2Dispatch.dispatchState s mem pa pb dst ret rest)
      (Cios2Dispatch.specializedEntryState s mem pa pb dst ret rest) := by
    by_cases hn4 : n = 4
    · subst n
      exact Cios2Dispatch.gasSteps_dispatch4 s mem pa pb dst ret rest (by omega) env.running env.code env.forkEq env.noPrecompile hact hs32
    · have hn8 : n = 8 := hn.resolve_left hn4
      subst n
      exact Cios2Dispatch.gasSteps_dispatch8 s mem pa pb dst ret rest (by omega) env.running env.code env.forkEq env.noPrecompile hact hs32
  refine hdispatch.trans <| (SquareSelect.gasSteps_select s mem (UInt256.ofNat pa) (UInt256.ofNat pb) dst ret rest
    (by omega) hact env.code env.forkEq env.running env.noPrecompile).trans ?_
  have hread (a : Nat) (hd : a+32 ≤ 8928 ∨ 9312 ≤ a) := read_select_outside mem (UInt256.ofNat pa) (UInt256.ofNat pb) a hd
  have he := CarryRowGas.gasSteps_entry s (SquareSelect.selectedMemory mem (UInt256.ofNat pa) (UInt256.ofNat pb)) pa pb n
    dst ret rest hcap env.running env.code env.forkEq env.noPrecompile hact hn2 hn8 hpa (by omega) hpb (by omega) hcds
    ((hread 9344 (Or.inr (by decide))).trans hs32) ((hread 9408 (Or.inr (by decide))).trans hml)
  simpa only [out, args, before, inputMemory, selected, if_pos hn, CiosCached.entryState, stateAt,
    hread 9376 (Or.inr (by decide)), hread (32*n-32) (Or.inl (by omega)),
    hread 9440 (Or.inr (by decide)), hread 96 (Or.inl (by decide)),
    hread 64 (Or.inl (by decide)), hread 32 (Or.inl (by decide)),
    hread (pa+32*n-32) (Or.inl (by omega))] using he

def routerBlock : Block Artifact.submissionArtifact .Osaka 4160 SquareRoute.headerProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3141 3 4160 SquareRoute.headerProgram
    (by decide) (by rfl) (by rfl) (by decide)

def gasSteps_route (s : State) (mem : ByteArray) (route : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1022) (hact : 296 ≤ s.activeWords.toNat)
    (hr : MachineState.readWord mem 9280 = route)
    (hj : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode route.toNat = true)
    (env : Environment Artifact.submissionArtifact .Osaka s) :
    Challenge.EvmProof.GasSteps (stateAt s mem 4160 rest) (framed {s with memory := mem} route rest) :=
  routerBlock.steps (env.transfer rfl rfl) rfl
    (SquareRoute.run_header s mem route rest hcap hact hr (by rw [env.code]; exact hj))

theorem control_before (mem : ByteArray) (pa pb n : Nat) (hn : n=4 ∨ n=8)
    (hguard : ¬UInt256.isTrue (SquareSelect.guard mem (UInt256.ofNat pa) (UInt256.ofNat pb))) :
    CarryControl.Control (before mem pa pb n) := by
  have hn8 : n ≤ 8 := by rcases hn with rfl | rfl <;> decide
  simp only [before, inputMemory, selected, if_pos hn, SquareSelect.selectedMemory, if_neg hguard]
  constructor
  · rw [read_stage_outside _ _ _ _ (Or.inl (by decide)), read_storeWord_outside _ _ _ _ (Or.inl (by decide)), read_storeWord]
  · rw [read_stage_outside _ _ _ _ (Or.inr (by omega)), read_storeWord]

end Challenge.Modexp.Submission.Proofs.Fast.SquareEntry
