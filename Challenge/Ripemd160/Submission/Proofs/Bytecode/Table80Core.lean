import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80CoreAll
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTableLayout
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Tail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80WideFinalWord
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80ConsumedTerminalTail
import Mathlib.Tactic.FinCases
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Core
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired80WordRound Paired80Algorithm Table80CoreCommon

def pcs : Array Nat := #[1154, 1198, 1242, 1286, 1328, 1372, 1416, 1460, 1503, 1546, 1588, 1630, 1674, 1718, 1761, 1806, 1864, 1910, 1956, 2001, 2046, 2090, 2132, 2178, 2224, 2263, 2309, 2356, 2402, 2448, 2493, 2532, 2594, 2633, 2671, 2711, 2749, 2787, 2825, 2864, 2901, 2941, 2980, 3019, 3058, 3096, 3133, 3165, 3211, 3257, 3302, 3347, 3393, 3433, 3476, 3522, 3567, 3613, 3660, 3706, 3751, 3796, 3839, 3886, 3939, 3980, 4025, 4069, 4114, 4157, 4201, 4243, 4285, 4328, 4370, 4413, 4458, 4503, 4546, 4585, 4615]
def shapes : Array (List Reg) := #[
  [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.k, .d, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower],
  [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower],
  [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower],
  [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower],
  [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower],
  [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower],
  [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower],
  [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower],
  [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower],
  [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower],
  [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower],
  [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower],
  [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower],
  [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower],
  [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower],
  [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.k, .d, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower],
  [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower],
  [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower],
  [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower],
  [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower],
  [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower],
  [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower],
  [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower],
  [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower],
  [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower],
  [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower],
  [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower],
  [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower],
  [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower],
  [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower],
  [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower],
  [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower],
  [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower]]
def message (memory : ByteArray) (i : Nat) : UInt256 :=
  MachineState.readWord memory (10 * PairTableLayout.pairIndices[i]!)
def atRound (s : State) (i : Nat) (q : WordLane) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat pcs[i]!, stack := stack shapes[i]! q (physicalKey i) rho}

def gasSteps_step (s : State) (i : Fin 78) (q : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s i.val q rho)
      (atRound s (i.val + 1) (step i.val (message s.memory i.val) q) rho) := by
  match i with
  | ⟨0, _⟩ =>
    have gs := Table80CoreRound0.gasSteps s q (physicalKey 0) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound0.eval_physical, Table80CoreRound0.nextKey_physical] at gs
    exact gs
  | ⟨1, _⟩ =>
    have gs := Table80CoreRound1.gasSteps s q (physicalKey 1) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound1.eval_physical, Table80CoreRound1.nextKey_physical] at gs
    exact gs
  | ⟨2, _⟩ =>
    have gs := Table80CoreRound2.gasSteps s q (physicalKey 2) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound2.eval_physical, Table80CoreRound2.nextKey_physical] at gs
    exact gs
  | ⟨3, _⟩ =>
    have gs := Table80CoreRound3.gasSteps s q (physicalKey 3) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound3.eval_physical, Table80CoreRound3.nextKey_physical] at gs
    exact gs
  | ⟨4, _⟩ =>
    have gs := Table80CoreRound4.gasSteps s q (physicalKey 4) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound4.eval_physical, Table80CoreRound4.nextKey_physical] at gs
    exact gs
  | ⟨5, _⟩ =>
    have gs := Table80CoreRound5.gasSteps s q (physicalKey 5) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound5.eval_physical, Table80CoreRound5.nextKey_physical] at gs
    exact gs
  | ⟨6, _⟩ =>
    have gs := Table80CoreRound6.gasSteps s q (physicalKey 6) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound6.eval_physical, Table80CoreRound6.nextKey_physical] at gs
    exact gs
  | ⟨7, _⟩ =>
    have gs := Table80CoreRound7.gasSteps s q (physicalKey 7) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound7.eval_physical, Table80CoreRound7.nextKey_physical] at gs
    exact gs
  | ⟨8, _⟩ =>
    have gs := Table80CoreRound8.gasSteps s q (physicalKey 8) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound8.eval_physical, Table80CoreRound8.nextKey_physical] at gs
    exact gs
  | ⟨9, _⟩ =>
    have gs := Table80CoreRound9.gasSteps s q (physicalKey 9) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound9.eval_physical, Table80CoreRound9.nextKey_physical] at gs
    exact gs
  | ⟨10, _⟩ =>
    have gs := Table80CoreRound10.gasSteps s q (physicalKey 10) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound10.eval_physical, Table80CoreRound10.nextKey_physical] at gs
    exact gs
  | ⟨11, _⟩ =>
    have gs := Table80CoreRound11.gasSteps s q (physicalKey 11) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound11.eval_physical, Table80CoreRound11.nextKey_physical] at gs
    exact gs
  | ⟨12, _⟩ =>
    have gs := Table80CoreRound12.gasSteps s q (physicalKey 12) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound12.eval_physical, Table80CoreRound12.nextKey_physical] at gs
    exact gs
  | ⟨13, _⟩ =>
    have gs := Table80CoreRound13.gasSteps s q (physicalKey 13) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound13.eval_physical, Table80CoreRound13.nextKey_physical] at gs
    exact gs
  | ⟨14, _⟩ =>
    have gs := Table80CoreRound14.gasSteps s q (physicalKey 14) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound14.eval_physical, Table80CoreRound14.nextKey_physical] at gs
    exact gs
  | ⟨15, _⟩ =>
    have gs := Table80CoreRound15.gasSteps s q (physicalKey 15) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound15.eval_physical, Table80CoreRound15.nextKey_physical] at gs
    exact gs
  | ⟨16, _⟩ =>
    have gs := Table80CoreRound16.gasSteps s q (physicalKey 16) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound16.eval_physical, Table80CoreRound16.nextKey_physical] at gs
    exact gs
  | ⟨17, _⟩ =>
    have gs := Table80CoreRound17.gasSteps s q (physicalKey 17) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound17.eval_physical, Table80CoreRound17.nextKey_physical] at gs
    exact gs
  | ⟨18, _⟩ =>
    have gs := Table80CoreRound18.gasSteps s q (physicalKey 18) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound18.eval_physical, Table80CoreRound18.nextKey_physical] at gs
    exact gs
  | ⟨19, _⟩ =>
    have gs := Table80CoreRound19.gasSteps s q (physicalKey 19) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound19.eval_physical, Table80CoreRound19.nextKey_physical] at gs
    exact gs
  | ⟨20, _⟩ =>
    have gs := Table80CoreRound20.gasSteps s q (physicalKey 20) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound20.eval_physical, Table80CoreRound20.nextKey_physical] at gs
    exact gs
  | ⟨21, _⟩ =>
    have gs := Table80CoreRound21.gasSteps s q (physicalKey 21) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound21.eval_physical, Table80CoreRound21.nextKey_physical] at gs
    exact gs
  | ⟨22, _⟩ =>
    have gs := Table80CoreRound22.gasSteps s q (physicalKey 22) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound22.eval_physical, Table80CoreRound22.nextKey_physical] at gs
    exact gs
  | ⟨23, _⟩ =>
    have gs := Table80CoreRound23.gasSteps s q (physicalKey 23) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound23.eval_physical, Table80CoreRound23.nextKey_physical] at gs
    exact gs
  | ⟨24, _⟩ =>
    have gs := Table80CoreRound24.gasSteps s q (physicalKey 24) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound24.eval_physical, Table80CoreRound24.nextKey_physical] at gs
    exact gs
  | ⟨25, _⟩ =>
    have gs := Table80CoreRound25.gasSteps s q (physicalKey 25) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound25.eval_physical, Table80CoreRound25.nextKey_physical] at gs
    exact gs
  | ⟨26, _⟩ =>
    have gs := Table80CoreRound26.gasSteps s q (physicalKey 26) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound26.eval_physical, Table80CoreRound26.nextKey_physical] at gs
    exact gs
  | ⟨27, _⟩ =>
    have gs := Table80CoreRound27.gasSteps s q (physicalKey 27) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound27.eval_physical, Table80CoreRound27.nextKey_physical] at gs
    exact gs
  | ⟨28, _⟩ =>
    have gs := Table80CoreRound28.gasSteps s q (physicalKey 28) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound28.eval_physical, Table80CoreRound28.nextKey_physical] at gs
    exact gs
  | ⟨29, _⟩ =>
    have gs := Table80CoreRound29.gasSteps s q (physicalKey 29) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound29.eval_physical, Table80CoreRound29.nextKey_physical] at gs
    exact gs
  | ⟨30, _⟩ =>
    have gs := Table80CoreRound30.gasSteps s q (physicalKey 30) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound30.eval_physical, Table80CoreRound30.nextKey_physical] at gs
    exact gs
  | ⟨31, _⟩ =>
    have gs := Table80CoreRound31.gasSteps s q (physicalKey 31) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound31.eval_physical, Table80CoreRound31.nextKey_physical] at gs
    exact gs
  | ⟨32, _⟩ =>
    have gs := Table80CoreRound32.gasSteps s q (physicalKey 32) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound32.eval_physical, Table80CoreRound32.nextKey_physical] at gs
    exact gs
  | ⟨33, _⟩ =>
    have gs := Table80CoreRound33.gasSteps s q (physicalKey 33) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound33.eval_physical, Table80CoreRound33.nextKey_physical] at gs
    exact gs
  | ⟨34, _⟩ =>
    have gs := Table80CoreRound34.gasSteps s q (physicalKey 34) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound34.eval_physical, Table80CoreRound34.nextKey_physical] at gs
    exact gs
  | ⟨35, _⟩ =>
    have gs := Table80CoreRound35.gasSteps s q (physicalKey 35) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound35.eval_physical, Table80CoreRound35.nextKey_physical] at gs
    exact gs
  | ⟨36, _⟩ =>
    have gs := Table80CoreRound36.gasSteps s q (physicalKey 36) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound36.eval_physical, Table80CoreRound36.nextKey_physical] at gs
    exact gs
  | ⟨37, _⟩ =>
    have gs := Table80CoreRound37.gasSteps s q (physicalKey 37) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound37.eval_physical, Table80CoreRound37.nextKey_physical] at gs
    exact gs
  | ⟨38, _⟩ =>
    have gs := Table80CoreRound38.gasSteps s q (physicalKey 38) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound38.eval_physical, Table80CoreRound38.nextKey_physical] at gs
    exact gs
  | ⟨39, _⟩ =>
    have gs := Table80CoreRound39.gasSteps s q (physicalKey 39) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound39.eval_physical, Table80CoreRound39.nextKey_physical] at gs
    exact gs
  | ⟨40, _⟩ =>
    have gs := Table80CoreRound40.gasSteps s q (physicalKey 40) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound40.eval_physical, Table80CoreRound40.nextKey_physical] at gs
    exact gs
  | ⟨41, _⟩ =>
    have gs := Table80CoreRound41.gasSteps s q (physicalKey 41) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound41.eval_physical, Table80CoreRound41.nextKey_physical] at gs
    exact gs
  | ⟨42, _⟩ =>
    have gs := Table80CoreRound42.gasSteps s q (physicalKey 42) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound42.eval_physical, Table80CoreRound42.nextKey_physical] at gs
    exact gs
  | ⟨43, _⟩ =>
    have gs := Table80CoreRound43.gasSteps s q (physicalKey 43) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound43.eval_physical, Table80CoreRound43.nextKey_physical] at gs
    exact gs
  | ⟨44, _⟩ =>
    have gs := Table80CoreRound44.gasSteps s q (physicalKey 44) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound44.eval_physical, Table80CoreRound44.nextKey_physical] at gs
    exact gs
  | ⟨45, _⟩ =>
    have gs := Table80CoreRound45.gasSteps s q (physicalKey 45) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound45.eval_physical, Table80CoreRound45.nextKey_physical] at gs
    exact gs
  | ⟨46, _⟩ =>
    have gs := Table80CoreRound46.gasSteps s q (physicalKey 46) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound46.eval_physical, Table80CoreRound46.nextKey_physical] at gs
    exact gs
  | ⟨47, _⟩ =>
    have gs := Table80CoreRound47.gasSteps s q (physicalKey 47) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound47.eval_physical, Table80CoreRound47.nextKey_physical] at gs
    exact gs
  | ⟨48, _⟩ =>
    have gs := Table80CoreRound48.gasSteps s q (physicalKey 48) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound48.eval_physical, Table80CoreRound48.nextKey_physical] at gs
    exact gs
  | ⟨49, _⟩ =>
    have gs := Table80CoreRound49.gasSteps s q (physicalKey 49) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound49.eval_physical, Table80CoreRound49.nextKey_physical] at gs
    exact gs
  | ⟨50, _⟩ =>
    have gs := Table80CoreRound50.gasSteps s q (physicalKey 50) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound50.eval_physical, Table80CoreRound50.nextKey_physical] at gs
    exact gs
  | ⟨51, _⟩ =>
    have gs := Table80CoreRound51.gasSteps s q (physicalKey 51) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound51.eval_physical, Table80CoreRound51.nextKey_physical] at gs
    exact gs
  | ⟨52, _⟩ =>
    have gs := Table80CoreRound52.gasSteps s q (physicalKey 52) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound52.eval_physical, Table80CoreRound52.nextKey_physical] at gs
    exact gs
  | ⟨53, _⟩ =>
    have gs := Table80CoreRound53.gasSteps s q (physicalKey 53) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound53.eval_physical, Table80CoreRound53.nextKey_physical] at gs
    exact gs
  | ⟨54, _⟩ =>
    have gs := Table80CoreRound54.gasSteps s q (physicalKey 54) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound54.eval_physical, Table80CoreRound54.nextKey_physical] at gs
    exact gs
  | ⟨55, _⟩ =>
    have gs := Table80CoreRound55.gasSteps s q (physicalKey 55) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound55.eval_physical, Table80CoreRound55.nextKey_physical] at gs
    exact gs
  | ⟨56, _⟩ =>
    have gs := Table80CoreRound56.gasSteps s q (physicalKey 56) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound56.eval_physical, Table80CoreRound56.nextKey_physical] at gs
    exact gs
  | ⟨57, _⟩ =>
    have gs := Table80CoreRound57.gasSteps s q (physicalKey 57) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound57.eval_physical, Table80CoreRound57.nextKey_physical] at gs
    exact gs
  | ⟨58, _⟩ =>
    have gs := Table80CoreRound58.gasSteps s q (physicalKey 58) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound58.eval_physical, Table80CoreRound58.nextKey_physical] at gs
    exact gs
  | ⟨59, _⟩ =>
    have gs := Table80CoreRound59.gasSteps s q (physicalKey 59) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound59.eval_physical, Table80CoreRound59.nextKey_physical] at gs
    exact gs
  | ⟨60, _⟩ =>
    have gs := Table80CoreRound60.gasSteps s q (physicalKey 60) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound60.eval_physical, Table80CoreRound60.nextKey_physical] at gs
    exact gs
  | ⟨61, _⟩ =>
    have gs := Table80CoreRound61.gasSteps s q (physicalKey 61) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound61.eval_physical, Table80CoreRound61.nextKey_physical] at gs
    exact gs
  | ⟨62, _⟩ =>
    have gs := Table80CoreRound62.gasSteps s q (physicalKey 62) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound62.eval_physical, Table80CoreRound62.nextKey_physical] at gs
    exact gs
  | ⟨63, _⟩ =>
    have gs := Table80CoreRound63.gasSteps s q (physicalKey 63) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound63.eval_physical, Table80CoreRound63.nextKey_physical] at gs
    exact gs
  | ⟨64, _⟩ =>
    have gs := Table80CoreRound64.gasSteps s q (physicalKey 64) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound64.eval_physical, Table80CoreRound64.nextKey_physical] at gs
    exact gs
  | ⟨65, _⟩ =>
    have gs := Table80CoreRound65.gasSteps s q (physicalKey 65) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound65.eval_physical, Table80CoreRound65.nextKey_physical] at gs
    exact gs
  | ⟨66, _⟩ =>
    have gs := Table80CoreRound66.gasSteps s q (physicalKey 66) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound66.eval_physical, Table80CoreRound66.nextKey_physical] at gs
    exact gs
  | ⟨67, _⟩ =>
    have gs := Table80CoreRound67.gasSteps s q (physicalKey 67) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound67.eval_physical, Table80CoreRound67.nextKey_physical] at gs
    exact gs
  | ⟨68, _⟩ =>
    have gs := Table80CoreRound68.gasSteps s q (physicalKey 68) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound68.eval_physical, Table80CoreRound68.nextKey_physical] at gs
    exact gs
  | ⟨69, _⟩ =>
    have gs := Table80CoreRound69.gasSteps s q (physicalKey 69) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound69.eval_physical, Table80CoreRound69.nextKey_physical] at gs
    exact gs
  | ⟨70, _⟩ =>
    have gs := Table80CoreRound70.gasSteps s q (physicalKey 70) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound70.eval_physical, Table80CoreRound70.nextKey_physical] at gs
    exact gs
  | ⟨71, _⟩ =>
    have gs := Table80CoreRound71.gasSteps s q (physicalKey 71) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound71.eval_physical, Table80CoreRound71.nextKey_physical] at gs
    exact gs
  | ⟨72, _⟩ =>
    have gs := Table80CoreRound72.gasSteps s q (physicalKey 72) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound72.eval_physical, Table80CoreRound72.nextKey_physical] at gs
    exact gs
  | ⟨73, _⟩ =>
    have gs := Table80CoreRound73.gasSteps s q (physicalKey 73) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound73.eval_physical, Table80CoreRound73.nextKey_physical] at gs
    exact gs
  | ⟨74, _⟩ =>
    have gs := Table80CoreRound74.gasSteps s q (physicalKey 74) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound74.eval_physical, Table80CoreRound74.nextKey_physical] at gs
    exact gs
  | ⟨75, _⟩ =>
    have gs := Table80CoreRound75.gasSteps s q (physicalKey 75) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound75.eval_physical, Table80CoreRound75.nextKey_physical] at gs
    exact gs
  | ⟨76, _⟩ =>
    have gs := Table80CoreRound76.gasSteps s q (physicalKey 76) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound76.eval_physical, Table80CoreRound76.nextKey_physical] at gs
    exact gs
  | ⟨77, _⟩ =>
    have gs := Table80CoreRound77.gasSteps s q (physicalKey 77) rho hstack hrun hactive hcode hfork hnp
    rw [Table80CoreRound77.eval_physical, Table80CoreRound77.nextKey_physical] at gs
    exact gs
  | ⟨n + 78, hi⟩ => exact False.elim (by omega)

def gasSteps_prefix (s : State) (n : Nat) (hn : n ≤ 78) (q : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s 0 q rho) (atRound s n (fold (message s.memory) n q) rho) := by
  induction n with
  | zero => exact GasSteps.refl _
  | succ n ih =>
    exact (ih (by omega)).trans
      (gasSteps_step s ⟨n, by omega⟩ (fold (message s.memory) n q) rho
        hstack hrun hactive hcode hfork hnp)

def finalLane (memory : ByteArray) (q : WordLane) : WordLane :=
  Paired80FinalWord.finish (message memory) (fold (message memory) 78 q)

def physicalFinalLane (memory : ByteArray) (q : WordLane) : WordLane :=
  Table80WideFinalWord.finish (message memory) (fold (message memory) 78 q)

def gasSteps_core (s : State) (q : WordLane) (ret : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 995) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s 0 q (ret :: rho))
      {s with pc := UInt256.ofNat 4615, stack := Table80ConsumedTerminalTail.entryStack Table80WideCoreBridge.wideFactorWord (physicalFinalLane s.memory q) ret rho} := by
  have hs : (ret :: rho).length ≤ 996 := by simp only [List.length_cons]; omega
  let q78 := fold (message s.memory) 78 q
  let q79 := Table80CoreRound78.eval (message s.memory 78) (physicalKey 78) q78
  have gp := gasSteps_prefix s 78 (by decide) q (ret :: rho) hs hrun hactive hcode hfork hnp
  have g78 := Table80CoreRound78.gasSteps s q78 (physicalKey 78) (ret :: rho) hs hrun hactive hcode hfork hnp
  have g79 := Table80CoreRound79.gasSteps s q79 (physicalKey 79) (ret :: rho) hs hrun hactive hcode hfork hnp
  rw [Table80CoreRound78.nextKey_physical] at g78
  exact gp.trans (g78.trans g79)
#print axioms gasSteps_step
#print axioms gasSteps_prefix
#print axioms gasSteps_core
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Core
