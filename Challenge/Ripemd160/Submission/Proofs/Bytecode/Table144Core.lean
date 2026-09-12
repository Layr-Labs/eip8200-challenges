import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144CoreAll
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTable144Layout
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144Core
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound Paired144Algorithm Table144CoreCommon

def pcs : Array Nat := #[1129, 1172, 1216, 1259, 1301, 1346, 1390, 1435, 1479, 1522, 1564, 1607, 1650, 1695, 1738, 1783, 1839, 1886, 1932, 1978, 2023, 2067, 2111, 2158, 2204, 2244, 2291, 2336, 2381, 2428, 2474, 2513, 2574, 2611, 2649, 2690, 2729, 2767, 2804, 2843, 2880, 2918, 2958, 2998, 3038, 3077, 3114, 3147, 3193, 3238, 3283, 3328, 3373, 3413, 3456, 3501, 3548, 3593, 3640, 3686, 3733, 3778, 3822, 3870, 3923, 3965, 4011, 4055, 4098, 4143, 4186, 4228, 4271, 4316, 4358, 4402, 4448, 4492, 4536, 4581, 4620]
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
  MachineState.readWord memory (18 * PairTable144Layout.pairIndices[i]!)
def atRound (s : State) (i : Nat) (q : WordLane) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat pcs[i]!, stack := stack shapes[i]! q (physicalKey i) rho}

def gasSteps_step (s : State) (i : Fin 79) (q : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 53 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s i.val q rho)
      (atRound s (i.val + 1) (step i.val (message s.memory i.val) q) rho) := by
  match i with
  | ⟨0, _⟩ =>
    have gs := Table144CoreRound0.gasSteps s q (physicalKey 0) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound0.eval_physical, Table144CoreRound0.nextKey_physical] at gs
    exact gs
  | ⟨1, _⟩ =>
    have gs := Table144CoreRound1.gasSteps s q (physicalKey 1) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound1.eval_physical, Table144CoreRound1.nextKey_physical] at gs
    exact gs
  | ⟨2, _⟩ =>
    have gs := Table144CoreRound2.gasSteps s q (physicalKey 2) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound2.eval_physical, Table144CoreRound2.nextKey_physical] at gs
    exact gs
  | ⟨3, _⟩ =>
    have gs := Table144CoreRound3.gasSteps s q (physicalKey 3) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound3.eval_physical, Table144CoreRound3.nextKey_physical] at gs
    exact gs
  | ⟨4, _⟩ =>
    have gs := Table144CoreRound4.gasSteps s q (physicalKey 4) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound4.eval_physical, Table144CoreRound4.nextKey_physical] at gs
    exact gs
  | ⟨5, _⟩ =>
    have gs := Table144CoreRound5.gasSteps s q (physicalKey 5) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound5.eval_physical, Table144CoreRound5.nextKey_physical] at gs
    exact gs
  | ⟨6, _⟩ =>
    have gs := Table144CoreRound6.gasSteps s q (physicalKey 6) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound6.eval_physical, Table144CoreRound6.nextKey_physical] at gs
    exact gs
  | ⟨7, _⟩ =>
    have gs := Table144CoreRound7.gasSteps s q (physicalKey 7) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound7.eval_physical, Table144CoreRound7.nextKey_physical] at gs
    exact gs
  | ⟨8, _⟩ =>
    have gs := Table144CoreRound8.gasSteps s q (physicalKey 8) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound8.eval_physical, Table144CoreRound8.nextKey_physical] at gs
    exact gs
  | ⟨9, _⟩ =>
    have gs := Table144CoreRound9.gasSteps s q (physicalKey 9) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound9.eval_physical, Table144CoreRound9.nextKey_physical] at gs
    exact gs
  | ⟨10, _⟩ =>
    have gs := Table144CoreRound10.gasSteps s q (physicalKey 10) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound10.eval_physical, Table144CoreRound10.nextKey_physical] at gs
    exact gs
  | ⟨11, _⟩ =>
    have gs := Table144CoreRound11.gasSteps s q (physicalKey 11) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound11.eval_physical, Table144CoreRound11.nextKey_physical] at gs
    exact gs
  | ⟨12, _⟩ =>
    have gs := Table144CoreRound12.gasSteps s q (physicalKey 12) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound12.eval_physical, Table144CoreRound12.nextKey_physical] at gs
    exact gs
  | ⟨13, _⟩ =>
    have gs := Table144CoreRound13.gasSteps s q (physicalKey 13) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound13.eval_physical, Table144CoreRound13.nextKey_physical] at gs
    exact gs
  | ⟨14, _⟩ =>
    have gs := Table144CoreRound14.gasSteps s q (physicalKey 14) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound14.eval_physical, Table144CoreRound14.nextKey_physical] at gs
    exact gs
  | ⟨15, _⟩ =>
    have gs := Table144CoreRound15.gasSteps s q (physicalKey 15) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound15.eval_physical, Table144CoreRound15.nextKey_physical] at gs
    exact gs
  | ⟨16, _⟩ =>
    have gs := Table144CoreRound16.gasSteps s q (physicalKey 16) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound16.eval_physical, Table144CoreRound16.nextKey_physical] at gs
    exact gs
  | ⟨17, _⟩ =>
    have gs := Table144CoreRound17.gasSteps s q (physicalKey 17) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound17.eval_physical, Table144CoreRound17.nextKey_physical] at gs
    exact gs
  | ⟨18, _⟩ =>
    have gs := Table144CoreRound18.gasSteps s q (physicalKey 18) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound18.eval_physical, Table144CoreRound18.nextKey_physical] at gs
    exact gs
  | ⟨19, _⟩ =>
    have gs := Table144CoreRound19.gasSteps s q (physicalKey 19) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound19.eval_physical, Table144CoreRound19.nextKey_physical] at gs
    exact gs
  | ⟨20, _⟩ =>
    have gs := Table144CoreRound20.gasSteps s q (physicalKey 20) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound20.eval_physical, Table144CoreRound20.nextKey_physical] at gs
    exact gs
  | ⟨21, _⟩ =>
    have gs := Table144CoreRound21.gasSteps s q (physicalKey 21) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound21.eval_physical, Table144CoreRound21.nextKey_physical] at gs
    exact gs
  | ⟨22, _⟩ =>
    have gs := Table144CoreRound22.gasSteps s q (physicalKey 22) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound22.eval_physical, Table144CoreRound22.nextKey_physical] at gs
    exact gs
  | ⟨23, _⟩ =>
    have gs := Table144CoreRound23.gasSteps s q (physicalKey 23) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound23.eval_physical, Table144CoreRound23.nextKey_physical] at gs
    exact gs
  | ⟨24, _⟩ =>
    have gs := Table144CoreRound24.gasSteps s q (physicalKey 24) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound24.eval_physical, Table144CoreRound24.nextKey_physical] at gs
    exact gs
  | ⟨25, _⟩ =>
    have gs := Table144CoreRound25.gasSteps s q (physicalKey 25) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound25.eval_physical, Table144CoreRound25.nextKey_physical] at gs
    exact gs
  | ⟨26, _⟩ =>
    have gs := Table144CoreRound26.gasSteps s q (physicalKey 26) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound26.eval_physical, Table144CoreRound26.nextKey_physical] at gs
    exact gs
  | ⟨27, _⟩ =>
    have gs := Table144CoreRound27.gasSteps s q (physicalKey 27) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound27.eval_physical, Table144CoreRound27.nextKey_physical] at gs
    exact gs
  | ⟨28, _⟩ =>
    have gs := Table144CoreRound28.gasSteps s q (physicalKey 28) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound28.eval_physical, Table144CoreRound28.nextKey_physical] at gs
    exact gs
  | ⟨29, _⟩ =>
    have gs := Table144CoreRound29.gasSteps s q (physicalKey 29) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound29.eval_physical, Table144CoreRound29.nextKey_physical] at gs
    exact gs
  | ⟨30, _⟩ =>
    have gs := Table144CoreRound30.gasSteps s q (physicalKey 30) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound30.eval_physical, Table144CoreRound30.nextKey_physical] at gs
    exact gs
  | ⟨31, _⟩ =>
    have gs := Table144CoreRound31.gasSteps s q (physicalKey 31) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound31.eval_physical, Table144CoreRound31.nextKey_physical] at gs
    exact gs
  | ⟨32, _⟩ =>
    have gs := Table144CoreRound32.gasSteps s q (physicalKey 32) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound32.eval_physical, Table144CoreRound32.nextKey_physical] at gs
    exact gs
  | ⟨33, _⟩ =>
    have gs := Table144CoreRound33.gasSteps s q (physicalKey 33) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound33.eval_physical, Table144CoreRound33.nextKey_physical] at gs
    exact gs
  | ⟨34, _⟩ =>
    have gs := Table144CoreRound34.gasSteps s q (physicalKey 34) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound34.eval_physical, Table144CoreRound34.nextKey_physical] at gs
    exact gs
  | ⟨35, _⟩ =>
    have gs := Table144CoreRound35.gasSteps s q (physicalKey 35) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound35.eval_physical, Table144CoreRound35.nextKey_physical] at gs
    exact gs
  | ⟨36, _⟩ =>
    have gs := Table144CoreRound36.gasSteps s q (physicalKey 36) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound36.eval_physical, Table144CoreRound36.nextKey_physical] at gs
    exact gs
  | ⟨37, _⟩ =>
    have gs := Table144CoreRound37.gasSteps s q (physicalKey 37) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound37.eval_physical, Table144CoreRound37.nextKey_physical] at gs
    exact gs
  | ⟨38, _⟩ =>
    have gs := Table144CoreRound38.gasSteps s q (physicalKey 38) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound38.eval_physical, Table144CoreRound38.nextKey_physical] at gs
    exact gs
  | ⟨39, _⟩ =>
    have gs := Table144CoreRound39.gasSteps s q (physicalKey 39) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound39.eval_physical, Table144CoreRound39.nextKey_physical] at gs
    exact gs
  | ⟨40, _⟩ =>
    have gs := Table144CoreRound40.gasSteps s q (physicalKey 40) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound40.eval_physical, Table144CoreRound40.nextKey_physical] at gs
    exact gs
  | ⟨41, _⟩ =>
    have gs := Table144CoreRound41.gasSteps s q (physicalKey 41) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound41.eval_physical, Table144CoreRound41.nextKey_physical] at gs
    exact gs
  | ⟨42, _⟩ =>
    have gs := Table144CoreRound42.gasSteps s q (physicalKey 42) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound42.eval_physical, Table144CoreRound42.nextKey_physical] at gs
    exact gs
  | ⟨43, _⟩ =>
    have gs := Table144CoreRound43.gasSteps s q (physicalKey 43) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound43.eval_physical, Table144CoreRound43.nextKey_physical] at gs
    exact gs
  | ⟨44, _⟩ =>
    have gs := Table144CoreRound44.gasSteps s q (physicalKey 44) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound44.eval_physical, Table144CoreRound44.nextKey_physical] at gs
    exact gs
  | ⟨45, _⟩ =>
    have gs := Table144CoreRound45.gasSteps s q (physicalKey 45) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound45.eval_physical, Table144CoreRound45.nextKey_physical] at gs
    exact gs
  | ⟨46, _⟩ =>
    have gs := Table144CoreRound46.gasSteps s q (physicalKey 46) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound46.eval_physical, Table144CoreRound46.nextKey_physical] at gs
    exact gs
  | ⟨47, _⟩ =>
    have gs := Table144CoreRound47.gasSteps s q (physicalKey 47) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound47.eval_physical, Table144CoreRound47.nextKey_physical] at gs
    exact gs
  | ⟨48, _⟩ =>
    have gs := Table144CoreRound48.gasSteps s q (physicalKey 48) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound48.eval_physical, Table144CoreRound48.nextKey_physical] at gs
    exact gs
  | ⟨49, _⟩ =>
    have gs := Table144CoreRound49.gasSteps s q (physicalKey 49) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound49.eval_physical, Table144CoreRound49.nextKey_physical] at gs
    exact gs
  | ⟨50, _⟩ =>
    have gs := Table144CoreRound50.gasSteps s q (physicalKey 50) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound50.eval_physical, Table144CoreRound50.nextKey_physical] at gs
    exact gs
  | ⟨51, _⟩ =>
    have gs := Table144CoreRound51.gasSteps s q (physicalKey 51) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound51.eval_physical, Table144CoreRound51.nextKey_physical] at gs
    exact gs
  | ⟨52, _⟩ =>
    have gs := Table144CoreRound52.gasSteps s q (physicalKey 52) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound52.eval_physical, Table144CoreRound52.nextKey_physical] at gs
    exact gs
  | ⟨53, _⟩ =>
    have gs := Table144CoreRound53.gasSteps s q (physicalKey 53) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound53.eval_physical, Table144CoreRound53.nextKey_physical] at gs
    exact gs
  | ⟨54, _⟩ =>
    have gs := Table144CoreRound54.gasSteps s q (physicalKey 54) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound54.eval_physical, Table144CoreRound54.nextKey_physical] at gs
    exact gs
  | ⟨55, _⟩ =>
    have gs := Table144CoreRound55.gasSteps s q (physicalKey 55) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound55.eval_physical, Table144CoreRound55.nextKey_physical] at gs
    exact gs
  | ⟨56, _⟩ =>
    have gs := Table144CoreRound56.gasSteps s q (physicalKey 56) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound56.eval_physical, Table144CoreRound56.nextKey_physical] at gs
    exact gs
  | ⟨57, _⟩ =>
    have gs := Table144CoreRound57.gasSteps s q (physicalKey 57) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound57.eval_physical, Table144CoreRound57.nextKey_physical] at gs
    exact gs
  | ⟨58, _⟩ =>
    have gs := Table144CoreRound58.gasSteps s q (physicalKey 58) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound58.eval_physical, Table144CoreRound58.nextKey_physical] at gs
    exact gs
  | ⟨59, _⟩ =>
    have gs := Table144CoreRound59.gasSteps s q (physicalKey 59) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound59.eval_physical, Table144CoreRound59.nextKey_physical] at gs
    exact gs
  | ⟨60, _⟩ =>
    have gs := Table144CoreRound60.gasSteps s q (physicalKey 60) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound60.eval_physical, Table144CoreRound60.nextKey_physical] at gs
    exact gs
  | ⟨61, _⟩ =>
    have gs := Table144CoreRound61.gasSteps s q (physicalKey 61) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound61.eval_physical, Table144CoreRound61.nextKey_physical] at gs
    exact gs
  | ⟨62, _⟩ =>
    have gs := Table144CoreRound62.gasSteps s q (physicalKey 62) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound62.eval_physical, Table144CoreRound62.nextKey_physical] at gs
    exact gs
  | ⟨63, _⟩ =>
    have gs := Table144CoreRound63.gasSteps s q (physicalKey 63) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound63.eval_physical, Table144CoreRound63.nextKey_physical] at gs
    exact gs
  | ⟨64, _⟩ =>
    have gs := Table144CoreRound64.gasSteps s q (physicalKey 64) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound64.eval_physical, Table144CoreRound64.nextKey_physical] at gs
    exact gs
  | ⟨65, _⟩ =>
    have gs := Table144CoreRound65.gasSteps s q (physicalKey 65) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound65.eval_physical, Table144CoreRound65.nextKey_physical] at gs
    exact gs
  | ⟨66, _⟩ =>
    have gs := Table144CoreRound66.gasSteps s q (physicalKey 66) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound66.eval_physical, Table144CoreRound66.nextKey_physical] at gs
    exact gs
  | ⟨67, _⟩ =>
    have gs := Table144CoreRound67.gasSteps s q (physicalKey 67) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound67.eval_physical, Table144CoreRound67.nextKey_physical] at gs
    exact gs
  | ⟨68, _⟩ =>
    have gs := Table144CoreRound68.gasSteps s q (physicalKey 68) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound68.eval_physical, Table144CoreRound68.nextKey_physical] at gs
    exact gs
  | ⟨69, _⟩ =>
    have gs := Table144CoreRound69.gasSteps s q (physicalKey 69) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound69.eval_physical, Table144CoreRound69.nextKey_physical] at gs
    exact gs
  | ⟨70, _⟩ =>
    have gs := Table144CoreRound70.gasSteps s q (physicalKey 70) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound70.eval_physical, Table144CoreRound70.nextKey_physical] at gs
    exact gs
  | ⟨71, _⟩ =>
    have gs := Table144CoreRound71.gasSteps s q (physicalKey 71) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound71.eval_physical, Table144CoreRound71.nextKey_physical] at gs
    exact gs
  | ⟨72, _⟩ =>
    have gs := Table144CoreRound72.gasSteps s q (physicalKey 72) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound72.eval_physical, Table144CoreRound72.nextKey_physical] at gs
    exact gs
  | ⟨73, _⟩ =>
    have gs := Table144CoreRound73.gasSteps s q (physicalKey 73) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound73.eval_physical, Table144CoreRound73.nextKey_physical] at gs
    exact gs
  | ⟨74, _⟩ =>
    have gs := Table144CoreRound74.gasSteps s q (physicalKey 74) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound74.eval_physical, Table144CoreRound74.nextKey_physical] at gs
    exact gs
  | ⟨75, _⟩ =>
    have gs := Table144CoreRound75.gasSteps s q (physicalKey 75) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound75.eval_physical, Table144CoreRound75.nextKey_physical] at gs
    exact gs
  | ⟨76, _⟩ =>
    have gs := Table144CoreRound76.gasSteps s q (physicalKey 76) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound76.eval_physical, Table144CoreRound76.nextKey_physical] at gs
    exact gs
  | ⟨77, _⟩ =>
    have gs := Table144CoreRound77.gasSteps s q (physicalKey 77) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound77.eval_physical, Table144CoreRound77.nextKey_physical] at gs
    exact gs
  | ⟨78, _⟩ =>
    have gs := Table144CoreRound78.gasSteps s q (physicalKey 78) rho hstack hrun hactive hcode hfork hnp
    rw [Table144CoreRound78.eval_physical, Table144CoreRound78.nextKey_physical] at gs
    exact gs
  | ⟨n + 79, hi⟩ => exact False.elim (by omega)

def gasSteps_prefix (s : State) (n : Nat) (hn : n ≤ 79) (q : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 53 ≤ s.activeWords.toNat)
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

def gasSteps_core (s : State) (q : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 53 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s 0 q rho)
      (atRound s 80 (Paired144Algorithm.finalLane (message s.memory) q) rho) := by
  have gp := gasSteps_prefix s 79 (by decide) q rho hstack hrun hactive hcode hfork hnp
  have gf := Table144CoreRound79.gasSteps s (fold (message s.memory) 79 q)
    (physicalKey 79) rho hstack hrun hactive hcode hfork hnp
  exact gp.trans gf
#print axioms gasSteps_step
#print axioms gasSteps_prefix
#print axioms gasSteps_core
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144Core
