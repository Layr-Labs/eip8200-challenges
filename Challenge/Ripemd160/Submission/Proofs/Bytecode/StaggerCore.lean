import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCorePairedAll
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreBoundaryAll
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCore
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Paired80WordRound StaggerCoreCommon StaggerCoreModel
open StaggerAlgorithm (step fold physicalKey)
def pcs : Array Nat := #[1130, 1181, 1224, 1260, 1306, 1344, 1387, 1425, 1468, 1507, 1550, 1589, 1635, 1673, 1737, 1785, 1833, 1888, 1936, 1974, 2022, 2063, 2110, 2151, 2199, 2239, 2287, 2328, 2375, 2413, 2477, 2524, 2572, 2624, 2664, 2695, 2732, 2766, 2806, 2840, 2881, 2912, 2952, 2983, 3020, 3051, 3118, 3167, 3215, 3272, 3320, 3360, 3409, 3447, 3496, 3536, 3583, 3621, 3669, 3707, 3756, 3794, 3848, 3889, 3929, 3974, 4020, 4058, 4104, 4140, 4178, 4214, 4259, 4295, 4341, 4380, 4426, 4464]
def shapes : Array (List Reg) := #[
  [ .pair, .upper, .e, .b, .a, .d, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .k, .b, .e, .a, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .k, .c, .a, .e, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .k, .b, .e, .a, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .b, .k, .e, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .c, .k, .a, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .b, .k, .e, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .k, .c, .e, .a, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .k, .b, .a, .e, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .k, .c, .e, .a, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .k, .b, .a, .e, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .k, .c, .e, .a, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .k, .b, .a, .e, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .k, .c, .e, .a, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .k, .b, .a, .e, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .k, .c, .e, .a, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .k, .b, .a, .e, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .k, .c, .e, .a, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .k, .b, .a, .e, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .k, .c, .e, .a, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .b, .a, .k, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .c, .e, .k, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .b, .a, .k, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .k, .b, .e, .a, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .k, .c, .a, .e, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .k, .b, .e, .a, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ],
  [ .d, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ]]
def atRound (s : State) (i : Nat) (q right : WordLane) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat pcs[i]!, stack := stack s.memory shapes[i]! q right (physicalKey (i-1)) rho}

def gasSteps_step (s : State) (i : Fin 77) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s i.val q right rho)
      (atRound s (i.val+1) (step i.val (message s.memory i.val) q) right rho) := by
  match i with
  | ⟨0, _⟩ => exact StaggerCorePaired0.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨1, _⟩ => exact StaggerCorePaired1.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨2, _⟩ => exact StaggerCorePaired2.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨3, _⟩ => exact StaggerCorePaired3.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨4, _⟩ => exact StaggerCorePaired4.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨5, _⟩ => exact StaggerCorePaired5.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨6, _⟩ => exact StaggerCorePaired6.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨7, _⟩ => exact StaggerCorePaired7.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨8, _⟩ => exact StaggerCorePaired8.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨9, _⟩ => exact StaggerCorePaired9.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨10, _⟩ => exact StaggerCorePaired10.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨11, _⟩ => exact StaggerCorePaired11.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨12, _⟩ => exact StaggerCorePaired12.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨13, _⟩ => exact StaggerCorePaired13.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨14, _⟩ => exact StaggerCorePaired14.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨15, _⟩ => exact StaggerCorePaired15.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨16, _⟩ => exact StaggerCorePaired16.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨17, _⟩ => exact StaggerCorePaired17.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨18, _⟩ => exact StaggerCorePaired18.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨19, _⟩ => exact StaggerCorePaired19.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨20, _⟩ => exact StaggerCorePaired20.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨21, _⟩ => exact StaggerCorePaired21.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨22, _⟩ => exact StaggerCorePaired22.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨23, _⟩ => exact StaggerCorePaired23.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨24, _⟩ => exact StaggerCorePaired24.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨25, _⟩ => exact StaggerCorePaired25.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨26, _⟩ => exact StaggerCorePaired26.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨27, _⟩ => exact StaggerCorePaired27.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨28, _⟩ => exact StaggerCorePaired28.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨29, _⟩ => exact StaggerCorePaired29.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨30, _⟩ => exact StaggerCorePaired30.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨31, _⟩ => exact StaggerCorePaired31.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨32, _⟩ => exact StaggerCorePaired32.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨33, _⟩ => exact StaggerCorePaired33.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨34, _⟩ => exact StaggerCorePaired34.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨35, _⟩ => exact StaggerCorePaired35.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨36, _⟩ => exact StaggerCorePaired36.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨37, _⟩ => exact StaggerCorePaired37.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨38, _⟩ => exact StaggerCorePaired38.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨39, _⟩ => exact StaggerCorePaired39.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨40, _⟩ => exact StaggerCorePaired40.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨41, _⟩ => exact StaggerCorePaired41.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨42, _⟩ => exact StaggerCorePaired42.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨43, _⟩ => exact StaggerCorePaired43.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨44, _⟩ => exact StaggerCorePaired44.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨45, _⟩ => exact StaggerCorePaired45.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨46, _⟩ => exact StaggerCorePaired46.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨47, _⟩ => exact StaggerCorePaired47.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨48, _⟩ => exact StaggerCorePaired48.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨49, _⟩ => exact StaggerCorePaired49.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨50, _⟩ => exact StaggerCorePaired50.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨51, _⟩ => exact StaggerCorePaired51.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨52, _⟩ => exact StaggerCorePaired52.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨53, _⟩ => exact StaggerCorePaired53.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨54, _⟩ => exact StaggerCorePaired54.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨55, _⟩ => exact StaggerCorePaired55.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨56, _⟩ => exact StaggerCorePaired56.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨57, _⟩ => exact StaggerCorePaired57.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨58, _⟩ => exact StaggerCorePaired58.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨59, _⟩ => exact StaggerCorePaired59.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨60, _⟩ => exact StaggerCorePaired60.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨61, _⟩ => exact StaggerCorePaired61.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨62, _⟩ => exact StaggerCorePaired62.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨63, _⟩ => exact StaggerCorePaired63.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨64, _⟩ => exact StaggerCorePaired64.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨65, _⟩ => exact StaggerCorePaired65.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨66, _⟩ => exact StaggerCorePaired66.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨67, _⟩ => exact StaggerCorePaired67.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨68, _⟩ => exact StaggerCorePaired68.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨69, _⟩ => exact StaggerCorePaired69.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨70, _⟩ => exact StaggerCorePaired70.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨71, _⟩ => exact StaggerCorePaired71.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨72, _⟩ => exact StaggerCorePaired72.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨73, _⟩ => exact StaggerCorePaired73.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨74, _⟩ => exact StaggerCorePaired74.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨75, _⟩ => exact StaggerCorePaired75.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨76, _⟩ => exact StaggerCorePaired76.gasSteps s q right rho hs hr ha hcode hfork hnp
  | ⟨n+77, hi⟩ => exact False.elim (by omega)

def gasSteps_prefix (s : State) (n : Nat) (hn : n ≤ 77) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s 0 q right rho)
      (atRound s n (fold (message s.memory) n q) right rho) := by
  induction n with
  | zero => exact GasSteps.refl _
  | succ n ih =>
    exact (ih (by omega)).trans
      (gasSteps_step s ⟨n, by omega⟩ (fold (message s.memory) n q) right rho hs hr ha hcode hfork hnp)

def gasSteps_core (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 926, stack := rho}
      {s with pc := UInt256.ofNat 4675, stack := rho, memory := resultMemory s.memory} := by
  let q0 := initial s.memory
  let q1 := right0 s.memory q0
  let q2 := right1 s.memory q1
  let q3 := right2 s.memory q2
  let p0 := pair q0 q3
  let p77 := fold (message s.memory) 77 p0
  let l0 := left p77
  let l1 := left77 s.memory l0
  let l2 := left78 s.memory l1
  let l3 := left79 s.memory l2
  have gb := StaggerCoreBootstrap.gasSteps s q0 q0 rho hs hr ha hcode hfork hnp
  have gr0 := StaggerCoreRight0.gasSteps s q0 q0 rho hs hr ha hcode hfork hnp
  have gr1 := StaggerCoreRight1.gasSteps s q1 q0 rho hs hr ha hcode hfork hnp
  have gr2 := StaggerCoreRight2.gasSteps s q2 q0 rho hs hr ha hcode hfork hnp
  have gpack := StaggerCorePack.gasSteps s q3 q0 rho hs hr ha hcode hfork hnp
  have gp := gasSteps_prefix s 77 (by decide) p0 q0 rho hs hr ha hcode hfork hnp
  have gu := StaggerCoreUnpack.gasSteps s p77 q0 rho hs hr ha hcode hfork hnp
  have gl1 := StaggerCoreLeft77.gasSteps s l0 p77 rho hs hr ha hcode hfork hnp
  have gl2 := StaggerCoreLeft78.gasSteps s l1 p77 rho hs hr ha hcode hfork hnp
  have gl3 := StaggerCoreLeft79.gasSteps s l2 p77 rho hs hr ha hcode hfork hnp
  have gt := StaggerCoreTail.gasSteps s l3 p77 rho hs hr ha hcode hfork hnp
  exact gb.trans (gr0.trans (gr1.trans (gr2.trans (gpack.trans
    (gp.trans (gu.trans (gl1.trans (gl2.trans (gl3.trans gt)))))))))
#print axioms gasSteps_step
#print axioms gasSteps_prefix
#print axioms gasSteps_core
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCore
