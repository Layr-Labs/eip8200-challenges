import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCorePairedAll
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreBoundaryAll
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCore
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Paired144WordRound StaggerCoreCommon StaggerCoreModel
open StaggerAlgorithm (physicalKey)
open StaggerTerminal75 (step fold)
def pcs : Array Nat := #[1144, 1206, 1249, 1288, 1332, 1371, 1414, 1452, 1495, 1534, 1577, 1616, 1660, 1699, 1769, 1817, 1865, 1931, 1979, 2019, 2067, 2108, 2155, 2196, 2242, 2283, 2329, 2370, 2417, 2458, 2528, 2573, 2619, 2679, 2720, 2754, 2791, 2825, 2863, 2897, 2938, 2972, 3013, 3047, 3084, 3117, 3190, 3239, 3286, 3351, 3397, 3437, 3486, 3527, 3576, 3617, 3665, 3705, 3753, 3794, 3843, 3884, 3937, 3978, 4019, 4065, 4109, 4148, 4192, 4231, 4269, 4308, 4352, 4391, 4435, 4474, 4516, 4554]
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
def atRound (s : State) (h4 : UInt256) (i : Nat) (q right : WordLane) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat pcs[i]!, stack := stack s.memory h4 shapes[i]! q right (physicalKey (i-1)) rho}

def gasSteps_step (s : State) (h4 : UInt256) (i : Fin 77) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 i.val q right rho)
      (atRound s h4 (i.val+1) (step i.val (message s.memory i.val) q) right rho) := by
  match i with
  | ⟨0, _⟩ => exact StaggerCorePaired0.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨1, _⟩ => exact StaggerCorePaired1.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨2, _⟩ => exact StaggerCorePaired2.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨3, _⟩ => exact StaggerCorePaired3.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨4, _⟩ => exact StaggerCorePaired4.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨5, _⟩ => exact StaggerCorePaired5.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨6, _⟩ => exact StaggerCorePaired6.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨7, _⟩ => exact StaggerCorePaired7.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨8, _⟩ => exact StaggerCorePaired8.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨9, _⟩ => exact StaggerCorePaired9.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨10, _⟩ => exact StaggerCorePaired10.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨11, _⟩ => exact StaggerCorePaired11.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨12, _⟩ => exact StaggerCorePaired12.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨13, _⟩ => exact StaggerCorePaired13.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨14, _⟩ => exact StaggerCorePaired14.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨15, _⟩ => exact StaggerCorePaired15.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨16, _⟩ => exact StaggerCorePaired16.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨17, _⟩ => exact StaggerCorePaired17.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨18, _⟩ => exact StaggerCorePaired18.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨19, _⟩ => exact StaggerCorePaired19.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨20, _⟩ => exact StaggerCorePaired20.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨21, _⟩ => exact StaggerCorePaired21.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨22, _⟩ => exact StaggerCorePaired22.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨23, _⟩ => exact StaggerCorePaired23.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨24, _⟩ => exact StaggerCorePaired24.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨25, _⟩ => exact StaggerCorePaired25.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨26, _⟩ => exact StaggerCorePaired26.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨27, _⟩ => exact StaggerCorePaired27.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨28, _⟩ => exact StaggerCorePaired28.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨29, _⟩ => exact StaggerCorePaired29.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨30, _⟩ => exact StaggerCorePaired30.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨31, _⟩ => exact StaggerCorePaired31.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨32, _⟩ => exact StaggerCorePaired32.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨33, _⟩ => exact StaggerCorePaired33.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨34, _⟩ => exact StaggerCorePaired34.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨35, _⟩ => exact StaggerCorePaired35.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨36, _⟩ => exact StaggerCorePaired36.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨37, _⟩ => exact StaggerCorePaired37.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨38, _⟩ => exact StaggerCorePaired38.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨39, _⟩ => exact StaggerCorePaired39.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨40, _⟩ => exact StaggerCorePaired40.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨41, _⟩ => exact StaggerCorePaired41.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨42, _⟩ => exact StaggerCorePaired42.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨43, _⟩ => exact StaggerCorePaired43.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨44, _⟩ => exact StaggerCorePaired44.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨45, _⟩ => exact StaggerCorePaired45.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨46, _⟩ => exact StaggerCorePaired46.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨47, _⟩ => exact StaggerCorePaired47.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨48, _⟩ => exact StaggerCorePaired48.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨49, _⟩ => exact StaggerCorePaired49.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨50, _⟩ => exact StaggerCorePaired50.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨51, _⟩ => exact StaggerCorePaired51.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨52, _⟩ => exact StaggerCorePaired52.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨53, _⟩ => exact StaggerCorePaired53.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨54, _⟩ => exact StaggerCorePaired54.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨55, _⟩ => exact StaggerCorePaired55.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨56, _⟩ => exact StaggerCorePaired56.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨57, _⟩ => exact StaggerCorePaired57.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨58, _⟩ => exact StaggerCorePaired58.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨59, _⟩ => exact StaggerCorePaired59.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨60, _⟩ => exact StaggerCorePaired60.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨61, _⟩ => exact StaggerCorePaired61.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨62, _⟩ => exact StaggerCorePaired62.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨63, _⟩ => exact StaggerCorePaired63.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨64, _⟩ => exact StaggerCorePaired64.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨65, _⟩ => exact StaggerCorePaired65.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨66, _⟩ => exact StaggerCorePaired66.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨67, _⟩ => exact StaggerCorePaired67.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨68, _⟩ => exact StaggerCorePaired68.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨69, _⟩ => exact StaggerCorePaired69.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨70, _⟩ => exact StaggerCorePaired70.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨71, _⟩ => exact StaggerCorePaired71.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨72, _⟩ => exact StaggerCorePaired72.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨73, _⟩ => exact StaggerCorePaired73.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨74, _⟩ => exact StaggerCorePaired74.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨75, _⟩ => exact StaggerCorePaired75.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨76, _⟩ => exact StaggerCorePaired76.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨n+77, hi⟩ => exact False.elim (by omega)

def gasSteps_prefix (s : State) (h4 : UInt256) (n : Nat) (hn : n ≤ 77) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 0 q right rho)
      (atRound s h4 n (fold (message s.memory) n q) right rho) := by
  induction n with
  | zero => exact GasSteps.refl _
  | succ n ih =>
    exact (ih (by omega)).trans
      (gasSteps_step s h4 ⟨n, by omega⟩ (fold (message s.memory) n q) right rho hs hr ha hcode hfork hnp)


def suffixState (s : State) (h4 : UInt256) (q : WordLane) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 4708, stack := stack s.memory h4 [ .d, .b, .e, .a, .k, .c, .er, .cr, .ar, .dr, .br, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ] (epilogue s.memory q) q (UInt256.ofNat 2840853838) rho}

def gasSteps_suffix (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 77 q right rho) (suffixState s h4 q rho) := by
  have gu := StaggerCoreUnpack.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  have g1 := StaggerCoreLeft77.gasSteps s h4 (left q) q rho hs hr ha hcode hfork hnp
  have g2 := StaggerCoreLeft78.gasSteps s h4 (left77 s.memory (left q)) q rho hs hr ha hcode hfork hnp
  have g3 := StaggerCoreLeft79.gasSteps s h4 (left78 s.memory (left77 s.memory (left q))) q rho hs hr ha hcode hfork hnp
  exact gu.trans (g1.trans (g2.trans g3))

def gasSteps_pairedSuffix (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 0 q right rho)
      (suffixState s h4 (fold (message s.memory) 77 q) rho) :=
  (gasSteps_prefix s h4 77 (by decide) q right rho hs hr ha hcode hfork hnp).trans
    (gasSteps_suffix s h4 (fold (message s.memory) 77 q) right rho hs hr ha hcode hfork hnp)

#print axioms gasSteps_step
#print axioms gasSteps_prefix
#print axioms gasSteps_suffix
#print axioms gasSteps_pairedSuffix
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCore
