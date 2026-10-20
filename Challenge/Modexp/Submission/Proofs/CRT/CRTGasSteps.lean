import Challenge.Modexp.Submission.Proofs.Fast.CRTArtifactBlocks
import Challenge.Modexp.Submission.Proofs.CRT.CRTControl
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 3000000
namespace HistoricalSearch.CRTGasSteps
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.CRTArtifactBlocks
open HistoricalSearch.GeneratedColumns HistoricalSearch.CRTControl

def environment (s : State) (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256
      rw [Challenge.Modexp.submissionBytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩
#print axioms environment

def gasSteps_entry (s : State) (pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 4816, stack := pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest}
      (entryModel s pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest) := by
  have hc : (pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest).length ≤ 1022 := by simp only [List.length_cons]; omega
  have hv : Decode.isValidJumpDest s.executionEnv.code 5615 = true := by
    rw [env.code]; exact validJump5615
  have g0 := block_hook.steps (s := {s with pc := UInt256.ofNat 4816, stack := pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest}) (env.transfer rfl rfl) rfl (hook_run s (pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest) hc hv)
  have g1 := block_entry.steps (s := {s with pc := UInt256.ofNat 5615, stack := pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest}) (env.transfer rfl rfl) rfl (entry_run s pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest hcap hact)
  exact g0.trans g1
#print axioms gasSteps_entry

def gasSteps_kernel (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 5859, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}
      (kernelModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest) :=
  block_kernel.steps (env.transfer rfl rfl) rfl (kernel_run s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest hcap hact)
#print axioms gasSteps_kernel

def gasSteps_overflow (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 8507, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest}
      (conditionalModel (overflowModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest)) := by
  have g0 := block_overflow.steps (s := {s with pc := UInt256.ofNat 8507, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest}) (env.transfer rfl rfl) rfl (overflow_run s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest hcap hact)
  have hv : Decode.isValidJumpDest s.executionEnv.code 8800 = true := by
    rw [env.code]; exact validJump8800
  have g1 := block_overflowBranch.steps (s := overflowModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest) (env.transfer rfl rfl) rfl
    (overflow_control s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest hcap hv)
  exact g0.trans g1
#print axioms gasSteps_overflow

def gasSteps_count (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 8523, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest}
      (conditionalModel (countModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest)) := by
  have g0 := block_count.steps (s := {s with pc := UInt256.ofNat 8523, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest}) (env.transfer rfl rfl) rfl (count_run s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest hcap hact)
  have hv : Decode.isValidJumpDest s.executionEnv.code 8800 = true := by
    rw [env.code]; exact validJump8800
  have g1 := block_countBranch.steps (s := countModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest) (env.transfer rfl rfl) rfl
    (count_control s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest hcap hv)
  exact g0.trans g1
#print axioms gasSteps_count

def gasSteps_retain (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 8532, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest}
      (resumeModel (retainModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest)) := by
  let t := retainModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest
  have g0 := block_retain.steps (s := {s with pc := UInt256.ofNat 8532, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest}) (env.transfer rfl rfl) rfl (retain_run s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest hcap hact)
  have et : Environment Artifact.submissionArtifact .Osaka t := env.transfer rfl rfl
  have hv : Decode.isValidJumpDest t.executionEnv.code (UInt256.ofNat 5858).toNat = true := by
    rw [et.code]; exact validJump5858
  have hc : t.stack.length < 1024 := by
    dsimp only [t, retainModel]
    simp only [List.length_cons]
    omega
  have g1 := block_retainBranch.steps et rfl
    (jump_run t (UInt256.ofNat 5858) (t.stack.drop 1) rfl hc hv)
  have hd : (jumpModel t).stack.length < 1024 := by
    dsimp only [jumpModel, t, retainModel]
    simp only [List.drop_succ_cons, List.drop_zero, List.length_cons]
    omega
  have g2 := block_loopHead.steps (s := jumpModel t) (et.transfer rfl rfl) rfl (jumpDest_run (jumpModel t) hd)
  exact (g0.trans g1).trans g2
#print axioms gasSteps_retain

def gasSteps_exit (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 8800, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest}
      (jumpModel (exitModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest)) := by
  have hv : Decode.isValidJumpDest s.executionEnv.code 3942 = true := by
    rw [env.code]; exact validJump3942
  have g0 := block_exit.steps (s := {s with pc := UInt256.ofNat 8800, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest}) (env.transfer rfl rfl) rfl (exit_run s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest hcap hact)
  have g1 := block_exitBranch.steps (s := exitModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest) (env.transfer rfl rfl) rfl
    (exit_control s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest hcap hv)
  exact g0.trans g1
#print axioms gasSteps_exit

end HistoricalSearch.CRTGasSteps
