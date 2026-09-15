import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLocated

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof Challenge.EvmProof.Stepper WindowNibbleKernel

/-- All premises needed to lift a symbolic step to the real EVM relation. -/
structure Environment (artifact : ProgramArtifact) (fork : Fork) (s : State) : Prop where
  sizeBound : artifact.code.size < 2 ^ 256
  code : s.executionEnv.code = artifact.code
  forkEq : s.fork = fork
  running : s.halt = .Running
  noPrecompile : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false

def Environment.transfer {artifact : ProgramArtifact} {fork : Fork} {s t : State}
    (env : Environment artifact fork s)
    (henv : t.executionEnv = s.executionEnv) (hhalt : t.halt = s.halt) :
    Environment artifact fork t where
  sizeBound := env.sizeBound
  code := henv ▸ env.code
  forkEq := by change t.executionEnv.fork = fork; rw [henv]; exact env.forkEq
  running := hhalt.trans env.running
  noPrecompile := by rw [henv]; exact env.noPrecompile

/-- Exact opcode and instruction-location certificate for one straight block.
The last instruction may be a jump or RETURN. -/
structure Block (artifact : ProgramArtifact) (fork : Fork) (pc : Nat)
    (instructions : List Instr) where
  path : List (Located artifact fork)
  instructions_eq : path.map Located.instruction = instructions
  layout : WindowTwentyOneLocated.LinearPath (UInt256.ofNat pc) path

def Block.steps {artifact : ProgramArtifact} {fork : Fork} {pc : Nat}
    {instructions : List Instr} (block : Block artifact fork pc instructions)
    {s t : State} (env : Environment artifact fork s)
    (hpc : s.pc = UInt256.ofNat pc) (hrun : runInstructions instructions s = some t) :
    GasSteps s t := by
  have hraw : runInstructions (block.path.map Located.instruction) s = some t := by
    rw [block.instructions_eq]
    exact hrun
  exact runLocatedBlock_sound artifact fork block.path env.code env.forkEq
    (WindowTwentyOneLocated.run_linear block.path _ s t env.sizeBound block.layout hpc env.running hraw)
    env.running env.noPrecompile

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
