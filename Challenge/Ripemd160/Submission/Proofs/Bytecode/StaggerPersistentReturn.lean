import Challenge.EvmProof.Memory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedHelperBooleanTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentReturn
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace

@[simp] private theorem rawZeroNat : (⟨0⟩ : UInt256).toNat = 0 := rfl

def template : List Instr :=
  [.push ⟨0, by decide⟩ (UInt256.ofNat 0), .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 32), .push ⟨0, by decide⟩ (UInt256.ofNat 0), .op .RETURN]
def outputMemory (s : State) (value : UInt256) : ByteArray :=
  MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded value.toNat 32) 0

def result (s : State) (pc value : UInt256) (rho : List UInt256) : State :=
  {s with
    pc := pcAfter pc template.dropLast
    stack := rho
    memory := outputMemory s value
    activeWords := UInt256.ofNat (MachineState.activeWordsAfter
      (s.activeWordsAfterUInt256 0 32).toNat 0 32)
    halt := .Returned
    hReturn := MachineState.readPadded (outputMemory s value) 0 32}

theorem run_template (s : State) (pc value : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1019) (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := pc, stack := value :: rho} =
      some (result s pc value rho) := by
  have hcap (n : Nat) (hn : n ≤ 4) : rho.length + n < 1024 := by omega
  have hs : rho.length < 1024 := by omega
  simp (discharger := omega) [template, result, outputMemory, runInstrSeq, Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, hrun, hcap, hs, Nat.add_assoc,
    State.activeWordsAfterUInt256, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl

theorem advances : ∀ instruction ∈ template.dropLast, DenseScheduleLift.Advances instruction := by
  apply Table80SiteCommon.coreAdvancesAll_sound
  decide

def gasSteps_site {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork template)
    (s : State) (value : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1019) (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := site.startPC, stack := value :: rho}
      (result s site.startPC value rho) :=
  gasSteps_terminal_of_raw site _ _ hcode hfork hrun hnp rfl advances
    (run_template s site.startPC value rho hstack hrun)

theorem returned_bytes (s : State) (pc value : UInt256) (rho : List UInt256) :
    (result s pc value rho).hReturn = Data.Bytes.natToBytesPadded value.toNat 32 := by
  unfold result outputMemory
  have h := Memory.readPadded_writeBytes_same s.memory
    (Data.Bytes.natToBytesPadded value.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using h
#print axioms run_template
#print axioms gasSteps_site
#print axioms returned_bytes
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentReturn
