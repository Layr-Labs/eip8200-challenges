import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80CoreCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackMemory
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Bootstrap
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate Table80Raw
open Paired80WordRound Paired80WordRotate Paired80WordBoolean

def template : List Instr :=
 [ .op .JUMPDEST,
   .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295),
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 80),
   .op .SHL,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .OR,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .DIV,
   .push ⟨2, by decide⟩ (UInt256.ofNat 960),
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op .MUL,
   .push ⟨2, by decide⟩ (UInt256.ofNat 928),
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op .MUL,
   .push ⟨2, by decide⟩ (UInt256.ofNat 896),
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push ⟨2, by decide⟩ (UInt256.ofNat 864),
   .op .MLOAD,
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .push ⟨2, by decide⟩ (UInt256.ofNat 832),
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .push ⟨24, by decide⟩ (UInt256.ofNat 196159429276505700036459135669104726525582452008043937793),
   .op (.Swap ⟨5, by decide⟩),
   .op .POP,
   .push ⟨14, by decide⟩ (UInt256.ofNat 1635471027088748134935197149822976) ]
def packedHash (memory : ByteArray) (address : Nat) : UInt256 :=
  UInt256.mul (UInt256.ofNat 1208925819614629174706177) (MachineState.readWord memory address)
def resultStack (memory : ByteArray) (rho : List UInt256) : List UInt256 :=
 [ UInt256.ofNat 1635471027088748134935197149822976,
   packedHash memory 832, packedHash memory 864, packedHash memory 896,
   packedHash memory 928, packedHash memory 960,
   UInt256.ofNat 196159429276505700036459135669104726525582452008043937793, UInt256.ofNat 5192296857325901808915871449481215, UInt256.ofNat 5192296857325901808915867154513920, UInt256.ofNat 4294967295 ] ++ (cache ++ rho)
theorem upper_const : UInt256.shiftLeft (UInt256.ofNat 4294967295) (UInt256.ofNat 80) = UInt256.ofNat 5192296857325901808915867154513920 := by decide
theorem pair_const : UInt256.lor (UInt256.ofNat 4294967295) (UInt256.ofNat 5192296857325901808915867154513920) = UInt256.ofNat 5192296857325901808915871449481215 := by decide
theorem factor_const : UInt256.div (UInt256.ofNat 5192296857325901808915871449481215) (UInt256.ofNat 4294967295) = UInt256.ofNat 1208925819614629174706177 := by decide

theorem run_actual (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := cache ++ rho} =
      some {s with pc := pcAfter pc template, stack := resultStack s.memory rho} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [template, resultStack, packedHash, cache,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat,
    upper_const, pair_const, factor_const, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_actual

theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 668).take template.length = template := by rfl
def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 668 actual_slice
    (by change 668 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 1048 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 668) = UInt256.ofNat 1048
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem runInstr_pc_div {s t : State}
    (hresult : Stepper.runInstr (.op .DIV) s = some t) :
    t.pc = s.pc + UInt256.ofNat (Instr.op .DIV).size := by
  by_cases hcap : s.stack.length < 1024
  · rw [Stepper.runInstr, if_pos hcap] at hresult
    cases hs : s.stack with
    | nil => simp [hs] at hresult
    | cons a tail =>
        cases ht : tail with
        | nil => simp [hs, ht] at hresult
        | cons b rest =>
            simp [hs, ht] at hresult
            subst t
            rfl
  · simp [Stepper.runInstr, hcap] at hresult


theorem advances (instruction : Instr) (hm : instruction ∈ template) (s t : State)
    (h : Stepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  by_cases hd : instruction = .op .DIV
  · subst instruction; exact runInstr_pc_div h
  · apply DenseScheduleLift.runInstr_pc_of_advances ?_ h
    apply Table80SiteCommon.coreAdvancesCheck_sound
    have hc : ∀ i ∈ template, i = .op .DIV ∨ Table80SiteCommon.coreAdvancesCheck i = true := by
      intro i hi
      simp only [template, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact Or.inl rfl | exact Or.inr (by decide)
    exact (hc instruction hm).resolve_left hd

def gasSteps (s : State) (rho : List UInt256)
    (hstack : rho.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 1048, stack := cache ++ rho}
      {s with pc := UInt256.ofNat 1136, stack := resultStack s.memory rho} := by
  apply Stepper.runLocatedBlock_sound _ _ site.path
  · exact hcode
  · exact hfork
  · have hpc : ({s with pc := UInt256.ofNat 1048, stack := cache ++ rho} : State).pc = site.startPC := site_pc.symm
    rw [runLocatedBlock_eq_runInstrSeq_site site _ hpc (by
      intro located hm u v hu
      apply advances _ ?_ u v hu
      rw [← site.instruction_eq]
      exact List.mem_map_of_mem hm)]
    have hraw := run_actual s (UInt256.ofNat 1048) rho hstack hrun hactive
    have hend : pcAfter (UInt256.ofNat 1048) template = UInt256.ofNat 1136 := by decide
    rw [hend] at hraw
    exact hraw
  · exact hrun
  · exact hnp
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Bootstrap
