import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80RawCommon
 import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
 set_option warningAsError true
 set_option maxRecDepth 100000
 set_option maxHeartbeats 4000000
 set_option linter.unusedSimpArgs false
 namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80RawRound29
 open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
 open StackRoundTrace Table80Raw

 def template : List Instr :=
   [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨7, by decide⟩),
    .op .OR,
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op .AND,
    .op .OR,
    .op .ADD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 50),
    .op .MLOAD,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 255),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .op (.Dup ⟨14, by decide⟩),
    .op .SHR,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .op (.Dup ⟨10, by decide⟩),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
 def outputStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
   [ (UInt256.land x.v7 (UInt256.shiftRight (UInt256.mul x.v6 x.v2) (UInt256.ofNat 22))),
    x.v1,
    (UInt256.land x.v7 (UInt256.add x.v1 (UInt256.shiftRight (UInt256.mul x.v6 (UInt256.add (UInt256.mul (UInt256.ofNat 255) (UInt256.land x.v8 (UInt256.land x.v7 (UInt256.add x.v4 (UInt256.add (MachineState.readWord memory 50) (UInt256.add (UInt256.lor (UInt256.land x.v2 x.v3) (UInt256.xor x.v0 (UInt256.land (UInt256.lor x.v0 x.v2) (UInt256.xor x.v8 x.v3)))) x.v5)))))) (UInt256.land x.v7 (UInt256.add x.v4 (UInt256.add (MachineState.readWord memory 50) (UInt256.add (UInt256.lor (UInt256.land x.v2 x.v3) (UInt256.xor x.v0 (UInt256.land (UInt256.lor x.v0 x.v2) (UInt256.xor x.v8 x.v3)))) x.v5)))))) (UInt256.ofNat 25)))),
    x.v3,
    x.v4,
    x.v0,
    x.v6,
    x.v7,
    x.v8,
    x.v9 ] ++ (cache ++ rho)

 theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
     (hstack : rho.length ≤ 996) (hrun : s.halt = .Running)
     (hactive : 34 ≤ s.activeWords.toNat) :
     runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
       some {s with pc := pcAfter pc template, stack := outputStack s.memory x rho} := by
   have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
   have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
       UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
     active_preserved s.activeWords address hactive haddress
   simp (discharger := omega) [template, inputStack, outputStack, cache,
     runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat,
     Word.literal_eq_ofNat]
   all_goals repeat first | apply And.intro | rfl
 #print axioms run_actual

 theorem actual_slice :
     (Artifact.submissionArtifact.instructions.drop 1910).take template.length = template := by rfl
 def site : StackRoundTemplate.GenericRoundSite Artifact.submissionArtifact .Osaka template :=
   StackSiteBuilder.ofSlice template 1910 actual_slice
     (by change 1910 + template.length ≤ Artifact.submissionInstructions.length
         rw [Artifact.referenceInstructions_count]; decide)
     StackRoundData.artifact_code_bound
     (StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
     (by decide)
 theorem site_pc : site.startPC = UInt256.ofNat 2438 := by
   change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1910) = UInt256.ofNat 2438
   rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
 theorem advances : ∀ instruction ∈ template, DenseScheduleLift.Advances instruction := by
   apply Table80SiteCommon.coreAdvancesAll_sound
   decide

 def gasSteps (s : State) (x : Input) (rho : List UInt256)
     (hstack : rho.length ≤ 996) (hrun : s.halt = .Running)
     (hactive : 34 ≤ s.activeWords.toNat)
     (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
     (hfork : s.fork = .Osaka)
     (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
       s.executionEnv.fork s.executionEnv.codeAddr = false) :
     GasSteps {s with pc := UInt256.ofNat 2438, stack := inputStack x rho}
       {s with pc := UInt256.ofNat 2483, stack := outputStack s.memory x rho} := by
   have hraw := run_actual s (UInt256.ofNat 2438) x rho hstack hrun hactive
   have hend : pcAfter (UInt256.ofNat 2438) template = UInt256.ofNat 2483 := by decide
   rw [hend] at hraw
   exact DenseScheduleLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp site_pc.symm advances hraw
 #print axioms gasSteps

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80RawRound29
