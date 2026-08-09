import Challenge.Sha256.Submission.Proofs.Bytecode.ResidentLoop

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

namespace Challenge.Sha256.Submission.Proofs.Bytecode.ResidentExitSegments

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Sha256.Submission.Proofs.Bytecode

def conditionPath := Compression.pairConditionPath
def write0Path := (Compression.pairExitPath.drop 6).take 4
def write1Path := (Compression.pairExitPath.drop 10).take 3
def write2Path := (Compression.pairExitPath.drop 13).take 3
def write3Path := (Compression.pairExitPath.drop 16).take 3
def write4Path := (Compression.pairExitPath.drop 19).take 3
def write5Path := (Compression.pairExitPath.drop 22).take 3
def write6Path := (Compression.pairExitPath.drop 25).take 3
def write7Path := (Compression.pairExitPath.drop 28).take 3
def cleanupPath := Compression.pairExitPath.drop 31

@[simp] private theorem toNat288 : (288 : UInt256).toNat = 288 := by decide
@[simp] private theorem toNat320 : (320 : UInt256).toNat = 320 := by decide
@[simp] private theorem toNat352 : (352 : UInt256).toNat = 352 := by decide
@[simp] private theorem toNat384 : (384 : UInt256).toNat = 384 := by decide
@[simp] private theorem toNat416 : (416 : UInt256).toNat = 416 := by decide
@[simp] private theorem toNat448 : (448 : UInt256).toNat = 448 := by decide
@[simp] private theorem toNat480 : (480 : UInt256).toNat = 480 := by decide
@[simp] private theorem toNat512 : (512 : UInt256).toNat = 512 := by decide

def q0 (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  { Compression.residentAt base ghost msgOff returnDest rest 64 with
    pc := UInt256.ofNat 886 }

def q1 (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  { Compression.storedWord (q0 base ghost msgOff returnDest rest)
      288 (Compression.hValue ghost 0) with pc := UInt256.ofNat 892 }

def q2 (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  { Compression.storedWord (q1 base ghost msgOff returnDest rest)
      320 (Compression.hValue ghost 1) with pc := UInt256.ofNat 897 }

def q3 (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  { Compression.storedWord (q2 base ghost msgOff returnDest rest)
      352 (Compression.hValue ghost 2) with pc := UInt256.ofNat 902 }

def q4 (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  { Compression.storedWord (q3 base ghost msgOff returnDest rest)
      384 (Compression.hValue ghost 3) with pc := UInt256.ofNat 907 }

def q5 (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  { Compression.storedWord (q4 base ghost msgOff returnDest rest)
      416 (Compression.hValue ghost 4) with pc := UInt256.ofNat 912 }

def q6 (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  { Compression.storedWord (q5 base ghost msgOff returnDest rest)
      448 (Compression.hValue ghost 5) with pc := UInt256.ofNat 917 }

def q7 (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  { Compression.storedWord (q6 base ghost msgOff returnDest rest)
      480 (Compression.hValue ghost 6) with pc := UInt256.ofNat 922 }

def q8 (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  { Compression.storedWord (q7 base ghost msgOff returnDest rest)
      512 (Compression.hValue ghost 7) with pc := UInt256.ofNat 927 }

@[simp] private theorem q0_env (b g : State) (m r : UInt256) (xs) :
    (q0 b g m r xs).executionEnv = b.executionEnv := by rfl
@[simp] private theorem q1_env (b g : State) (m r : UInt256) (xs) :
    (q1 b g m r xs).executionEnv = b.executionEnv := by rfl
@[simp] private theorem q2_env (b g : State) (m r : UInt256) (xs) :
    (q2 b g m r xs).executionEnv = b.executionEnv := by rfl
@[simp] private theorem q3_env (b g : State) (m r : UInt256) (xs) :
    (q3 b g m r xs).executionEnv = b.executionEnv := by rfl
@[simp] private theorem q4_env (b g : State) (m r : UInt256) (xs) :
    (q4 b g m r xs).executionEnv = b.executionEnv := by rfl
@[simp] private theorem q5_env (b g : State) (m r : UInt256) (xs) :
    (q5 b g m r xs).executionEnv = b.executionEnv := by rfl
@[simp] private theorem q6_env (b g : State) (m r : UInt256) (xs) :
    (q6 b g m r xs).executionEnv = b.executionEnv := by rfl
@[simp] private theorem q7_env (b g : State) (m r : UInt256) (xs) :
    (q7 b g m r xs).executionEnv = b.executionEnv := by rfl
@[simp] private theorem q8_env (b g : State) (m r : UInt256) (xs) :
    (q8 b g m r xs).executionEnv = b.executionEnv := by rfl

@[simp] private theorem q0_halt (b g : State) (m r : UInt256) (xs) :
    (q0 b g m r xs).halt = b.halt := by rfl
@[simp] private theorem q1_halt (b g : State) (m r : UInt256) (xs) :
    (q1 b g m r xs).halt = b.halt := by rfl
@[simp] private theorem q2_halt (b g : State) (m r : UInt256) (xs) :
    (q2 b g m r xs).halt = b.halt := by rfl
@[simp] private theorem q3_halt (b g : State) (m r : UInt256) (xs) :
    (q3 b g m r xs).halt = b.halt := by rfl
@[simp] private theorem q4_halt (b g : State) (m r : UInt256) (xs) :
    (q4 b g m r xs).halt = b.halt := by rfl
@[simp] private theorem q5_halt (b g : State) (m r : UInt256) (xs) :
    (q5 b g m r xs).halt = b.halt := by rfl
@[simp] private theorem q6_halt (b g : State) (m r : UInt256) (xs) :
    (q6 b g m r xs).halt = b.halt := by rfl
@[simp] private theorem q7_halt (b g : State) (m r : UInt256) (xs) :
    (q7 b g m r xs).halt = b.halt := by rfl
@[simp] private theorem q8_halt (b g : State) (m r : UInt256) (xs) :
    (q8 b g m r xs).halt = b.halt := by rfl

set_option linter.unusedSimpArgs false in
theorem runCondition (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcode : base.executionEnv.code = submissionBytecode)
    (hrun : base.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock conditionPath
      (Compression.residentAt base ghost msgOff returnDest rest 64) =
        some (q0 base ghost msgOff returnDest rest) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hterminal : (2848 : UInt256).toNat = 2848 := by decide
  have h1 : (1 : UInt256).toNat = 1 := by decide
  have h886 : (886 : UInt256).toNat = 886 := by decide
  have h886Eq : (886 : UInt256) = UInt256.ofNat 886 := by decide
  have hdest : Decode.isValidJumpDest submissionBytecode 886 = true := by decide
  have hw64 : (Compression.pairWPtr 64).toNat = 2848 := by decide
  simp [conditionPath, Compression.pairConditionPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Compression.residentAt, q0, Nat.add_assoc, hc12, hc13, hc14,
    hcode, hrun, UInt256.eq, UInt256.isTrue, hterminal, h1,
    h886, h886Eq, hdest, hw64]

private theorem runWrite0 (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hrun : base.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock write0Path
      (q0 base ghost msgOff returnDest rest) =
        some (q1 base ghost msgOff returnDest rest) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  simp [write0Path, Compression.pairExitPath, Compression.pairConditionPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    q0, q1, Compression.residentAt, Compression.storedWord,
    Nat.add_assoc, hc12, hc13, hc14, hrun,
    State.activeWordsAfterUInt256]

private theorem runWrite1 (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hrun : base.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock write1Path
      (q1 base ghost msgOff returnDest rest) =
        some (q2 base ghost msgOff returnDest rest) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  simp [write1Path, Compression.pairExitPath, Compression.pairConditionPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    q0, q1, q2, Compression.residentAt, Compression.storedWord,
    Nat.add_assoc, hc12, hc13, hc14, hrun,
    State.activeWordsAfterUInt256]

private theorem runWrite2 (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hrun : base.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock write2Path
      (q2 base ghost msgOff returnDest rest) =
        some (q3 base ghost msgOff returnDest rest) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  simp [write2Path, Compression.pairExitPath, Compression.pairConditionPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    q0, q1, q2, q3, Compression.residentAt, Compression.storedWord,
    Nat.add_assoc, hc12, hc13, hc14, hrun,
    State.activeWordsAfterUInt256]

private theorem runWrite3 (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hrun : base.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock write3Path
      (q3 base ghost msgOff returnDest rest) =
        some (q4 base ghost msgOff returnDest rest) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  simp [write3Path, Compression.pairExitPath, Compression.pairConditionPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    q0, q1, q2, q3, q4, Compression.residentAt, Compression.storedWord,
    Nat.add_assoc, hc12, hc13, hc14, hrun,
    State.activeWordsAfterUInt256]

private theorem runWrite4 (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hrun : base.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock write4Path
      (q4 base ghost msgOff returnDest rest) =
        some (q5 base ghost msgOff returnDest rest) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  simp [write4Path, Compression.pairExitPath, Compression.pairConditionPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    q0, q1, q2, q3, q4, q5, Compression.residentAt, Compression.storedWord,
    Nat.add_assoc, hc12, hc13, hc14, hrun,
    State.activeWordsAfterUInt256]

private theorem runWrite5 (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hrun : base.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock write5Path
      (q5 base ghost msgOff returnDest rest) =
        some (q6 base ghost msgOff returnDest rest) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  simp [write5Path, Compression.pairExitPath, Compression.pairConditionPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    q0, q1, q2, q3, q4, q5, q6, Compression.residentAt,
    Compression.storedWord, Nat.add_assoc, hc12, hc13, hc14, hrun,
    State.activeWordsAfterUInt256]

private theorem runWrite6 (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hrun : base.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock write6Path
      (q6 base ghost msgOff returnDest rest) =
        some (q7 base ghost msgOff returnDest rest) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  simp [write6Path, Compression.pairExitPath, Compression.pairConditionPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    q0, q1, q2, q3, q4, q5, q6, q7, Compression.residentAt,
    Compression.storedWord, Nat.add_assoc, hc12, hc13, hc14, hrun,
    State.activeWordsAfterUInt256]

private theorem runWrite7 (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hrun : base.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock write7Path
      (q7 base ghost msgOff returnDest rest) =
        some (q8 base ghost msgOff returnDest rest) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  simp [write7Path, Compression.pairExitPath, Compression.pairConditionPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    q0, q1, q2, q3, q4, q5, q6, q7, q8, Compression.residentAt,
    Compression.storedWord, Nat.add_assoc, hc12, hc13, hc14, hrun,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem runCleanup (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hrun : base.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock cleanupPath
      (q8 base ghost msgOff returnDest rest) =
        some (Compression.residentExitStored base ghost msgOff returnDest rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have h935Eq : (935 : UInt256) = UInt256.ofNat 935 := by decide
  simp [cleanupPath, Compression.pairExitPath, Compression.pairConditionPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    q0, q1, q2, q3, q4, q5, q6, q7, q8,
    Compression.residentAt, Compression.residentExitStored,
    Compression.storedWord, List.exchange, Nat.add_assoc,
    hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12,
    hrun, h935Eq,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    State.activeWordsAfterUInt256]

private def sound {a b : State}
    (path : List (Challenge.EvmProof.Stepper.Located
      Artifact.referenceArtifact .Osaka))
    (hexec : Challenge.EvmProof.Stepper.runLocatedBlock path a = some b)
    (hcode : a.executionEnv.code = submissionBytecode)
    (hfork : a.fork = .Osaka) (hrun : a.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig a.executionEnv.precompileConfig
      a.executionEnv.fork a.executionEnv.codeAddr = false)
    : Challenge.EvmProof.GasSteps a b :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path hcode hfork hexec hrun hnp

def gasStepsExit (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1000)
    (hcode : base.executionEnv.code = submissionBytecode)
    (hfork : base.fork = .Osaka) (hrun : base.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig base.executionEnv.precompileConfig
      base.executionEnv.fork base.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (Compression.residentAt base ghost msgOff returnDest rest 64)
      (Compression.residentExitStored base ghost msgOff returnDest rest) := by
  have g0 := sound conditionPath
    (runCondition base ghost msgOff returnDest rest hcap hcode hrun)
    (by simpa using hcode) (by simpa [State.fork] using hfork)
    (by simpa using hrun) (by simpa using hnp)
  have g1 := sound write0Path
    (runWrite0 base ghost msgOff returnDest rest hcap hrun)
    (by simpa using hcode) (by simpa [State.fork] using hfork)
    (by simpa using hrun) (by simpa using hnp)
  have g2 := sound write1Path
    (runWrite1 base ghost msgOff returnDest rest hcap hrun)
    (by simpa using hcode) (by simpa [State.fork] using hfork)
    (by simpa using hrun) (by simpa using hnp)
  have g3 := sound write2Path
    (runWrite2 base ghost msgOff returnDest rest hcap hrun)
    (by simpa using hcode) (by simpa [State.fork] using hfork)
    (by simpa using hrun) (by simpa using hnp)
  have g4 := sound write3Path
    (runWrite3 base ghost msgOff returnDest rest hcap hrun)
    (by simpa using hcode) (by simpa [State.fork] using hfork)
    (by simpa using hrun) (by simpa using hnp)
  have g5 := sound write4Path
    (runWrite4 base ghost msgOff returnDest rest hcap hrun)
    (by simpa using hcode) (by simpa [State.fork] using hfork)
    (by simpa using hrun) (by simpa using hnp)
  have g6 := sound write5Path
    (runWrite5 base ghost msgOff returnDest rest hcap hrun)
    (by simpa using hcode) (by simpa [State.fork] using hfork)
    (by simpa using hrun) (by simpa using hnp)
  have g7 := sound write6Path
    (runWrite6 base ghost msgOff returnDest rest hcap hrun)
    (by simpa using hcode) (by simpa [State.fork] using hfork)
    (by simpa using hrun) (by simpa using hnp)
  have g8 := sound write7Path
    (runWrite7 base ghost msgOff returnDest rest hcap hrun)
    (by simpa using hcode) (by simpa [State.fork] using hfork)
    (by simpa using hrun) (by simpa using hnp)
  have g9 := sound cleanupPath
    (runCleanup base ghost msgOff returnDest rest hcap hrun)
    (by simpa using hcode) (by simpa [State.fork] using hfork)
    (by simpa using hrun) (by simpa using hnp)
  exact g0.trans (g1.trans (g2.trans (g3.trans (g4.trans
    (g5.trans (g6.trans (g7.trans (g8.trans g9))))))))

theorem foldAt_zero_eq (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hpc : s.pc = UInt256.ofNat 939)
    (hstack : s.stack = [UInt256.ofNat 0, msgOff, returnDest] ++ rest) :
    Compression.foldAt s msgOff returnDest rest 0 = s := by
  cases s with
  | mk shared pc stack execLength halt callStack =>
    simp_all [Compression.foldAt]

end Challenge.Sha256.Submission.Proofs.Bytecode.ResidentExitSegments
