import Challenge.Sha256.Submission.Proofs.Bytecode.Functions
import Mathlib.Data.Nat.Bitwise
set_option warningAsError true
set_option maxRecDepth 10000

/-! Certified summaries for the fused SHA-256 big-sigma helpers. -/

namespace Challenge.Sha256.Submission.Proofs.Bytecode.BigSigma

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private theorem word_land_comm (a b : UInt256) : a.land b = b.land a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_land, Nat.land_comm]

private theorem mask32_add_distrib (x y : UInt256) :
    Challenge.EvmProof.Word.mask32 (x + y) =
      Challenge.EvmProof.Word.mask32
        (Challenge.EvmProof.Word.mask32 x +
          Challenge.EvmProof.Word.mask32 y) := by
  rw [Challenge.EvmProof.Word.mask32_eq_ofUInt32,
    Challenge.EvmProof.Word.mask32_eq_ofUInt32 x,
    Challenge.EvmProof.Word.mask32_eq_ofUInt32 y,
    Challenge.EvmProof.Word.mask32_add]
  congr 1
  apply UInt32.toNat_inj.mp
  simp only [Challenge.EvmProof.Word.toUInt32_toNat, UInt32.toNat_add]
  change ((x.val + y.val).val % 2 ^ 32) =
    (x.toNat % 2 ^ 32 + y.toNat % 2 ^ 32) % 2 ^ 32
  rw [Fin.val_add]
  change ((x.toNat + y.toNat) % UInt256.size) % 2 ^ 32 = _
  rw [show UInt256.size = 2 ^ 256 by rfl,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)), Nat.add_mod]

private theorem mask32_add_congr {x x' y y' : UInt256}
    (hx : Challenge.EvmProof.Word.mask32 x =
      Challenge.EvmProof.Word.mask32 x')
    (hy : Challenge.EvmProof.Word.mask32 y =
      Challenge.EvmProof.Word.mask32 y') :
    Challenge.EvmProof.Word.mask32 (x + y) =
      Challenge.EvmProof.Word.mask32 (x' + y') := by
  rw [mask32_add_distrib x y, mask32_add_distrib x' y', hx, hy]

private theorem mask32_t1_fused (x addend1 addend2 h7 : UInt256) :
    Challenge.EvmProof.Word.mask32
        (((h7 + Word.rawFusedBigSigma1 x) + addend1) + addend2) =
      Challenge.EvmProof.Word.mask32
        (((h7 + Word.evmBigSigma1 x) + addend1) + addend2) := by
  have h0 := mask32_add_congr (x := h7) (x' := h7)
    (y := Word.rawFusedBigSigma1 x) (y' := Word.evmBigSigma1 x)
    rfl (Word.mask32_rawFusedBigSigma1 x)
  have h1 := mask32_add_congr h0
    (y := addend1) (y' := addend1) rfl
  have h2 := mask32_add_congr h1 (y := addend2) (y' := addend2) rfl
  exact h2

/-- Two-word ABI used by the fused helpers: input followed by return PC. -/
def entry (s : State) (entryPC : Nat) (x returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat entryPC
    stack := [x, returnDest] ++ rest }

/-- Specialized ABI for BSIG0 fused with the T2 addition and mask. -/
def t2Entry (s : State) (x addend : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 114
    stack := [x, addend, UInt256.ofNat 0xffffffff] ++ rest }

def t2Returned (s : State) (x addend : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 783
    stack := Challenge.EvmProof.Word.mask32
      (Word.evmBigSigma0 x + addend) :: rest }

/-- Specialized ABI for BSIG1 fused through all remaining T1 arithmetic. -/
def t1Entry (s : State) (x addend1 addend2 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 163
    stack := [x, addend1, addend2, UInt256.ofNat 0xffffffff] ++ rest }

def t1Returned (s : State) (x addend1 addend2 : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 725
    stack := Challenge.EvmProof.Word.mask32
      (((MachineState.readWord s.memory 512 + Word.evmBigSigma1 x) +
        addend1) + addend2) :: rest
    activeWords := s.activeWordsAfterUInt256 512 32 }

def bigSigma0Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨79, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨80, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨81, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨82, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨83, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨84, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨85, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨86, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨87, .push ⟨1, by decide⟩ (UInt256.ofNat 11), by rfl, by decide⟩,
   ⟨88, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨89, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨90, .push ⟨1, by decide⟩ (UInt256.ofNat 9), by rfl, by decide⟩,
   ⟨91, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨92, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨93, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨94, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨95, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨96, .push ⟨2, by decide⟩ (UInt256.ofNat 783), by rfl, by decide⟩,
   ⟨97, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def bigSigma1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨111, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨112, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨113, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨114, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨115, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨116, .push ⟨1, by decide⟩ (UInt256.ofNat 6), by rfl, by decide⟩,
   ⟨117, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨118, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨119, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨120, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨121, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨122, .push ⟨1, by decide⟩ (UInt256.ofNat 14), by rfl, by decide⟩,
   ⟨123, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨124, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨125, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨126, .push ⟨2, by decide⟩ (UInt256.ofNat 512), by rfl, by decide⟩,
   ⟨127, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨128, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨129, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨130, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨131, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨132, .push ⟨2, by decide⟩ (UInt256.ofNat 725), by rfl, by decide⟩,
   ⟨133, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem bigSigma0PC (i : Nat) (hlo : 79 ≤ i) (hhi : i ≤ 97) :
    Artifact.referenceArtifact.instructionPC i =
      [114, 115, 116, 118, 119, 120, 122, 123, 124, 126, 127, 128, 130,
        131, 132, 133, 134, 135, 138][i - 79]! := by
  interval_cases i <;> decide

@[simp] private theorem bigSigma1PC (i : Nat) (hlo : 111 ≤ i) (hhi : i ≤ 133) :
    Artifact.referenceArtifact.instructionPC i =
      [163, 164, 165, 167, 168, 169, 171, 172, 173, 175, 176, 177, 179,
        180, 181, 182, 185, 186, 187, 188, 189, 190, 193][i - 111]! := by
  interval_cases i <;> decide

set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
theorem run_bigSigma0 (s : State) (x addend : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock bigSigma0Path
      (t2Entry s x addend rest) =
        some (t2Returned s x addend rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hdest : Decode.isValidJumpDest submissionBytecode 783 = true := by decide
  simp [bigSigma0Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    t2Entry, t2Returned, Word.rawFusedBigSigma0, Word.duplicateLane,
    Challenge.EvmProof.Word.mask32, List.exchange,
    hc1, hc2, hc3, hc4, hc5, hc6, hcode, hrun, hdest]
  change Challenge.EvmProof.Word.mask32
      (Word.rawFusedBigSigma0 x + addend) =
    Challenge.EvmProof.Word.mask32 (Word.evmBigSigma0 x + addend)
  exact mask32_add_congr (Word.mask32_rawFusedBigSigma0 x) rfl

set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
theorem run_bigSigma1 (s : State) (x addend1 addend2 : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock bigSigma1Path
      (t1Entry s x addend1 addend2 rest) =
        some (t1Returned s x addend1 addend2 rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hdest : Decode.isValidJumpDest submissionBytecode 725 = true := by decide
  simp [bigSigma1Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    t1Entry, t1Returned, Word.rawFusedBigSigma1, Word.duplicateLane,
    Challenge.EvmProof.Word.mask32, List.exchange,
    hc1, hc2, hc3, hc4, hc5, hc6, hc7, hcode, hrun, hdest,
    State.activeWordsAfterUInt256]
  change Challenge.EvmProof.Word.mask32
      (((MachineState.readWord s.memory 512 + Word.rawFusedBigSigma1 x) +
        addend1) + addend2) =
    Challenge.EvmProof.Word.mask32
      (((MachineState.readWord s.memory 512 + Word.evmBigSigma1 x) +
        addend1) + addend2)
  exact mask32_t1_fused x addend1 addend2
    (MachineState.readWord s.memory 512)

def gasSteps_bigSigma0 (s : State) (x addend : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (t2Entry s x addend rest)
      (t2Returned s x addend rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka bigSigma0Path
  · exact hcode
  · exact hfork
  · exact run_bigSigma0 s x addend rest hcap hcode hrun
  · exact hrun
  · exact hnp

def gasSteps_bigSigma1 (s : State) (x addend1 addend2 : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (t1Entry s x addend1 addend2 rest)
      (t1Returned s x addend1 addend2 rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka bigSigma1Path
  · exact hcode
  · exact hfork
  · exact run_bigSigma1 s x addend1 addend2 rest hcap hcode hrun
  · exact hrun
  · exact hnp

end Challenge.Sha256.Submission.Proofs.Bytecode.BigSigma
