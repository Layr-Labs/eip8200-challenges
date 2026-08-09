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

private theorem mask32_t1_fused (x y z addend1 addend2 : UInt256) :
    Challenge.EvmProof.Word.mask32
        (((Word.rawFusedBigSigma1 x + Word.evmCh x y z) +
          addend1) + addend2) =
      Challenge.EvmProof.Word.mask32
        (((Word.evmBigSigma1 x + Word.evmCh x y z) +
          addend1) + addend2) := by
  have h0 := mask32_add_congr (Word.mask32_rawFusedBigSigma1 x)
    (y := Word.evmCh x y z)
    (y' := Word.evmCh x y z) rfl
  have h1 := mask32_add_congr h0
    (y := addend1) (y' := addend1) rfl
  have h2 := mask32_add_congr h1 (y := addend2) (y' := addend2) rfl
  exact h2

private theorem mask32_t2_fused (x y z : UInt256) :
    Challenge.EvmProof.Word.mask32
        (Word.rawFusedBigSigma0 x + Word.evmMaj x y z) =
      Challenge.EvmProof.Word.mask32
        (Word.evmBigSigma0 x + Word.evmMaj x y z) := by
  exact mask32_add_congr (Word.mask32_rawFusedBigSigma0 x) rfl

/-- Two-word ABI used by the fused helpers: input followed by return PC. -/
def entry (s : State) (entryPC : Nat) (x returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat entryPC
    stack := [x, returnDest] ++ rest }

/-- Specialized ABI for BSIG0 fused with the T2 addition and mask. -/
def t2Entry (s : State) (x y z returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 114
    stack := [x, y, z, UInt256.ofNat 0xffffffff, returnDest] ++ rest }

def t2Returned (s : State) (x y z returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := returnDest
    stack := Challenge.EvmProof.Word.mask32
      (Word.evmBigSigma0 x + Word.evmMaj x y z) :: rest }

/-- Specialized ABI for BSIG1 fused through all remaining T1 arithmetic. -/
def t1Entry (s : State) (x y z addend1 addend2 returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 163
    stack := [x, y, z, addend1, addend2,
      UInt256.ofNat 0xffffffff, returnDest] ++ rest }

def t1Returned (s : State) (x y z addend1 addend2 returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := returnDest
    stack := Challenge.EvmProof.Word.mask32
      (((Word.evmBigSigma1 x + Word.evmCh x y z) + addend1) +
        addend2) :: rest }

def bigSigma0Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨104, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨105, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨106, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨107, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨108, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨109, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨110, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨111, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨112, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨113, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨114, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨115, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨116, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨117, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨118, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨119, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨120, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨121, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨122, .push ⟨1, by decide⟩ (UInt256.ofNat 11), by rfl, by decide⟩,
   ⟨123, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨124, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨125, .push ⟨1, by decide⟩ (UInt256.ofNat 9), by rfl, by decide⟩,
   ⟨126, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨127, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨128, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨129, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨130, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨131, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨132, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨133, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨134, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨135, .op (.Swap ⟨0, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨136, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def bigSigma1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨148, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨149, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨150, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨151, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨152, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨153, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨154, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨155, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨156, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨157, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨158, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨159, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨160, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨161, .push ⟨1, by decide⟩ (UInt256.ofNat 6), by rfl, by decide⟩,
   ⟨162, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨163, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨164, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨165, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨166, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨167, .push ⟨1, by decide⟩ (UInt256.ofNat 14), by rfl, by decide⟩,
   ⟨168, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨169, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨170, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨171, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨172, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨173, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨174, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨175, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨176, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨177, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨178, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨179, .op (.Swap ⟨0, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨180, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem bigSigma0PC (i : Nat) (hlo : 104 ≤ i) (hhi : i ≤ 136) :
    Artifact.referenceArtifact.instructionPC i =
      [114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126,
        128, 129, 130, 132, 133, 134, 136, 137, 138, 140, 141, 142, 143,
        144, 145, 146, 147, 148, 149, 150][i - 104]! := by
  interval_cases i <;> decide

@[simp] private theorem bigSigma1PC (i : Nat) (hlo : 148 ≤ i) (hhi : i ≤ 180) :
    Artifact.referenceArtifact.instructionPC i =
      [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176,
        177, 179, 180, 181, 183, 184, 185, 187, 188, 189, 190, 191, 192,
        193, 194, 195, 196, 197, 198, 199][i - 148]! := by
  interval_cases i <;> decide

set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
theorem run_bigSigma0 (s : State) (x y z returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock bigSigma0Path
      (t2Entry s x y z returnDest rest) =
        some (t2Returned s x y z returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  simp [bigSigma0Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    t2Entry, t2Returned, Word.rawFusedBigSigma0, Word.duplicateLane,
    Challenge.EvmProof.Word.mask32, List.exchange,
    hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10,
    hcode, hrun, hvalid]
  change Challenge.EvmProof.Word.mask32
      (Word.rawFusedBigSigma0 x + Word.evmMaj x y z) =
    Challenge.EvmProof.Word.mask32
      (Word.evmBigSigma0 x + Word.evmMaj x y z)
  exact mask32_t2_fused x y z

set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
theorem run_bigSigma1 (s : State) (x y z addend1 addend2 returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock bigSigma1Path
      (t1Entry s x y z addend1 addend2 returnDest rest) =
        some (t1Returned s x y z addend1 addend2 returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  simp [bigSigma1Path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    t1Entry, t1Returned, Word.rawFusedBigSigma1, Word.duplicateLane,
    Challenge.EvmProof.Word.mask32, List.exchange,
    hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12,
    hcode, hrun, hvalid]
  change Challenge.EvmProof.Word.mask32
      (((Word.rawFusedBigSigma1 x + Word.evmCh x y z) + addend1) +
        addend2) =
    Challenge.EvmProof.Word.mask32
      (((Word.evmBigSigma1 x + Word.evmCh x y z) + addend1) + addend2)
  exact mask32_t1_fused x y z addend1 addend2

def gasSteps_bigSigma0 (s : State) (x y z returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (t2Entry s x y z returnDest rest)
      (t2Returned s x y z returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka bigSigma0Path
  · exact hcode
  · exact hfork
  · exact run_bigSigma0 s x y z returnDest rest hcap hcode hrun hvalid
  · exact hrun
  · exact hnp

def gasSteps_bigSigma1 (s : State) (x y z addend1 addend2 returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (t1Entry s x y z addend1 addend2 returnDest rest)
      (t1Returned s x y z addend1 addend2 returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka bigSigma1Path
  · exact hcode
  · exact hfork
  · exact run_bigSigma1 s x y z addend1 addend2 returnDest rest hcap hcode hrun hvalid
  · exact hrun
  · exact hnp

end Challenge.Sha256.Submission.Proofs.Bytecode.BigSigma
