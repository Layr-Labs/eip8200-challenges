import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreBridge
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWrapperBlock
import Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryDecodeBlock

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWrapperBlock
open Challenge.Modexp.Submission.Proofs.Montgomery

def frame (eWord A : UInt256) (n : Nat) (tail : List UInt256) : List UInt256 :=
  [eWord, A, UInt256.ofNat n] ++ tail

def atFrame (s : State) (eWord A : UInt256) (n : Nat)
    (tail : List UInt256) (pc : Nat) : State :=
  { s with pc := UInt256.ofNat pc, stack := frame eWord A n tail }

def decodeEntry (s : State) (eWord A : UInt256) (n : Nat)
    (tail : List UInt256) : State :=
  atFrame s eWord A n tail 2298

def decodeEffects (s : State) (n : Nat) : Effects :=
  if n = 0 then
    effectsOf s
  else if 32 < n then
    effectsOf s
  else
    let touched := loadLowLeaf s 0
    if (MachineState.readWord s.memory 0).toNat % 2 = 0 then
      effectsOf touched
    else
      let cleared := OneMemory.clearLeaf touched 7168 n 0 []
      let seeded := OneMemory.storeOneLeaf cleared 7168
      let cached := loadLowLeaf seeded 11264
      let reduced := MontgomeryWrapperValue.coreLeaf cached 2048 7168 3072 n
        (MachineState.readWord cached.memory 11264)
      effectsOf (BigHelpers.copyReturned reduced 2048 3072 n 0 [])

def decodeReturned (s : State) (eWord A : UInt256) (n : Nat)
    (tail : List UInt256) : State :=
  returnedState s (decodeEffects s n) (UInt256.ofNat 1118)
    (frame eWord A n tail)

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def zeroGuardPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1651 .JUMPDEST,
   opAt 1652 (.Dup ⟨2, by decide⟩),
   opAt 1653 .ISZERO,
   pushAt 1654 2 2388,
   opAt 1655 .JUMPI]

def largeGuardPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1656 1 32,
   opAt 1657 (.Dup ⟨3, by decide⟩),
   opAt 1658 .GT,
   pushAt 1659 2 2388,
   opAt 1660 .JUMPI]

def parityGuardPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1661 0 0,
   opAt 1662 .MLOAD,
   pushAt 1663 1 1,
   opAt 1664 .AND,
   opAt 1665 .ISZERO,
   pushAt 1666 2 2388,
   opAt 1667 .JUMPI]

def clearCallPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1668 (.Dup ⟨2, by decide⟩),
   pushAt 1669 2 2335,
   opAt 1670 (.Swap ⟨0, by decide⟩),
   pushAt 1671 2 7168,
   pushAt 1672 2 19,
   opAt 1673 .JUMP]

def clearReturnPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1674 .JUMPDEST,
   pushAt 1675 1 1,
   pushAt 1676 2 7168,
   opAt 1677 .MSTORE,
   opAt 1678 (.Dup ⟨2, by decide⟩),
   pushAt 1679 2 11264,
   opAt 1680 .MLOAD,
   opAt 1681 (.Swap ⟨0, by decide⟩),
   pushAt 1682 2 2367,
   opAt 1683 (.Swap ⟨1, by decide⟩),
   opAt 1684 (.Swap ⟨0, by decide⟩),
   pushAt 1685 0 0,
   pushAt 1686 2 3072,
   pushAt 1687 2 7168,
   pushAt 1688 2 2048,
   pushAt 1689 2 1625,
   opAt 1690 .JUMP]

def coreReturnPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1691 .JUMPDEST,
   opAt 1692 (.Dup ⟨2, by decide⟩),
   pushAt 1693 2 2383,
   opAt 1694 (.Swap ⟨0, by decide⟩),
   pushAt 1695 2 3072,
   pushAt 1696 2 2048,
   pushAt 1697 2 58,
   opAt 1698 .JUMP]

def copyReturnPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1699 .JUMPDEST,
   pushAt 1700 2 1118,
   opAt 1701 .JUMP]

def fallbackPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1702 .JUMPDEST,
   pushAt 1703 2 1118,
   opAt 1704 .JUMP]

@[simp] private theorem localPCs (i : Nat) (hi : 1651 ≤ i) (hii : i ≤ 1704) :
    Artifact.submissionArtifact.instructionPC i =
      [2298,2299,2300,2301,2304,2305,2307,2308,2309,2312,
       2313,2314,2315,2317,2318,2319,2322,2323,2324,2327,
       2328,2331,2334,2335,2336,2338,2341,2342,2343,2346,
       2347,2348,2351,2352,2353,2354,2357,2360,2363,2366,
       2367,2368,2369,2372,2373,2376,2379,2382,2383,2384,
       2387,2388,2389,2392][i - 1651]! := by
  interval_cases i <;> decide

@[simp] private theorem jumpClearReturn :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2335 = true :=
  Artifact.isValidJumpDest_index 1674 (by rfl)

@[simp] private theorem jumpCoreReturn :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2367 = true :=
  Artifact.isValidJumpDest_index 1691 (by rfl)

@[simp] private theorem jumpCopyReturn :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2383 = true :=
  Artifact.isValidJumpDest_index 1699 (by rfl)

@[simp] private theorem jumpFallback :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2388 = true :=
  Artifact.isValidJumpDest_index 1702 (by rfl)

@[simp] private theorem jumpSerializer :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1118 = true :=
  Artifact.isValidJumpDest_index 838 (by rfl)

private theorem zeroWord : (0 : UInt256) = UInt256.ofNat 0 := by
  decide

private theorem zeroWord_toNat : (0 : UInt256).toNat = 0 := by
  decide

private theorem zeroLiteral_toNat : ({ val := 0 } : UInt256).toNat = 0 := by
  decide

private theorem zeroLiteral_eq_ofNat :
    ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by
  decide

private theorem coreLeaf_code (s : State) (n : Nat) (np : UInt256) :
    (MontgomeryWrapperValue.coreLeaf s 2048 7168 3072 n np).executionEnv.code =
      s.executionEnv.code := by
  simp [MontgomeryWrapperValue.coreLeaf,
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.finishLeaf,
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.reducedLeaf,
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.flatLeaf,
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.loadLeaf,
    MontgomeryCoreExecution.progress_executionEnv]

private theorem coreLeaf_executionEnv (s : State) (n : Nat) (np : UInt256) :
    (MontgomeryWrapperValue.coreLeaf s 2048 7168 3072 n np).executionEnv =
      s.executionEnv := by
  simp [MontgomeryWrapperValue.coreLeaf,
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.finishLeaf,
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.reducedLeaf,
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.flatLeaf,
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.loadLeaf,
    MontgomeryCoreExecution.progress_executionEnv]

private theorem coreLeaf_halt (s : State) (n : Nat) (np : UInt256) :
    (MontgomeryWrapperValue.coreLeaf s 2048 7168 3072 n np).halt = s.halt := by
  simp [MontgomeryWrapperValue.coreLeaf,
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.finishLeaf,
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.reducedLeaf,
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.flatLeaf,
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.loadLeaf,
    MontgomeryCoreExecution.progress_halt]

private theorem coreLeaf_fork (s : State) (n : Nat) (np : UInt256) :
    (MontgomeryWrapperValue.coreLeaf s 2048 7168 3072 n np).fork = s.fork := by
  simp [MontgomeryWrapperValue.coreLeaf,
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.finishLeaf,
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.reducedLeaf,
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.flatLeaf,
    Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.loadLeaf,
    MontgomeryCoreExecution.progress_fork, State.fork]

private theorem lowBit (w : UInt256) :
    (UInt256.land (UInt256.ofNat 1) w).toNat = w.toNat % 2 := by
  rw [Word.word_toNat_land, Word.word_toNat_ofNat]
  change 1 &&& w.toNat = w.toNat % 2
  rw [Nat.and_comm]
  exact Nat.and_two_pow_sub_one_eq_mod _ 1

private theorem task53_reframe (s t : State)
    (hframe : { t with memory := s.memory, activeWords := s.activeWords } = s)
    (memory : ByteArray) (activeWords : UInt256) :
    { t with memory := memory, activeWords := activeWords } =
      { s with memory := memory, activeWords := activeWords } := by
  have h := congrArg (fun u : State =>
    { u with memory := memory, activeWords := activeWords }) hframe
  simpa using h

private theorem task53_returned_of_frame (s t : State) (ret : UInt256)
    (rest : List UInt256)
    (hframe : { t with memory := s.memory, activeWords := s.activeWords } = s) :
    returnedState s (effectsOf t) ret rest = { t with pc := ret, stack := rest } := by
  have h := congrArg (fun u : State =>
    returnedState u (effectsOf t) ret rest) hframe
  exact h.symm

theorem run_zeroPass (s : State) (eWord A : UInt256) (n : Nat)
    (tail : List UInt256) (hcap : tail.length < 977)
    (hn : 1 ≤ n) (hbound : n < 2 ^ 256) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock zeroGuardPath
      (decodeEntry s eWord A n tail) =
        some (atFrame s eWord A n tail 2305) := by
  have hc : ¬ UInt256.isTrue (UInt256.isZero (UInt256.ofNat n)) := by
    simp only [UInt256.isZero, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hbound, if_neg (show n ≠ 0 by omega)]
    decide
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  simp [zeroGuardPath, opAt, pushAt, wfOp, decodeEntry, atFrame, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc]

theorem run_zeroFallback (s : State) (eWord A : UInt256) (tail : List UInt256)
    (hcap : tail.length < 977)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock zeroGuardPath
      (decodeEntry s eWord A 0 tail) =
        some (atFrame s eWord A 0 tail 2388) := by
  have hc : UInt256.isTrue (UInt256.isZero (UInt256.ofNat 0)) := by decide
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  simp [zeroGuardPath, opAt, pushAt, wfOp, decodeEntry, atFrame, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc, hcode]

theorem run_largePass (s : State) (eWord A : UInt256) (n : Nat)
    (tail : List UInt256) (hcap : tail.length < 977)
    (hN : n ≤ 32) (hbound : n < 2 ^ 256) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock largeGuardPath
      (atFrame s eWord A n tail 2305) =
        some (atFrame s eWord A n tail 2313) := by
  have hc : ¬ UInt256.isTrue (UInt256.gt (UInt256.ofNat n) (UInt256.ofNat 32)) := by
    simp only [UInt256.gt, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hbound,
      Nat.mod_eq_of_lt (show 32 < 2 ^ 256 by decide),
      if_neg (show ¬n > 32 by omega)]
    decide
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  simp [largeGuardPath, opAt, pushAt, wfOp, atFrame, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc]

theorem run_largeFallback (s : State) (eWord A : UInt256) (n : Nat)
    (tail : List UInt256) (hcap : tail.length < 977)
    (hlarge : 32 < n) (hbound : n < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock largeGuardPath
      (atFrame s eWord A n tail 2305) =
        some (atFrame s eWord A n tail 2388) := by
  have hc : UInt256.isTrue (UInt256.gt (UInt256.ofNat n) (UInt256.ofNat 32)) := by
    simp only [UInt256.gt, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hbound,
      Nat.mod_eq_of_lt (show 32 < 2 ^ 256 by decide), if_pos hlarge]
    decide
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  simp [largeGuardPath, opAt, pushAt, wfOp, atFrame, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc, hcode]

theorem run_parityOdd (s : State) (eWord A : UInt256) (n : Nat)
    (tail : List UInt256) (hcap : tail.length < 977)
    (hodd : (MachineState.readWord s.memory 0).toNat % 2 = 1)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock parityGuardPath
      (atFrame s eWord A n tail 2313) =
        some (atFrame (loadLowLeaf s 0) eWord A n tail 2323) := by
  have hc : ¬ UInt256.isTrue (UInt256.isZero
      (UInt256.land (UInt256.ofNat 1) (MachineState.readWord s.memory 0))) := by
    simp [UInt256.isTrue, UInt256.isZero, lowBit, hodd]
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  simp [parityGuardPath, opAt, pushAt, wfOp, atFrame, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc,
    MontgomeryWrapperBlock.loadLowLeaf, State.activeWordsAfterUInt256,
    Word.word_toNat_ofNat, Nat.mod_eq_of_lt, List.exchange, zeroWord,
    zeroWord_toNat, zeroLiteral_toNat]

theorem run_parityEven (s : State) (eWord A : UInt256) (n : Nat)
    (tail : List UInt256) (hcap : tail.length < 977)
    (heven : (MachineState.readWord s.memory 0).toNat % 2 = 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock parityGuardPath
      (atFrame s eWord A n tail 2313) =
        some (atFrame (loadLowLeaf s 0) eWord A n tail 2388) := by
  have hc : UInt256.isTrue (UInt256.isZero
      (UInt256.land (UInt256.ofNat 1) (MachineState.readWord s.memory 0))) := by
    simp [UInt256.isTrue, UInt256.isZero, lowBit, heven]
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  simp [parityGuardPath, opAt, pushAt, wfOp, atFrame, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Nat.add_assoc, cap, hrun, hc, hcode,
    MontgomeryWrapperBlock.loadLowLeaf, State.activeWordsAfterUInt256,
    Word.word_toNat_ofNat, Nat.mod_eq_of_lt, List.exchange, zeroWord,
    zeroWord_toNat, zeroLiteral_toNat]

theorem run_clearCall (s : State) (eWord A : UInt256) (n : Nat)
    (tail : List UInt256) (hcap : tail.length < 977)
    (_hcount : n < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock clearCallPath
      (atFrame s eWord A n tail 2323) =
        some (BigHelpers.clearEntry s 7168 n 2335
          (frame eWord A n tail)) := by
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  simp [clearCallPath, opAt, pushAt, wfOp, atFrame, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Word.word_toNat_ofNat, Nat.mod_eq_of_lt, Nat.add_assoc, cap,
    hrun, hcode, List.exchange, jumpClearReturn, BigHelpers.clearEntry]

theorem run_clearReturn (s : State) (eWord A : UInt256) (n : Nat)
    (tail : List UInt256) (hcap : tail.length < 977)
    (_hcount : n < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock clearReturnPath
      (BigHelpers.clearReturned s 7168 n 2335 (frame eWord A n tail)) =
        let cleared := OneMemory.clearLeaf s 7168 n 0 []
        let seeded := OneMemory.storeOneLeaf cleared 7168
        let cached := loadLowLeaf seeded 11264
        some (MontgomerySetupBlock.coreEntry cached 2048 7168 3072 0 n
          (MachineState.readWord cached.memory 11264) 2367
          (frame eWord A n tail)) := by
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  simp [clearReturnPath, opAt, pushAt, wfOp, BigHelpers.clearReturned,
    OneMemory.clearLeaf, OneMemory.flatLeaf, OneMemory.storeOneLeaf,
    OneMemory.storeOneMemory, OneMemory.storeOneActiveWords, atFrame, frame,
    MontgomerySetupBlock.coreEntry, Stepper.runLocatedBlock,
    Stepper.runLocated, Stepper.runInstr, Word.succ_ofNat_mod,
    Word.ofNat_add_mod, Word.literal_eq_ofNat, Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt, Nat.add_assoc, cap, hrun, hcode,
    MontgomeryWrapperBlock.loadLowLeaf, State.activeWordsAfterUInt256,
    List.exchange, jumpClearReturn, jumpCoreReturn, zeroWord,
    zeroLiteral_eq_ofNat]

theorem run_coreReturn (s : State) (eWord A : UInt256) (n : Nat)
    (np : UInt256) (tail : List UInt256) (hcap : tail.length < 977)
    (_hcount : n < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock coreReturnPath
      ({ MontgomeryWrapperValue.coreLeaf s 2048 7168 3072 n np with
          pc := 2367, stack := frame eWord A n tail }) =
        some (BigHelpers.copyEntry
          (MontgomeryWrapperValue.coreLeaf s 2048 7168 3072 n np)
          2048 3072 n 2383 (frame eWord A n tail)) := by
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  simp [coreReturnPath, opAt, pushAt, wfOp, BigHelpers.copyEntry,
    atFrame, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Word.word_toNat_ofNat, Nat.mod_eq_of_lt, Nat.add_assoc, cap,
    hrun, hcode, List.exchange, jumpCopyReturn, coreLeaf_halt,
    coreLeaf_code]

theorem run_copyReturn (s : State) (eWord A : UInt256) (n : Nat)
    (np : UInt256) (tail : List UInt256) (hcap : tail.length < 977)
    (_hcount : n < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock copyReturnPath
      (BigHelpers.copyReturned
        (MontgomeryWrapperValue.coreLeaf s 2048 7168 3072 n np)
        2048 3072 n 2383 (frame eWord A n tail)) =
        some ({ BigHelpers.copyReturned
          (MontgomeryWrapperValue.coreLeaf s 2048 7168 3072 n np)
          2048 3072 n 2383 (frame eWord A n tail) with
            pc := 1118, stack := frame eWord A n tail }) := by
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  simp [copyReturnPath, opAt, pushAt, wfOp, BigHelpers.copyReturned,
    atFrame, frame, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, cap, hrun, hcode, List.exchange, jumpSerializer,
    coreLeaf_halt, coreLeaf_code]

theorem run_fallback (s : State) (eWord A : UInt256) (n : Nat)
    (tail : List UInt256) (hcap : tail.length < 977)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock fallbackPath
      (atFrame s eWord A n tail 2388) =
        some ({ atFrame s eWord A n tail 2388 with
          pc := 1118, stack := frame eWord A n tail }) := by
  have cap : ∀ k, k ≤ 24 → tail.length + k < 1024 := by omega
  simp [fallbackPath, opAt, pushAt, wfOp, atFrame, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
    Word.word_toNat_ofNat, Nat.mod_eq_of_lt, Nat.add_assoc, cap,
    hrun, hcode, List.exchange, jumpSerializer]

private theorem positive_count (s : State) (n m : Nat)
    (hm : 0 < m) (hmod : Limbs.Represents s.memory 0 n m) : 1 ≤ n := by
  by_contra h
  have hn : n = 0 := by omega
  have hbound := hmod.1
  rw [hn, pow_zero] at hbound
  omega

def gasSteps_decode (s : State) (eWord A : UInt256) (n : Nat)
    (tail : List UInt256) (hcap : tail.length < 977)
    (hcount : n < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (decodeEntry s eWord A n tail)
      (decodeReturned s eWord A n tail) := by
  have hframeClear : (frame eWord A n tail).length < 1017 := by
    simp [frame]
    omega
  have hframeCopy : (frame eWord A n tail).length < 1016 := by
    simp [frame]
    omega
  have hframeCore : (frame eWord A n tail).length + 8 < 1000 := by
    simp [frame]
    omega
  have h1118 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat 1118).toNat = true := by
    simp only [Word.word_toNat_ofNat]
    exact jumpSerializer
  have h2335 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat 2335).toNat = true := by
    simp only [Word.word_toNat_ofNat]
    exact jumpClearReturn
  have h2367 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat 2367).toNat = true := by
    simp only [Word.word_toNat_ofNat]
    exact jumpCoreReturn
  have h2383 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat 2383).toNat = true := by
    simp only [Word.word_toNat_ofNat]
    exact jumpCopyReturn
  have hArtifactCode : s.executionEnv.code = Artifact.submissionArtifact.code := by
    simpa [Artifact.submissionArtifact] using hcode
  by_cases hzero : n = 0
  · subst n
    have guard := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
      zeroGuardPath (s := decodeEntry s eWord A 0 tail)
      (by simpa [decodeEntry, atFrame, frame] using hArtifactCode)
      (by simpa [decodeEntry, atFrame, frame, State.fork] using hfork)
      (run_zeroFallback s eWord A tail hcap hcode hrun) hrun hnp
    have fallback := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
      fallbackPath (s := atFrame s eWord A 0 tail 2388)
      (by simpa [atFrame, frame] using hArtifactCode)
      (by simpa [atFrame, frame, State.fork] using hfork)
      (run_fallback s eWord A 0 tail hcap hcode hrun)
      (by simpa [atFrame, frame] using hrun)
      (by simpa [atFrame, frame, State.fork] using hnp)
    have hsteps := guard.trans fallback
    refine GasSteps.cast hsteps rfl ?_
    simp [decodeReturned, decodeEffects, atFrame, frame, returnedState,
      effectsOf, Word.literal_eq_ofNat]
  · have hn : 1 ≤ n := by omega
    have zeroPass := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
      zeroGuardPath (s := decodeEntry s eWord A n tail)
      (by simpa [decodeEntry, atFrame, frame] using hArtifactCode)
      (by simpa [decodeEntry, atFrame, frame, State.fork] using hfork)
      (run_zeroPass s eWord A n tail hcap hn hcount hrun)
      (by simpa [decodeEntry, atFrame, frame] using hrun)
      (by simpa [decodeEntry, atFrame, frame, State.fork] using hnp)
    by_cases hlarge : 32 < n
    · have guard := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
        largeGuardPath (s := atFrame s eWord A n tail 2305)
        (by simpa [atFrame, frame] using hArtifactCode)
        (by simpa [atFrame, frame, State.fork] using hfork)
        (run_largeFallback s eWord A n tail hcap hlarge hcount hcode hrun)
        (by simpa [atFrame, frame] using hrun)
        (by simpa [atFrame, frame, State.fork] using hnp)
      have fallback := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
        fallbackPath (s := atFrame s eWord A n tail 2388)
        (by simpa [atFrame, frame] using hArtifactCode)
        (by simpa [atFrame, frame, State.fork] using hfork)
        (run_fallback s eWord A n tail hcap hcode hrun)
        (by simpa [atFrame, frame] using hrun)
        (by simpa [atFrame, frame, State.fork] using hnp)
      have hsteps := zeroPass.trans (guard.trans fallback)
      refine GasSteps.cast hsteps rfl ?_
      simp [decodeReturned, decodeEffects, atFrame, frame, returnedState,
        effectsOf, hzero, hlarge, Word.literal_eq_ofNat]
    · have hN : n ≤ 32 := by omega
      have largePass := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
        largeGuardPath (s := atFrame s eWord A n tail 2305)
        (by simpa [atFrame, frame] using hArtifactCode)
        (by simpa [atFrame, frame, State.fork] using hfork)
        (run_largePass s eWord A n tail hcap hN hcount hrun)
        (by simpa [atFrame, frame] using hrun)
        (by simpa [atFrame, frame, State.fork] using hnp)
      by_cases heven : (MachineState.readWord s.memory 0).toNat % 2 = 0
      · have parity := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
          parityGuardPath (s := atFrame s eWord A n tail 2313)
          (by simpa [atFrame, frame] using hArtifactCode)
          (by simpa [atFrame, frame, State.fork] using hfork)
          (run_parityEven s eWord A n tail hcap heven hcode hrun)
          (by simpa [atFrame, frame] using hrun)
          (by simpa [atFrame, frame, State.fork] using hnp)
        have fallback := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
          fallbackPath (s := atFrame (loadLowLeaf s 0) eWord A n tail 2388)
          (by simpa [atFrame, frame, loadLowLeaf] using hArtifactCode)
          (by simpa [atFrame, frame, loadLowLeaf, State.fork] using hfork)
          (run_fallback (loadLowLeaf s 0) eWord A n tail hcap hcode hrun)
          (by simpa [atFrame, frame, loadLowLeaf] using hrun)
          (by simpa [atFrame, frame, loadLowLeaf, State.fork] using hnp)
        have hsteps := zeroPass.trans (largePass.trans (parity.trans fallback))
        refine GasSteps.cast hsteps rfl ?_
        simp [decodeReturned, decodeEffects, atFrame, frame, returnedState,
          effectsOf, loadLowLeaf, hzero, hlarge, heven,
          Word.literal_eq_ofNat]
      · have hmod2 : (MachineState.readWord s.memory 0).toNat % 2 < 2 :=
          Nat.mod_lt _ (by decide)
        have hodd : (MachineState.readWord s.memory 0).toNat % 2 = 1 := by
          omega
        let touched := loadLowLeaf s 0
        let cleared := OneMemory.clearLeaf touched 7168 n 0 []
        let seeded := OneMemory.storeOneLeaf cleared 7168
        let cached := loadLowLeaf seeded 11264
        let np := MachineState.readWord cached.memory 11264
        have parity := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
          parityGuardPath (s := atFrame s eWord A n tail 2313)
          (by simpa [atFrame, frame] using hArtifactCode)
          (by simpa [atFrame, frame, State.fork] using hfork)
          (run_parityOdd s eWord A n tail hcap hodd hrun)
          (by simpa [atFrame, frame] using hrun)
          (by simpa [atFrame, frame, State.fork] using hnp)
        have call := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
          clearCallPath (s := atFrame touched eWord A n tail 2323)
          (by simpa [atFrame, frame, touched, loadLowLeaf] using hArtifactCode)
          (by simpa [atFrame, frame, touched, loadLowLeaf, State.fork] using hfork)
          (run_clearCall touched eWord A n tail hcap hcount hcode hrun)
          (by simpa [atFrame, frame, touched, loadLowLeaf] using hrun)
          (by simpa [atFrame, frame, touched, loadLowLeaf, State.fork] using hnp)
        have clear := BigHelpers.gasSteps_clear touched 7168 n 2335
          (frame eWord A n tail) hframeClear hcount
          (by simpa [touched, loadLowLeaf, Artifact.submissionArtifact] using hcode)
          (by simpa [touched, loadLowLeaf, State.fork] using hfork)
          (by simpa [touched, loadLowLeaf] using hrun)
          (by simpa [touched, loadLowLeaf, State.fork] using hnp) h2335
        have clearReturn := Stepper.runLocatedBlock_sound
          Artifact.submissionArtifact .Osaka clearReturnPath
          (s := BigHelpers.clearReturned touched 7168 n 2335 (frame eWord A n tail))
          (by simpa [touched, loadLowLeaf, BigHelpers.clearReturned,
            Artifact.submissionArtifact] using hArtifactCode)
          (by simpa [touched, loadLowLeaf, BigHelpers.clearReturned,
            State.fork] using hfork)
          (run_clearReturn touched eWord A n tail hcap hcount hcode hrun)
          (by simpa [touched, loadLowLeaf, BigHelpers.clearReturned] using hrun)
          (by simpa [touched, loadLowLeaf, BigHelpers.clearReturned,
            State.fork] using hnp)
        have core := MontgomeryCoreBridge.gasSteps_coreLeaf cached
          2048 7168 3072 n np 2367 (frame eWord A n tail) hN
          (by omega) (by omega) hframeCore
          (by simpa [cached, seeded, cleared, touched, loadLowLeaf,
            OneMemory.clearLeaf, OneMemory.flatLeaf, OneMemory.storeOneLeaf,
            OneMemory.storeOneMemory, OneMemory.storeOneActiveWords,
            BigHelpers.clearReturned]
            using hcode)
          (by simpa [cached, seeded, cleared, touched, loadLowLeaf,
            OneMemory.clearLeaf, OneMemory.flatLeaf, OneMemory.storeOneLeaf,
            OneMemory.storeOneMemory, OneMemory.storeOneActiveWords,
            BigHelpers.clearReturned, State.fork] using hfork)
          (by simpa [cached, seeded, cleared, touched, loadLowLeaf,
            coreLeaf_halt, OneMemory.clearLeaf, OneMemory.flatLeaf,
            OneMemory.storeOneLeaf, OneMemory.storeOneMemory,
            OneMemory.storeOneActiveWords, BigHelpers.clearReturned] using hrun)
          (by simpa [cached, seeded, cleared, touched, loadLowLeaf,
            OneMemory.clearLeaf, OneMemory.flatLeaf, OneMemory.storeOneLeaf,
            OneMemory.storeOneMemory, OneMemory.storeOneActiveWords,
            BigHelpers.clearReturned, State.fork] using hnp) h2367
        have coreReturn := Stepper.runLocatedBlock_sound
          Artifact.submissionArtifact .Osaka coreReturnPath
          (s := { MontgomeryWrapperValue.coreLeaf cached 2048 7168 3072 n np with
              pc := 2367, stack := frame eWord A n tail })
          (by simpa [cached, seeded, cleared, touched, loadLowLeaf,
            coreLeaf_code, coreLeaf_executionEnv,
            OneMemory.clearLeaf, OneMemory.flatLeaf, OneMemory.storeOneLeaf,
            OneMemory.storeOneMemory, OneMemory.storeOneActiveWords,
            BigHelpers.clearReturned] using hArtifactCode)
          (by simpa [cached, seeded, cleared, touched, loadLowLeaf,
            State.fork, coreLeaf_fork, coreLeaf_executionEnv,
            OneMemory.clearLeaf, OneMemory.flatLeaf, OneMemory.storeOneLeaf,
            OneMemory.storeOneMemory, OneMemory.storeOneActiveWords,
            BigHelpers.clearReturned] using hfork)
          (run_coreReturn cached eWord A n np tail hcap hcount hcode hrun)
          (by simpa [cached, seeded, cleared, touched, loadLowLeaf,
            coreLeaf_halt, OneMemory.clearLeaf, OneMemory.flatLeaf,
            OneMemory.storeOneLeaf, OneMemory.storeOneMemory,
            OneMemory.storeOneActiveWords, BigHelpers.clearReturned] using hrun)
          (by simpa [cached, seeded, cleared, touched, loadLowLeaf,
            State.fork, coreLeaf_fork, coreLeaf_executionEnv,
            OneMemory.clearLeaf, OneMemory.flatLeaf, OneMemory.storeOneLeaf,
            OneMemory.storeOneMemory, OneMemory.storeOneActiveWords,
            BigHelpers.clearReturned] using hnp)
        have copy := BigHelpers.gasSteps_copy
          (MontgomeryWrapperValue.coreLeaf cached 2048 7168 3072 n np)
          2048 3072 n 2383 (frame eWord A n tail) hframeCopy hcount
          (by simpa [cached, seeded, cleared, touched, loadLowLeaf,
            coreLeaf_code, coreLeaf_executionEnv, BigHelpers.copyReturned,
            OneMemory.clearLeaf, OneMemory.flatLeaf, OneMemory.storeOneLeaf,
            OneMemory.storeOneMemory, OneMemory.storeOneActiveWords,
            BigHelpers.clearReturned] using hcode)
          (by simpa [cached, seeded, cleared, touched, loadLowLeaf,
            State.fork, coreLeaf_fork, coreLeaf_executionEnv,
            BigHelpers.copyReturned, OneMemory.clearLeaf, OneMemory.flatLeaf,
            OneMemory.storeOneLeaf, OneMemory.storeOneMemory,
            OneMemory.storeOneActiveWords, BigHelpers.clearReturned] using hfork)
          (by simpa [cached, seeded, cleared, touched, loadLowLeaf,
            coreLeaf_halt, BigHelpers.copyReturned, OneMemory.clearLeaf,
            OneMemory.flatLeaf, OneMemory.storeOneLeaf,
            OneMemory.storeOneMemory, OneMemory.storeOneActiveWords,
            BigHelpers.clearReturned] using hrun)
          (by simpa [cached, seeded, cleared, touched, loadLowLeaf,
            State.fork, coreLeaf_fork, coreLeaf_executionEnv,
            coreLeaf_code, BigHelpers.copyReturned, OneMemory.clearLeaf,
            OneMemory.flatLeaf, OneMemory.storeOneLeaf,
            OneMemory.storeOneMemory, OneMemory.storeOneActiveWords,
            BigHelpers.clearReturned] using hnp) h2383
        have copyReturn := Stepper.runLocatedBlock_sound
          Artifact.submissionArtifact .Osaka copyReturnPath
          (s := BigHelpers.copyReturned
            (MontgomeryWrapperValue.coreLeaf cached 2048 7168 3072 n np)
            2048 3072 n 2383 (frame eWord A n tail))
          (by simpa [cached, seeded, cleared, touched, loadLowLeaf,
            coreLeaf_code, coreLeaf_executionEnv, BigHelpers.copyReturned,
            OneMemory.clearLeaf, OneMemory.flatLeaf, OneMemory.storeOneLeaf,
            OneMemory.storeOneMemory, OneMemory.storeOneActiveWords,
            BigHelpers.clearReturned] using hArtifactCode)
          (by simpa [cached, seeded, cleared, touched, loadLowLeaf,
            State.fork, coreLeaf_fork, coreLeaf_executionEnv,
            BigHelpers.copyReturned, OneMemory.clearLeaf, OneMemory.flatLeaf,
            OneMemory.storeOneLeaf, OneMemory.storeOneMemory,
            OneMemory.storeOneActiveWords, BigHelpers.clearReturned] using hfork)
          (run_copyReturn cached eWord A n np tail hcap hcount hcode hrun)
          (by simpa [cached, seeded, cleared, touched, loadLowLeaf,
            coreLeaf_halt, BigHelpers.copyReturned, OneMemory.clearLeaf,
            OneMemory.flatLeaf, OneMemory.storeOneLeaf,
            OneMemory.storeOneMemory, OneMemory.storeOneActiveWords,
            BigHelpers.clearReturned] using hrun)
          (by simpa [cached, seeded, cleared, touched, loadLowLeaf,
            State.fork, coreLeaf_fork, coreLeaf_executionEnv,
            coreLeaf_code, BigHelpers.copyReturned, OneMemory.clearLeaf,
            OneMemory.flatLeaf, OneMemory.storeOneLeaf,
            OneMemory.storeOneMemory, OneMemory.storeOneActiveWords,
            BigHelpers.clearReturned] using hnp)
        have hsteps := zeroPass.trans (largePass.trans
          (parity.trans (call.trans (clear.trans
            (clearReturn.trans (core.trans (coreReturn.trans
              (copy.trans copyReturn))))))))
        have hcacheFrame :
            { cached with memory := s.memory, activeWords := s.activeWords } = s := by
          rfl
        have hcoreFrame :
            { MontgomeryWrapperValue.coreLeaf cached 2048 7168 3072 n np with
                memory := cached.memory, activeWords := cached.activeWords } = cached :=
          MontgomeryWrapperValue.coreLeaf_frame cached 2048 7168 3072 n np
        let copiedState :=
          { MontgomeryWrapperValue.coreLeaf cached 2048 7168 3072 n np with
              memory :=
                (BigHelpers.copyReturned
                  (MontgomeryWrapperValue.coreLeaf cached 2048 7168 3072 n np)
                  2048 3072 n 2383 (frame eWord A n tail)).memory
              activeWords :=
                (BigHelpers.copyReturned
                  (MontgomeryWrapperValue.coreLeaf cached 2048 7168 3072 n np)
                  2048 3072 n 2383 (frame eWord A n tail)).activeWords }
        have hcopyFrame :
            { copiedState with
                memory := s.memory, activeWords := s.activeWords } = s := by
          simpa [copiedState] using
            (task53_reframe cached
              (MontgomeryWrapperValue.coreLeaf cached 2048 7168 3072 n np)
              hcoreFrame s.memory s.activeWords).trans hcacheFrame
        have hreturned := task53_returned_of_frame s
          copiedState
          (UInt256.ofNat 1118) (frame eWord A n tail) hcopyFrame
        have heffects :
            decodeEffects s n = effectsOf copiedState := by
          simp [decodeEffects, touched, cleared, seeded, cached, np,
            hzero, hlarge, heven, copiedState, BigHelpers.copyReturned,
            effectsOf]
        refine GasSteps.cast hsteps rfl ?_
        rw [decodeReturned, heffects]
        simpa [copiedState, BigHelpers.copyReturned, Word.literal_eq_ofNat]
          using hreturned.symm

theorem decodeReturned_correct (s : State) (eWord A : UInt256) (n acc M : Nat)
    (tail : List UInt256)
    (hN : n ≤ 32) (hm : 0 < M) (hacc : acc < M)
    (hmod : Limbs.Represents s.memory 0 n M)
    (haccRep : Limbs.Represents s.memory 2048 n
      (if M % 2 = 1 then Domain.encode M n acc else acc))
    (hinv : M % 2 = 1 →
      (M * (MachineState.readWord s.memory 11264).toNat + 1) %
        (2 ^ 256) = 0) :
    Limbs.Represents (decodeReturned s eWord A n tail).memory 2048 n acc := by
  have hn : 1 ≤ n := positive_count s n M hm hmod
  have hparity := modulusLow_parity s n M hn hmod
  have hzero : n ≠ 0 := by omega
  have hlarge : ¬32 < n := by omega
  unfold decodeReturned decodeEffects
  rw [if_neg hzero, if_neg hlarge]
  by_cases heven : (MachineState.readWord s.memory 0).toNat % 2 = 0
  · rw [if_pos heven]
    have hModEven : M % 2 = 0 := by omega
    have hacc0 : Limbs.Represents s.memory 2048 n acc := by
      simpa [hModEven] using haccRep
    simpa [returnedState, effectsOf, loadLowLeaf] using hacc0
  · rw [if_neg heven]
    have hodd : M % 2 = 1 := by omega
    have hMR : M < Domain.R n := by
      simpa [Domain.R, CIOS.B, Limbs.radix] using hmod.1
    have hcop : Nat.Coprime M (Domain.R n) :=
      Domain.coprime_R_of_odd M n hm hodd
    have haccEnc : Limbs.Represents s.memory 2048 n (Domain.encode M n acc) := by
      simpa [hodd] using haccRep
    have haccLe : Domain.encode M n acc ≤ M := by
      exact (Nat.mod_lt _ hm).le
    let touched := loadLowLeaf s 0
    let cleared := OneMemory.clearLeaf touched 7168 n 0 []
    let seeded := OneMemory.storeOneLeaf cleared 7168
    let cached := loadLowLeaf seeded 11264
    have hdisMod : OneMemory.unit + 32 * n ≤ 0 ∨
        0 + 32 * n ≤ OneMemory.unit :=
      Or.inr (by change 0 + 32 * n ≤ 7168; omega)
    have hdisAcc : OneMemory.unit + 32 * n ≤ 2048 ∨
        2048 + 32 * n ≤ OneMemory.unit :=
      Or.inr (by change 2048 + 32 * n ≤ 7168; omega)
    have hclearedMod : Limbs.Represents cleared.memory 0 n M :=
      OneMemory.clearLeaf_preserves_region touched n 0 M hN hdisMod hmod 0 []
    have hclearedAcc : Limbs.Represents cleared.memory 2048 n
        (Domain.encode M n acc) :=
      OneMemory.clearLeaf_preserves_region touched n 2048
        (Domain.encode M n acc) hN hdisAcc haccEnc 0 []
    have hseededMod : Limbs.Represents seeded.memory 0 n M :=
      OneMemory.storeOne_preserves_region cleared n 0 M hN hdisMod hclearedMod
    have hseededAcc : Limbs.Represents seeded.memory 2048 n
        (Domain.encode M n acc) :=
      OneMemory.storeOne_preserves_region cleared n 2048
        (Domain.encode M n acc) hN hdisAcc hclearedAcc
    have hone : Limbs.Represents seeded.memory 7168 n 1 :=
      OneMemory.storeOne_represents_one touched n hn hN 0 []
    have hcacheMod : Limbs.Represents cached.memory 0 n M := by
      simpa [cached, seeded, cleared, touched, loadLowLeaf] using hseededMod
    have hcacheAcc : Limbs.Represents cached.memory 2048 n
        (Domain.encode M n acc) := by
      simpa [cached, seeded, cleared, touched, loadLowLeaf] using hseededAcc
    have hcacheOne : Limbs.Represents cached.memory 7168 n 1 := by
      simpa [cached, seeded, cleared, touched, loadLowLeaf] using hone
    have hclearInv : MachineState.readWord cleared.memory 11264 =
        MachineState.readWord touched.memory 11264 := by
      change MachineState.readWord
        (BigHelpers.clearMemory touched.memory (UInt256.ofNat OneMemory.unit) n)
          11264 = _
      simpa [OneMemory.unit] using
        (BigHelpers.readWord_clearMemory_disjoint_region touched.memory
          OneMemory.unit 11264 n n 0 (by omega) (by omega)
          (by norm_num [OneMemory.unit]; omega)
          (Or.inl (by norm_num [OneMemory.unit]; omega)))
    have hstoreInv : MachineState.readWord seeded.memory 11264 =
        MachineState.readWord cleared.memory 11264 := by
      change MachineState.readWord
        (OneMemory.storeOneMemory cleared.memory OneMemory.unit) 11264 = _
      unfold OneMemory.storeOneMemory
      rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      simp [Data.Bytes.natToBytesPadded, ByteArray.size]
      norm_num [OneMemory.unit]
    have hcachedInv :
        (M * (MachineState.readWord cached.memory 11264).toNat + 1) %
          (2 ^ 256) = 0 := by
      calc
        (M * (MachineState.readWord cached.memory 11264).toNat + 1) %
              (2 ^ 256) =
            (M * (MachineState.readWord seeded.memory 11264).toNat + 1) %
              (2 ^ 256) := by rfl
        _ = (M * (MachineState.readWord cleared.memory 11264).toNat + 1) %
              (2 ^ 256) := by rw [hstoreInv]
        _ = (M * (MachineState.readWord touched.memory 11264).toNat + 1) %
              (2 ^ 256) := by rw [hclearInv]
        _ = (M * (MachineState.readWord s.memory 11264).toNat + 1) %
              (2 ^ 256) := by rfl
        _ = 0 := hinv hodd
    let reduced := MontgomeryWrapperValue.coreLeaf cached 2048 7168 3072 n
      (MachineState.readWord cached.memory 11264)
    have core := MontgomeryWrapperValue.coreLeaf_correct cached 2048 7168 3072 n
      (MachineState.readWord cached.memory 11264)
      (Domain.encode M n acc) 1 M hN (by omega) (by omega) (by decide) (by decide)
      hcacheAcc hcacheOne hcacheMod hm (by omega) hcachedInv
    have hdecoded : Limbs.Represents reduced.memory 3072 n acc := by
      rw [← Nat.mod_eq_of_lt hacc, ← Domain.mont_decode M
        (MachineState.readWord cached.memory 11264).toNat n acc hm hmod.1
        (Domain.coprime_R_of_odd M n hm hodd) hcachedInv]
      exact core.1
    have copied := BigHelpers.copyMemory_represents reduced.memory
      2048 3072 n acc hdecoded (by omega) (by omega) (Or.inl (by omega))
    simpa [returnedState, effectsOf, touched, cleared, seeded, cached,
      reduced, loadLowLeaf, BigHelpers.copyReturned, Word.literal_eq_ofNat]
      using copied

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryDecodeBlock
