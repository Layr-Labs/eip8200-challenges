import Challenge.Ripemd160.Submission.Proofs.Bytecode.Trace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Schedule
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduleCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.InitializationCorrect
import Challenge.EvmProof.Bytes
import YulEvmCompiler.BytesLemmas

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Direct traces for RIPEMD-160 memory helpers

This module certifies the five small word/table accessors at artifact indices
23 through 104.  The state transformers are caller-parametric, so the facts
compose both with initialization and with the schedule/round traces.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.TableTrace

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

def hAtPath : List Located :=
  [⟨23, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨24, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨25, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨26, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨27, .push ⟨1, by decide⟩ (UInt256.ofNat 0x20), by rfl, by decide⟩,
   ⟨28, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨29, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨30, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨31, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨32, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨33, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨34, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def hSetPath : List Located :=
  [⟨1011, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1012, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1013, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨1014, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1015, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1016, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1017, .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), by rfl, by decide⟩,
   ⟨1018, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1019, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1020, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1021, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def xAtPath : List Located :=
  [⟨1001, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1002, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨1003, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1004, .push ⟨2, by decide⟩ (UInt256.ofNat 0x2a0), by rfl, by decide⟩,
   ⟨1005, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1006, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1007, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1008, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1009, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨1010, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def xSetPath : List Located := Schedule.xSetPath

def tableAtPath : List Located :=
  [⟨979, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨980, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨981, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨982, .push ⟨1, by decide⟩ (UInt256.ofNat 31), by rfl, by decide⟩,
   ⟨983, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨984, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨985, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨986, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨987, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem hAtPC (j : Nat) (hlo : 23 ≤ j) (hhi : j ≤ 34) :
    Artifact.submissionArtifact.instructionPC j =
      [0x20, 0x21, 0x22, 0x24, 0x25, 0x27, 0x28, 0x29,
        0x2a, 0x2b, 0x2c, 0x2d][j - 23]! := by
  interval_cases j <;> rfl

@[simp] private theorem hSetPC (j : Nat) (hlo : 1011 ≤ j) (hhi : j ≤ 1021) :
    Artifact.submissionArtifact.instructionPC j =
      [0x758, 0x759, 0x75a, 0x75c, 0x75d, 0x75e, 0x75f,
        0x764, 0x765, 0x766, 0x767][j - 1011]! := by
  interval_cases j <;> rfl

@[simp] private theorem xAtPC (j : Nat) (hlo : 1001 ≤ j) (hhi : j ≤ 1010) :
    Artifact.submissionArtifact.instructionPC j =
      [0x74b, 0x74c, 0x74e, 0x74f, 0x752, 0x753, 0x754, 0x755, 0x756, 0x757][j - 1001]! := by
  interval_cases j <;> rfl

@[simp] private theorem xSetPC (j : Nat) (hlo : 70 ≤ j) (hhi : j ≤ 82) :
    Artifact.submissionArtifact.instructionPC j =
      [0x5f, 0x60, 0x65, 0x66, 0x67, 0x68, 0x6a,
        0x6b, 0x6e, 0x6f, 0x70, 0x71, 0x72][j - 70]! := by
  interval_cases j <;> rfl

@[simp] private theorem tableAtPC (j : Nat) (hlo : 979 ≤ j) (hhi : j ≤ 987) :
    Artifact.submissionArtifact.instructionPC j =
      [0x726, 0x727, 0x728, 0x729, 0x72b, 0x72c, 0x72d, 0x72e, 0x72f][j - 979]! := by
  interval_cases j <;> rfl

def slotAddress (base i : UInt256) : UInt256 :=
  UInt256.shiftLeft i (UInt256.ofNat 5) + base

def loadedWord (s : State) (base i : UInt256) : UInt256 :=
  MachineState.readWord s.memory (slotAddress base i).toNat

def storedWord (s : State) (base i value : UInt256) : State :=
  let address := slotAddress base i
  let masked := UInt256.land value (UInt256.ofNat 0xffffffff)
  { s with
    memory := MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded masked.toNat 32) address.toNat
    activeWords := s.activeWordsAfterUInt256 address.toNat 32 }

/-- The compiled helper is now called with `base - 31` and reads the 32-byte
window *ending* at `base + i`, so only the window's final byte is significant.
The argument `base` remains the logical table base, keeping every caller and
the `tableByte` bridge below unchanged. -/
theorem land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_land]
  simp [Nat.and_comm]

def tableAddress (base i : UInt256) : UInt256 :=
  (base - UInt256.ofNat 31) + i

def tableValue (s : State) (base i : UInt256) : UInt256 :=
  UInt256.byteAt (UInt256.ofNat 31)
    (MachineState.readWord s.memory (tableAddress base i).toNat)

def atEntry (s : State) (pc i returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := pc
           stack := [i, 0, returnDest] ++ rest }

def atReturned (s : State) (base i returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := returnDest
           stack := loadedWord s base i :: rest
           activeWords := s.activeWordsAfterUInt256 (slotAddress base i).toNat 32 }

def setEntry (s : State) (base i value returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x758
           stack := [base, i, value, returnDest] ++ rest }

def setReturned (s : State) (base i value returnDest : UInt256)
    (rest : List UInt256) : State :=
  { storedWord s base i value with
    pc := returnDest
    stack := rest }

def hSetEntry (s : State) (i value returnDest : UInt256)
    (rest : List UInt256) : State :=
  setEntry s (UInt256.ofNat 0x20) i value returnDest rest

def hSetReturned (s : State) (i value returnDest : UInt256)
    (rest : List UInt256) : State :=
  setReturned s (UInt256.ofNat 0x20) i value returnDest rest

def xSetEntry (s : State) (i value returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x5f
           stack := [i, value, returnDest] ++ rest }

def xSetReturned (s : State) (i value returnDest : UInt256)
    (rest : List UInt256) : State :=
  { storedWord s (UInt256.ofNat 0x2a0) i value with
      pc := returnDest
      stack := rest }

def tableAtEntry (s : State) (base i returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x726
           stack := [base - UInt256.ofNat 31, i, 0, returnDest] ++ rest }

/-- The four RIPEMD table bases as they are actually pushed by the compiled
call sites, which now supply `base - 31`. -/
@[simp] theorem shiftedBase_1184 :
    (UInt256.ofNat 1184) - UInt256.ofNat 31 = UInt256.ofNat 1153 := by
  have h := Challenge.EvmProof.Word.ofNat_sub_ofNat
    (a := 1184) (b := 31) (by omega) (by omega)
  simpa using h

@[simp] theorem shiftedBase_1280 :
    (UInt256.ofNat 1280) - UInt256.ofNat 31 = UInt256.ofNat 1249 := by
  have h := Challenge.EvmProof.Word.ofNat_sub_ofNat
    (a := 1280) (b := 31) (by omega) (by omega)
  simpa using h

@[simp] theorem shiftedBase_1376 :
    (UInt256.ofNat 1376) - UInt256.ofNat 31 = UInt256.ofNat 1345 := by
  have h := Challenge.EvmProof.Word.ofNat_sub_ofNat
    (a := 1376) (b := 31) (by omega) (by omega)
  simpa using h

@[simp] theorem shiftedBase_1472 :
    (UInt256.ofNat 1472) - UInt256.ofNat 31 = UInt256.ofNat 1441 := by
  have h := Challenge.EvmProof.Word.ofNat_sub_ofNat
    (a := 1472) (b := 31) (by omega) (by omega)
  simpa using h

def tableAtReturned (s : State) (base i returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := returnDest
           stack := tableValue s base i :: rest
           activeWords := s.activeWordsAfterUInt256 (tableAddress base i).toNat 32 }

set_option linter.unusedSimpArgs false in
theorem run_hAt (s : State) (i returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1018)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock hAtPath
      (atEntry s (UInt256.ofNat 0x20) i returnDest rest) =
        some (atReturned s (UInt256.ofNat 0x20) i returnDest rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have haddr : UInt256.ofNat 0x20 +
      UInt256.shiftLeft i (UInt256.ofNat 5) =
        slotAddress (UInt256.ofNat 0x20) i := by
    rw [slotAddress, Challenge.EvmProof.Word.word_add_comm]
  simp [hAtPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    atEntry, atReturned, loadedWord, hc2, hc3, hc4, hc5, hrun, hcode, hvalid,
    haddr, List.exchange, State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_xAt (s : State) (i returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1018)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock xAtPath
      (atEntry s (UInt256.ofNat 0x74b) i returnDest rest) =
        some (atReturned s (UInt256.ofNat 0x2a0) i returnDest rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have haddr : UInt256.ofNat 0x2a0 +
      UInt256.shiftLeft i (UInt256.ofNat 5) =
        slotAddress (UInt256.ofNat 0x2a0) i := by
    rw [slotAddress, Challenge.EvmProof.Word.word_add_comm]
  simp [xAtPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    atEntry, atReturned, loadedWord, hc2, hc3, hc4, hc5, hrun, hcode, hvalid,
    haddr, List.exchange, State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_wordSet (s : State) (base i value returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock hSetPath
      (setEntry s base i value returnDest rest) =
        some (setReturned s base i value returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have haddr : UInt256.shiftLeft i (UInt256.ofNat 5) + base =
      slotAddress base i := rfl
  simp [hSetPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    setEntry, setReturned, storedWord, Challenge.EvmProof.Word.mask32,
    hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hrun, hcode, hvalid, haddr,
    land_comm, List.exchange, State.activeWordsAfterUInt256]

theorem run_hSet (s : State) (i value returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock hSetPath
      (hSetEntry s i value returnDest rest) =
        some (hSetReturned s i value returnDest rest) := by
  exact run_wordSet s (UInt256.ofNat 0x20) i value returnDest rest
    hstack hcode hrun hvalid

set_option linter.unusedSimpArgs false in
theorem run_xSet (s : State) (i value returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1017)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock xSetPath
      (xSetEntry s i value returnDest rest) =
        some (xSetReturned s i value returnDest rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have haddr : UInt256.ofNat 0x2a0 +
      UInt256.shiftLeft i (UInt256.ofNat 5) =
        slotAddress (UInt256.ofNat 0x2a0) i := by
    rw [slotAddress, Challenge.EvmProof.Word.word_add_comm]
  simp [xSetPath, Schedule.xSetPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    xSetEntry, xSetReturned, storedWord, Challenge.EvmProof.Word.mask32,
    hc1, hc2, hc3, hc4, hc5, hc6, hc7, hrun, hcode, hvalid, haddr,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_tableAt (s : State) (base i returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock tableAtPath
      (tableAtEntry s base i returnDest rest) =
        some (tableAtReturned s base i returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have haddr : (base - UInt256.ofNat 31) + i = tableAddress base i := rfl
  simp [tableAtPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    tableAtEntry, tableAtReturned, tableValue,
    hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hrun, hcode, hvalid, haddr,
    List.exchange, State.activeWordsAfterUInt256]

def gasSteps_hAt (s : State) (i returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1018)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (atEntry s (UInt256.ofNat 0x20) i returnDest rest)
      (atReturned s (UInt256.ofNat 0x20) i returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka hAtPath
      (s := atEntry s (UInt256.ofNat 0x20) i returnDest rest)
  · exact hcode
  · exact hfork
  · exact run_hAt s i returnDest rest hstack hcode hrun hvalid
  · exact hrun
  · exact hnp

def gasSteps_wordSet (s : State) (base i value returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (setEntry s base i value returnDest rest)
      (setReturned s base i value returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka hSetPath
      (s := setEntry s base i value returnDest rest)
  · exact hcode
  · exact hfork
  · exact run_wordSet s base i value returnDest rest hstack hcode hrun hvalid
  · exact hrun
  · exact hnp

def gasSteps_hSet (s : State) (i value returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (hSetEntry s i value returnDest rest)
      (hSetReturned s i value returnDest rest) :=
  gasSteps_wordSet s (UInt256.ofNat 0x20) i value returnDest rest
    hstack hcode hfork hrun hnp hvalid

def gasSteps_xAt (s : State) (i returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1018)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (atEntry s (UInt256.ofNat 0x74b) i returnDest rest)
      (atReturned s (UInt256.ofNat 0x2a0) i returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka xAtPath
      (s := atEntry s (UInt256.ofNat 0x74b) i returnDest rest)
  · exact hcode
  · exact hfork
  · exact run_xAt s i returnDest rest hstack hcode hrun hvalid
  · exact hrun
  · exact hnp

def gasSteps_xSet (s : State) (i value returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1017)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (xSetEntry s i value returnDest rest)
      (xSetReturned s i value returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka xSetPath
      (s := xSetEntry s i value returnDest rest)
  · exact hcode
  · exact hfork
  · exact run_xSet s i value returnDest rest hstack hcode hrun hvalid
  · exact hrun
  · exact hnp

def gasSteps_tableAt (s : State) (base i returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (tableAtEntry s base i returnDest rest)
      (tableAtReturned s base i returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tableAtPath
      (s := tableAtEntry s base i returnDest rest)
  · exact hcode
  · exact hfork
  · exact run_tableAt s base i returnDest rest hstack hcode hrun hvalid
  · exact hrun
  · exact hnp

@[simp] theorem storedWord_memory (s : State) (base i value : UInt256) :
    (storedWord s base i value).memory =
      MachineState.writeBytes s.memory
        (Data.Bytes.natToBytesPadded
          (UInt256.land value (UInt256.ofNat 0xffffffff)).toNat 32)
        (slotAddress base i).toNat := by
  rfl

@[simp] theorem loadedWord_storedWord (s : State) (base i value : UInt256) :
    loadedWord (storedWord s base i value) base i =
      UInt256.land value (UInt256.ofNat 0xffffffff) := by
  unfold loadedWord
  rw [storedWord_memory, Challenge.EvmProof.Memory.readWord_writeWord]

theorem loadedWord_storedWord_disjoint (s : State)
    (writeBase writeI value readBase readI : UInt256)
    (hdisjoint :
      (slotAddress readBase readI).toNat + 32 ≤
          (slotAddress writeBase writeI).toNat ∨
        (slotAddress writeBase writeI).toNat + 32 ≤
          (slotAddress readBase readI).toNat) :
    loadedWord (storedWord s writeBase writeI value) readBase readI =
      loadedWord s readBase readI := by
  unfold loadedWord
  rw [storedWord_memory,
    Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  · simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using
      hdisjoint

theorem slotAddress_ofNat (base i : Nat)
    (hi : i < 2 ^ 256) (haddr : i * 32 + base < 2 ^ 256) :
    slotAddress (UInt256.ofNat base) (UInt256.ofNat i) =
      UInt256.ofNat (base + i * 32) := by
  unfold slotAddress
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat hi (by omega) (by
    norm_num at haddr ⊢
    omega)]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by
    norm_num at haddr ⊢
    exact haddr)]
  congr 1
  omega

/-- The generic `xAt` value specializes to the schedule's X-slot accessor. -/
theorem loadedWord_xValue (s : State) (i : Nat) (hi : i < 16) :
    loadedWord s (UInt256.ofNat 0x2a0) (UInt256.ofNat i) =
      ScheduleCorrect.xValue s i := by
  unfold loadedWord ScheduleCorrect.xValue
  rw [slotAddress_ofNat 0x2a0 i (by omega) (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), ScheduleCorrect.xSlotWord_toNat i hi]

private theorem land31_ofNat (i : Nat) (hi : i < 2 ^ 256) :
    UInt256.land (UInt256.ofNat i) (UInt256.ofNat 31) =
      UInt256.ofNat (i % 32) := by
  apply Challenge.EvmProof.Word.word_ext
  simp only [UInt256.land, UInt256.toNat]
  have hland : (↑(Fin.land (UInt256.ofNat i).val
      (UInt256.ofNat 31).val) : Nat) =
      (UInt256.ofNat i).val.val &&& (UInt256.ofNat 31).val.val :=
    Fin.and_val _ _
  rw [hland]
  change (UInt256.ofNat i).toNat &&& (UInt256.ofNat 31).toNat =
    (UInt256.ofNat (i % 32)).toNat
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hi,
    show (UInt256.ofNat 31).toNat = 31 by decide,
    show 31 = 2 ^ 5 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  norm_num
  rw [Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt i (by omega)) (by norm_num))]

private theorem tableAddress_ofNat (base i : Nat)
    (hbase31 : 31 ≤ base) (hbase : base < 2 ^ 64) (hi : i < 80) :
    tableAddress (UInt256.ofNat base) (UInt256.ofNat i) =
      UInt256.ofNat (base - 31 + i) := by
  unfold tableAddress
  rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega),
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]

/-- The executed packed-table helper is exactly the initialization proof's
`tableByte` accessor on every RIPEMD table index. -/
theorem tableValue_tableByte (s : State) (base i : Nat)
    (hbase31 : 31 ≤ base) (hbase : base < 2 ^ 64) (hi : i < 80) :
    tableValue s (UInt256.ofNat base) (UInt256.ofNat i) =
      InitializationCorrect.tableByte s.memory base i := by
  unfold tableValue InitializationCorrect.tableByte
  rw [tableAddress_ofNat base i hbase31 hbase hi,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (show base - 31 + i < 2 ^ 256 by omega)]
  have hL := Challenge.EvmProof.Bytes.byteAt_readWord
    s.memory (base - 31 + i) 31 (by norm_num)
  have hR := Challenge.EvmProof.Bytes.byteAt_readWord
    s.memory (base + 32 * (i / 32)) (i % 32) (by omega)
  have hidx : base - 31 + i + 31 = base + 32 * (i / 32) + i % 32 := by omega
  rw [hL, hR, hidx]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.TableTrace
