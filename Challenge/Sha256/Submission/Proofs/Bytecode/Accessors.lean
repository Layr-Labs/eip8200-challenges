import Challenge.Sha256.Submission.Proofs.Bytecode.PaddingTrace
set_option warningAsError true
set_option maxRecDepth 10000
/-!
# Certified summaries for the reference memory accessors

The compiler implements Yul functions as internal jumps.  These summaries
execute those raw instruction ranges once and expose compact call lemmas for
the schedule and compression proofs.
-/

namespace Challenge.Sha256.Submission.Proofs.Bytecode.Accessors

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def wAtPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨231, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨232, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨233, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨234, .push ⟨2, by decide⟩ (UInt256.ofNat 800), by rfl, by decide⟩,
   ⟨235, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨236, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨237, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨238, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨239, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨240, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def hAtPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨260, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨261, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨262, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨263, .push ⟨2, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨264, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨265, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨266, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨267, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨268, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨269, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def slotOffset (base : Nat) (index : UInt256) : Nat :=
  (UInt256.shiftLeft index (UInt256.ofNat 5) + UInt256.ofNat base).toNat

def loadEntry (s : State) (entry : Nat) (index output returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat entry
    stack := [index, output, returnDest] ++ rest }

def loadReturned (s : State) (base : Nat) (index returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := returnDest
    stack := MachineState.readWord s.memory (slotOffset base index) :: rest
    activeWords := s.activeWordsAfterUInt256 (slotOffset base index) 32 }

@[simp] private theorem pc201 : Artifact.referenceArtifact.instructionPC 231 = 279 := by decide
@[simp] private theorem pc202 : Artifact.referenceArtifact.instructionPC 232 = 280 := by decide
@[simp] private theorem pc203 : Artifact.referenceArtifact.instructionPC 233 = 282 := by decide
@[simp] private theorem pc204 : Artifact.referenceArtifact.instructionPC 234 = 283 := by decide
@[simp] private theorem pc205 : Artifact.referenceArtifact.instructionPC 235 = 286 := by decide
@[simp] private theorem pc206 : Artifact.referenceArtifact.instructionPC 236 = 287 := by decide
@[simp] private theorem pc207 : Artifact.referenceArtifact.instructionPC 237 = 288 := by decide
@[simp] private theorem pc208 : Artifact.referenceArtifact.instructionPC 238 = 289 := by decide
@[simp] private theorem pc209 : Artifact.referenceArtifact.instructionPC 239 = 290 := by decide
@[simp] private theorem pc210 : Artifact.referenceArtifact.instructionPC 240 = 291 := by decide
@[simp] private theorem next201 : (UInt256.ofNat 279).succ = UInt256.ofNat 280 := by decide
@[simp] private theorem next202 : UInt256.ofNat 280 + UInt256.ofNat 2 = UInt256.ofNat 282 := by decide
@[simp] private theorem next203 : (UInt256.ofNat 282).succ = UInt256.ofNat 283 := by decide
@[simp] private theorem next204 : UInt256.ofNat 283 + UInt256.ofNat 3 = UInt256.ofNat 286 := by decide
@[simp] private theorem next205 : (UInt256.ofNat 286).succ = UInt256.ofNat 287 := by decide
@[simp] private theorem next206 : (UInt256.ofNat 287).succ = UInt256.ofNat 288 := by decide
@[simp] private theorem next207 : (UInt256.ofNat 288).succ = UInt256.ofNat 289 := by decide
@[simp] private theorem next208 : (UInt256.ofNat 289).succ = UInt256.ofNat 290 := by decide
@[simp] private theorem next209 : (UInt256.ofNat 290).succ = UInt256.ofNat 291 := by decide

@[simp] private theorem pc230 : Artifact.referenceArtifact.instructionPC 260 = 318 := by decide
@[simp] private theorem pc231 : Artifact.referenceArtifact.instructionPC 261 = 319 := by decide
@[simp] private theorem pc232 : Artifact.referenceArtifact.instructionPC 262 = 321 := by decide
@[simp] private theorem pc233 : Artifact.referenceArtifact.instructionPC 263 = 322 := by decide
@[simp] private theorem pc234 : Artifact.referenceArtifact.instructionPC 264 = 325 := by decide
@[simp] private theorem pc235 : Artifact.referenceArtifact.instructionPC 265 = 326 := by decide
@[simp] private theorem pc236 : Artifact.referenceArtifact.instructionPC 266 = 327 := by decide
@[simp] private theorem pc237 : Artifact.referenceArtifact.instructionPC 267 = 328 := by decide
@[simp] private theorem pc238 : Artifact.referenceArtifact.instructionPC 268 = 329 := by decide
@[simp] private theorem pc239 : Artifact.referenceArtifact.instructionPC 269 = 330 := by decide
@[simp] private theorem next230 : (UInt256.ofNat 318).succ = UInt256.ofNat 319 := by decide
@[simp] private theorem next231 : UInt256.ofNat 319 + UInt256.ofNat 2 = UInt256.ofNat 321 := by decide
@[simp] private theorem next232 : (UInt256.ofNat 321).succ = UInt256.ofNat 322 := by decide
@[simp] private theorem next233 : UInt256.ofNat 322 + UInt256.ofNat 3 = UInt256.ofNat 325 := by decide
@[simp] private theorem next234 : (UInt256.ofNat 325).succ = UInt256.ofNat 326 := by decide
@[simp] private theorem next235 : (UInt256.ofNat 326).succ = UInt256.ofNat 327 := by decide
@[simp] private theorem next236 : (UInt256.ofNat 327).succ = UInt256.ofNat 328 := by decide
@[simp] private theorem next237 : (UInt256.ofNat 328).succ = UInt256.ofNat 329 := by decide
@[simp] private theorem next238 : (UInt256.ofNat 329).succ = UInt256.ofNat 330 := by decide

set_option linter.unusedSimpArgs false in
theorem run_load (path : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    (s : State) (entry base : Nat) (index output returnDest : UInt256)
    (rest : List UInt256)
    (hmatch : (path = wAtPath ∧ entry = 279 ∧ base = 800) ∨
      (path = hAtPath ∧ entry = 318 ∧ base = 288))
    (hcap : rest.length < 1018)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock path
      (loadEntry s entry index output returnDest rest) =
        some (loadReturned s base index returnDest rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hca3 : 1 + (1 + (rest.length + 1)) < 1024 := by omega
  have hca4 : 1 + (1 + (1 + (rest.length + 1))) < 1024 := by omega
  have hca5 : 1 + (1 + (1 + (1 + (rest.length + 1)))) < 1024 := by omega
  rcases hmatch with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · have hoff : UInt256.ofNat 800 + UInt256.shiftLeft index (UInt256.ofNat 5) =
      UInt256.shiftLeft index (UInt256.ofNat 5) + UInt256.ofNat 800 :=
      Challenge.EvmProof.Word.word_add_comm _ _
    simp [wAtPath, hAtPath, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      loadEntry, loadReturned, slotOffset, List.exchange, hc2, hc3, hc4, hc5,
      hca3, hca4, hca5, hcode, hrun, hvalid, hoff,
      State.activeWordsAfterUInt256]
  · have hoff : UInt256.ofNat 288 + UInt256.shiftLeft index (UInt256.ofNat 5) =
      UInt256.shiftLeft index (UInt256.ofNat 5) + UInt256.ofNat 288 :=
      Challenge.EvmProof.Word.word_add_comm _ _
    simp [wAtPath, hAtPath, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      loadEntry, loadReturned, slotOffset, List.exchange, hc2, hc3, hc4, hc5,
      hca3, hca4, hca5, hcode, hrun, hvalid, hoff,
      State.activeWordsAfterUInt256]

def gasSteps_wAt (s : State) (index output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1018)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (loadEntry s 279 index output returnDest rest)
      (loadReturned s 800 index returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka wAtPath
  · exact hcode
  · exact hfork
  · exact run_load wAtPath s 279 800 index output returnDest rest
      (Or.inl ⟨rfl, rfl, rfl⟩) hcap hcode hrun hvalid
  · exact hrun
  · exact hnp

def gasSteps_hAt (s : State) (index output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1018)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (loadEntry s 318 index output returnDest rest)
      (loadReturned s 288 index returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka hAtPath
  · exact hcode
  · exact hfork
  · exact run_load hAtPath s 318 288 index output returnDest rest
      (Or.inr ⟨rfl, rfl, rfl⟩) hcap hcode hrun hvalid
  · exact hrun
  · exact hnp

def wSetPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨246, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨247, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨248, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨249, .push ⟨2, by decide⟩ (UInt256.ofNat 800), by rfl, by decide⟩,
   ⟨250, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨251, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨252, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def hSetPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨275, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨276, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨277, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨278, .push ⟨2, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨279, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨280, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨281, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def storeEntry (s : State) (entry : Nat) (index value returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat entry
    stack := [index, value, returnDest] ++ rest }

def storeReturned (s : State) (base : Nat) (index value returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := returnDest
    stack := rest
    memory := MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded value.toNat 32) (slotOffset base index)
    activeWords := s.activeWordsAfterUInt256 (slotOffset base index) 32 }

@[simp] private theorem pc216 : Artifact.referenceArtifact.instructionPC 246 = 299 := by decide
@[simp] private theorem pc217 : Artifact.referenceArtifact.instructionPC 247 = 300 := by decide
@[simp] private theorem pc218 : Artifact.referenceArtifact.instructionPC 248 = 302 := by decide
@[simp] private theorem pc219 : Artifact.referenceArtifact.instructionPC 249 = 303 := by decide
@[simp] private theorem pc220 : Artifact.referenceArtifact.instructionPC 250 = 306 := by decide
@[simp] private theorem pc221 : Artifact.referenceArtifact.instructionPC 251 = 307 := by decide
@[simp] private theorem pc222 : Artifact.referenceArtifact.instructionPC 252 = 308 := by decide
@[simp] private theorem next216 : (UInt256.ofNat 299).succ = UInt256.ofNat 300 := by decide
@[simp] private theorem next217 : UInt256.ofNat 300 + UInt256.ofNat 2 = UInt256.ofNat 302 := by decide
@[simp] private theorem next218 : (UInt256.ofNat 302).succ = UInt256.ofNat 303 := by decide
@[simp] private theorem next219 : UInt256.ofNat 303 + UInt256.ofNat 3 = UInt256.ofNat 306 := by decide
@[simp] private theorem next220 : (UInt256.ofNat 306).succ = UInt256.ofNat 307 := by decide
@[simp] private theorem next221 : (UInt256.ofNat 307).succ = UInt256.ofNat 308 := by decide

@[simp] private theorem pc245 : Artifact.referenceArtifact.instructionPC 275 = 338 := by decide
@[simp] private theorem pc246 : Artifact.referenceArtifact.instructionPC 276 = 339 := by decide
@[simp] private theorem pc247 : Artifact.referenceArtifact.instructionPC 277 = 341 := by decide
@[simp] private theorem pc248 : Artifact.referenceArtifact.instructionPC 278 = 342 := by decide
@[simp] private theorem pc249 : Artifact.referenceArtifact.instructionPC 279 = 345 := by decide
@[simp] private theorem pc250 : Artifact.referenceArtifact.instructionPC 280 = 346 := by decide
@[simp] private theorem pc251 : Artifact.referenceArtifact.instructionPC 281 = 347 := by decide
@[simp] private theorem next245 : (UInt256.ofNat 338).succ = UInt256.ofNat 339 := by decide
@[simp] private theorem next246 : UInt256.ofNat 339 + UInt256.ofNat 2 = UInt256.ofNat 341 := by decide
@[simp] private theorem next247 : (UInt256.ofNat 341).succ = UInt256.ofNat 342 := by decide
@[simp] private theorem next248 : UInt256.ofNat 342 + UInt256.ofNat 3 = UInt256.ofNat 345 := by decide
@[simp] private theorem next249 : (UInt256.ofNat 345).succ = UInt256.ofNat 346 := by decide
@[simp] private theorem next250 : (UInt256.ofNat 346).succ = UInt256.ofNat 347 := by decide

set_option linter.unusedSimpArgs false in
theorem run_store (path : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    (s : State) (entry base : Nat) (index value returnDest : UInt256)
    (rest : List UInt256)
    (hmatch : (path = wSetPath ∧ entry = 299 ∧ base = 800) ∨
      (path = hSetPath ∧ entry = 338 ∧ base = 288))
    (hcap : rest.length < 1017)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock path
      (storeEntry s entry index value returnDest rest) =
        some (storeReturned s base index value returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hca3 : 1 + (1 + (rest.length + 1)) < 1024 := by omega
  have hca4 : 1 + (1 + (1 + (rest.length + 1))) < 1024 := by omega
  have hca5 : 1 + (1 + (1 + (1 + (rest.length + 1)))) < 1024 := by omega
  have hca6 : 1 + (1 + (1 + (1 + (1 + (rest.length + 1))))) < 1024 := by omega
  rcases hmatch with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · have hoff : UInt256.ofNat 800 + UInt256.shiftLeft index (UInt256.ofNat 5) =
        UInt256.shiftLeft index (UInt256.ofNat 5) + UInt256.ofNat 800 :=
      Challenge.EvmProof.Word.word_add_comm _ _
    simp [wSetPath, hSetPath, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      storeEntry, storeReturned, slotOffset, List.exchange, hc1, hc2, hc3, hc4,
      hc5, hc6, hca3, hca4, hca5, hca6, hcode, hrun, hvalid, hoff,
      State.activeWordsAfterUInt256]
  · have hoff : UInt256.ofNat 288 + UInt256.shiftLeft index (UInt256.ofNat 5) =
        UInt256.shiftLeft index (UInt256.ofNat 5) + UInt256.ofNat 288 :=
      Challenge.EvmProof.Word.word_add_comm _ _
    simp [wSetPath, hSetPath, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      storeEntry, storeReturned, slotOffset, List.exchange, hc1, hc2, hc3, hc4,
      hc5, hc6, hca3, hca4, hca5, hca6, hcode, hrun, hvalid, hoff,
      State.activeWordsAfterUInt256]

def gasSteps_wSet (s : State) (index value returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1017)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (storeEntry s 299 index value returnDest rest)
      (storeReturned s 800 index value returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka wSetPath
  · exact hcode
  · exact hfork
  · exact run_store wSetPath s 299 800 index value returnDest rest
      (Or.inl ⟨rfl, rfl, rfl⟩) hcap hcode hrun hvalid
  · exact hrun
  · exact hnp

def gasSteps_hSet (s : State) (index value returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1017)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (storeEntry s 338 index value returnDest rest)
      (storeReturned s 288 index value returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka hSetPath
  · exact hcode
  · exact hfork
  · exact run_store hSetPath s 338 288 index value returnDest rest
      (Or.inr ⟨rfl, rfl, rfl⟩) hcap hcode hrun hvalid
  · exact hrun
  · exact hnp

def kAtPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨214, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨215, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨216, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨217, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨218, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨219, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨220, .push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨221, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨222, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨223, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨224, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨225, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def kAtReturned (s : State) (index returnDest : UInt256)
    (rest : List UInt256) : State :=
  let offset := (UInt256.shiftLeft index (UInt256.ofNat 2) + UInt256.ofNat 32).toNat
  { s with
    pc := returnDest
    stack := UInt256.shiftRight (MachineState.readWord s.memory offset)
      (UInt256.ofNat 224) :: rest
    activeWords := s.activeWordsAfterUInt256 offset 32 }

@[simp] private theorem pc184 : Artifact.referenceArtifact.instructionPC 214 = 257 := by decide
@[simp] private theorem pc185 : Artifact.referenceArtifact.instructionPC 215 = 258 := by decide
@[simp] private theorem pc186 : Artifact.referenceArtifact.instructionPC 216 = 260 := by decide
@[simp] private theorem pc187 : Artifact.referenceArtifact.instructionPC 217 = 261 := by decide
@[simp] private theorem pc188 : Artifact.referenceArtifact.instructionPC 218 = 263 := by decide
@[simp] private theorem pc189 : Artifact.referenceArtifact.instructionPC 219 = 264 := by decide
@[simp] private theorem pc190 : Artifact.referenceArtifact.instructionPC 220 = 265 := by decide
@[simp] private theorem pc191 : Artifact.referenceArtifact.instructionPC 221 = 267 := by decide
@[simp] private theorem pc192 : Artifact.referenceArtifact.instructionPC 222 = 268 := by decide
@[simp] private theorem pc193 : Artifact.referenceArtifact.instructionPC 223 = 269 := by decide
@[simp] private theorem pc194 : Artifact.referenceArtifact.instructionPC 224 = 270 := by decide
@[simp] private theorem pc195 : Artifact.referenceArtifact.instructionPC 225 = 271 := by decide
@[simp] private theorem next184 : (UInt256.ofNat 257).succ = UInt256.ofNat 258 := by decide
@[simp] private theorem next185 : UInt256.ofNat 258 + UInt256.ofNat 2 = UInt256.ofNat 260 := by decide
@[simp] private theorem next186 : (UInt256.ofNat 260).succ = UInt256.ofNat 261 := by decide
@[simp] private theorem next187 : UInt256.ofNat 261 + UInt256.ofNat 2 = UInt256.ofNat 263 := by decide
@[simp] private theorem next188 : (UInt256.ofNat 263).succ = UInt256.ofNat 264 := by decide
@[simp] private theorem next189 : (UInt256.ofNat 264).succ = UInt256.ofNat 265 := by decide
@[simp] private theorem next190 : UInt256.ofNat 265 + UInt256.ofNat 2 = UInt256.ofNat 267 := by decide
@[simp] private theorem next191 : (UInt256.ofNat 267).succ = UInt256.ofNat 268 := by decide
@[simp] private theorem next192 : (UInt256.ofNat 268).succ = UInt256.ofNat 269 := by decide
@[simp] private theorem next193 : (UInt256.ofNat 269).succ = UInt256.ofNat 270 := by decide
@[simp] private theorem next194 : (UInt256.ofNat 270).succ = UInt256.ofNat 271 := by decide

set_option linter.unusedSimpArgs false in
theorem run_kAt (s : State) (index output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1018)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock kAtPath
      (loadEntry s 257 index output returnDest rest) =
        some (kAtReturned s index returnDest rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hca3 : 1 + (1 + (rest.length + 1)) < 1024 := by omega
  have hca4 : 1 + (1 + (1 + (rest.length + 1))) < 1024 := by omega
  have hca5 : 1 + (1 + (1 + (1 + (rest.length + 1)))) < 1024 := by omega
  have hoff : UInt256.ofNat 32 + UInt256.shiftLeft index (UInt256.ofNat 2) =
      UInt256.shiftLeft index (UInt256.ofNat 2) + UInt256.ofNat 32 :=
    Challenge.EvmProof.Word.word_add_comm _ _
  simp [kAtPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loadEntry, kAtReturned, List.exchange, hc2, hc3, hc4, hc5, hca3, hca4,
    hca5, hcode, hrun, hvalid, hoff, State.activeWordsAfterUInt256]

def gasSteps_kAt (s : State) (index output returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1018)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (loadEntry s 257 index output returnDest rest)
      (kAtReturned s index returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka kAtPath
  · exact hcode
  · exact hfork
  · exact run_kAt s index output returnDest rest hcap hcode hrun hvalid
  · exact hrun
  · exact hnp

end Challenge.Sha256.Submission.Proofs.Bytecode.Accessors
