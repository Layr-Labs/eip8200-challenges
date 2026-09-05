import Challenge.Ripemd160.Submission.Proofs.Bytecode.RoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Trace

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-!
# Immediate round-call wrapper (first left site probe)

The compression body calls the verified `RoundTrace` helper through eight
immediate pushes followed by `JUMP`:

```
PUSH ret; PUSH K; PUSH rotation; PUSH wordIndex; PUSH j; PUSH base;
PUSH2 0x114; JUMP
```

`WrapperSite` is the reusable descriptor for any such site.  This probe
instantiates only the first left site (artifact indices 997--1004) and
composes its pushes with the unchanged `RoundTrace.gasSteps_round`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateWrapper

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

/-- Reusable descriptor for an eight-instruction immediate round call.

`startIndex` is the first of the eight consecutive artifact indices.  Widths
are explicit so later sites with wider `K`/`wordIndex`/`j` encodings reuse
the same `wrapperPath` constructor; the probe below fixes them to the first
left site's minimal widths. -/
structure WrapperSite where
  startIndex : Nat
  retW : Fin 33
  ret : UInt256
  kW : Fin 33
  k : UInt256
  rotW : Fin 33
  rotation : UInt256
  wiW : Fin 33
  wordIndex : UInt256
  jW : Fin 33
  j : UInt256
  baseW : Fin 33
  base : UInt256
deriving DecidableEq, Repr

/-- Proof-carrying located path for a generic wrapper site. -/
def wrapperPath (site : WrapperSite)
    (h0 : Artifact.submissionArtifact.instructions[site.startIndex]? =
      some (.push site.retW site.ret))
    (h1 : Artifact.submissionArtifact.instructions[site.startIndex + 1]? =
      some (.push site.kW site.k))
    (h2 : Artifact.submissionArtifact.instructions[site.startIndex + 2]? =
      some (.push site.rotW site.rotation))
    (h3 : Artifact.submissionArtifact.instructions[site.startIndex + 3]? =
      some (.push site.wiW site.wordIndex))
    (h4 : Artifact.submissionArtifact.instructions[site.startIndex + 4]? =
      some (.push site.jW site.j))
    (h5 : Artifact.submissionArtifact.instructions[site.startIndex + 5]? =
      some (.push site.baseW site.base))
    (h6 : Artifact.submissionArtifact.instructions[site.startIndex + 6]? =
      some (.push ⟨2, by decide⟩ (UInt256.ofNat 0x114)))
    (h7 : Artifact.submissionArtifact.instructions[site.startIndex + 7]? =
      some (.op .JUMP))
    (wf0 : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push site.retW site.ret))
    (wf1 : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push site.kW site.k))
    (wf2 : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push site.rotW site.rotation))
    (wf3 : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push site.wiW site.wordIndex))
    (wf4 : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push site.jW site.j))
    (wf5 : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push site.baseW site.base))
    (wf6 : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push ⟨2, by decide⟩ (UInt256.ofNat 0x114)))
    (wf7 : Challenge.EvmProof.Stepper.WellFormed .Osaka (.op .JUMP)) :
    List Located :=
  [⟨site.startIndex, .push site.retW site.ret, h0, wf0⟩,
   ⟨site.startIndex + 1, .push site.kW site.k, h1, wf1⟩,
   ⟨site.startIndex + 2, .push site.rotW site.rotation, h2, wf2⟩,
   ⟨site.startIndex + 3, .push site.wiW site.wordIndex, h3, wf3⟩,
   ⟨site.startIndex + 4, .push site.jW site.j, h4, wf4⟩,
   ⟨site.startIndex + 5, .push site.baseW site.base, h5, wf5⟩,
   ⟨site.startIndex + 6, .push ⟨2, by decide⟩ (UInt256.ofNat 0x114),
     h6, wf6⟩,
   ⟨site.startIndex + 7, .op .JUMP, h7, wf7⟩]

/-- First left call site: indices 997--1004. -/
def firstLeftSite : WrapperSite :=
  { startIndex := 997
    retW := ⟨2, by decide⟩
    ret := UInt256.ofNat 0x755
    kW := ⟨0, by decide⟩
    k := UInt256.ofNat 0
    rotW := ⟨1, by decide⟩
    rotation := UInt256.ofNat 11
    wiW := ⟨0, by decide⟩
    wordIndex := UInt256.ofNat 0
    jW := ⟨0, by decide⟩
    j := UInt256.ofNat 0
    baseW := ⟨1, by decide⟩
    base := UInt256.ofNat 0xc0 }

/-- Located path for the first left site. -/
def firstLeftPath : List Located :=
  wrapperPath firstLeftSite
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (wfOp (by decide) trivial rfl)

@[simp] private theorem pc997 :
    Artifact.submissionArtifact.instructionPC 997 = 0x747 := by decide
@[simp] private theorem pc998 :
    Artifact.submissionArtifact.instructionPC 998 = 0x74a := by decide
@[simp] private theorem pc999 :
    Artifact.submissionArtifact.instructionPC 999 = 0x74b := by decide
@[simp] private theorem pc1000 :
    Artifact.submissionArtifact.instructionPC 1000 = 0x74d := by decide
@[simp] private theorem pc1001 :
    Artifact.submissionArtifact.instructionPC 1001 = 0x74e := by decide
@[simp] private theorem pc1002 :
    Artifact.submissionArtifact.instructionPC 1002 = 0x74f := by decide
@[simp] private theorem pc1003 :
    Artifact.submissionArtifact.instructionPC 1003 = 0x751 := by decide
@[simp] private theorem pc1004 :
    Artifact.submissionArtifact.instructionPC 1004 = 0x754 := by decide

@[simp] private theorem valid114 :
    Decode.isValidJumpDest submissionBytecode 0x114 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 208 (by rfl)

@[simp] private theorem valid755 :
    Decode.isValidJumpDest submissionBytecode 0x755 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 1005 (by rfl)

/-- Wrapper entry: outer compression stack underneath the call. -/
def wrapperEntry (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 0x747
    stack := [messageOffset, outerReturn] ++ rest }

/-- Round entry reached after the eight pushes and jump. -/
def wrapperRoundEntry (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 0)
    (UInt256.ofNat 11) (UInt256.ofNat 0) (UInt256.ofNat 0x755)
    ([messageOffset, outerReturn] ++ rest)

private theorem pushSucc0 (s : State) (pcVal : Nat)
    (hpc : s.pc = UInt256.ofNat pcVal) (hbound : pcVal + 1 < 2 ^ 256) :
    s.pc.succ = UInt256.ofNat (pcVal + 1) := by
  rw [hpc]
  exact Challenge.EvmProof.Word.succ_ofNat hbound

private theorem pushAdd (s : State) (pcVal w : Nat)
    (hpc : s.pc = UInt256.ofNat pcVal) (hbound : pcVal + (w + 1) < 2 ^ 256) :
    s.pc + UInt256.ofNat (w + 1) = UInt256.ofNat (pcVal + (w + 1)) := by
  rw [hpc]
  exact Challenge.EvmProof.Word.ofNat_add_ofNat hbound

theorem run_wrapper (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock firstLeftPath
      (wrapperEntry s messageOffset outerReturn rest) =
        some (wrapperRoundEntry s messageOffset outerReturn rest) := by
  have hc0 : ([messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc1 : ([UInt256.ofNat 0x755, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc2 : ([UInt256.ofNat 0, UInt256.ofNat 0x755, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc3 : ([UInt256.ofNat 11, UInt256.ofNat 0, UInt256.ofNat 0x755,
      messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc4 : ([UInt256.ofNat 0, UInt256.ofNat 11, UInt256.ofNat 0,
      UInt256.ofNat 0x755, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc5 : ([UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 11,
      UInt256.ofNat 0, UInt256.ofNat 0x755, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc6 : ([UInt256.ofNat 0xc0, UInt256.ofNat 0, UInt256.ofNat 0,
      UInt256.ofNat 11, UInt256.ofNat 0, UInt256.ofNat 0x755, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc7 : ([UInt256.ofNat 0x114, UInt256.ofNat 0xc0, UInt256.ofNat 0,
      UInt256.ofNat 0, UInt256.ofNat 11, UInt256.ofNat 0,
      UInt256.ofNat 0x755, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hcap (m : Nat) (hm : m ≤ 9) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [firstLeftPath, wrapperPath, firstLeftSite, wrapperEntry,
      wrapperRoundEntry, RoundTrace.roundEntry,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hrun, hcode, valid114, pc997, pc998, pc999, pc1000, pc1001,
      pc1002, pc1003, pc1004,
      hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat]

def gasSteps_wrapper (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (wrapperEntry s messageOffset outerReturn rest)
      (wrapperRoundEntry s messageOffset outerReturn rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka firstLeftPath
  · simpa [wrapperEntry, Artifact.submissionArtifact] using hcode
  · simpa [wrapperEntry, State.fork] using hfork
  · exact run_wrapper s messageOffset outerReturn rest hstack hcode hrun
  · simpa [wrapperEntry] using hrun
  · simpa [wrapperEntry] using hnp

/-- One full helper call: eight pushes plus the verified round body. -/
def gasSteps_immediateRound (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (wrapperEntry s messageOffset outerReturn rest)
      (RoundTrace.roundReturned s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 0)
        (UInt256.ofNat 11) (UInt256.ofNat 0) (UInt256.ofNat 0x755)
        ([messageOffset, outerReturn] ++ rest)) := by
  have hstackRound : ([messageOffset, outerReturn] ++ rest).length < 980 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have gWrap := gasSteps_wrapper s messageOffset outerReturn rest hstack hcode
    hfork hrun hnp
  have gRound := RoundTrace.gasSteps_round s (UInt256.ofNat 0xc0) 0
    (by decide) (UInt256.ofNat 0) (UInt256.ofNat 11) (UInt256.ofNat 0)
    (UInt256.ofNat 0x755) ([messageOffset, outerReturn] ++ rest) hstackRound
    hcode hfork hrun hnp valid755
  have hEq : wrapperRoundEntry s messageOffset outerReturn rest =
      RoundTrace.roundEntry s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 0)
        (UInt256.ofNat 11) (UInt256.ofNat 0) (UInt256.ofNat 0x755)
        ([messageOffset, outerReturn] ++ rest) := by
    rfl
  exact gWrap.trans (Challenge.EvmProof.GasSteps.cast gRound hEq.symm rfl)

/-! ## Generic immediate wrapper execution -/

theorem instructionPC_push_succ
    (i : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionArtifact.instructions[i]? =
      some (.push width value)) :
    Artifact.submissionArtifact.instructionPC (i + 1) =
      Artifact.submissionArtifact.instructionPC i + width.val + 1 := by
  unfold Challenge.EvmProof.ProgramArtifact.instructionPC
  have htake : Artifact.submissionArtifact.instructions.take (i + 1) =
      Artifact.submissionArtifact.instructions.take i ++ [.push width value] := by
    simp [List.take_add_one, hget]
  rw [htake, YulEvmCompiler.assembleBytes_append,
    YulEvmCompiler.assembleBytes_cons]
  simp [YulEvmCompiler.Instr.bytes]
  omega

/-- Exact code and fork certificates for one immediate helper call. -/
structure WrapperSiteCertificate (site : WrapperSite) : Prop where
  h0 : Artifact.submissionArtifact.instructions[site.startIndex]? =
    some (.push site.retW site.ret)
  h1 : Artifact.submissionArtifact.instructions[site.startIndex + 1]? =
    some (.push site.kW site.k)
  h2 : Artifact.submissionArtifact.instructions[site.startIndex + 2]? =
    some (.push site.rotW site.rotation)
  h3 : Artifact.submissionArtifact.instructions[site.startIndex + 3]? =
    some (.push site.wiW site.wordIndex)
  h4 : Artifact.submissionArtifact.instructions[site.startIndex + 4]? =
    some (.push site.jW site.j)
  h5 : Artifact.submissionArtifact.instructions[site.startIndex + 5]? =
    some (.push site.baseW site.base)
  h6 : Artifact.submissionArtifact.instructions[site.startIndex + 6]? =
    some (.push ⟨2, by decide⟩ (UInt256.ofNat 0x114))
  h7 : Artifact.submissionArtifact.instructions[site.startIndex + 7]? =
    some (.op .JUMP)
  wf0 : Challenge.EvmProof.Stepper.WellFormed .Osaka
    (.push site.retW site.ret)
  wf1 : Challenge.EvmProof.Stepper.WellFormed .Osaka
    (.push site.kW site.k)
  wf2 : Challenge.EvmProof.Stepper.WellFormed .Osaka
    (.push site.rotW site.rotation)
  wf3 : Challenge.EvmProof.Stepper.WellFormed .Osaka
    (.push site.wiW site.wordIndex)
  wf4 : Challenge.EvmProof.Stepper.WellFormed .Osaka
    (.push site.jW site.j)
  wf5 : Challenge.EvmProof.Stepper.WellFormed .Osaka
    (.push site.baseW site.base)
  wf6 : Challenge.EvmProof.Stepper.WellFormed .Osaka
    (.push ⟨2, by decide⟩ (UInt256.ofNat 0x114))
  wf7 : Challenge.EvmProof.Stepper.WellFormed .Osaka (.op .JUMP)

/-- Located instructions obtained from a wrapper-site certificate. -/
def wrapperSitePath (site : WrapperSite) (h : WrapperSiteCertificate site) :
    List Located :=
  wrapperPath site h.h0 h.h1 h.h2 h.h3 h.h4 h.h5 h.h6 h.h7
    h.wf0 h.wf1 h.wf2 h.wf3 h.wf4 h.wf5 h.wf6 h.wf7

/-- State at the first immediate push of a wrapper site. -/
def wrapperEntryAt (site : WrapperSite) (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (Artifact.submissionArtifact.instructionPC site.startIndex)
    stack := [messageOffset, outerReturn] ++ rest }

/-- State at the verified round helper after one immediate wrapper. -/
def wrapperRoundEntryAt (site : WrapperSite) (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) : State :=
  RoundTrace.roundEntry s site.base site.j.toNat site.wordIndex site.rotation site.k
    site.ret ([messageOffset, outerReturn] ++ rest)

private theorem wrapperPushValue_eq {width : Fin 33} {value : UInt256}
    (hfit : value.toNat < 256 ^ width.val) :
    (if width.val = 0 then (0 : UInt256) else value) = value := by
  by_cases hz : width.val = 0
  · have hv : value.toNat = 0 := by
      simp [hz] at hfit
      omega
    have hv' : value = (0 : UInt256) := by
      apply Challenge.EvmProof.Word.word_ext
      rw [hv]
      rfl
    simp [hz, hv']
  · simp [hz]

private theorem wrapperPushPC_eq (index pc : Nat) (width : Fin 33)
    (hpc : Artifact.submissionArtifact.instructionPC index = pc)
    (hnext : Artifact.submissionArtifact.instructionPC (index + 1) =
      Artifact.submissionArtifact.instructionPC index + width.val + 1)
    (hbound : Artifact.submissionArtifact.instructionPC (index + 1) < 2 ^ 256) :
    (if width.val = 0 then (UInt256.ofNat pc).succ
      else UInt256.ofNat pc + UInt256.ofNat (width.val + 1)) =
      UInt256.ofNat (Artifact.submissionArtifact.instructionPC (index + 1)) := by
  by_cases hz : width.val = 0
  · simp [hz, hpc] at hnext ⊢
    rw [Challenge.EvmProof.Word.succ_ofNat (by omega)]
    congr 1
    omega
  · simp only [if_neg hz]
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
    congr 1
    omega

private theorem run_wrapper_push
    (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionArtifact.instructions[index]? =
      some (.push width value))
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value))
    (s : State)
    (hpc : s.pc = UInt256.ofNat
      (Artifact.submissionArtifact.instructionPC index))
    (hstack : s.stack.length < 1024) :
    Challenge.EvmProof.Stepper.runLocated
      (⟨index, .push width value, hget, hwf⟩ : Located) s =
      some {s with
        stack := value :: s.stack
        pc := UInt256.ofNat
          (Artifact.submissionArtifact.instructionPC (index + 1))} := by
  have hnext := instructionPC_push_succ index width value hget
  have hpc' := wrapperPushPC_eq index
    (Artifact.submissionArtifact.instructionPC index) width rfl hnext
    (Trace.pcBound (index + 1))
  have hvalue := wrapperPushValue_eq hwf.1
  unfold Challenge.EvmProof.Stepper.runLocated
  change (if s.pc.toNat = Artifact.submissionArtifact.instructionPC index then
      Challenge.EvmProof.Stepper.runInstr (.push width value) s else none) = _
  by_cases hmatch : s.pc.toNat = Artifact.submissionArtifact.instructionPC index
  · simp only [if_pos hmatch]
    unfold Challenge.EvmProof.Stepper.runInstr
    rw [if_pos hstack]
    by_cases hz : width.val = 0
    · have hv : (0 : UInt256) = value := by
        simpa [hz] using hvalue
      have hpc'' :
          (UInt256.ofNat (Artifact.submissionArtifact.instructionPC index)).succ =
            UInt256.ofNat (Artifact.submissionArtifact.instructionPC (index + 1)) := by
        simpa [hz] using hpc'
      simp [hz, hv, hpc, hpc'']
    · simp only [hz, if_neg]
      have hpc'' :
          UInt256.ofNat (Artifact.submissionArtifact.instructionPC index) +
              UInt256.ofNat (width.val + 1) =
            UInt256.ofNat (Artifact.submissionArtifact.instructionPC (index + 1)) := by
        simpa [hz] using hpc'
      simp [hpc, hpc'']
  · simp only [if_neg hmatch]
    exact False.elim (hmatch (Trace.pcToNat hpc))

private theorem run_wrapper_jump
    (index : Nat)
    (hget : Artifact.submissionArtifact.instructions[index]? =
      some (.op .JUMP))
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.op .JUMP))
    (s : State) (dest : UInt256) (rest : List UInt256)
    (hpc : s.pc.toNat = Artifact.submissionArtifact.instructionPC index)
    (hstack : s.stack.length < 1024)
    (hstack_eq : s.stack = dest :: rest)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hvalid : Decode.isValidJumpDest submissionBytecode dest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocated
      (⟨index, .op .JUMP, hget, hwf⟩ : Located)
      s =
      some {s with stack := rest, pc := dest} := by
  unfold Challenge.EvmProof.Stepper.runLocated
  change (if s.pc.toNat = Artifact.submissionArtifact.instructionPC index then
      Challenge.EvmProof.Stepper.runInstr (.op .JUMP) s else none) = _
  simp only [if_pos hpc]
  unfold Challenge.EvmProof.Stepper.runInstr
  simp only [if_pos hstack]
  simp [hstack_eq, hcode, hvalid]

/-- Functional proof for one arbitrary immediate wrapper followed by RoundTrace's entry. -/
theorem run_wrapper_site (site : WrapperSite)
    (h : WrapperSiteCertificate site)
    (s : State) (messageOffset outerReturn : UInt256) (rest : List UInt256)
    (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock (wrapperSitePath site h)
      (wrapperEntryAt site s messageOffset outerReturn rest) =
        some (wrapperRoundEntryAt site s messageOffset outerReturn rest) := by
  let q0 : State := wrapperEntryAt site s messageOffset outerReturn rest
  let q1 : State := {q0 with
    stack := site.ret :: q0.stack
    pc := UInt256.ofNat
      (Artifact.submissionArtifact.instructionPC (site.startIndex + 1))}
  let q2 : State := {q1 with
    stack := site.k :: q1.stack
    pc := UInt256.ofNat
      (Artifact.submissionArtifact.instructionPC (site.startIndex + 2))}
  let q3 : State := {q2 with
    stack := site.rotation :: q2.stack
    pc := UInt256.ofNat
      (Artifact.submissionArtifact.instructionPC (site.startIndex + 3))}
  let q4 : State := {q3 with
    stack := site.wordIndex :: q3.stack
    pc := UInt256.ofNat
      (Artifact.submissionArtifact.instructionPC (site.startIndex + 4))}
  let q5 : State := {q4 with
    stack := site.j :: q4.stack
    pc := UInt256.ofNat
      (Artifact.submissionArtifact.instructionPC (site.startIndex + 5))}
  let q6 : State := {q5 with
    stack := site.base :: q5.stack
    pc := UInt256.ofNat
      (Artifact.submissionArtifact.instructionPC (site.startIndex + 6))}
  let q7 : State := {q6 with
    stack := UInt256.ofNat 0x114 :: q6.stack
    pc := UInt256.ofNat
      (Artifact.submissionArtifact.instructionPC (site.startIndex + 7))}
  have hc0 : q0.stack.length < 1024 := by
    dsimp [q0, wrapperEntryAt]
    omega
  have hc1 : q1.stack.length < 1024 := by
    dsimp [q1, q0, wrapperEntryAt]
    omega
  have hc2 : q2.stack.length < 1024 := by
    dsimp [q2, q1, q0, wrapperEntryAt]
    omega
  have hc3 : q3.stack.length < 1024 := by
    dsimp [q3, q2, q1, q0, wrapperEntryAt]
    omega
  have hc4 : q4.stack.length < 1024 := by
    dsimp [q4, q3, q2, q1, q0, wrapperEntryAt]
    omega
  have hc5 : q5.stack.length < 1024 := by
    dsimp [q5, q4, q3, q2, q1, q0, wrapperEntryAt]
    omega
  have hc6 : q6.stack.length < 1024 := by
    dsimp [q6, q5, q4, q3, q2, q1, q0, wrapperEntryAt]
    omega
  have hc7 : q7.stack.length < 1024 := by
    dsimp [q7, q6, q5, q4, q3, q2, q1, q0, wrapperEntryAt]
    omega
  have hp0 : q0.pc = UInt256.ofNat
      (Artifact.submissionArtifact.instructionPC site.startIndex) := by
    rfl
  have hp1 : q1.pc = UInt256.ofNat
      (Artifact.submissionArtifact.instructionPC (site.startIndex + 1)) := by
    rfl
  have hp2 : q2.pc = UInt256.ofNat
      (Artifact.submissionArtifact.instructionPC (site.startIndex + 2)) := by
    rfl
  have hp3 : q3.pc = UInt256.ofNat
      (Artifact.submissionArtifact.instructionPC (site.startIndex + 3)) := by
    rfl
  have hp4 : q4.pc = UInt256.ofNat
      (Artifact.submissionArtifact.instructionPC (site.startIndex + 4)) := by
    rfl
  have hp5 : q5.pc = UInt256.ofNat
      (Artifact.submissionArtifact.instructionPC (site.startIndex + 5)) := by
    rfl
  have hp6 : q6.pc = UInt256.ofNat
      (Artifact.submissionArtifact.instructionPC (site.startIndex + 6)) := by
    rfl
  have hp7 : q7.pc = UInt256.ofNat
      (Artifact.submissionArtifact.instructionPC (site.startIndex + 7)) := by
    rfl
  have r0 :
      Challenge.EvmProof.Stepper.runLocated
        (⟨site.startIndex, .push site.retW site.ret, h.h0, h.wf0⟩ : Located) q0 =
        some q1 := by
    simpa [q1] using
      (run_wrapper_push site.startIndex site.retW site.ret h.h0 h.wf0 q0 hp0 hc0)
  have r1 :
      Challenge.EvmProof.Stepper.runLocated
        (⟨site.startIndex + 1, .push site.kW site.k, h.h1, h.wf1⟩ : Located) q1 =
        some q2 := by
    simpa [q2] using
      (run_wrapper_push (site.startIndex + 1) site.kW site.k h.h1 h.wf1 q1 hp1 hc1)
  have r2 :
      Challenge.EvmProof.Stepper.runLocated
        (⟨site.startIndex + 2, .push site.rotW site.rotation, h.h2, h.wf2⟩ : Located) q2 =
        some q3 := by
    simpa [q3] using
      (run_wrapper_push (site.startIndex + 2) site.rotW site.rotation h.h2 h.wf2 q2 hp2 hc2)
  have r3 :
      Challenge.EvmProof.Stepper.runLocated
        (⟨site.startIndex + 3, .push site.wiW site.wordIndex, h.h3, h.wf3⟩ : Located) q3 =
        some q4 := by
    simpa [q4] using
      (run_wrapper_push (site.startIndex + 3) site.wiW site.wordIndex h.h3 h.wf3 q3 hp3 hc3)
  have r4 :
      Challenge.EvmProof.Stepper.runLocated
        (⟨site.startIndex + 4, .push site.jW site.j, h.h4, h.wf4⟩ : Located) q4 =
        some q5 := by
    simpa [q5] using
      (run_wrapper_push (site.startIndex + 4) site.jW site.j h.h4 h.wf4 q4 hp4 hc4)
  have r5 :
      Challenge.EvmProof.Stepper.runLocated
        (⟨site.startIndex + 5, .push site.baseW site.base, h.h5, h.wf5⟩ : Located) q5 =
        some q6 := by
    simpa [q6] using
      (run_wrapper_push (site.startIndex + 5) site.baseW site.base h.h5 h.wf5 q5 hp5 hc5)
  have r6 :
      Challenge.EvmProof.Stepper.runLocated
        (⟨site.startIndex + 6, .push ⟨2, by decide⟩ (UInt256.ofNat 0x114),
          h.h6, h.wf6⟩ : Located) q6 =
        some q7 := by
    simpa [q7] using
      (run_wrapper_push (site.startIndex + 6) ⟨2, by decide⟩ (UInt256.ofNat 0x114)
        h.h6 h.wf6 q6 hp6 hc6)
  have hp7Nat : q7.pc.toNat =
      Artifact.submissionArtifact.instructionPC (site.startIndex + 7) := by
    calc
      q7.pc.toNat =
          (UInt256.ofNat
            (Artifact.submissionArtifact.instructionPC (site.startIndex + 7))).toNat := by
        rw [hp7]
      _ = Artifact.submissionArtifact.instructionPC (site.startIndex + 7) % 2 ^ 256 := by
        exact Challenge.EvmProof.Word.word_toNat_ofNat _
      _ = Artifact.submissionArtifact.instructionPC (site.startIndex + 7) :=
        Nat.mod_eq_of_lt (Trace.pcBound (site.startIndex + 7))
  have r7 :
      Challenge.EvmProof.Stepper.runLocated
        (⟨site.startIndex + 7, .op .JUMP, h.h7, h.wf7⟩ : Located) q7 =
        some {q7 with stack := q6.stack, pc := UInt256.ofNat 0x114} := by
    apply run_wrapper_jump (site.startIndex + 7) h.h7 h.wf7 q7
      (UInt256.ofNat 0x114) q6.stack hp7Nat hc7
    · rfl
    · change s.executionEnv.code = submissionBytecode
      exact hcode
    · exact Artifact.submissionArtifact.isValidJumpDest_index 208 (by rfl)
  let q8 : State := {q7 with stack := q6.stack, pc := UInt256.ofNat 0x114}
  let l0 : Located :=
    ⟨site.startIndex, .push site.retW site.ret, h.h0, h.wf0⟩
  let l1 : Located :=
    ⟨site.startIndex + 1, .push site.kW site.k, h.h1, h.wf1⟩
  let l2 : Located :=
    ⟨site.startIndex + 2, .push site.rotW site.rotation, h.h2, h.wf2⟩
  let l3 : Located :=
    ⟨site.startIndex + 3, .push site.wiW site.wordIndex, h.h3, h.wf3⟩
  let l4 : Located :=
    ⟨site.startIndex + 4, .push site.jW site.j, h.h4, h.wf4⟩
  let l5 : Located :=
    ⟨site.startIndex + 5, .push site.baseW site.base, h.h5, h.wf5⟩
  let l6 : Located :=
    ⟨site.startIndex + 6, .push ⟨2, by decide⟩ (UInt256.ofNat 0x114), h.h6, h.wf6⟩
  let l7 : Located :=
    ⟨site.startIndex + 7, .op .JUMP, h.h7, h.wf7⟩
  have b0 :
      Challenge.EvmProof.Stepper.runLocatedBlock [l0] q0 = some q1 := by
    have rr : Challenge.EvmProof.Stepper.runLocated l0 q0 = some q1 := by
      simpa [l0] using r0
    simp only [Challenge.EvmProof.Stepper.runLocatedBlock]
    rw [rr]
  have b1 :
      Challenge.EvmProof.Stepper.runLocatedBlock [l1] q1 = some q2 := by
    have rr : Challenge.EvmProof.Stepper.runLocated l1 q1 = some q2 := by
      simpa [l1] using r1
    simp only [Challenge.EvmProof.Stepper.runLocatedBlock]
    rw [rr]
  have b2 :
      Challenge.EvmProof.Stepper.runLocatedBlock [l2] q2 = some q3 := by
    have rr : Challenge.EvmProof.Stepper.runLocated l2 q2 = some q3 := by
      simpa [l2] using r2
    simp only [Challenge.EvmProof.Stepper.runLocatedBlock]
    rw [rr]
  have b3 :
      Challenge.EvmProof.Stepper.runLocatedBlock [l3] q3 = some q4 := by
    have rr : Challenge.EvmProof.Stepper.runLocated l3 q3 = some q4 := by
      simpa [l3] using r3
    simp only [Challenge.EvmProof.Stepper.runLocatedBlock]
    rw [rr]
  have b4 :
      Challenge.EvmProof.Stepper.runLocatedBlock [l4] q4 = some q5 := by
    have rr : Challenge.EvmProof.Stepper.runLocated l4 q4 = some q5 := by
      simpa [l4] using r4
    simp only [Challenge.EvmProof.Stepper.runLocatedBlock]
    rw [rr]
  have b5 :
      Challenge.EvmProof.Stepper.runLocatedBlock [l5] q5 = some q6 := by
    have rr : Challenge.EvmProof.Stepper.runLocated l5 q5 = some q6 := by
      simpa [l5] using r5
    simp only [Challenge.EvmProof.Stepper.runLocatedBlock]
    rw [rr]
  have b6 :
      Challenge.EvmProof.Stepper.runLocatedBlock [l6] q6 = some q7 := by
    have rr : Challenge.EvmProof.Stepper.runLocated l6 q6 = some q7 := by
      simpa [l6] using r6
    simp only [Challenge.EvmProof.Stepper.runLocatedBlock]
    rw [rr]
  have b7 :
      Challenge.EvmProof.Stepper.runLocatedBlock [l7] q7 = some q8 := by
    have rr : Challenge.EvmProof.Stepper.runLocated l7 q7 = some q8 := by
      simpa [l7, q8] using r7
    simp only [Challenge.EvmProof.Stepper.runLocatedBlock]
    rw [rr]
  have hr1 : q1.halt = .Running := by
    simpa [q1, q0, wrapperEntryAt] using hrun
  have hr2 : q2.halt = .Running := by
    simpa [q2, q1, q0, wrapperEntryAt] using hrun
  have hr3 : q3.halt = .Running := by
    simpa [q3, q2, q1, q0, wrapperEntryAt] using hrun
  have hr4 : q4.halt = .Running := by
    simpa [q4, q3, q2, q1, q0, wrapperEntryAt] using hrun
  have hr5 : q5.halt = .Running := by
    simpa [q5, q4, q3, q2, q1, q0, wrapperEntryAt] using hrun
  have hr6 : q6.halt = .Running := by
    simpa [q6, q5, q4, q3, q2, q1, q0, wrapperEntryAt] using hrun
  have hr7 : q7.halt = .Running := by
    simpa [q7, q6, q5, q4, q3, q2, q1, q0, wrapperEntryAt] using hrun
  have h01 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [l0] [l1] q0 q1 q2 b0 hr1 b1
  have h012 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    ([l0] ++ [l1]) [l2] q0 q2 q3 h01 hr2 b2
  have h0123 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    ([l0] ++ [l1] ++ [l2]) [l3] q0 q3 q4 h012 hr3 b3
  have h01234 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    ([l0] ++ [l1] ++ [l2] ++ [l3]) [l4] q0 q4 q5 h0123 hr4 b4
  have h012345 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    ([l0] ++ [l1] ++ [l2] ++ [l3] ++ [l4]) [l5] q0 q5 q6 h01234 hr5 b5
  have h0123456 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    ([l0] ++ [l1] ++ [l2] ++ [l3] ++ [l4] ++ [l5]) [l6]
      q0 q6 q7 h012345 hr6 b6
  have h01234567 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    ([l0] ++ [l1] ++ [l2] ++ [l3] ++ [l4] ++ [l5] ++ [l6]) [l7]
      q0 q7 q8 h0123456 hr7 b7
  have hblock :
      Challenge.EvmProof.Stepper.runLocatedBlock (wrapperSitePath site h) q0 = some q8 := by
    change Challenge.EvmProof.Stepper.runLocatedBlock
      [l0, l1, l2, l3, l4, l5, l6, l7] q0 = some q8
    exact h01234567
  have hj : site.j = UInt256.ofNat site.j.toNat :=
    Challenge.EvmProof.Word.word_eq_ofNat_toNat site.j
  have hfinal :
      q8 = wrapperRoundEntryAt site s messageOffset outerReturn rest := by
    unfold wrapperRoundEntryAt RoundTrace.roundEntry
    dsimp [q8, q7, q6, q5, q4, q3, q2, q1, q0, wrapperEntryAt]
    rw [hj]
    congr 1
    congr 1
    congr 1
    exact Challenge.EvmProof.Word.word_eq_ofNat_toNat
      (UInt256.ofNat site.j.toNat)
  simpa [q0] using hblock.trans (congrArg some hfinal)

/-- GasSteps lift for one generic immediate wrapper. -/
def gasSteps_wrapper_site (site : WrapperSite)
    (h : WrapperSiteCertificate site)
    (s : State) (messageOffset outerReturn : UInt256) (rest : List UInt256)
    (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (wrapperEntryAt site s messageOffset outerReturn rest)
      (wrapperRoundEntryAt site s messageOffset outerReturn rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka (wrapperSitePath site h)
  · simpa [wrapperEntryAt, Artifact.submissionArtifact] using hcode
  · simpa [wrapperEntryAt, State.fork] using hfork
  · exact run_wrapper_site site h s messageOffset outerReturn rest hstack hcode hrun
  · simpa [wrapperEntryAt] using hrun
  · simpa [wrapperEntryAt] using hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateWrapper
