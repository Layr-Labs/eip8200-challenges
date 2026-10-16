import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFinish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduledTailFrame
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentOutput
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-!
# The digest epilogue entered from the block exit

The block exit at 4537 jumps to 4733 with the resident tail unfinished: the `h4`, `h1` and `h0`
words are masked in their slots, the `h3` sum is on top and the two `h2` addends are below it.
The epilogue stores the five words descending at 16, 12, 8, 4 and 0. The `h3` and `h2` sums are
stored unmasked: of their 32-byte stores only the low four bytes survive the lower stores that
follow, so the memory is exactly the masked image of the old epilogue (`StaggerPersistentOutput.prepared`).
The byte swap then reads the masks from slots 16 and 15.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PreSerialize
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate

/-! ## Memory: only the low 32 bits of the two unmasked sums survive -/

private theorem byte_low (x : Nat) (w : UInt32) (hw : w.toNat = x % 2 ^ 32) (k : Nat) (hk : 28 ≤ k) :
    (Data.Bytes.natToBytesPadded x 32)[k]?.getD 0 =
      (Data.Bytes.natToBytesPadded w.toNat 32)[k]?.getD 0 := by
  by_cases hk32 : k < 32
  · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hk32,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hk32, hw]
    congr 1
    interval_cases k <;> norm_num <;> omega
  · rw [getElem?_neg _ k (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
      getElem?_neg _ k (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)]

theorem stores_eq (m : ByteArray) (w : Compression.HashState) (X Y : UInt256)
    (hX : Word.toUInt32 X = w.h3) (hY : Word.toUInt32 Y = w.h2) :
    MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes
      (MachineState.writeBytes (MachineState.writeBytes m
        (Data.Bytes.natToBytesPadded w.h4.toNat 32) 16)
        (Data.Bytes.natToBytesPadded X.toNat 32) 12)
        (Data.Bytes.natToBytesPadded Y.toNat 32) 8)
        (Data.Bytes.natToBytesPadded w.h1.toNat 32) 4)
        (Data.Bytes.natToBytesPadded w.h0.toNat 32) 0 =
      MemoryPackedOutput.memory m w := by
  have hx : w.h3.toNat = X.toNat % 2 ^ 32 := by rw [← hX, Word.toUInt32_toNat]
  have hy : w.h2.toNat = Y.toNat % 2 ^ 32 := by rw [← hY, Word.toUInt32_toNat]
  apply ByteArray.ext_getElem
  · simp only [MemoryPackedOutput.memory, MemoryPackedOutput.store, MachineState.writeBytes_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro i hiA hiB
    rw [← Memory.getD0_eq_getElem _ _ hiA, ← Memory.getD0_eq_getElem _ _ hiB]
    simp only [MemoryPackedOutput.memory, MemoryPackedOutput.store,
      MachineState.writeBytes_getElem?_getD, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    split_ifs <;> first
      | rfl
      | omega
      | exact byte_low _ _ hx _ (by omega)
      | exact byte_low _ _ hy _ (by omega)

/-! ## The store sequence -/

/-- `DUP10 PUSH1 16 MSTORE PUSH1 12 MSTORE ADD DUP9 ADD PUSH1 8 MSTORE DUP10 PUSH1 4 MSTORE
DUP11 PUSH0 MSTORE PUSH1 16 MLOAD` (4734..4756). -/
def storeCode : List Instr :=
  [.op (.Dup ⟨9, by decide⟩), .push ⟨1, by decide⟩ (UInt256.ofNat 16), .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 12), .op .MSTORE,
   .op .ADD, .op (.Dup ⟨8, by decide⟩), .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 8), .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩), .push ⟨1, by decide⟩ (UInt256.ofNat 4), .op .MSTORE,
   .op (.Dup ⟨10, by decide⟩), .push ⟨0, by decide⟩ (UInt256.ofNat 0), .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 16), .op .MLOAD]

def put (s : State) (address : Nat) (v : UInt256) : State :=
  {s with memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v.toNat 32) address, activeWords := s.activeWordsAfterUInt256 address 32}

def putAll (s : State) (a x y b c : UInt256) : State :=
  let t := put (put (put (put (put s 16 a) 12 x) 8 y) 4 b) 0 c
  {t with activeWords := t.activeWordsAfterUInt256 16 32}

theorem run_store (s : State) (pc : UInt256)
    (x1 x2 x3 a4 a5 a6 a7 a8 a9 m0 h3 h2 m2 m1 off lim : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) :
    runInstrSeq storeCode {s with pc := pc, stack := [x1, x2, x3, a4, a5, a6, a7, a8, a9, m0, h3, h2, m2, m1, off, lim] ++ rho} =
      some {putAll s m0 x1 (UInt256.add h3 (UInt256.add x2 x3)) m2 m1 with pc := pcAfter pc storeCode, stack := MachineState.readWord (putAll s m0 x1 (UInt256.add h3 (UInt256.add x2 x3)) m2 m1).memory 16 :: [a4, a5, a6, a7, a8, a9, m0, h3, h2, m2, m1, off, lim] ++ rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [storeCode, putAll, put,
    runInstrSeq, DataStepper.runInstr, UInt256.succ, pcAfter, Instr.size,
    hrun, hcap, Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, State.activeWordsAfterUInt256]
  all_goals repeat first | apply And.intro | rfl

theorem putAll_prepared (s : State) (w : Compression.HashState) (X Y : UInt256)
    (hX : Word.toUInt32 X = w.h3) (hY : Word.toUInt32 Y = w.h2) :
    putAll s (Word.ofUInt32 w.h4) X Y (Word.ofUInt32 w.h1) (Word.ofUInt32 w.h0) =
      StaggerPersistentOutput.prepared s w := by
  have hm := stores_eq s.memory w X Y hX hY
  simp only [putAll, put, StaggerPersistentOutput.prepared, StaggerPersistentOutput.stored,
    MemoryPackedOutput.store, Word.ofUInt32_toNat, State.activeWordsAfterUInt256]
  simp only [MemoryPackedOutput.memory, MemoryPackedOutput.store] at hm
  rw [hm]

/-! ## The byte swap with the masks in slots 16 and 15 -/

def stagesCode : List Instr :=
  [.op (.Dup ⟨15, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .AND,
   .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), .op .MUL, .op .ADD,
   .op (.Dup ⟨14, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 65535), .op .MUL, .op .ADD]

theorem run_stages (s : State) (pc value r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 m8 m16 : UInt256)
    (rest : List UInt256) (hstack : rest.length < 990) (hrun : s.halt = .Running) :
    runInstrSeq stagesCode {s with pc := pc, stack := value :: [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, m8, m16] ++ rest} =
      some {s with pc := pcAfter pc stagesCode, stack := StaggerPersistentFinish.finish m8 m16 value :: [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, m8, m16] ++ rest} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rest.length + n < 1024 := by omega
  simp (discharger := omega) [stagesCode, StaggerPersistentFinish.finish,
    StaggerPersistentFinish.stage16, StaggerPersistentFinish.stage8, runInstrSeq, DataStepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, hrun, hcap, Nat.add_assoc, List.getElem?_cons_zero,
    List.exchange, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [RawExpressionAC.land_comm]
  all_goals repeat first | apply And.intro | rfl


/-! ## The exit stack of a block -/

section Exit
open ScheduledTailFrame

theorem run_storeQ (s : State) (pc : UInt256) (h : Compression.HashState)
    (q : ScheduledTailRaw.Input) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) :
    runInstrSeq storeCode {s with pc := pc, stack := ScheduledTailRaw.stack3a (bind h q) rho} =
      some {StaggerPersistentOutput.prepared s (combine h q) with pc := pcAfter pc storeCode, stack := StaggerPersistentOutput.packedHash (combine h q) :: (ScheduledTailRaw.stack3a (bind h q) rho).drop 3} := by
  have h1 := run_store s pc
    (UInt256.add (UInt256.add (bind h q).h4 (bind h q).la) (UInt256.shiftRight (bind h q).rb (UInt256.ofNat 144)))
    (bind h q).le (UInt256.shiftRight (bind h q).ra (UInt256.ofNat 144))
    (bind h q).factor (bind h q).lower (bind h q).cache140 (bind h q).cache350 (bind h q).cache310
    (bind h q).cache190
    (UInt256.land (bind h q).lower (UInt256.add (bind h q).h0 (UInt256.add (bind h q).lb
      (UInt256.shiftRight (bind h q).rc (UInt256.ofNat 144)))))
    (bind h q).h3 (bind h q).h2
    (UInt256.land (bind h q).lower (UInt256.add (bind h q).h2 (UInt256.add
      (UInt256.shiftRight (UInt256.mul (bind h q).ld (bind h q).factor) (UInt256.ofNat 23))
      (UInt256.shiftRight (bind h q).re (UInt256.ofNat 144)))))
    (UInt256.land (bind h q).lower (UInt256.add (bind h q).h1 (UInt256.add
      (UInt256.shiftRight (bind h q).rd (UInt256.ofNat 144)) (bind h q).lc)))
    (bind h q).off (bind h q).limit rho hstack hrun
  have hread := MemoryPackedOutput.readWord_eq s.memory (combine h q)
  have hpack : PackedOutputMath.pack5 (combine h q).h0 (combine h q).h1 (combine h q).h2
      (combine h q).h3 (combine h q).h4 = StaggerPersistentOutput.packedHash (combine h q) := by
    simp only [PackedOutputMath.pack5, PackedOutputMath.append32, StaggerPersistentOutput.packedHash,
      Word.lor_comm]
  rw [hpack] at hread
  have hm : (StaggerPersistentOutput.prepared s (combine h q)).memory =
      MemoryPackedOutput.memory s.memory (combine h q) := rfl
  rw [← hread, ← hm,
    ← putAll_prepared s (combine h q) _ _ (exit_h3 h q) (exit_h2 h q), ← exit_h4, ← exit_h1, ← exit_h0]
  exact h1

end Exit

theorem store_slice :
    (Artifact.submissionArtifact.instructions.drop 3485).take storeCode.length = storeCode := by rfl
def storeSite : GenericRoundSite Artifact.submissionArtifact .Osaka storeCode :=
  StackSiteBuilder.ofSlice storeCode 3485 store_slice
    (by change 3485 + storeCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := storeCode) (by decide)) (by decide)
theorem store_pc : storeSite.startPC = UInt256.ofNat 4734 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3485) = UInt256.ofNat 4734
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem store_advances : ∀ instruction ∈ storeCode, DenseScheduleLift.Advances instruction :=
  Table80SiteCommon.coreAdvancesAll_sound storeCode (by decide)

theorem stages_slice :
    (Artifact.submissionArtifact.instructions.drop 3503).take stagesCode.length = stagesCode := by rfl
def stagesSite : GenericRoundSite Artifact.submissionArtifact .Osaka stagesCode :=
  StackSiteBuilder.ofSlice stagesCode 3503 stages_slice
    (by change 3503 + stagesCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := stagesCode) (by decide)) (by decide)
theorem stages_pc : stagesSite.startPC = UInt256.ofNat 4757 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3503) = UInt256.ofNat 4757
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem stages_advances : ∀ instruction ∈ stagesCode, DenseScheduleLift.Advances instruction :=
  Table80SiteCommon.coreAdvancesAll_sound stagesCode (by decide)

/-- The epilogue's final state for the exit stack of hash `h` and lanes `q`. -/
def resultQ (s : State) (h : Compression.HashState) (q : ScheduledTailRaw.Input)
    (rho : List UInt256) : State :=
  StaggerPersistentFinish.terminalResult (StaggerPersistentOutput.prepared s (ScheduledTailFrame.combine h q))
    (UInt256.ofNat 4775)
    (StaggerPersistentFinish.finish DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16
      (StaggerPersistentOutput.packedHash (ScheduledTailFrame.combine h q)))
    ((ScheduledTailRaw.stack3a (ScheduledTailFrame.bind h q)
      (DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho)).drop 3)

theorem resultQ_hReturn (s : State) (h : Compression.HashState) (q : ScheduledTailRaw.Input)
    (rho : List UInt256) :
    (resultQ s h q rho).hReturn = Data.Bytes.natToBytesPadded
      (DenseScheduleTemplate.packedWord (StaggerPersistentOutput.packedHash (ScheduledTailFrame.combine h q))).toNat 32 :=
  StaggerPersistentFinish.hReturn_eq s _ _ _

def gasStepsQ (s : State) (h : Compression.HashState) (q : ScheduledTailRaw.Input)
    (rho : List UInt256) (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4733, stack := ScheduledTailRaw.stack3a (ScheduledTailFrame.bind h q) (DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho)}
      (resultQ s h q rho) := by
  let L := DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho
  have hL : L.length ≤ 1000 := by simp only [L, List.length_cons]; omega
  have ge := StaggerPersistentOutput.gasSteps_entry s (ScheduledTailRaw.stack3a (ScheduledTailFrame.bind h q) L)
    (by simp only [ScheduledTailRaw.stack3a, List.length_append, List.length_cons, List.length_nil]; omega)
    hrun hcode hfork hnp
  have g1 : GasSteps {s with pc := UInt256.ofNat 4734, stack := ScheduledTailRaw.stack3a (ScheduledTailFrame.bind h q) L}
      {StaggerPersistentOutput.prepared s (ScheduledTailFrame.combine h q) with pc := UInt256.ofNat 4757, stack := StaggerPersistentOutput.packedHash (ScheduledTailFrame.combine h q) :: (ScheduledTailRaw.stack3a (ScheduledTailFrame.bind h q) L).drop 3} := by
    apply DenseScheduleLift.gasSteps_of_raw storeSite {s with pc := UInt256.ofNat 4734, stack := ScheduledTailRaw.stack3a (ScheduledTailFrame.bind h q) L} _ hcode hfork hrun hnp store_pc.symm store_advances
    have hr := run_storeQ s (UInt256.ofNat 4734) h q L hL hrun
    have he : pcAfter (UInt256.ofNat 4734) storeCode = UInt256.ofNat 4757 := by decide
    rw [he] at hr
    exact hr
  let t := StaggerPersistentOutput.prepared s (ScheduledTailFrame.combine h q)
  have htr : t.halt = .Running := hrun
  have htc : t.executionEnv.code = Artifact.submissionArtifact.code := hcode
  have htf : t.fork = .Osaka := hfork
  have htn : Precompile.isPrecompileWithConfig t.executionEnv.precompileConfig
      t.executionEnv.fork t.executionEnv.codeAddr = false := hnp
  let Q := ScheduledTailFrame.bind h q
  have g2 : GasSteps {t with pc := UInt256.ofNat 4757, stack := StaggerPersistentOutput.packedHash (ScheduledTailFrame.combine h q) :: (ScheduledTailRaw.stack3a Q L).drop 3}
      {t with pc := UInt256.ofNat 4775, stack := StaggerPersistentFinish.finish DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16 (StaggerPersistentOutput.packedHash (ScheduledTailFrame.combine h q)) :: (ScheduledTailRaw.stack3a Q L).drop 3} := by
    apply DenseScheduleLift.gasSteps_of_raw stagesSite {t with pc := UInt256.ofNat 4757, stack := StaggerPersistentOutput.packedHash (ScheduledTailFrame.combine h q) :: (ScheduledTailRaw.stack3a Q L).drop 3} _ htc htf htr htn stages_pc.symm stages_advances
    have hr := run_stages t (UInt256.ofNat 4757) (StaggerPersistentOutput.packedHash (ScheduledTailFrame.combine h q))
      Q.factor Q.lower Q.cache140 Q.cache350 Q.cache310 Q.cache190
      (UInt256.land Q.lower (UInt256.add Q.h0 (UInt256.add Q.lb (UInt256.shiftRight Q.rc (UInt256.ofNat 144)))))
      Q.h3 Q.h2
      (UInt256.land Q.lower (UInt256.add Q.h2 (UInt256.add (UInt256.shiftRight (UInt256.mul Q.ld Q.factor) (UInt256.ofNat 23)) (UInt256.shiftRight Q.re (UInt256.ofNat 144)))))
      (UInt256.land Q.lower (UInt256.add Q.h1 (UInt256.add (UInt256.shiftRight Q.rd (UInt256.ofNat 144)) Q.lc)))
      Q.off Q.limit DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16 rho (by omega) htr
    have he : pcAfter (UInt256.ofNat 4757) stagesCode = UInt256.ofNat 4775 := by decide
    rw [he] at hr
    exact hr
  have g3 := StaggerPersistentFinish.gasSteps_terminal t
    (StaggerPersistentFinish.finish DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16 (StaggerPersistentOutput.packedHash (ScheduledTailFrame.combine h q)))
    ((ScheduledTailRaw.stack3a Q L).drop 3)
    (by simp only [ScheduledTailRaw.stack3a, List.length_drop, List.length_append, List.length_cons, List.length_nil, L]; omega)
    htc htf htr htn
  exact ge.trans (g1.trans (g2.trans g3))

#print axioms run_storeQ
#print axioms gasStepsQ
#print axioms resultQ_hReturn
#print axioms stores_eq
#print axioms run_store
#print axioms putAll_prepared
#print axioms run_stages
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PreSerialize
