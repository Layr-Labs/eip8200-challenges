import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighModel
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerTable PersistentStaggerIteration ColdHighPaddingMemory StaggerPersistentFrame
noncomputable opaque gasSteps_normal (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0<input.size) (i : Nat)
    (hi : i<DriverTrace.blockCount input) :
    GasSteps {paddedState input i with pc:=UInt256.ofNat 480,stack:=frame (hashes input i) (DriverTrace.blockOffsetWord i) (Padding.paddedWord input) maskRho}
      {tableState input i with pc:=UInt256.ofNat 884,stack:=frame (hashes input i) (DriverTrace.blockOffsetWord i) (Padding.paddedWord input) maskRho} := by
  let h:=hashes input i
  let off:=DriverTrace.blockOffsetWord i
  have hc : (paddedState input i).executionEnv.code=Artifact.submissionArtifact.code := states_code input i
  have hf : (paddedState input i).fork=.Osaka := states_fork input i
  have hr : (paddedState input i).halt=.Running := states_halt input i
  have hnp:=states_noPrecompile input i
  have hb:=messagePointer_bound input hfit i hi
  have hq0 : off+UInt256.ofNat 1120=UInt256.ofNat (messagePointer i) := by
    change UInt256.ofNat (DriverTrace.blockOffset i)+UInt256.ofNat 1120=_
    rw [Word.ofNat_add_ofNat (by unfold messagePointer Padding.messageOffset at hb;omega)]
    unfold messagePointer Padding.messageOffset
    congr 1
    omega
  have hq1 : off+UInt256.ofNat 1152=UInt256.ofNat (messagePointer i+32) := by
    change UInt256.ofNat (DriverTrace.blockOffset i)+UInt256.ofNat 1152=_
    rw [Word.ofNat_add_ofNat (by unfold messagePointer Padding.messageOffset at hb;omega)]
    unfold messagePointer Padding.messageOffset
    congr 1
    omega
  have gn:=ColdOrdinarySites.gasSteps_normal (paddedState input i) Paired144WordRound.factorPlusWord
    (Paired144WordRound.fusedModulusWord 5 7) (Paired144WordRound.fusedModulusWord 8 5)
    (Paired144WordRound.fusedCoefficientWord 0 3) (Paired144WordRound.fusedCoefficientWord 0 2)
    (Word.ofUInt32 h.h4) (Word.ofUInt32 h.h3) (Word.ofUInt32 h.h2) (Word.ofUInt32 h.h1)
    (Word.ofUInt32 h.h0) off (Padding.paddedWord input) [] (messagePointer i) (by decide) hr
    (messagePointer_lower i) hb hq1 hq0
    (by change (MachineState.readWord (finalMemory input i) 0).toNat % 2 ^ 144<2^32
        rw [finalMemory_lowClear input hfit hpositive i (by omega)];decide)
    (finalMemory_gapClear input hfit hpositive i (by omega)) hc hf hnp
  exact gn.cast
    (by simp only [h,off,frame,maskRho,PersistentMaskEndian.stk,Pair13Endian.stk,List.cons_append,List.nil_append])
    (by simp only [h,off,tableState,ColdHighReady.tableMemory,paddedState,frame,maskRho,
        PersistentMaskEndian.stk,Pair13Endian.stk,List.cons_append,List.nil_append])

#print axioms gasSteps_normal

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighTrace
