import Challenge.Ripemd160.Submission.Local20261028.FirstSpec
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.FirstMessageSpec
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedScheduleMemory GeneralMessageReady

theorem entry_lower (m : ByteArray) (i : Nat) (hi : i < 8) :
    (entryWords (FirstInitial.memory m) i).toNat =
      (PairedScheduleData.extractedWord m 1056 i).toNat := by
  have he := DecodedMemory.entry_eq_extracted m 1056 i (by omega)
  rw [DecodedMemory.entry_eq_pool _ _ _ _ (by omega),
    StaggerScratch.poolWord_eq _ _ _ _ (by omega), if_pos hi] at he
  change (entryWords (DecodedMemory.scratch m _ FirstInitial.highWord) i).toNat = _
  rw [DecodedMemory.entry_eq_pool _ _ _ _ (by omega),
    StaggerScratch.poolWord_eq _ _ _ _ (by omega), if_pos hi]
  exact he

theorem entry_upper (m : ByteArray) (i : Nat) (hi : 8 ≤ i) (hj : i < 16) :
    entryWords (FirstInitial.memory m) i = UInt32.ofNat (FirstSpec.highScalar i) := by
  apply UInt32.toNat_inj.mp
  change (entryWords (DecodedMemory.scratch m _ FirstInitial.highWord) i).toNat = _
  rw [DecodedMemory.entry_eq_pool _ _ _ _ hj, StaggerScratch.poolWord_eq _ _ _ _ hj,
    if_neg (by omega : ¬i < 8)]
  interval_cases i <;> rfl

theorem entry_spec (input : ByteArray) (h32 : input.size = 32) (i : Nat) (hi : i < 16) :
    entryWords (FirstInitial.memory (FirstSpec.copiedMemory input)) i =
      (CompressionCorrect.schedule (Padding.paddedMessage input) 0)[i]! := by
  rw [← FirstSpec.scalars_schedule input h32 i hi]
  by_cases hl : i < 8
  · apply UInt32.toNat_inj.mp
    rw [FirstSpec.scalars, if_pos hl, entry_lower _ _ hl, UInt32.toNat_ofNat']
    have he := FirstSpec.extracted_readLE32 (FirstSpec.copiedMemory input) i hi
    rw [he, Word.ofUInt32_toNat, Nat.mod_eq_of_lt (UInt32.toNat_lt _)]
  · rw [FirstSpec.scalars, if_neg hl]
    exact entry_upper _ i (by omega) hi

theorem copied_zero (input : ByteArray) (a : Nat) (ha : a < 1056) :
    (FirstSpec.copiedMemory input)[a]?.getD 0 = 0 := by
  simp [FirstSpec.copiedMemory, MachineState.writeBytes_getElem?_getD,
    show ¬1056 ≤ a by omega]

theorem ready_spec (s : State) (input : ByteArray) (h32 : input.size = 32)
    (hm : s.memory = writeWord (FirstSpec.copiedMemory input) 162 FirstInitial.highWord) :
    CoreMessage.Ready (FirstCore.prepared (FirstRead.result s)).memory
      (fun i => (CompressionCorrect.schedule (Padding.paddedMessage input) 0)[i]!) := by
  have hr := FirstReadGas.ready s (FirstSpec.copiedMemory input) hm (copied_zero input)
  apply NormalMessage.ready_congr _ _ _ hr
  intro i hi
  rw [FirstRead.memory_eq s _ hm]
  exact entry_spec input h32 i hi

theorem blockCount32 (input : ByteArray) (h32 : input.size = 32) :
    DriverTrace.blockCount input = 1 := by
  simp [DriverTrace.blockCount, Padding.paddedLength, h32]

theorem hash_spec (s : State) (input : ByteArray) (h32 : input.size = 32)
    (hm : s.memory = writeWord (FirstSpec.copiedMemory input) 162 FirstInitial.highWord) :
    CompressionCorrect.hashArray
      (CoreFunctional.result (FirstCore.prepared (FirstRead.result s)).memory FirstCore.initialHash) =
      CompressionSeamBridge.hashAfter input (DriverTrace.blockCount input) := by
  rw [CoreFunctional.result_compressBlock _ (Padding.paddedMessage input) 0
    FirstCore.initialHash (ready_spec s input h32 hm)]
  rw [blockCount32 input h32, show (1 : Nat) = 0+1 from rfl, StackRunBridge.hashAfter_succ]
  rfl
#print axioms entry_spec
#print axioms ready_spec
#print axioms hash_spec
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.FirstMessageSpec
