import Challenge.Ripemd160.Submission.Proofs.Bytecode.DeferredNormalEndian
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DeferredNormalInterleaved
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedMask32Cache PairedScheduleMemory
open PairTableActive Table80ScratchZero DeferredNormalEndian

private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl

def firstLoad : List Instr := [.op .MLOAD]
def secondLoad : List Instr :=
  [ .op (.Dup ⟨13, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 1116),
    .op .ADD,
    .op .MLOAD ]
def template : List Instr :=
  ((((((firstLoad ++ DeferredNormalEndian.lowerReverseFirst) ++ lowerStore) ++ secondLoad) ++ DeferredNormalEndian.finalReverse) ++ upperStore) ++ DeferredNormalEndian.finalCleanup)

private theorem run_firstLoad (s : State) (pc p : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 1000) (hrun : s.halt = .Running) :
    runInstrSeq firstLoad {s with pc := pc, stack := p :: rest} =
      some {s with
        pc := pcAfter pc firstLoad
        stack := MachineState.readWord s.memory p.toNat :: rest
        activeWords := activeAfterWord s.activeWords p} := by
  have hc : rest.length + 1 < 1024 := by omega
  simp [hc, firstLoad, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, hrun, activeAfterWord, State.activeWordsAfterUInt256]
  rfl

private theorem run_secondLoad (s : State) (pc ret off : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 996) (hrun : s.halt = .Running)
    (hoff : rest[9]? = some off) :
    runInstrSeq secondLoad {s with pc := pc, stack := mask8 :: mask16 :: ret :: maskWord :: rest} =
      some {s with
        pc := pcAfter pc secondLoad
        stack := MachineState.readWord s.memory (off + UInt256.ofNat 1116).toNat ::
          mask8 :: mask16 :: ret :: maskWord :: rest
        activeWords := activeAfterWord s.activeWords (off + UInt256.ofNat 1116)} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rest.length + n < 1024 := by omega
  simp [secondLoad, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ,
    Instr.size, hrun, hcap, Nat.add_assoc, activeAfterWord, State.activeWordsAfterUInt256,
    List.getElem?_cons_succ, List.getElem?_cons_zero, hoff, Word.literal_eq_ofNat]
  all_goals simp only [neutral_hadd, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

private theorem first_active_ge34 (s : State) (p : Nat)
    (hp : 1056 ≤ p) (hbound : p + 64 < 2 ^ 256) :
    34 ≤ (activeAfterWord s.activeWords (UInt256.ofNat p)).toNat := by
  have hptr : (UInt256.ofNat p).toNat = p := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hb : MachineState.activeWordsAfter s.activeWords.toNat p 32 < 2 ^ 256 := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
    exact Nat.max_lt.mpr ⟨s.activeWords.val.isLt, by omega⟩
  unfold activeAfterWord
  rw [hptr, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hb]
  simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
  apply Nat.le_trans ?_ (Nat.le_max_right _ _)
  omega

private theorem scratch_comm (memory : ByteArray) (low high : UInt256) :
    writeWord (writeWord memory 28 low) 60 high =
      Table80ScratchZero.scratchMemory memory low high := by
  change writeWord (writeWord memory 28 low) 60 high = writeWord (writeWord memory 60 high) 28 low
  apply ByteArray.ext_getElem
  · simp only [PairedScheduleMemory.writeWord_size]; omega
  · intro i hi hj
    rw [← Memory.getD0_eq_getElem _ _ hi, ← Memory.getD0_eq_getElem _ _ hj]
    simp only [writeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    by_cases ha : 28 ≤ i ∧ i < 28 + 32
    · have hb : ¬ (60 ≤ i ∧ i < 60 + 32) := by omega
      simp only [if_pos ha, if_neg hb]
    · by_cases hb : 60 ≤ i ∧ i < 60 + 32
      · simp only [if_pos hb, if_neg ha]
      · simp only [if_neg ha, if_neg hb]

theorem run_template (s : State) (pc ret : UInt256) (p : Nat) (rest : List UInt256)
    (hstack : rest.length ≤ 896) (hrun : s.halt = .Running)
    (hp : 1056 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hoff : rest[9]? = some (UInt256.ofNat (p - 1056))) :
    runInstrSeq template {s with pc := pc, stack := UInt256.ofNat p :: mask8 :: mask16 :: ret :: maskWord :: rest} =
      some {s with
        pc := pcAfter pc template
        stack := maskWord :: ret :: maskWord :: rest
        memory := Table80ScratchZero.scratchMemory s.memory
          (PairedScheduleData.reversedWord (MachineState.readWord s.memory p))
          (PairedScheduleData.reversedWord (MachineState.readWord s.memory (p + 32)))
        activeWords := loadedActiveWords s (UInt256.ofNat p)} := by
  let lo := PairedScheduleData.reversedWord (MachineState.readWord s.memory p)
  let hi := PairedScheduleData.reversedWord (MachineState.readWord s.memory (p + 32))
  let a0 := activeAfterWord s.activeWords (UInt256.ofNat p)
  let a1 := loadedActiveWords s (UInt256.ofNat p)
  let s0 : State := {s with activeWords := a0}
  let s1 : State := {s0 with memory := writeWord s.memory 28 lo}
  let s2 : State := {s1 with activeWords := a1}
  let s3 : State := {s2 with memory := writeWord s1.memory 60 hi}
  have hptr : (UInt256.ofNat p).toNat = p := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have haddr : UInt256.ofNat (p - 1056) + UInt256.ofNat 1116 = UInt256.ofNat p + UInt256.ofNat 32 := by
    rw [Word.ofNat_add_ofNat (by omega), Word.ofNat_add_ofNat (by omega)]
    congr 1; omega
  have hread : MachineState.readWord s1.memory (p + 32) = MachineState.readWord s.memory (p + 32) := by
    apply Memory.readWord_writeBytes_disjoint
    simp only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    exact Or.inr (by omega)
  have ha0 : 34 ≤ a0.toNat := first_active_ge34 s p hp hbound
  have ha1 : 34 ≤ a1.toNat := by
    exact Nat.le_trans (by decide) (Stagger144Active.loaded_active_ge35 s p hp hbound)
  have h1 := run_firstLoad s pc (UInt256.ofNat p) (mask8 :: mask16 :: ret :: maskWord :: rest) (by simp; omega) hrun
  rw [hptr] at h1
  have h2 := run_lowerFirst s0 (pcAfter pc firstLoad) (MachineState.readWord s.memory p) ret rest (by omega) hrun
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  have h3 := PairedSchedulePrimitives.run_storeTemplate s0
    (pcAfter (pcAfter pc firstLoad) DeferredNormalEndian.lowerReverseFirst) lo 28
    (mask8 :: mask16 :: ret :: maskWord :: rest) (by simp; omega) (by decide) hrun
  rw [word_active_preserved _ _ ha0 (by decide)] at h3
  change runInstrSeq lowerStore _ = some _ at h3
  have h123 := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  have h4 := run_secondLoad s1
    (pcAfter (pcAfter (pcAfter pc firstLoad) DeferredNormalEndian.lowerReverseFirst) lowerStore)
    ret (UInt256.ofNat (p - 1056)) rest (by omega) hrun hoff
  rw [haddr, PairedScheduleContract.pointer_add32_toNat p hbound, hread] at h4
  have h1234 := DenseScheduleTrace.runInstrSeq_append_running h123 (by exact hrun) h4
  have h5 := run_final s2
    (pcAfter (pcAfter (pcAfter (pcAfter pc firstLoad) DeferredNormalEndian.lowerReverseFirst) lowerStore) secondLoad)
    (MachineState.readWord s.memory (p + 32)) ret rest (by omega) hrun
  have h12345 := DenseScheduleTrace.runInstrSeq_append_running h1234 (by exact hrun) h5
  have h6 := PairedSchedulePrimitives.run_storeTemplate s2
    (pcAfter (pcAfter (pcAfter (pcAfter (pcAfter pc firstLoad) DeferredNormalEndian.lowerReverseFirst) lowerStore) secondLoad) DeferredNormalEndian.finalReverse)
    hi 60 (ret :: maskWord :: rest) (by simp; omega) (by decide) hrun
  rw [word_active_preserved _ _ ha1 (by decide)] at h6
  change runInstrSeq upperStore _ = some _ at h6
  have h123456 := DenseScheduleTrace.runInstrSeq_append_running h12345 (by exact hrun) h6
  have h7 := run_finalCleanup s3
    (pcAfter (pcAfter (pcAfter (pcAfter (pcAfter (pcAfter pc firstLoad) DeferredNormalEndian.lowerReverseFirst) lowerStore) secondLoad) DeferredNormalEndian.finalReverse) upperStore)
    ret rest (by omega) hrun
  have h := DenseScheduleTrace.runInstrSeq_append_running h123456 (by exact hrun) h7
  simpa only [template, DenseScheduleTrace.pcAfter_append, s3, s2, s1, s0, lo, hi, a1, scratch_comm] using h
#print axioms run_template
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DeferredNormalInterleaved
