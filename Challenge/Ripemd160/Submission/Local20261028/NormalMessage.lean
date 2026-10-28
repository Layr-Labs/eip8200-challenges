import Challenge.Ripemd160.Submission.Local20261028.NormalPrepare
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.NormalMessage
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
theorem ready_congr (m : ByteArray) (x y : Nat → UInt32) (hm : CoreMessage.Ready m x)
    (hxy : ∀ i, i < 16 → x i = y i) : CoreMessage.Ready m y := by
  constructor
  · intro i hi
    obtain ⟨hpos,hslot,hl,hr⟩ := StaggerTableLayout.layout_valid ⟨i,hi⟩
    have hlb : Crypto.Ripemd160.r[i]! < 16 := hl ▸ StaggerTableLayout.slots_lt _ hslot
    have hrb : Crypto.Ripemd160.rP[i+3]! < 16 := hr ▸ StaggerTableLayout.slots_lt _ (by omega)
    have h := hm.paired i hi
    simp only [StaggerAlgorithm.MessageWord, StaggerAlgorithm.LegacyMessageWord] at h ⊢
    rw [← hxy _ hlb, ← hxy _ hrb]
    exact h
  · intro j hj
    rw [hm.scalar j hj, hxy _ (StaggerTableLayout.slots_lt j hj)]
theorem schedule_word (bs : ByteArray) (off i : Nat) (hi : i < 16) :
    (CompressionCorrect.schedule bs off)[i]! = Crypto.Ripemd160.readLE32 bs (off+i*4) := by
  interval_cases i <;> simp [CompressionCorrect.schedule, List.range']
theorem ready (s : State) (p : Nat) (bs : ByteArray) (off : Nat)
    (hb : p+64 < 2^256) (hz : NormalPrepare.Clear s.memory)
    (hm : ScheduleCorrect.MessageBlockAt s.memory (UInt256.ofNat p) bs off) :
    CoreMessage.Ready (NormalPrepare.scheduled s p).memory
      (fun i => (CompressionCorrect.schedule bs off)[i]!) := by
  apply ready_congr _ _ _ (NormalPrepare.ready s p hz)
  intro i hi
  apply UInt32.toNat_inj.mp
  have he := DecodedMemory.entry_eq_expected s.memory p i hi hb
  rw [hm i hi, Word.ofUInt32_toNat, ← schedule_word bs off i hi] at he
  exact he
theorem result_compressBlock (s : State) (p : Nat) (bs : ByteArray) (off : Nat)
    (h : Compression.HashState) (hb : p+64 < 2^256) (hz : NormalPrepare.Clear s.memory)
    (hm : ScheduleCorrect.MessageBlockAt s.memory (UInt256.ofNat p) bs off) :
    CompressionCorrect.hashArray (CoreFunctional.result (NormalPrepare.scheduled s p).memory h) =
      Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h) bs off :=
  CoreFunctional.result_compressBlock _ bs off h (ready s p bs off hb hz hm)
#print axioms ready_congr
#print axioms ready
#print axioms result_compressBlock
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.NormalMessage
