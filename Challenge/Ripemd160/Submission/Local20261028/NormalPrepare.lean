import Challenge.Ripemd160.Submission.Local20261028.CoreEndianBase
import Challenge.Ripemd160.Submission.Local20261028.CoreBody
import Challenge.Ripemd160.Submission.Local20261028.DecodedMemory
import Challenge.Ripemd160.Submission.Local20261028.MemoryPreservation
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.NormalPrepare
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace Paired144WordRound RipemdSubmissionTables20261028 RipemdMemoryBridge20261028
def masks (rho : List UInt256) := DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho
def args (h : Compression.HashState) (off limit : UInt256) (j : Nat) : UInt256 :=
  ((StaggerPersistentFrame.frame h off limit (masks []))[j]?).getD 0
theorem frame_eq (h : Compression.HashState) (off limit : UInt256) (rho : List UInt256) :
    General0.inputs (args h off limit) rho = StaggerPersistentFrame.frame h off limit (masks rho) := by rfl
def decoded (s : State) (p : Nat) : State :=
  {s with memory := DecodedMemory.scratch s.memory (PairedScheduleData.reversedWord (MachineState.readWord s.memory p)) (PairedScheduleData.reversedWord (MachineState.readWord s.memory (p+32))), activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat p)}
def scheduled (s : State) (p : Nat) : State :=
  {decoded s p with memory := resultMemory (fanMemory (decoded s p).memory) RipemdTableOrder20261027.selected}
def template := (CoreEndian.candidateTemplate ++ GeneralTable.template) ++ [.op .JUMPDEST]

theorem run (s : State) (h : Compression.HashState) (p : Nat) (limit : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 890) (hr : s.halt = .Running) (hp : 1056 ≤ p) (hb : p+64 < 2^256) :
    runInstrSeq template
      {s with pc := UInt256.ofNat 462, stack := StaggerPersistentFrame.frame h (UInt256.ofNat p) limit (masks rho)} =
      some {scheduled s p with pc := UInt256.ofNat 824, stack := StaggerPersistentFrame.frame h (UInt256.ofNat p) limit (masks rho)} := by
  have ha : 35 ≤ (decoded s p).activeWords.toNat := Stagger144Active.loaded_active_ge35 s p hp hb
  have he := CoreEndian.run_candidate s (UInt256.ofNat 462) factorPlusWord (UInt256.ofNat 4294967295)
    (fusedModulusWord 5 7) (fusedModulusWord 8 5) (fusedCoefficientWord 0 3) (fusedCoefficientWord 0 2)
    (Word.ofUInt32 h.h4) (Word.ofUInt32 h.h3) (Word.ofUInt32 h.h2) (Word.ofUInt32 h.h1) (Word.ofUInt32 h.h0)
    (UInt256.ofNat p) limit rho p (by omega) hr hp hb (Word.ofNat_add_mod p 32) rfl
  rw [CoreEndian.candidate_end_pc] at he
  have ht := GeneralTable.run (decoded s p) (args h (UInt256.ofNat p) limit) rho (by omega) hr ha
  rw [frame_eq, actual_memory] at ht
  have het := DenseScheduleTrace.runInstrSeq_append_running he hr ht
  have hj : runInstrSeq [.op .JUMPDEST]
      {scheduled s p with pc := UInt256.ofNat 823, stack := StaggerPersistentFrame.frame h (UInt256.ofNat p) limit (masks rho)} =
      some {scheduled s p with pc := UInt256.ofNat 824, stack := StaggerPersistentFrame.frame h (UInt256.ofNat p) limit (masks rho)} := by
    have hcap : (StaggerPersistentFrame.frame h (UInt256.ofNat p) limit (masks rho)).length < 1024 := by
      simp only [StaggerPersistentFrame.frame, masks, List.length_append, List.length_cons, List.length_nil]
      omega
    simp only [runInstrSeq, DataStepper.runInstr, if_pos hcap]
    rfl
  exact DenseScheduleTrace.runInstrSeq_append_running het hr hj

def Clear (m : ByteArray) : Prop := ∀ a ∈ RipemdTableOrder20261027.clearAddresses, m[a]?.getD 0 = 0
theorem decoded_clear (s : State) (p : Nat) (hz : Clear s.memory) : Clear (decoded s p).memory := by
  have hsep : RipemdTableOrder20261027.clearAddresses.all (fun a =>
      decide ((a < 162 ∨ 194 ≤ a) ∧ (a < 252 ∨ 284 ≤ a))) = true := by decide +kernel
  intro a ha
  have hh : (a < 162 ∨ 194 ≤ a) ∧ (a < 252 ∨ 284 ≤ a) := of_decide_eq_true ((List.all_eq_true.mp hsep) a ha)
  simp only [decoded, DecodedMemory.scratch, write_getD, if_neg (by omega : ¬ (252 ≤ a ∧ a < 252+32)),
    if_neg (by omega : ¬ (162 ≤ a ∧ a < 162+32))]
  exact hz a ha
theorem scheduled_eq (s : State) (p : Nat) (x : Nat → UInt256) (rho : List UInt256) :
    (scheduled s p).memory = (GeneralTable.result8 (decoded s p) x rho).memory :=
  (actual_memory (decoded s p) x rho).symm
theorem clear (s : State) (p : Nat) (hz : Clear s.memory) : Clear (scheduled s p).memory := by
  rw [scheduled_eq s p (fun _ => 0) []]
  exact actual_preserves_zeros (decoded s p) _ _ (decoded_clear s p hz)
theorem ready (s : State) (p : Nat) (hz : Clear s.memory) :
    CoreMessage.Ready (scheduled s p).memory (GeneralMessageReady.entryWords (decoded s p).memory) := by
  rw [scheduled_eq s p (fun _ => 0) []]
  exact GeneralMessageReady.ready (decoded s p) _ _ (decoded_clear s p hz)
theorem outside (s : State) (p a : Nat) (ha : 1040 ≤ a) :
    (scheduled s p).memory[a]?.getD 0 = s.memory[a]?.getD 0 := by
  rw [scheduled_eq s p (fun _ => 0) [], general_outside _ _ _ a ha]
  simp only [decoded, DecodedMemory.scratch, write_getD,
    if_neg (by omega : ¬ (252 ≤ a ∧ a < 252+32)), if_neg (by omega : ¬ (162 ≤ a ∧ a < 162+32))]

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 462).take (824-462) = PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (448+14)).take (824-462) = _
  rw [← List.drop_drop, CandidateBytes.drop7]
  decide +kernel
#print axioms run
#print axioms ready
#print axioms clear
#print axioms outside
#print axioms exact_bytes
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.NormalPrepare
