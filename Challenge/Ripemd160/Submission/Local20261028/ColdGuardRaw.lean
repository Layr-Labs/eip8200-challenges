import Challenge.Ripemd160.Submission.Local20261028.ColdGuardSites
import Challenge.Ripemd160.Submission.Local20261028.ColdShared32Scratch
import Challenge.Ripemd160.Submission.Local20261028.ColdArtifact
import Challenge.Ripemd160.Submission.Local20261028.FirstEntry
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.ColdGuardFixup
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate Local20261028
def cstk (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256) (rho : List UInt256) :
    List UInt256 :=
  a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: off :: lim :: rho

/-- The two scratch bytes of the shared 32-byte block. -/
def wMemory (m : ByteArray) (b c : UInt8) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes m (ByteArray.mk #[b]) 165)
    (ByteArray.mk #[c]) 188

/-- The two scratch byte values the 32-byte block leaves on the generic route: the sentinel `0x80`
at 165 and the low byte of the resident coefficient word at 188. -/
def dirtyB : UInt8 := UInt8.ofNat ((UInt256.ofNat 128).toNat % 256)
def dirtyC : UInt8 := UInt8.ofNat ((Paired144WordRound.fusedCoefficientWord 0 3).toNat % 256)

/-- A zero word store would undo both scratch bytes on zero, active memory. -/
theorem restore (m : ByteArray) (b c : UInt8) (hsize : 189 ≤ m.size)
    (hzero : ∀ a, 157 ≤ a → a < 189 → m[a]?.getD 0 = 0) :
    MachineState.writeBytes (wMemory m b c) (Data.Bytes.natToBytesPadded 0 32) 157 = m := by
  have e1 : (ByteArray.mk #[c]).size = 1 := rfl
  have eb : (ByteArray.mk #[b]).size = 1 := rfl
  apply ByteArray.ext_getElem
  · simp only [wMemory, MachineState.writeBytes_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size, e1, eb]
    split_ifs <;> omega
  · intro a hA hB
    rw [← Memory.getD0_eq_getElem _ _ hA, ← Memory.getD0_eq_getElem _ _ hB]
    simp only [wMemory, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size, e1, eb]
    by_cases h1 : 157 ≤ a ∧ a < 157 + 32
    · rw [if_pos h1, YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by omega),
        hzero a h1.1 (by omega)]
      simp
    · rw [if_neg h1, if_neg (by omega), if_neg (by omega)]

/-- Away from the two scratch bytes the 32-byte block's writes are invisible. -/
theorem wMemory_getD (m : ByteArray) (b c : UInt8) (a : Nat) (h165 : a ≠ 165) (h188 : a ≠ 188) :
    (wMemory m b c)[a]?.getD 0 = m[a]?.getD 0 := by
  have e1 : (ByteArray.mk #[c]).size = 1 := rfl
  have eb : (ByteArray.mk #[b]).size = 1 := rfl
  simp only [wMemory, MachineState.writeBytes_getElem?_getD, e1, eb]
  rw [if_neg (by omega), if_neg (by omega)]


theorem run_special (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hs : rho.length ≤ 860) (hr : s.halt = .Running)
    (ha : 34 ≤ s.activeWords.toNat) (he : UInt256.eq (UInt256.ofNat 32) limit = UInt256.ofNat 0) :
    runInstrSeq ControlSites.specialTemplate
      {s with pc := UInt256.ofNat 143, stack := StaggerPersistentFrame.frame h off limit rho} =
      some {FirstEntry.high s with pc := UInt256.ofNat 188, stack := StaggerPersistentFrame.frame h off (UInt256.ofNat 9949) rho} := by
  have hcap (n : Nat) (hn : n ≤ 28) : rho.length+n < 1024 := by omega
  have hat : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 162 32) = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords 162 ha (by decide)
  have hz : (UInt256.ofNat 0).isTrue = false := by decide
  simp (discharger := omega) [ControlSites.specialTemplate,runInstrSeq,DataStepper.runInstr,
    StaggerPersistentFrame.frame,FirstEntry.high,PairedScheduleMemory.writeWord,FirstInitial.highWord,
    List.exchange,List.getElem?_cons_zero,hr,hcap,Nat.add_assoc,State.activeWordsAfterUInt256,hat,he,hz]
  rfl

#print axioms run_special
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.ColdGuardFixup
