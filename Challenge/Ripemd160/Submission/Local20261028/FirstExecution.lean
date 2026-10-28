import Challenge.Ripemd160.Submission.Local20261028.CandidateBytes
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace RipemdSubmissionTables20261028
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace

private theorem add_literals (a b : Nat) :
    UInt256.add (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a+b) := by
  apply Word.word_ext
  change (a % 2^256 + b % 2^256) % 2^256 = (a+b) % 2^256
  exact (Nat.add_mod a b (2^256)).symm

private theorem hadd_literals (a b : Nat) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a+b) := add_literals a b

private theorem active_preserved35 (current : UInt256) (address : Nat)
    (hc : 35 ≤ current.toNat) (ha : address ≤ 1088) :
    UInt256.ofNat (MachineState.activeWordsAfter current.toNat address 32) = current := by
  have h : MachineState.activeWordsAfter current.toNat address 32 = current.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
    apply Nat.max_eq_left
    omega
  rw [h]
  exact (Word.word_eq_ofNat_toNat _).symm

private theorem active_preserved34 (current : UInt256) (address : Nat)
    (hc : 34 ≤ current.toNat) (ha : address ≤ 1056) :
    UInt256.ofNat (MachineState.activeWordsAfter current.toNat address 32) = current := by
  have h : MachineState.activeWordsAfter current.toNat address 32 = current.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
    apply Nat.max_eq_left
    omega
  rw [h]
  exact (Word.word_eq_ofNat_toNat _).symm

namespace First0
def template : List Instr := [
    .push ⟨13, by decide⟩ (UInt256.ofNat 10141204801825835211973625643008),
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .op .MSTORE,
    .push ⟨22, by decide⟩ (UInt256.ofNat 374144419156711147060143317175368453031918731001856),
    .push ⟨1, by decide⟩ (UInt256.ofNat 196),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 236),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 218),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 268),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 286),
    .op .MSTORE ]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 128 ((UInt256.ofNat 10141204801825835211973625643008)))) 196 ((UInt256.ofNat 374144419156711147060143317175368453031918731001856)))) 218 ((MachineState.readWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 128 ((UInt256.ofNat 10141204801825835211973625643008)))) 196 ((UInt256.ofNat 374144419156711147060143317175368453031918731001856)))) 236)))) 286 ((MachineState.readWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 128 ((UInt256.ofNat 10141204801825835211973625643008)))) 196 ((UInt256.ofNat 374144419156711147060143317175368453031918731001856)))) 218 ((MachineState.readWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 128 ((UInt256.ofNat 10141204801825835211973625643008)))) 196 ((UInt256.ofNat 374144419156711147060143317175368453031918731001856)))) 236)))) 268)))

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 10141).take 57 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (10112+29)).take 57 = _
  rw [← List.drop_drop, CandidateBytes.drop158]
  decide +kernel

theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 10141), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 10198), stack := outputs x rho s, memory := memory x s} := by
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hactiveAt (address : Nat) (ha : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_preserved34 s.activeWords address hactive ha
  simp (discharger := omega) [template, inputs, outputs, memory,
    PairedScheduleMemory.writeWord, runInstrSeq, DataStepper.runInstr,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hcap, hzero, State.activeWordsAfterUInt256, hactiveAt,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, add_literals, hadd_literals]
#print axioms exact_bytes
#print axioms run
end First0

namespace First1
def template : List Instr := [
    .push ⟨19, by decide⟩ (UInt256.ofNat 2854495385411919762116571938898990272765493376),
    .push ⟨1, by decide⟩ (UInt256.ofNat 236),
    .op .MLOAD,
    .push ⟨24, by decide⟩ (UInt256.ofNat 24519928653854221733733552434404946937899827054449262592),
    .push ⟨20, by decide⟩ (UInt256.ofNat 5708990770823839524233143877797980545530986752),
    .push ⟨19, by decide⟩ (UInt256.ofNat 2854495385411919762116571938898990272765493248),
    .push ⟨2, by decide⟩ (UInt256.ofNat 262),
    .op .MLOAD,
    .op (.Dup ⟨5, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 266),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 228),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 224),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 258),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 232),
    .op .MLOAD,
    .push ⟨16, by decide⟩ (UInt256.ofNat 1329227995784915872903807060280344576),
    .push ⟨12, by decide⟩ (UInt256.ofNat 309485009821345068724781056),
    .op (.Dup ⟨6, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 18),
    .op .MSTORE ]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [(UInt256.ofNat 309485009821345068724781056), (UInt256.ofNat 1329227995784915872903807060280344576), (MachineState.readWord (s.memory) 232), (MachineState.readWord (s.memory) 258), (MachineState.readWord (s.memory) 224), (MachineState.readWord (s.memory) 228), (MachineState.readWord (s.memory) 266), (UInt256.ofNat 2854495385411919762116571938898990272765493376), (MachineState.readWord (s.memory) 262), (UInt256.ofNat 2854495385411919762116571938898990272765493248), (UInt256.ofNat 5708990770823839524233143877797980545530986752), (UInt256.ofNat 24519928653854221733733552434404946937899827054449262592), (MachineState.readWord (s.memory) 236), (UInt256.ofNat 2854495385411919762116571938898990272765493376), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (PairedScheduleMemory.writeWord (s.memory) 18 ((MachineState.readWord (s.memory) 266)))

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 10198).take 145 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (10176+22)).take 145 = _
  rw [← List.drop_drop, CandidateBytes.drop159]
  decide +kernel

theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 10198), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 10343), stack := outputs x rho s, memory := memory x s} := by
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hactiveAt (address : Nat) (ha : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_preserved34 s.activeWords address hactive ha
  simp (discharger := omega) [template, inputs, outputs, memory,
    PairedScheduleMemory.writeWord, runInstrSeq, DataStepper.runInstr,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hcap, hzero, State.activeWordsAfterUInt256, hactiveAt,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, add_literals, hadd_literals]
#print axioms exact_bytes
#print axioms run
end First1

namespace First2
def template : List Instr := [
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 108),
    .op .MSTORE,
    .op (.Dup ⟨4, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 90),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 72),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 54),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 216),
    .op .MSTORE ]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, x 26, x 27, x 28] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, x 26, x 27, x 28] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 108 (x 3))) 90 (x 4))) 72 (x 3))) 54 (x 0))) 216 (x 1))

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 10343).take 18 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (10304+39)).take 18 = _
  rw [← List.drop_drop, CandidateBytes.drop161]
  decide +kernel

theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 10343), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 10361), stack := outputs x rho s, memory := memory x s} := by
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hactiveAt (address : Nat) (ha : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_preserved34 s.activeWords address hactive ha
  simp (discharger := omega) [template, inputs, outputs, memory,
    PairedScheduleMemory.writeWord, runInstrSeq, DataStepper.runInstr,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hcap, hzero, State.activeWordsAfterUInt256, hactiveAt,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, add_literals, hadd_literals]
#print axioms exact_bytes
#print axioms run
end First2

namespace First3
def template : List Instr := [
    .push ⟨2, by decide⟩ (UInt256.ofNat 324),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 360),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 414),
    .op .MSTORE,
    .op (.Dup ⟨2, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 396),
    .op .MSTORE,
    .op (.Dup ⟨4, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 468),
    .op .MSTORE ]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, x 26] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25, x 26] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 324 (x 0))) 360 (x 1))) 414 (x 1))) 396 (x 4))) 468 (x 6))

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 10361).take 23 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (10304+57)).take 23 = _
  rw [← List.drop_drop, CandidateBytes.drop161]
  decide +kernel

theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 10361), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 10384), stack := outputs x rho s, memory := memory x s} := by
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hactiveAt (address : Nat) (ha : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_preserved34 s.activeWords address hactive ha
  simp (discharger := omega) [template, inputs, outputs, memory,
    PairedScheduleMemory.writeWord, runInstrSeq, DataStepper.runInstr,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hcap, hzero, State.activeWordsAfterUInt256, hactiveAt,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, add_literals, hadd_literals]
#print axioms exact_bytes
#print axioms run
end First3

namespace First4
def template : List Instr := [
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 522),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 540),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 558),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 684),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 756),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 738),
    .op .MSTORE ]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 522 (x 1))) 540 (x 0))) 558 (x 1))) 684 (x 2))) 756 (x 3))) 738 (x 4))

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 10384).take 26 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (10368+16)).take 26 = _
  rw [← List.drop_drop, CandidateBytes.drop162]
  decide +kernel

theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 10384), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 10410), stack := outputs x rho s, memory := memory x s} := by
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hactiveAt (address : Nat) (ha : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_preserved34 s.activeWords address hactive ha
  simp (discharger := omega) [template, inputs, outputs, memory,
    PairedScheduleMemory.writeWord, runInstrSeq, DataStepper.runInstr,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hcap, hzero, State.activeWordsAfterUInt256, hactiveAt,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, add_literals, hadd_literals]
#print axioms exact_bytes
#print axioms run
end First4

namespace First5
def template : List Instr := [
    .push ⟨2, by decide⟩ (UInt256.ofNat 720),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 828),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 972),
    .op .MSTORE,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .push ⟨1, by decide⟩ (UInt256.ofNat 252),
    .op .MSTORE,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .push ⟨2, by decide⟩ (UInt256.ofNat 450),
    .op .MSTORE ]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 720 (x 0))) 828 (x 4))) 972 (x 4))) 252 ((UInt256.ofNat 0)))) 450 ((UInt256.ofNat 0)))

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 10410).take 23 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (10368+42)).take 23 = _
  rw [← List.drop_drop, CandidateBytes.drop162]
  decide +kernel

theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 10410), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 10433), stack := outputs x rho s, memory := memory x s} := by
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hactiveAt (address : Nat) (ha : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_preserved34 s.activeWords address hactive ha
  simp (discharger := omega) [template, inputs, outputs, memory,
    PairedScheduleMemory.writeWord, runInstrSeq, DataStepper.runInstr,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hcap, hzero, State.activeWordsAfterUInt256, hactiveAt,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, add_literals, hadd_literals]
#print axioms exact_bytes
#print axioms run
end First5

namespace First6
def template : List Instr := [
    .push ⟨2, by decide⟩ (UInt256.ofNat 576),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 630),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 612),
    .op .MSTORE,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .push ⟨2, by decide⟩ (UInt256.ofNat 666),
    .op .MSTORE,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .push ⟨2, by decide⟩ (UInt256.ofNat 846),
    .op .MSTORE ]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 576 (x 0))) 630 (x 1))) 612 (x 2))) 666 ((UInt256.ofNat 0)))) 846 ((UInt256.ofNat 0)))

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 10433).take 22 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (10432+1)).take 22 = _
  rw [← List.drop_drop, CandidateBytes.drop163]
  decide +kernel

theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 10433), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 10455), stack := outputs x rho s, memory := memory x s} := by
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hactiveAt (address : Nat) (ha : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_preserved34 s.activeWords address hactive ha
  simp (discharger := omega) [template, inputs, outputs, memory,
    PairedScheduleMemory.writeWord, runInstrSeq, DataStepper.runInstr,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hcap, hzero, State.activeWordsAfterUInt256, hactiveAt,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, add_literals, hadd_literals]
#print axioms exact_bytes
#print axioms run
end First6

namespace First7
def template : List Instr := [
    .push ⟨2, by decide⟩ (UInt256.ofNat 864),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 936),
    .op .MSTORE ]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (PairedScheduleMemory.writeWord ((PairedScheduleMemory.writeWord (s.memory) 864 (x 0))) 936 (x 1))

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 10455).take 8 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (10432+23)).take 8 = _
  rw [← List.drop_drop, CandidateBytes.drop163]
  decide +kernel

theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 10455), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 10463), stack := outputs x rho s, memory := memory x s} := by
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hactiveAt (address : Nat) (ha : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    active_preserved34 s.activeWords address hactive ha
  simp (discharger := omega) [template, inputs, outputs, memory,
    PairedScheduleMemory.writeWord, runInstrSeq, DataStepper.runInstr,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hcap, hzero, State.activeWordsAfterUInt256, hactiveAt,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, add_literals, hadd_literals]
#print axioms exact_bytes
#print axioms run
end First7

end RipemdSubmissionTables20261028
