import Challenge.Ripemd160.Submission.Local20261028.TerminalMaskFacts
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace RipemdTerminalMaskWindows20261027
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace RipemdTerminalMasks20261027
def frame (x : Fin 23 → UInt256) (rho : List UInt256) : List UInt256 :=
  x 0 :: x 1 :: x 2 :: x 3 :: x 4 :: x 5 :: x 6 :: x 7 :: x 8 :: UInt256.ofNat 4294967295 :: x 10 :: x 11 :: x 12 :: x 13 :: x 14 :: x 15 :: x 16 :: x 17 :: x 18 :: x 19 :: x 20 :: x 21 :: x 22 :: rho
def a (x : Fin 23 → UInt256) := UInt256.add (x 18) (x 3)
def b (x : Fin 23 → UInt256) := UInt256.add (UInt256.add (x 14) (x 4)) (x 5)
def c (x : Fin 23 → UInt256) := UInt256.add (UInt256.add (x 15) (x 6)) (x 7)
def d (x : Fin 23 → UInt256) := UInt256.add (x 16) (UInt256.add (x 0) (x 1))
def e (x : Fin 23 → UInt256) := mask (UInt256.add (x 17) (x 2))
def written (s : State) (address : Nat) (w : UInt256) : State :=
  {s with memory := PairedScheduleMemory.writeWord s.memory address w, activeWords := s.activeWordsAfterUInt256 address 32}
def prepared (s : State) (x : Fin 23 → UInt256) : State :=
  written (written (written (written (written s 16 (a x)) 12 (b x)) 8 (c x)) 4 (d x)) 0 (e x)
theorem mask_first (w : UInt256) : UInt256.land (UInt256.ofNat 4294967295) w = mask w :=
  RawExpressionAC.land_comm _ _
def before : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .AND,
   .op (.Swap ⟨15, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨15, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op (.Swap ⟨10, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .op (.Swap ⟨9, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .AND,
   .op (.Swap ⟨8, by decide⟩),
   .op (.Swap ⟨12, by decide⟩),
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .push ⟨1, by decide⟩ (UInt256.ofNat 16),
   .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 12),
   .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 8),
   .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 4),
   .op .MSTORE,
   .push ⟨0, by decide⟩ (UInt256.ofNat 0),
   .op .MSTORE]
theorem before_run (s : State) (pc : UInt256) (x : Fin 23 → UInt256)
    (rho : List UInt256) (hs : rho.length ≤ 980) (hr : s.halt = .Running) :
    runInstrSeq before {s with pc := pc, stack := frame x rho} =
      some {prepared s x with pc := pcAfter pc before, stack := x 19 :: x 16 :: x 21 :: x 22 :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length+n < 1024 := by omega
  have hm := stores_eq s.memory (a x) (b x) (c x) (d x) (e x)
  simp only [stores, a, b, c, d, e, PairedScheduleMemory.writeWord] at hm
  simp (discharger := omega) [before, frame, prepared, written, a, b, c, d, e,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    hr, hcap, Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, State.activeWordsAfterUInt256,
    mask_first, PairedScheduleMemory.writeWord, hm]
  all_goals repeat first | apply And.intro | rfl | exact hm
#print axioms before_run
def after : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨15, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Swap ⟨15, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨10, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Swap ⟨9, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Swap ⟨8, by decide⟩),
   .op (.Swap ⟨12, by decide⟩),
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .push ⟨1, by decide⟩ (UInt256.ofNat 16),
   .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 12),
   .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 8),
   .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 4),
   .op .MSTORE,
   .push ⟨0, by decide⟩ (UInt256.ofNat 0),
   .op .MSTORE]
theorem after_run (s : State) (pc : UInt256) (x : Fin 23 → UInt256)
    (rho : List UInt256) (hs : rho.length ≤ 980) (hr : s.halt = .Running) :
    runInstrSeq after {s with pc := pc, stack := frame x rho} =
      some {prepared s x with pc := pcAfter pc after, stack := x 19 :: x 16 :: x 21 :: x 22 :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length+n < 1024 := by omega
  have hm := stores_eq s.memory (a x) (b x) (c x) (d x) (e x)
  simp only [stores, a, b, c, d, e, PairedScheduleMemory.writeWord] at hm
  simp (discharger := omega) [after, frame, prepared, written, a, b, c, d, e,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    hr, hcap, Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, State.activeWordsAfterUInt256,
    mask_first, PairedScheduleMemory.writeWord, hm]
  all_goals repeat first | apply And.intro | rfl | exact hm
#print axioms after_run
end RipemdTerminalMaskWindows20261027
