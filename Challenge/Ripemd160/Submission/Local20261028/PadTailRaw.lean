import Challenge.Ripemd160.Submission.Local20261028.TerminalMaskWindows
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduledTailFrame
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadTailRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof StackRoundTrace
open Paired144WordRound
def fields (q : ScheduledTailRaw.Input) (m8 m16 : UInt256) (i : Fin 23) : UInt256 := match i.val with
  | 0 => UInt256.shiftRight (UInt256.mul q.factor q.ld) (UInt256.ofNat 23)
  | 1 => UInt256.shiftRight q.re (UInt256.ofNat 144)
  | 2 => UInt256.add (UInt256.shiftRight q.rd (UInt256.ofNat 144)) q.lc
  | 3 => UInt256.add (UInt256.shiftRight q.rc (UInt256.ofNat 144)) q.lb
  | 4 => q.la
  | 5 => UInt256.shiftRight q.rb (UInt256.ofNat 144)
  | 6 => q.le
  | 7 => UInt256.shiftRight q.ra (UInt256.ofNat 144)
  | 8 => q.factor
  | 9 => q.lower
  | 10 => q.cache140
  | 11 => q.cache350
  | 12 => q.cache310
  | 13 => q.cache190
  | 14 => q.h4
  | 15 => q.h3
  | 16 => q.h2
  | 17 => q.h1
  | 18 => q.h0
  | 19 => q.off
  | 20 => q.limit
  | 21 => m8
  | _ => m16
def template : List Instr :=
  [ .op (.Swap ⟨3, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .SHR,
    .op .ADD,
    .op (.Swap ⟨6, by decide⟩),
    .op .POP,
    .op (.Dup ⟨12, by decide⟩),
    .op .MUL,
    .op (.Swap ⟨3, by decide⟩),
    .op .POP,
    .op (.Swap ⟨6, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .push ⟨2, by decide⟩ (UInt256.ofNat 10024),
    .op .JUMP,
    .op .JUMPDEST,
    .op .SHR,
    .op .ADD,
    .op (.Swap ⟨4, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .SHR,
    .op (.Swap ⟨2, by decide⟩),
    .op .POP,
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .SHR,
    .op (.Swap ⟨7, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .SHR,
    .op (.Swap ⟨5, by decide⟩),
    .op .SHR ]
theorem run (s : State) (pc : UInt256) (q : ScheduledTailRaw.Input) (m8 m16 : UInt256)
    (rho : List UInt256) (hs : rho.length ≤ 970) (hr : s.halt = .Running)
    (hlower : q.lower = UInt256.ofNat 4294967295)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 10024 = true) :
    runInstrSeq template {s with pc := pc, stack := ScheduledTailRaw.stack0 q (m8::m16::rho)} =
      some {s with pc := UInt256.ofNat 10042, stack := RipemdTerminalMaskWindows20261027.frame (fields q m8 m16) rho} := by
  have hcap (n : Nat) (hn : n ≤ 50) : rho.length+n < 1024 := by omega
  simp (discharger := omega) [template, fields, ScheduledTailRaw.stack0,
    RipemdTerminalMaskWindows20261027.frame, runInstrSeq, DataStepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hr, hcap, hlower, hvalid, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadTailRaw
