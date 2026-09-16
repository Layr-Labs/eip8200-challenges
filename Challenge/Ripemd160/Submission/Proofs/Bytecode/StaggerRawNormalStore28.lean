import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawNormalStore28
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
def template : List Instr :=
  [ .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 532),
    .op .MSTORE,
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 514),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 496),
    .op .MSTORE,
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 478),
    .op .MSTORE,
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 460),
    .op .MSTORE,
    .op (.Dup ⟨11, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 442),
    .op .MSTORE,
    .op (.Dup ⟨10, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 424),
    .op .MSTORE,
    .op (.Dup ⟨10, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 406),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 388),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 370),
    .op .MSTORE,
    .op (.Dup ⟨2, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 352),
    .op .MSTORE,
    .op (.Dup ⟨2, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 334),
    .op .MSTORE,
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 316),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 298),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 280),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 262),
    .op .MSTORE ]
def inputStack (x : Input) (rho : List UInt256) : List UInt256 :=
  [ x.v0, x.v1, x.v2, x.v3, x.v4, x.v5, x.v6, x.v7, x.v8, x.v9, x.v10, x.v11, x.v12 ] ++ rho
def outputStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ x.v4,
    x.v5,
    x.v6,
    x.v7,
    x.v8,
    x.v9,
    x.v10,
    x.v11,
    x.v12 ] ++ rho
def outputMemory (memory : ByteArray) (x : Input) : ByteArray :=
  (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord memory 504 x.v0) 486 x.v8) 468 x.v0) 450 x.v9) 432 x.v9) 414 x.v12) 396 x.v11) 378 x.v11) 360 x.v1) 342 x.v1) 324 x.v4) 306 x.v4) 288 x.v3) 270 x.v2) 252 x.v3) 234 x.v3)
theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack s.memory x rho, memory := outputMemory s.memory x} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 17) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [template, inputStack, outputStack, outputMemory, PairedScheduleMemory.writeWord,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_actual

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawNormalStore28
