import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionRecurrence
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionBodyRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace RecognitionRecurrence

private theorem hadd_eq (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem hmul_eq (a b : UInt256) : a * b = UInt256.mul a b := rfl
private theorem add_comm (a b : UInt256) : UInt256.add a b = UInt256.add b a := Word.word_add_comm a b
private theorem land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply PairedLaneUInt256Bridge.bits_injective
  simp only [PairedLaneUInt256Bridge.bits_land, BitVec.and_comm]
private theorem xor_comm (a b : UInt256) : UInt256.xor a b = UInt256.xor b a := by
  apply PairedLaneUInt256Bridge.bits_injective
  simp only [PairedLaneUInt256Bridge.bits_xor, BitVec.xor_comm]
private theorem mul_comm (a b : UInt256) : UInt256.mul a b = UInt256.mul b a := by
  apply PairedLaneUInt256Bridge.bits_injective
  simp only [PairedLaneUInt256Bridge.bits_mul, BitVec.mul_comm]

structure Frame where
  acc : UInt256
  off : UInt256
  word : UInt256
  stop : UInt256
  full : UInt256

def c32 : UInt256 := UInt256.mul (UInt256.ofNat 32) PatternedSwar.M

def frame (f : Frame) (rho : List UInt256) : List UInt256 :=
  [f.acc, f.off, f.word, f.stop, f.full, c32,
    PatternedSwar.m7, PatternedSwar.m8, PatternedSwar.M] ++ rho

def normalTemplate : List Instr := [
  .op .JUMPDEST,
  .op (.Dup ⟨1, by decide⟩),
  .op .CALLDATALOAD,
  .op (.Dup ⟨3, by decide⟩),
  .op .XOR,
  .op .OR,
  .op (.Swap ⟨0, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 32),
  .op .ADD,
  .op (.Swap ⟨0, by decide⟩),
  .op (.Dup ⟨7, by decide⟩),
  .op (.Dup ⟨3, by decide⟩),
  .op .NOT,
  .op .AND,
  .op (.Dup ⟨6, by decide⟩),
  .op (.Dup ⟨4, by decide⟩),
  .op (.Dup ⟨9, by decide⟩),
  .op .AND,
  .op .ADD,
  .op .XOR,
  .op (.Swap ⟨2, by decide⟩),
  .op .POP]

def normalResult (s : State) (f : Frame) : Frame :=
  { f with
    acc := UInt256.lor (UInt256.xor f.word (MachineState.readWord s.executionEnv.calldata f.off.toNat)) f.acc
    off := UInt256.add (UInt256.ofNat 32) f.off
    word := advance 32 f.word }

theorem run_normal (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq normalTemplate {s with pc := pc, stack := frame f rho} =
      some {s with
        pc := pcAfter pc normalTemplate
        stack := frame (normalResult s f) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (config := { maxSteps := 600000 }) (discharger := omega) [normalTemplate, normalResult, frame, c32,
    advance, runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hcap,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [hadd_eq, hmul_eq, land_comm, xor_comm, add_comm, mul_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

def boundaryTemplate : List Instr := [
  .op .JUMPDEST,
  .op (.Dup ⟨1, by decide⟩),
  .op .CALLDATALOAD,
  .op (.Dup ⟨3, by decide⟩),
  .op (.Dup ⟨9, by decide⟩),
  .op .AND,
  .op (.Dup ⟨10, by decide⟩),
  .op (.Dup ⟨4, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 8),
  .op .SHR,
  .push ⟨1, by decide⟩ (UInt256.ofNat 40),
  .op .MUL,
  .push ⟨1, by decide⟩ (UInt256.ofNat 216),
  .op .SUB,
  .op .SHR,
  .push ⟨1, by decide⟩ (UInt256.ofNat 11),
  .op .MUL,
  .op (.Dup ⟨9, by decide⟩),
  .op (.Dup ⟨6, by decide⟩),
  .op .AND,
  .op .ADD,
  .op .XOR,
  .op .XOR,
  .op .OR,
  .op (.Dup ⟨7, by decide⟩),
  .op (.Dup ⟨3, by decide⟩),
  .op .NOT,
  .op .AND,
  .op (.Dup ⟨9, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 43),
  .op .MUL,
  .op (.Dup ⟨4, by decide⟩),
  .op (.Dup ⟨9, by decide⟩),
  .op .AND,
  .op .ADD,
  .op .XOR,
  .op (.Swap ⟨2, by decide⟩),
  .op .POP,
  .op (.Swap ⟨0, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 32),
  .op .ADD,
  .op (.Swap ⟨0, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 224),
  .op (.Dup ⟨2, by decide⟩),
  .op .ADD,
  .op (.Swap ⟨3, by decide⟩),
  .op .POP]

def boundaryResult (s : State) (f : Frame) : Frame :=
  { f with
    acc := UInt256.lor
      (UInt256.xor
        (PatternedSwar.straddleAdd f.word (correction f.off))
        (MachineState.readWord s.executionEnv.calldata f.off.toNat)) f.acc
    off := UInt256.add (UInt256.ofNat 32) f.off
    word := advance 43 f.word
    stop := UInt256.add (UInt256.ofNat 224) (UInt256.add (UInt256.ofNat 32) f.off) }

theorem run_boundary (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq boundaryTemplate {s with pc := pc, stack := frame f rho} =
      some {s with
        pc := pcAfter pc boundaryTemplate
        stack := frame (boundaryResult s f) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (config := { maxSteps := 600000 }) (discharger := omega) [boundaryTemplate, boundaryResult, frame, c32,
    advance, correction, PatternedSwar.straddleAdd, runInstrSeq, Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [hadd_eq, hmul_eq, land_comm, xor_comm, add_comm, mul_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

#print axioms run_normal
#print axioms run_boundary
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionBodyRaw
