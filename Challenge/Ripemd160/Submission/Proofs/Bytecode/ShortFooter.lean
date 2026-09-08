import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortFooter

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof Challenge.EvmProof.Word
open StackRoundTrace

def guard : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 1 13, .op .SHR,
   .push 2 5308, .op .JUMPI]

def body : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .push 2 280, .op .ADD,
   .op (.Dup ⟨1, by decide⟩), .push 1 3, .op .SHL,
   .op (.Dup ⟨1, by decide⟩), .op .MSTORE8,
   .push 1 1, .op .ADD, .op (.Swap ⟨0, by decide⟩),
   .push 1 5, .op .SHR, .op (.Swap ⟨0, by decide⟩), .op .MSTORE8,
   .push 0 0, .op (.Swap ⟨0, by decide⟩), .op (.Swap ⟨1, by decide⟩)]

def address (padded : UInt256) : UInt256 := UInt256.add 280 padded

def writeByte (memory : ByteArray) (offset value : UInt256) : ByteArray :=
  MachineState.writeBytes memory (ByteArray.mk #[UInt8.ofNat (value.toNat % 256)]) offset.toNat

def expected (s : State) (n padded ret : UInt256) (rest : List UInt256) : State :=
  let addr := address padded
  let next := UInt256.add 1 addr
  let active := s.activeWordsAfterUInt256 addr.toNat 1
  { s with
    pc := 0x1b2
    stack := [ret, 0, padded] ++ rest
    memory := writeByte (writeByte s.memory addr (n.shiftLeft 3)) next (n.shiftRight 5),
    activeWords := UInt256.ofNat (MachineState.activeWordsAfter active.toNat next.toNat 1) }

theorem body_length : body.length = 18 := by rfl

theorem short_condition (n : UInt256) (hn : n.toNat < 8192) :
    n.shiftRight 13 = 0 := by
  apply word_ext
  change (n.shiftRight (UInt256.ofNat 13)).toNat = 0
  rw [shiftRight_toNat n (by norm_num : 13 < 256)]
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt hn

theorem run_guard_short (s : State) (n padded ret : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1018) (hrun : s.halt = .Running)
    (hn : n.toNat < 8192) :
    runInstrSeq guard { s with pc := 0x193, stack := [n, padded, ret] ++ rest } =
      some { s with pc := 0x19b, stack := [n, padded, ret] ++ rest } := by
  have hcap (m : Nat) (hm : m ≤ 6) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 1000000 })
    [guard, runInstrSeq, Stepper.runInstr, hrun, hcap, Nat.add_assoc,
      UInt256.succ, Instr.size, Instr.size_push, Instr.size_op,
      short_condition n hn, UInt256.isTrue]
  rfl

theorem run_guard_long (s : State) (n padded ret : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1018) (hrun : s.halt = .Running)
    (hn : UInt256.isTrue (n.shiftRight 13))
    (hdest : Decode.isValidJumpDest s.executionEnv.code 5308 = true) :
    runInstrSeq guard { s with pc := 0x193, stack := [n, padded, ret] ++ rest } =
      some { s with pc := 5308, stack := [n, padded, ret] ++ rest } := by
  have hcap (m : Nat) (hm : m ≤ 6) : rest.length + m < 1024 := by omega
  have hdest' : Decode.isValidJumpDest s.executionEnv.code (UInt256.toNat 5308) = true := hdest
  simp (config := { maxSteps := 1000000 })
    [guard, runInstrSeq, Stepper.runInstr, hrun, hcap, Nat.add_assoc,
      UInt256.succ, Instr.size, Instr.size_push, Instr.size_op, hn, hdest']

theorem run_body (s : State) (n padded ret : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1018) (hrun : s.halt = .Running) :
    runInstrSeq body { s with pc := 0x19b, stack := [n, padded, ret] ++ rest } =
      some (expected s n padded ret rest) := by
  have hcap (m : Nat) (hm : m ≤ 6) : rest.length + m < 1024 := by omega
  have hswap (a b : UInt256) (rho : List UInt256) :
      (a :: b :: rho).exchange 0 1 = some (b :: a :: rho) := by
    simpa using YulEvmCompiler.exchange_swap a b ([] : List UInt256) rho
  have hswap2 (a b c : UInt256) (rho : List UInt256) :
      (a :: b :: c :: rho).exchange 0 2 = some (c :: b :: a :: rho) := by
    simpa using YulEvmCompiler.exchange_swap a c ([b] : List UInt256) rho
  simp (config := { maxSteps := 1000000 })
    [body, runInstrSeq, Stepper.runInstr, expected, address, writeByte,
      hrun, hcap, hswap, hswap2, Nat.add_assoc, UInt256.succ, Instr.size,
      Instr.size_push, Instr.size_op, State.activeWordsAfterUInt256,
      List.getElem?_cons_zero, Option.bind_some]
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

theorem second_byte (n : Nat) :
    UInt8.ofNat (n / 32) = UInt8.ofNat (n * 8 / 256) := by
  congr 1
  omega

theorem high_bytes_zero (n i : Nat) (hn : n < 8192) (hi : 2 ≤ i) :
    UInt8.ofNat (n * 8 / 2 ^ (8 * i)) = 0 := by
  have hp : (2 : Nat) ^ 16 ≤ 2 ^ (8 * i) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hz : n * 8 < 2 ^ (8 * i) := by
    norm_num at hp
    omega
  rw [Nat.div_eq_of_lt hz]
  rfl

#print axioms run_body
#print axioms run_guard_short
#print axioms run_guard_long
#print axioms second_byte
#print axioms high_bytes_zero

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortFooter
