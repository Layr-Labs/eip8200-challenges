import Challenge.Ripemd160.Submission.Proofs.Bytecode.DataSuffixAppendCanary
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputData
import Challenge.Ripemd160.ProofSupport.InitialState

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

/-!
# Raw evaluator trace for the appended two-load pair

The executable instruction list before the append ends before an immutable
280-byte data suffix.  This module therefore does not manufacture an
instruction index for the appended bytes.  It constructs the exact raw
33-byte append separately and proves its evaluator transition at PC 5231.
The two `CALLDATALOAD` operations are reduced symbolically; no finite input
specialization is used.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardPairedRaw

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

def pairReferenceWord (input : ByteArray) : UInt256 :=
  MachineState.readWord input 0

def pairLoopAcc (input : ByteArray) : Nat → UInt256
  | 0 => UInt256.xor (pairReferenceWord input) KnownInputData.fullWord
  | n + 1 => UInt256.lor
      (UInt256.xor (MachineState.readWord input (32 * (n + 1)))
        (pairReferenceWord input))
      (pairLoopAcc input n)

private theorem pair_xor_comm (a b : UInt256) :
    UInt256.xor a b = UInt256.xor b a := by
  simp [UInt256.xor, Fin.xor, Nat.xor_comm]

private theorem pair_read_xor_comm (input : ByteArray) (address : Nat) :
    UInt256.xor (MachineState.readWord input address) (pairReferenceWord input) =
      UInt256.xor (pairReferenceWord input) (MachineState.readWord input address) := by
  exact pair_xor_comm _ _

@[simp] theorem pair_initialState_code (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).executionEnv.code = code := rfl

@[simp] theorem pair_initialState_halt (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).halt = .Running := rfl

@[simp] theorem pair_initialState_memory (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).memory = ByteArray.empty := rfl

@[simp] theorem pair_initialState_activeWords (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).activeWords = 0 := rfl

@[simp] theorem pair_initialState_calldata (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).executionEnv.calldata = calldata := rfl

def runInstrSeq : List Instr → State → Option State
  | [], s => some s
  | instruction :: rest, s =>
      match Challenge.EvmProof.DataStepper.runInstr instruction s with
      | none => none
      | some next =>
          match rest with
          | [] => some next
          | _ :: _ =>
              match next.halt with
              | .Running => runInstrSeq rest next
              | _ => none

def pairCode : List Instr :=
  [ .op .JUMPDEST,
    .op (.Swap ⟨0, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .op .CALLDATALOAD,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .OR,
    .op (.Swap ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 32),
    .op .ADD,
    .op (.Swap ⟨0, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .op .CALLDATALOAD,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .OR,
    .op (.Swap ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 32),
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 992),
    .op (.Dup ⟨1, by decide⟩),
    .op .LT,
    .push ⟨2, by decide⟩ (UInt256.ofNat 5231),
    .op .JUMPI,
    .push ⟨1, by decide⟩ (UInt256.ofNat 67),
    .op .JUMP ]

def pairBytes : List UInt8 := assembleBytes pairCode

def pairCodeMore : List Instr := pairCode.take 24

def pairCodeWithData
    (execPrefix dataSuffix : List UInt8) : ByteArray :=
  mkCode (execPrefix ++ dataSuffix ++ pairBytes)

theorem pairBytes_exact : pairBytes =
    [0x5b, 0x90, 0x81, 0x35, 0x83, 0x18, 0x17, 0x90,
     0x60, 0x20, 0x01, 0x90, 0x81, 0x35, 0x83, 0x18,
     0x17, 0x90, 0x60, 0x20, 0x01, 0x61, 0x03, 0xe0,
     0x81, 0x10, 0x61, 0x14, 0x6f, 0x57, 0x60, 0x43, 0x56] := by
  decide

theorem pair_pc
    (execPrefix dataSuffix : List UInt8)
    (hprefix : execPrefix.length = 4951)
    (hdata : dataSuffix.length = 280) :
    execPrefix.length + dataSuffix.length = 5231 := by
  omega

def pairLoopState (code input : ByteArray) (n : Nat) : State :=
  { initialState code input 0 with
    pc := UInt256.ofNat 5231
    stack := [UInt256.ofNat (32 * (n + 1)), pairLoopAcc input n,
      pairReferenceWord input] }

def pairExitState (code input : ByteArray) : State :=
  { initialState code input 0 with
    pc := UInt256.ofNat 67
    stack := [UInt256.ofNat 992, pairLoopAcc input 30,
      pairReferenceWord input] }

theorem run_pair_more_raw
    (code input : ByteArray) (n : Nat) (hn : n < 28)
    (hdest : Decode.isValidJumpDest code 5231 = true) :
    runInstrSeq pairCodeMore (pairLoopState code input n) =
      some (pairLoopState code input (n + 2)) := by
  have hstart : 32 * n + 32 < 2 ^ 256 := by omega
  have hnext : 32 * n + 64 < 2 ^ 256 := by omega
  have hnext2 : 32 * n + 96 < 2 ^ 256 := by omega
  have hlt : 32 * n + 96 < 992 := by omega
  have hmod : (32 * n + 32) % 2 ^ 256 = 32 * n + 32 :=
    Nat.mod_eq_of_lt hstart
  have hnextMod : (32 * n + 64) % 2 ^ 256 = 32 * n + 64 :=
    Nat.mod_eq_of_lt hnext
  have hnextMod2 : (32 * n + 96) % 2 ^ 256 = 32 * n + 96 :=
    Nat.mod_eq_of_lt hnext2
  have hmodN : (32 * n + 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * n + 32 := by
    apply Nat.mod_eq_of_lt
    omega
  have hnextN : (32 * n + 64) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * n + 64 := by
    apply Nat.mod_eq_of_lt
    omega
  have hnaddr : 32 * (n + 1) + 32 = 32 * n + 64 := by omega
  have hnaddr2 : 32 * (n + 2) + 32 = 32 * n + 96 := by omega
  have hnaddr0 : 32 + 32 * n = 32 * n + 32 := by omega
  have hnaddr1 : 32 + (32 + 32 * n) = 32 * n + 64 := by omega
  have hnaddr1' : 32 + (32 * n + 32) = 32 * n + 64 := by omega
  have hnaddr2' : 32 + (32 + (32 * n + 32)) = 32 * n + 96 := by omega
  have hacc1 : pairLoopAcc input (n + 1) =
      UInt256.lor (UInt256.xor
        (MachineState.readWord input (32 * (n + 1)))
        (pairReferenceWord input)) (pairLoopAcc input n) := by
    rw [pairLoopAcc]
  have hacc2 : pairLoopAcc input (n + 2) =
      UInt256.lor (UInt256.xor
        (MachineState.readWord input (32 * (n + 2)))
        (pairReferenceWord input)) (pairLoopAcc input (n + 1)) := by
    rw [show n + 2 = (n + 1) + 1 by omega, pairLoopAcc]
  have hcond : (UInt256.lt (UInt256.ofNat (32 * n + 96))
      (UInt256.ofNat 992)).toNat ≠ 0 := by
    unfold UInt256.lt
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, hnextMod2,
      Nat.mod_eq_of_lt (by norm_num : 992 < 2 ^ 256), if_pos hlt]
    decide
  have hcond' : UInt256.isTrue
      (UInt256.lt (UInt256.ofNat (32 + (32 + (32 * n + 32))))
        (UInt256.ofNat 992)) := by
    unfold UInt256.isTrue
    have hform : 32 + (32 + (32 * n + 32)) = 32 * n + 96 := by omega
    rw [hform]
    exact hcond
  simp (config := { maxSteps := 2000000 }) (discharger := omega)
    [pairCodeMore, pairCode, pairLoopState, pairBytes, hdest, hstart, hnext, hnext2,
      hmod, hnextMod, hnextMod2, hnaddr, hnaddr2, hlt,
      hcond, hcond',
      hacc1, hacc2,
      runInstrSeq, Challenge.EvmProof.DataStepper.runInstr,
      UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mul_add]
  constructor
  · have hpc : 32 * n + 64 + 32 = 32 * n + 96 := by omega
    rw [hnaddr2', hpc]
  · rw [hnaddr1', hnextN, hmodN,
        pair_xor_comm (pairReferenceWord input)
          (MachineState.readWord input (32 * n + 64)),
        pair_xor_comm (pairReferenceWord input)
          (MachineState.readWord input (32 * n + 32))]

theorem run_pair_terminal_raw
    (code input : ByteArray)
    (hdest : Decode.isValidJumpDest code 67 = true) :
    runInstrSeq pairCode (pairLoopState code input 28) =
      some (pairExitState code input) := by
  have hacc : pairLoopAcc input 30 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 960)
        (pairReferenceWord input))
        (UInt256.lor (UInt256.xor (MachineState.readWord input 928)
          (pairReferenceWord input)) (pairLoopAcc input 28)) := by
    rw [show 30 = 29 + 1 by omega, pairLoopAcc,
      show 29 = 28 + 1 by omega, pairLoopAcc]
  have hfalse : ¬ UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 992) (UInt256.ofNat 992)) := by
    decide
  have hcond : (UInt256.lt (UInt256.ofNat 992)
      (UInt256.ofNat 992)).toNat = 0 := by
    decide
  simp (config := { maxSteps := 2000000 }) (discharger := omega)
    [pairCode, pairLoopState, pairExitState, pairBytes, hdest,
      hacc, hfalse, hcond, runInstrSeq,
      Challenge.EvmProof.DataStepper.runInstr,
      UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mul_add]
  rw [pair_xor_comm (pairReferenceWord input)
        (MachineState.readWord input 960),
      pair_xor_comm (pairReferenceWord input)
        (MachineState.readWord input 928)]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardPairedRaw
