import Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32Hit

set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 400000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32Return

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
open Challenge.EvmProof.DataStepper
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Sites
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open YulEvmCompiler

def push0 : UInt256 := UInt256.ofNat 864225204616626385640043679974750823807691915652
def push1 : UInt256 := UInt256.ofNat 330311920271539217756235131599613361701789350134
def push2 : UInt256 := UInt256.ofNat 1449722157075762988299117569158461631583316913598

def stub0 : List Instr := [
  .op .JUMPDEST,
  .push ⟨20, by decide⟩ push0,
  .push ⟨0, by decide⟩ (UInt256.ofNat 0),
  .op .MSTORE,
  .push ⟨1, by decide⟩ (UInt256.ofNat 32),
  .push ⟨0, by decide⟩ (UInt256.ofNat 0),
  .op .RETURN]

def written (s : State) (value : UInt256) : ByteArray :=
  MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded value.toNat 32) 0

def returned (s : State) (stk : List UInt256) (value : UInt256) (pc : Nat) : State :=
  let mem := written s value
  let stored := { s with
    pc := UInt256.ofNat pc
    stack := stk
    memory := mem
    activeWords := s.activeWordsAfterUInt256 0 32 }
  { stored with
    halt := .Returned
    hReturn := MachineState.readPadded mem 0 32
    activeWords := stored.activeWordsAfterUInt256 0 32 }

private theorem toNat_zero : (0 : UInt256).toNat = 0 := by
  rw [Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat]
  decide

private theorem toNat_32 : (UInt256.ofNat 32).toNat = 32 := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by decide)]

theorem run_stub0 (s : State) (hrun : s.halt = .Running) (stk : List UInt256)
    (hlen : stk.length + 2 < 1024) :
    runInstrSeq stub0 (atState s 9792 stk) = some (returned s stk push0 9819) := by
  have h0 : stk.length < 1024 := by omega
  have h1 : stk.length + 1 < 1024 := by omega
  have h2 : stk.length + 2 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = 0 := by
    rw [Challenge.EvmProof.Word.literal_eq_ofNat]
    rfl
  simp (config := { maxSteps := 400000 }) (discharger := omega)
    [stub0, returned, written, atState, runInstrSeq, DataStepper.runInstr,
      State.activeWordsAfterUInt256, hrun,
      h0, h1, h2, if_pos h0, if_pos h1, if_pos h2, toNat_zero, toNat_32, hzero,
      List.length_cons, Nat.add_assoc,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]


def stub1 : List Instr := [
  .op .JUMPDEST,
  .push ⟨20, by decide⟩ push1,
  .push ⟨0, by decide⟩ (UInt256.ofNat 0),
  .op .MSTORE,
  .push ⟨1, by decide⟩ (UInt256.ofNat 32),
  .push ⟨0, by decide⟩ (UInt256.ofNat 0),
  .op .RETURN]

theorem run_stub1 (s : State) (hrun : s.halt = .Running) (stk : List UInt256)
    (hlen : stk.length + 2 < 1024) :
    runInstrSeq stub1 (atState s 9820 stk) = some (returned s stk push1 9847) := by
  have h0 : stk.length < 1024 := by omega
  have h1 : stk.length + 1 < 1024 := by omega
  have h2 : stk.length + 2 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = 0 := by
    rw [Challenge.EvmProof.Word.literal_eq_ofNat]
    rfl
  simp (config := { maxSteps := 400000 }) (discharger := omega)
    [stub1, returned, written, atState, runInstrSeq, DataStepper.runInstr,
      State.activeWordsAfterUInt256, hrun,
      h0, h1, h2, if_pos h0, if_pos h1, if_pos h2, toNat_zero, toNat_32, hzero,
      List.length_cons, Nat.add_assoc,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

def stub2 : List Instr := [
  .op .JUMPDEST,
  .push ⟨20, by decide⟩ push2,
  .push ⟨0, by decide⟩ (UInt256.ofNat 0),
  .op .MSTORE,
  .push ⟨1, by decide⟩ (UInt256.ofNat 32),
  .push ⟨0, by decide⟩ (UInt256.ofNat 0),
  .op .RETURN]

theorem run_stub2 (s : State) (hrun : s.halt = .Running) (stk : List UInt256)
    (hlen : stk.length + 2 < 1024) :
    runInstrSeq stub2 (atState s 9848 stk) = some (returned s stk push2 9875) := by
  have h0 : stk.length < 1024 := by omega
  have h1 : stk.length + 1 < 1024 := by omega
  have h2 : stk.length + 2 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = 0 := by
    rw [Challenge.EvmProof.Word.literal_eq_ofNat]
    rfl
  simp (config := { maxSteps := 400000 }) (discharger := omega)
    [stub2, returned, written, atState, runInstrSeq, DataStepper.runInstr,
      State.activeWordsAfterUInt256, hrun,
      h0, h1, h2, if_pos h0, if_pos h1, if_pos h2, toNat_zero, toNat_32, hzero,
      List.length_cons, Nat.add_assoc,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32Return
