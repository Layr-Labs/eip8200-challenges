import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreComposed

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-! Artifact-independent execution of the unchanged outer guards, with an
arbitrary stack frame and environment. The installed submission is unchanged. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreEntryRaw
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTrace StackRoundTemplate

def mask : UInt256 := UInt256.ofNat 0x108c86821c
def condition (input : ByteArray) : UInt256 :=
  UInt256.land (MachineState.readWord input 0) mask

/-- The initial mask is only a reject-to-generic filter, never a digest shortcut. -/
def filterTemplate : List Instr :=
  [.push ⟨5, by decide⟩ mask, .push ⟨0, by decide⟩ 0,
   .op .CALLDATALOAD, .op .AND, .push ⟨1, by decide⟩ 245, .op .JUMPI]

def sizeTemplate : List Instr :=
  [.op .CALLDATASIZE, .push ⟨2, by decide⟩ 1000, .op .SUB,
   .push ⟨2, by decide⟩ 4565, .op .JUMPI]

theorem run_filter_fall (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 976) (hrun : s.halt = .Running)
    (hc : condition s.executionEnv.calldata = 0) :
    runInstrSeq filterTemplate {s with pc := 0, stack := rho} =
      some {s with pc := UInt256.ofNat 12, stack := rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [filterTemplate, runInstrSeq, DataStepper.runInstr,
    hrun, show rho.length < 1024 by omega, hcap, UInt256.succ, Nat.add_assoc,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat,
    show UInt256.land (MachineState.readWord s.executionEnv.calldata 0) mask = 0 from hc, UInt256.isTrue]
  repeat first | apply And.intro | rfl

theorem run_size_fall (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 976) (hrun : s.halt = .Running)
    (hsize : s.executionEnv.calldata.size = 1000) :
    runInstrSeq sizeTemplate {s with pc := UInt256.ofNat 12, stack := rho} =
      some {s with pc := UInt256.ofNat 21, stack := rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [sizeTemplate, runInstrSeq, DataStepper.runInstr,
    hrun, show rho.length < 1024 by omega, hcap, UInt256.succ, Nat.add_assoc,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat, hsize, UInt256.isTrue,
    UInt256.sub]
  repeat first | apply And.intro | rfl

#print axioms run_filter_fall
#print axioms run_size_fall
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreEntryRaw
