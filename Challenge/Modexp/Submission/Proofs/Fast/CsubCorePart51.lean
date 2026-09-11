import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart50

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

theorem readPadded_mcopy (memory : ByteArray) (src dst sz i : Nat)
    (h : 32 * i + 32 ≤ sz) :
    MachineState.readPadded (MachineState.writeBytes memory
        (MachineState.readPadded memory src sz) dst) (dst + 32 * i) 32 =
      MachineState.readPadded memory (src + 32 * i) 32 := by
  apply ByteArray.ext_getElem
  · simp
  · intro k hk1 hk2
    have hk : k < 32 := by simpa using hk1
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hk1,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hk2,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hk, if_pos hk,
      MachineState.writeBytes_getElem?_getD,
      Challenge.EvmProof.Memory.readPadded_size,
      if_pos (show dst ≤ dst + 32 * i + k ∧ dst + 32 * i + k < dst + sz from
        ⟨by omega, by omega⟩),
      show dst + 32 * i + k - dst = 32 * i + k from by omega,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos (show 32 * i + k < sz from by omega)]
    simp only [Nat.add_assoc]

end Challenge.Modexp.Submission.Proofs.Fast.Csub
