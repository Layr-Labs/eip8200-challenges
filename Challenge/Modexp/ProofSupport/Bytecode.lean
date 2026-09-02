import Challenge.EvmProof
import Challenge.Modexp.Spec
set_option warningAsError true

namespace Challenge.Modexp.ProofSupport.Bytecode

/-- Reusable direct small-step obligation for MODEXP bytecode. -/
def DirectProof (code : ByteArray) : Prop :=
  Challenge.EvmProof.EventuallyEvaluates
    (Input := { calldata : ByteArray // Challenge.Modexp.ValidInput calldata })
    (fun calldata gas => Challenge.Modexp.initialState code calldata.1 gas)
    (fun calldata => .returned (Challenge.Modexp.spec calldata.1))

theorem correct_of_directProof {code : ByteArray} (h : DirectProof code) :
    Challenge.Modexp.Correct code := by
  intro calldata hvalid
  simpa using h.sound ⟨calldata, hvalid⟩

end Challenge.Modexp.ProofSupport.Bytecode
