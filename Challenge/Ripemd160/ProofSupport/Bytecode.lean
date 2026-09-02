import Challenge.EvmProof
import Challenge.Ripemd160.Spec
set_option warningAsError true

namespace Challenge.Ripemd160.ProofSupport.Bytecode

open EvmSemantics.EVM

/-- Direct small-step obligation for arbitrary RIPEMD-160 bytecode. -/
def DirectProof (code : ByteArray) : Prop :=
  Challenge.EvmProof.EventuallyEvaluates
    (Input := { calldata : ByteArray // CalldataFits calldata })
    (fun calldata gas => initialState code calldata.1 gas)
    (fun calldata => .returned (spec calldata.1))

theorem correct_of_directProof {code : ByteArray} (h : DirectProof code) :
    Correct code := by
  intro calldata hfit
  simpa using h.sound ⟨calldata, hfit⟩

end Challenge.Ripemd160.ProofSupport.Bytecode
