import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate4
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate5
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate6
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate7
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate8
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate9
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate10
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate11
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate12
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate13
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate14
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableUpdate15
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableFinish

set_option warningAsError true

/-!
# Complete fixed-width lookup-table construction

The table build is composed exclusively from opaque one-slot certificates.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableBuild

open EvmSemantics
open EvmSemantics.EVM
open WindowControlDefs
open WindowHitStates

def gasSteps_tableBuild (input : ByteArray) (hmodulus : modulusWord input ≠ 0) :
    Challenge.EvmProof.GasSteps (hitState input)
      (loopState input 128 (UInt256.ofNat 1)) := by
  let h0 := WindowHitTableEntry.gasSteps_modulusNonzero input hmodulus
  let h1 := h0.trans (WindowHitTableEntry.gasSteps_tablePrelude input)
  let h2 := h1.trans (WindowHitTableUpdate.gasSteps_table3 input)
  let h3 := h2.trans (WindowHitTableUpdate4.gasSteps_table4 input)
  let h4 := h3.trans (WindowHitTableUpdate5.gasSteps_table5 input)
  let h5 := h4.trans (WindowHitTableUpdate6.gasSteps_table6 input)
  let h6 := h5.trans (WindowHitTableUpdate7.gasSteps_table7 input)
  let h7 := h6.trans (WindowHitTableUpdate8.gasSteps_table8 input)
  let h8 := h7.trans (WindowHitTableUpdate9.gasSteps_table9 input)
  let h9 := h8.trans (WindowHitTableUpdate10.gasSteps_table10 input)
  let h10 := h9.trans (WindowHitTableUpdate11.gasSteps_table11 input)
  let h11 := h10.trans (WindowHitTableUpdate12.gasSteps_table12 input)
  let h12 := h11.trans (WindowHitTableUpdate13.gasSteps_table13 input)
  let h13 := h12.trans (WindowHitTableUpdate14.gasSteps_table14 input)
  let h14 := h13.trans (WindowHitTableUpdate15.gasSteps_table15 input)
  exact h14.trans (WindowHitTableFinish.gasSteps_tableFinish input)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableBuild

