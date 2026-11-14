import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
import Challenge.Modexp.Submission.Proofs.Fast.Exp
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.R5.ExecSquare
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.EvmProof.Word (succ_ofNat_mod ofNat_add_mod ofNat_sub_ofNat literal_eq_ofNat)
open Challenge.EvmProof.Stepper (runInstr)
open Challenge.Modexp.Submission.Proofs.Fast.Exp (activeWords_fix)
theorem fusePair (a b c : UInt256) :
    ((b + a) + (b + a)) + c = (b + b) + ((a + a) + c) := by
  apply Challenge.EvmProof.Word.word_ext
  simp only [Challenge.EvmProof.Word.word_toNat_add]
  omega
def sqCol0_o0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (UInt256.shiftRight (inv * (a0 * a0)) (UInt256.ofNat 16)) n0 P) + (UInt256.mulMod a0 a0 P)) P)
def sqCol0_o1 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  (UInt256.shiftRight (inv * (a0 * a0)) (UInt256.ofNat 16))
def sqCol1_o0 (c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (UInt256.shiftRight (inv * ((q0 * n1) + (((x0 * x1) + (x0 * x1)) + c))) (UInt256.ofNat 16)) n0 P) + ((UInt256.mulMod q0 n1 P) + (((UInt256.mulMod x0 x1 P) + (UInt256.mulMod x0 x1 P)) + c))) P)
def sqCol1_o1 (c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  (UInt256.shiftRight (inv * ((q0 * n1) + (((x0 * x1) + (x0 * x1)) + c))) (UInt256.ofNat 16))
def sqCol2_o0 (c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (UInt256.shiftRight (inv * ((q1 * n1) + ((q0 * n2) + ((x1 * x1) + (((x0 * x2) + (x0 * x2)) + c))))) (UInt256.ofNat 16)) n0 P) + ((UInt256.mulMod q1 n1 P) + ((UInt256.mulMod q0 n2 P) + ((UInt256.mulMod x1 x1 P) + (((UInt256.mulMod x0 x2 P) + (UInt256.mulMod x0 x2 P)) + c))))) P)
def sqCol2_o1 (c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  (UInt256.shiftRight (inv * ((q1 * n1) + ((q0 * n2) + ((x1 * x1) + (((x0 * x2) + (x0 * x2)) + c))))) (UInt256.ofNat 16))
def sqCol3_o0 (c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (UInt256.shiftRight (inv * ((q2 * n1) + ((q1 * n2) + ((q0 * n3) + ((((x1 * x2) + (x0 * x3)) + ((x1 * x2) + (x0 * x3))) + c))))) (UInt256.ofNat 16)) n0 P) + ((UInt256.mulMod q2 n1 P) + ((UInt256.mulMod q1 n2 P) + ((UInt256.mulMod q0 n3 P) + ((((UInt256.mulMod x1 x2 P) + (UInt256.mulMod x0 x3 P)) + ((UInt256.mulMod x1 x2 P) + (UInt256.mulMod x0 x3 P))) + c))))) P)
def sqCol3_o1 (c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  (UInt256.shiftRight (inv * ((q2 * n1) + ((q1 * n2) + ((q0 * n3) + ((((x1 * x2) + (x0 * x3)) + ((x1 * x2) + (x0 * x3))) + c))))) (UInt256.ofNat 16))
def sqCol4_o0 (c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (UInt256.shiftRight (inv * ((q3 * n1) + ((q2 * n2) + ((q1 * n3) + ((q0 * n4) + ((x2 * x2) + (((x1 * x3) + (x1 * x3)) + (((x0 * x4) + (x0 * x4)) + c)))))))) (UInt256.ofNat 16)) n0 P) + ((UInt256.mulMod q3 n1 P) + ((UInt256.mulMod q2 n2 P) + ((UInt256.mulMod q1 n3 P) + ((UInt256.mulMod q0 n4 P) + ((UInt256.mulMod x2 x2 P) + (((UInt256.mulMod x1 x3 P) + (UInt256.mulMod x1 x3 P)) + (((UInt256.mulMod x0 x4 P) + (UInt256.mulMod x0 x4 P)) + c)))))))) P)
def sqCol4_o4 (c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  (UInt256.shiftRight (inv * ((q3 * n1) + ((q2 * n2) + ((q1 * n3) + ((q0 * n4) + ((x2 * x2) + (((x1 * x3) + (x1 * x3)) + (((x0 * x4) + (x0 * x4)) + c)))))))) (UInt256.ofNat 16))
def sqCol5_o0 (c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : UInt256 :=
  (UInt256.mulMod (P + (((UInt256.mulMod q4 n1 P) + ((UInt256.mulMod q3 n2 P) + ((UInt256.mulMod q2 n3 P) + ((UInt256.mulMod q1 n4 P) + (((UInt256.mulMod x2 x3 P) + (UInt256.mulMod x2 x3 P)) + (((UInt256.mulMod x1 x4 P) + (UInt256.mulMod x1 x4 P)) + c)))))) - (UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) ((q4 * n1) + ((q3 * n2) + ((q2 * n3) + ((q1 * n4) + (((x2 * x3) + (x2 * x3)) + (((x1 * x4) + (x1 * x4)) + c))))))))) (UInt256.ofNat 2048) P)
def sqCol5_o5 (c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : UInt256 :=
  (UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) ((q4 * n1) + ((q3 * n2) + ((q2 * n3) + ((q1 * n4) + (((x2 * x3) + (x2 * x3)) + (((x1 * x4) + (x1 * x4)) + c)))))))
def sqCol6_o0 (c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : UInt256 :=
  (UInt256.mulMod (P + (((UInt256.mulMod q4 n2 P) + ((UInt256.mulMod q3 n3 P) + ((UInt256.mulMod q2 n4 P) + ((UInt256.mulMod x3 x3 P) + (((UInt256.mulMod x2 x4 P) + (UInt256.mulMod x2 x4 P)) + c))))) - (UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) ((q4 * n2) + ((q3 * n3) + ((q2 * n4) + ((x3 * x3) + (((x2 * x4) + (x2 * x4)) + c)))))))) (UInt256.ofNat 2048) P)
def sqCol6_o6 (c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : UInt256 :=
  (UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) ((q4 * n2) + ((q3 * n3) + ((q2 * n4) + ((x3 * x3) + (((x2 * x4) + (x2 * x4)) + c))))))
def sqCol7_o0 (c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : UInt256 :=
  (UInt256.mulMod (P + (((UInt256.mulMod q4 n3 P) + ((UInt256.mulMod q3 n4 P) + (((UInt256.mulMod x3 x4 P) + (UInt256.mulMod x3 x4 P)) + c))) - (UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) ((q4 * n3) + ((q3 * n4) + (((x3 * x4) + (x3 * x4)) + c)))))) (UInt256.ofNat 2048) P)
def sqCol7_o7 (c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : UInt256 :=
  (UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) ((q4 * n3) + ((q3 * n4) + (((x3 * x4) + (x3 * x4)) + c))))
def sqCol8_o0 (c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : UInt256 :=
  (UInt256.mulMod (P + (((UInt256.mulMod q4 n4 P) + ((UInt256.mulMod x4 x4 P) + c)) - (UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) ((q4 * n4) + ((x4 * x4) + c))))) (UInt256.ofNat 2048) P)
def sqCol8_o8 (c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : UInt256 :=
  (UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) ((q4 * n4) + ((x4 * x4) + c)))
def sqTail_o12 (c q3 q2 q1 q4 z0 z1 z2 z3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : UInt256 :=
  (cnt - (UInt256.ofNat 1))
end CycleSubmission.R5.ExecSquare
