import Challenge.Modexp.Submission.Proofs.Prepared.R5CachedSquare
import Challenge.Modexp.Submission.Proofs.R5.ExecSquare
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.R5.SquareRun
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open CycleSubmission.R5.ExecSquare
def sqProgram : List Instr := CycleSubmission.Prepared.R5CachedSquare.newProgram
theorem sq_run (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h_n0 : MachineState.readWord s.memory 160 = n0)
    (h_inv : MachineState.readWord s.memory 192 = inv)
    (hP : P = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240) :
    runInstructions sqProgram {s with pc := UInt256.ofNat 8814,stack := a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::(MachineState.readWord s.memory 160)::cnt::rest} =
      some {s with pc := UInt256.ofNat 9433,stack := cnt::(sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)::(sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)::(sqV7_7 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)::(sqV8_8 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)::(sqV8_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)::n1::n2::n3::n4::P::inv::(MachineState.readWord s.memory 160)::(sqV9_12 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)::rest} := by
  exact CycleSubmission.Prepared.R5CachedSquare.new_run s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 rest
    hcap hact h_n0 h_inv hP ha0 ha1 ha2 ha3
#print axioms sq_run
end CycleSubmission.R5.SquareRun
