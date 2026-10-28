import Challenge.Ripemd160.Submission.Local20261028.PadBoundary0
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary1
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary2
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary3
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary4
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary5
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary6
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary7
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary8
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary9
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary10
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary11
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary12
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary13
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary14
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary15
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary16
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary17
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary18
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary19
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary20
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary21
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary22
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary23
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary24
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary25
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary26
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary27
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary28
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary29
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary30
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary31
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary32
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary33
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary34
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary35
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary36
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary37
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary38
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary39
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary40
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary41
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary42
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary43
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary44
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary45
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary46
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary47
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary48
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary49
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary50
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary51
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary52
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary53
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary54
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary55
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary56
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary57
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary58
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary59
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary60
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary61
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary62
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary63
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary64
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary65
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary66
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary67
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary68
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary69
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary70
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary71
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary72
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary73
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary74
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary75
import Challenge.Ripemd160.Submission.Local20261028.PadBoundary76
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open PairedLaneUInt256Bridge Paired144WordRound StackRoundTrace PadCommon
theorem step (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162)
    (i : Fin 77) :
    runInstrSeq (templates i.val) (state s len h4 right rho i.val q) =
      some (state s len h4 right rho (i.val+1) (StaggerModeSeven.step i.val (PadModel.message len i.val) q)) := by
  fin_cases i
  · exact boundary0 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary1 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary2 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary3 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary4 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary5 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary6 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary7 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary8 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary9 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary10 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary11 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary12 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary13 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary14 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary15 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary16 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary17 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary18 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary19 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary20 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary21 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary22 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary23 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary24 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary25 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary26 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary27 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary28 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary29 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary30 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary31 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary32 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary33 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary34 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary35 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary36 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary37 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary38 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary39 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary40 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary41 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary42 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary43 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary44 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary45 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary46 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary47 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary48 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary49 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary50 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary51 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary52 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary53 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary54 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary55 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary56 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary57 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary58 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary59 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary60 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary61 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary62 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary63 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary64 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary65 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary66 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary67 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary68 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary69 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary70 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary71 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary72 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary73 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary74 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary75 s len h4 q right rho hstack hrun hactive hcal hmem
  · exact boundary76 s len h4 q right rho hstack hrun hactive hcal hmem

def block : Nat → List Instr
  | 0 => []
  | n+1 => block n ++ (templates n)

theorem run_block (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162)
    (n : Nat) (hn : n ≤ 77) :
    runInstrSeq (block n) (state s len h4 right rho 0 q) =
      some (state s len h4 right rho n (StaggerModeSeven.fold (PadModel.message len) n q)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 := ih (by omega)
    have h2 := step s len h4 (StaggerModeSeven.fold (PadModel.message len) n q) right rho
      hstack hrun hactive hcal hmem ⟨n,by omega⟩
    exact DenseScheduleTrace.runInstrSeq_append_running h1 hrun h2

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 4738).take (7964-4738) =
      PcEncoding.assembleBytes (block 77) := by
  rw [RipemdSubmissionTables20261028.CandidateBytes.exact_list]
  change (RipemdSubmissionTables20261028.CandidateBytes.bytes.drop (4736+2)).take (7964-4738) = _
  rw [← List.drop_drop, RipemdSubmissionTables20261028.CandidateBytes.drop74]
  decide +kernel
#print axioms step
#print axioms run_block
#print axioms exact_bytes
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
