import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary0
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary1
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary2
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary3
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary4
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary5
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary6
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary7
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary8
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary9
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary10
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary11
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary12
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary13
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary14
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary15
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary16
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary17
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary18
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary19
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary20
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary21
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary22
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary23
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary24
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary25
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary26
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary27
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary28
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary29
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary30
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary31
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary32
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary33
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary34
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary35
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary36
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary37
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary38
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary39
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary40
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary41
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary42
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary43
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary44
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary45
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary46
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary47
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary48
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary49
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary50
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary51
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary52
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary53
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary54
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary55
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary56
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary57
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary58
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary59
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary60
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary61
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary62
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary63
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary64
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary65
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary66
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary67
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary68
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary69
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary70
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary71
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary72
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary73
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary74
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary75
import Challenge.Ripemd160.Submission.Local20261028.RoundBoundary76
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open PairedLaneUInt256Bridge Paired144WordRound StackRoundTrace CoreCommon
theorem step (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (i : Fin 77) :
    runInstrSeq (templates i.val) (state s h4 right rho i.val q) =
      some (state s h4 right rho (i.val+1) (StaggerModeSeven.step i.val (CoreModel.message s.memory i.val) q)) := by
  fin_cases i
  · exact boundary0 s h4 q right rho hstack hrun hactive
  · exact boundary1 s h4 q right rho hstack hrun hactive
  · exact boundary2 s h4 q right rho hstack hrun hactive
  · exact boundary3 s h4 q right rho hstack hrun hactive
  · exact boundary4 s h4 q right rho hstack hrun hactive
  · exact boundary5 s h4 q right rho hstack hrun hactive
  · exact boundary6 s h4 q right rho hstack hrun hactive
  · exact boundary7 s h4 q right rho hstack hrun hactive
  · exact boundary8 s h4 q right rho hstack hrun hactive
  · exact boundary9 s h4 q right rho hstack hrun hactive
  · exact boundary10 s h4 q right rho hstack hrun hactive
  · exact boundary11 s h4 q right rho hstack hrun hactive
  · exact boundary12 s h4 q right rho hstack hrun hactive
  · exact boundary13 s h4 q right rho hstack hrun hactive
  · exact boundary14 s h4 q right rho hstack hrun hactive
  · exact boundary15 s h4 q right rho hstack hrun hactive
  · exact boundary16 s h4 q right rho hstack hrun hactive
  · exact boundary17 s h4 q right rho hstack hrun hactive
  · exact boundary18 s h4 q right rho hstack hrun hactive
  · exact boundary19 s h4 q right rho hstack hrun hactive
  · exact boundary20 s h4 q right rho hstack hrun hactive
  · exact boundary21 s h4 q right rho hstack hrun hactive
  · exact boundary22 s h4 q right rho hstack hrun hactive
  · exact boundary23 s h4 q right rho hstack hrun hactive
  · exact boundary24 s h4 q right rho hstack hrun hactive
  · exact boundary25 s h4 q right rho hstack hrun hactive
  · exact boundary26 s h4 q right rho hstack hrun hactive
  · exact boundary27 s h4 q right rho hstack hrun hactive
  · exact boundary28 s h4 q right rho hstack hrun hactive
  · exact boundary29 s h4 q right rho hstack hrun hactive
  · exact boundary30 s h4 q right rho hstack hrun hactive
  · exact boundary31 s h4 q right rho hstack hrun hactive
  · exact boundary32 s h4 q right rho hstack hrun hactive
  · exact boundary33 s h4 q right rho hstack hrun hactive
  · exact boundary34 s h4 q right rho hstack hrun hactive
  · exact boundary35 s h4 q right rho hstack hrun hactive
  · exact boundary36 s h4 q right rho hstack hrun hactive
  · exact boundary37 s h4 q right rho hstack hrun hactive
  · exact boundary38 s h4 q right rho hstack hrun hactive
  · exact boundary39 s h4 q right rho hstack hrun hactive
  · exact boundary40 s h4 q right rho hstack hrun hactive
  · exact boundary41 s h4 q right rho hstack hrun hactive
  · exact boundary42 s h4 q right rho hstack hrun hactive
  · exact boundary43 s h4 q right rho hstack hrun hactive
  · exact boundary44 s h4 q right rho hstack hrun hactive
  · exact boundary45 s h4 q right rho hstack hrun hactive
  · exact boundary46 s h4 q right rho hstack hrun hactive
  · exact boundary47 s h4 q right rho hstack hrun hactive
  · exact boundary48 s h4 q right rho hstack hrun hactive
  · exact boundary49 s h4 q right rho hstack hrun hactive
  · exact boundary50 s h4 q right rho hstack hrun hactive
  · exact boundary51 s h4 q right rho hstack hrun hactive
  · exact boundary52 s h4 q right rho hstack hrun hactive
  · exact boundary53 s h4 q right rho hstack hrun hactive
  · exact boundary54 s h4 q right rho hstack hrun hactive
  · exact boundary55 s h4 q right rho hstack hrun hactive
  · exact boundary56 s h4 q right rho hstack hrun hactive
  · exact boundary57 s h4 q right rho hstack hrun hactive
  · exact boundary58 s h4 q right rho hstack hrun hactive
  · exact boundary59 s h4 q right rho hstack hrun hactive
  · exact boundary60 s h4 q right rho hstack hrun hactive
  · exact boundary61 s h4 q right rho hstack hrun hactive
  · exact boundary62 s h4 q right rho hstack hrun hactive
  · exact boundary63 s h4 q right rho hstack hrun hactive
  · exact boundary64 s h4 q right rho hstack hrun hactive
  · exact boundary65 s h4 q right rho hstack hrun hactive
  · exact boundary66 s h4 q right rho hstack hrun hactive
  · exact boundary67 s h4 q right rho hstack hrun hactive
  · exact boundary68 s h4 q right rho hstack hrun hactive
  · exact boundary69 s h4 q right rho hstack hrun hactive
  · exact boundary70 s h4 q right rho hstack hrun hactive
  · exact boundary71 s h4 q right rho hstack hrun hactive
  · exact boundary72 s h4 q right rho hstack hrun hactive
  · exact boundary73 s h4 q right rho hstack hrun hactive
  · exact boundary74 s h4 q right rho hstack hrun hactive
  · exact boundary75 s h4 q right rho hstack hrun hactive
  · exact boundary76 s h4 q right rho hstack hrun hactive

def block : Nat → List Instr
  | 0 => []
  | n+1 => block n ++ (templates n)

theorem run_block (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (n : Nat) (hn : n ≤ 77) :
    runInstrSeq (block n) (state s h4 right rho 0 q) =
      some (state s h4 right rho n (StaggerModeSeven.fold (CoreModel.message s.memory) n q)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 := ih (by omega)
    have h2 := step s h4 (StaggerModeSeven.fold (CoreModel.message s.memory) n q) right rho
      hstack hrun hactive ⟨n,by omega⟩
    exact DenseScheduleTrace.runInstrSeq_append_running h1 hrun h2

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 1006).take (4441-1006) =
      PcEncoding.assembleBytes (block 77) := by
  rw [RipemdSubmissionTables20261028.CandidateBytes.exact_list]
  change (RipemdSubmissionTables20261028.CandidateBytes.bytes.drop (960+46)).take (4441-1006) = _
  rw [← List.drop_drop, RipemdSubmissionTables20261028.CandidateBytes.drop15]
  decide +kernel
#print axioms step
#print axioms run_block
#print axioms exact_bytes
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
