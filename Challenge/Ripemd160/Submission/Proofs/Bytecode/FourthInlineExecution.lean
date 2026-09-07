import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCavitySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.FourthInlineCaps
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityFragmentCap

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FourthInlineExecution

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundTemplate CavityQuadGroup CavityFragmentChain
open CachedMaskQuadGroup CachedMaskParams CachedMaskCaps CachedMaskCavitySites

theorem first_end : left4Bridge1.push.pc = left4First.endPC := by rfl
theorem second_start : left4Second.startPC = left4Bridge1.destination.pc.succ := by rfl
theorem second_end : left4Bridge2.push.pc = left4Second.endPC := by rfl
theorem third_start : left4Third.startPC = left4Bridge2.destination.pc.succ := by rfl
theorem third_end : left4Bridge3.push.pc = left4Third.endPC := by rfl
theorem fourth_start : left4Fourth.startPC = left4Bridge3.destination.pc.succ := by rfl
theorem return_start : left4Return.push.pc = left4Fourth.endPC := by rfl

noncomputable def left4_core (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hfit : ∀ k, ((left 4) k).Fits s)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s left4First.startPC w (mask :: rho))
      (stateAt s left4Fourth.endPC (fourResult (left 4) s w) (mask :: rho)) := by
  have hwhole := run_leftCode 4 s left4First.startPC w rho hfit hstack hrun
  let result := stateAt s (pcAfter left4First.startPC (leftCode 4))
    (fourResult (left 4) s w) (mask :: rho)
  apply CavityFragmentCap.gasSteps_splice_cap
    ((leftCode 4).take 213) ((leftCode 4).drop 213)
    left4First left4Bridge1 first_end
    (fun i hi => left_advances 4 i (List.mem_of_mem_take hi))
    (fun i hi => left_advances 4 i (List.mem_of_mem_drop hi))
    (stateAt s left4First.startPC w (mask :: rho)) result
    (stateAt s left4Fourth.endPC (fourResult (left 4) s w) (mask :: rho))
    rfl (by simpa only [List.take_append_drop] using hwhole)
    (FourthInlineCaps.first_cap s left4First.startPC w rho hstack)
    hcode hfork hrun hnp
  intro middle hpc henv hrunMiddle hcapMiddle hraw
  let result2 := {result with pc := pcAfter middle.pc ((leftCode 4).drop 213)}
  have hraw2 :
      runInstrSeq (((leftCode 4).drop 213).take 97 ++ (leftCode 4).drop 310) middle =
        some result2 := by
    rw [FourthInlineCaps.second_split]
    exact hraw
  apply CavityFragmentCap.gasSteps_splice_cap
    (((leftCode 4).drop 213).take 97) ((leftCode 4).drop 310)
    left4Second left4Bridge2 second_end
    (fun i hi => left_advances 4 i (List.mem_of_mem_drop (List.mem_of_mem_take hi)))
    (fun i hi => left_advances 4 i (List.mem_of_mem_drop hi))
    middle result2
    (stateAt s left4Fourth.endPC (fourResult (left 4) s w) (mask :: rho))
    (hpc.trans second_start.symm) hraw2
    (FourthInlineCaps.second_cap middle hcapMiddle)
    (by rw [henv]; exact hcode)
    (by change middle.executionEnv.fork = .Osaka; rw [henv]; exact hfork)
    hrunMiddle (by rw [henv]; exact hnp)
  intro later hpcLater henvLater hrunLater hcapLater hrawLater
  have hraw3 :
      runInstrSeq (((leftCode 4).drop 310).take 54 ++ (leftCode 4).drop 364) later =
        some {result2 with pc := pcAfter later.pc ((leftCode 4).drop 310)} := by
    rw [FourthInlineCaps.third_split]
    exact hrawLater
  have g := gasSteps_twoPieces
    (((leftCode 4).drop 310).take 54) ((leftCode 4).drop 364)
    left4Third left4Fourth left4Bridge3 third_end fourth_start
    (fun i hi => left_advances 4 i (List.mem_of_mem_drop (List.mem_of_mem_take hi)))
    (fun i hi => left_advances 4 i (List.mem_of_mem_drop hi))
    later {result2 with pc := pcAfter later.pc ((leftCode 4).drop 310)}
    (hpcLater.trans third_start.symm) hraw3
    (FourthInlineCaps.third_cap later hcapLater)
    (by rw [henvLater, henv]; exact hcode)
    (by change later.executionEnv.fork = .Osaka; rw [henvLater, henv]; exact hfork)
    hrunLater (by rw [henvLater, henv]; exact hnp)
  exact g

noncomputable def left4_group (s : State) (w : Compression.EvmWorking)
    (rho : List UInt256) (hfit : ∀ k, ((left 4) k).Fits s)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = A.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s left4First.startPC w (mask :: rho))
      (stateAt s left4Return.destination.pc.succ (fourResult (left 4) s w) (mask :: rho)) := by
  have core := left4_core s w rho hfit hstack hrun hcode hfork hnp
  have hcap (work : Compression.EvmWorking) :
      ([work.a, work.b, work.c, work.d, work.e] ++ factor :: (mask :: rho)).length < 1023 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have ret := gasSteps_bridge left4Return s
    ([(fourResult (left 4) s w).a, (fourResult (left 4) s w).b,
      (fourResult (left 4) s w).c, (fourResult (left 4) s w).d,
      (fourResult (left 4) s w).e] ++ factor :: (mask :: rho))
    (hcap (fourResult (left 4) s w)) hcode hfork hrun hnp
  rw [return_start] at ret
  exact core.trans ret

#print axioms left4_core
#print axioms left4_group

end Challenge.Ripemd160.Submission.Proofs.Bytecode.FourthInlineExecution
