import Challenge.Modexp.Submission.Proofs.Fast.TnCacheFirstTrace
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheL1Trace
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheFrameOps

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheHeadTrace
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCachedMacCore CiosReadonly

def load : List Instr := [.op .JUMPDEST, .op (.Dup ⟨0, by decide⟩), .op .MLOAD]
def dispatch : List Instr := [.op (.Dup ⟨5, by decide⟩), .op .JUMP]
def program : List Instr := (load ++ commonFirstProgram) ++ dispatch

theorem run_head (s : State) (pc pa n : Nat)
    (pbi hd pb ent tn target tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : 1 ≤ n ∧ n ≤ 8)
    (hact : 88 ≤ s.activeWords.toNat) (hpbi : pbi.toNat ≤ 2784)
    (hpa : pa+32*n ≤ 2048 ∨ pa = 2368)
    (ha : aEnd.toNat = pa+32*(n-1)) (ht : tl.toNat = 2112+32*(n-1))
    (hj : Decode.isValidJumpDest s.executionEnv.code ent.toNat = true) :
    runInstructions program
      (framed s (UInt256.ofNat pc)
        (TnCacheFrameOps.frame pbi hd pb ent tn target inv
          (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) =
    some (TnCacheL1Trace.qState s ent
      (l1Step s.memory (MachineState.readWord s.memory pbi.toNat) pa n 1)
      (MachineState.readWord s.memory pbi.toNat) pbi hd pb ent tn target inv
      (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  let bi := MachineState.readWord s.memory pbi.toNat
  let q := l1Step s.memory bi pa n 1
  let tail := m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest
  have hc16 : rest.length+16 < 1024 := by omega
  have hc17 : rest.length+17 < 1024 := by omega
  have hc18 : rest.length+18 < 1024 := by omega
  have hc19 : rest.length+19 < 1024 := by omega
  have hp := activeWords_fix s pbi.toNat 32 (by decide) (by omega) hact
  have hA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat aEnd.toNat 32) =
      s.activeWords := by
    apply activeWords_fix s _ 32 (by decide) _ hact
    rcases hpa with hpa | rfl <;> omega
  have hT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tl.toNat 32) =
      s.activeWords := activeWords_fix s _ 32 (by decide) (by omega) hact
  have hl : runInstructions load
      (framed s (UInt256.ofNat pc) (TnCacheFrameOps.frame pbi hd pb ent tn target inv tail)) =
      some (framed s (UInt256.ofNat (pc+3))
        ([bi] ++ TnCacheFirstTrace.tail pbi hd pb ent tn target tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
    simp [load, runInstructions, Challenge.EvmProof.Stepper.runInstr, framed,
      TnCacheFrameOps.frame, TnCacheFirstTrace.tail, tail, bi, hc16, hc17,
      State.activeWordsAfterUInt256, hp, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]
  have hf := TnCacheFirstTrace.run_first (pc+3) s bi pbi hd pb ent tn target tl inv m0
    aEnd m96 m64 m32 dst ret rest hcap hA hT
  have hf' : runInstructions commonFirstProgram
      (framed s (UInt256.ofNat (pc+3))
        ([bi] ++ TnCacheFirstTrace.tail pbi hd pb ent tn target tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
      some (TnCacheL1Trace.qState s (UInt256.ofNat (pc+27)) q bi
        pbi hd pb ent tn target inv tail) := by
    simpa only [TnCacheL1Trace.qState, q, l1Step, Nat.sub_zero, ha, ht,
      framed, TnCacheFirstTrace.tail, tail, List.cons_append, List.nil_append,
      Nat.add_assoc, Nat.reduceAdd] using hf
  have hjump : runInstructions dispatch
      (TnCacheL1Trace.qState s (UInt256.ofNat (pc+27)) q bi
        pbi hd pb ent tn target inv tail) =
      some (TnCacheL1Trace.qState s ent q bi pbi hd pb ent tn target inv tail) := by
    simp [dispatch, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      TnCacheL1Trace.qState, tail, hc18, hc19, hj]
  have first := runInstructions_append_some _ _ _ _ _ hl hf'
  exact runInstructions_append_some _ _ _ _ _ first hjump

#print axioms run_head
end Challenge.Modexp.Submission.Proofs.Fast.TnCacheHeadTrace
