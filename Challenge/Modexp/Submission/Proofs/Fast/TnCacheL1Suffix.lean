import Challenge.Modexp.Submission.Proofs.Fast.TnCacheL1Chain
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedLast

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheL1Suffix
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareModel StagedOperand CiosCached CiosCachedMacCore
open TnCacheL1Trace

theorem program_eq (n j0 m i0 k : Nat)
    (hn : j0+k ≤ n) (hm : i0+k ≤ m) (he : n-j0 = m-i0) :
    TnCacheL1Chain.program n j0 k = TnCacheL1Chain.program m i0 k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hp := ih (by omega) (by omega)
      have ho : n-1-(j0+k) = m-1-(i0+k) := by omega
      simp only [TnCacheL1Chain.program, hp, ho]

def program (k : Nat) : List Instr :=
  TnCacheL1Chain.program 8 (8-k) k ++ [.op .JUMPDEST]

theorem run_suffix (s : State) (pc : Nat) (q : MacState) (bi : UInt256)
    (pa n j0 k : Nat) (pbi hd pbEnd flag tn destination returnPC : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hactive : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hk : j0+k = n)
    (hpa : pa+32*n ≤ 2048 ∨ pa = 2368) (hsnapshot : Snapshot q.memory pa n) :
    runInstructions (program k)
      (TnCacheL1Trace.qState s (UInt256.ofNat pc) q bi pbi hd pbEnd flag tn destination returnPC rest) =
    some (TnCacheL1Trace.qState s (UInt256.ofNat (pc+37*k+1)) (l1Run q bi pa n j0 k)
      bi pbi hd pbEnd flag tn destination returnPC rest) := by
  have chain := TnCacheL1Chain.run_chain s pc q bi pa n j0 k
    pbi hd pbEnd flag tn destination returnPC rest hcap hactive hn (by omega) hpa hsnapshot
  have hp := program_eq n j0 8 (8-k) k (by omega) (by omega) (by omega)
  rw [hp] at chain
  have hc : rest.length+10 < 1024 := by omega
  have hd : runInstructions [.op .JUMPDEST]
      (TnCacheL1Trace.qState s (UInt256.ofNat (pc+37*k)) (l1Run q bi pa n j0 k)
        bi pbi hd pbEnd flag tn destination returnPC rest) =
      some (TnCacheL1Trace.qState s (UInt256.ofNat (pc+37*k+1)) (l1Run q bi pa n j0 k)
        bi pbi hd pbEnd flag tn destination returnPC rest) := by
    simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, TnCacheL1Trace.qState, hc,
      Challenge.EvmProof.Word.succ_ofNat_mod]
  exact runInstructions_append_some _ _ _ _ _ chain hd

def l1LastEntry : List Instr :=
  [.op (.Dup ⟨7, by decide⟩), .push 2 2368, .op .MLOAD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op .MUL, .op (.Swap ⟨3, by decide⟩), .op .MULMOD]

def l1LastProgram : List Instr :=
  l1LastEntry ++ CiosCachedLast.restProgram 2112 2112

def qStateLast (template : State) (pc : UInt256) (q : MacState)
    (pbi hd pbEnd flag tn destination returnPC : UInt256) (rest : List UInt256) : State :=
  { template with
    pc := pc
    stack := [q.carry, pbi, hd, pbEnd, flag, tn, allOnes, destination, returnPC] ++ rest
    memory := q.memory }

theorem run_l1LastEntry (template : State) (pc carry bi pbi hd pbEnd flag tn destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat 2368 32) = template.activeWords) :
    runInstructions l1LastEntry
      (framed template pc
        ([carry, bi, pbi, hd, pbEnd, flag, tn, allOnes, destination, returnPC] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 10)
      ([UInt256.mulMod bi (MachineState.readWord template.memory 2368) maxWord, carry,
        bi * MachineState.readWord template.memory 2368,
        pbi, hd, pbEnd, flag, tn, allOnes, destination, returnPC] ++ rest)) := by
  have capacity (j : Nat) (hj : j ≤ 14) : rest.length + j < 1024 := by omega
  have hN : allOnes = maxWord := allOnes_value
  have hx : (2368 : UInt256).toNat = 2368 := by decide
  simp [runInstructions, l1LastEntry, framed, Challenge.EvmProof.Stepper.runInstr,
    capacity, Nat.add_assoc, State.activeWordsAfterUInt256, hx, hactive, hN,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc,
    List.exchange]

theorem run_l1Last (template : State) (pc : UInt256) (q : MacState)
    (bi : UInt256) (pa : Nat)
    (pbi hd pbEnd flag tn destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 88 ≤ template.activeWords.toNat)
    (hsnapshot : Snapshot q.memory pa 4) :
    runInstructions l1LastProgram
      (TnCacheL1Trace.qState template pc q bi pbi hd pbEnd flag tn destination returnPC rest) =
    some (qStateLast template (pc + UInt256.ofNat 35) (SquareModel.l1StepOn q bi pa 4 3)
      pbi hd pbEnd flag tn destination returnPC rest) := by
  have hsread : MachineState.readWord q.memory 2368 =
      MachineState.readWord q.memory (pa + 32*(4-1-3)) :=
    TnCacheL1Trace.snapshot_read q.memory pa 4 3 hsnapshot (by decide)
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      2368 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      2112 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  let st : State := { template with memory := q.memory }
  have hA : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat
      2368 32) = st.activeWords := by simpa only [st] using hactA
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat
      (2112 : UInt256).toNat 32) = st.activeWords := by
    simpa only [st, show (2112 : UInt256).toNat = 2112 from by decide] using hactT
  have hl := run_l1LastEntry st pc q.carry bi pbi hd pbEnd flag tn destination returnPC rest hrest hA
  rw [show MachineState.readWord st.memory 2368 =
    MachineState.readWord q.memory (pa + 32*(4-1-3)) from hsread] at hl
  have hf := CiosCachedLast.run_rest st (pc + UInt256.ofNat 10)
    (MachineState.readWord q.memory (pa + 32*(4-1-3))) bi q.carry 2112 2112
    ([pbi, hd, pbEnd, flag, tn, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT hT
  have hall := runInstructions_append_some _ _ _ _ _ hl hf
  have hpc : (pc + UInt256.ofNat 10) + UInt256.ofNat 25 =
      pc + UInt256.ofNat 35 := by
    simp [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  have ht2112 : (2112 : UInt256).toNat = 2112 + 32 * (4 - 1 - 3) := by decide
  simpa only [l1LastProgram, st, TnCacheL1Trace.qState, qStateLast, framed,
    SquareModel.l1StepOn, ht2112, hpc, List.cons_append, List.nil_append] using hall

def privateProgram3 : List Instr :=
  (TnCacheL1Trace.l1Program 64 2176 ++ TnCacheL1Trace.l1Program 32 2144) ++
    l1LastProgram

theorem run_private3 (s : State) (pc : Nat) (q : MacState) (bi : UInt256)
    (pa : Nat) (pbi hd pbEnd flag tn destination returnPC : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hactive : 88 ≤ s.activeWords.toNat)
    (hpa : pa+32*4 ≤ 2048 ∨ pa = 2368) (hsnapshot : Snapshot q.memory pa 4) :
    runInstructions privateProgram3
      (TnCacheL1Trace.qState s (UInt256.ofNat pc) q bi pbi hd pbEnd flag tn destination returnPC rest) =
    some (qStateLast s (UInt256.ofNat (pc+107)) (l1Run q bi pa 4 1 3)
      pbi hd pbEnd flag tn destination returnPC rest) := by
  have hs0 : Snapshot (l1Run q bi pa 4 1 0).memory pa 4 := hsnapshot
  have hs1 : Snapshot (l1Run q bi pa 4 1 1).memory pa 4 :=
    TnCacheL1Chain.snapshot_l1Run_pres hsnapshot bi 1 (by decide) hpa 1 (by decide)
  have hs2 : Snapshot (l1Run q bi pa 4 1 2).memory pa 4 :=
    TnCacheL1Chain.snapshot_l1Run_pres hsnapshot bi 1 (by decide) hpa 2 (by decide)
  have c0 := TnCacheL1Trace.run_l1 s (UInt256.ofNat pc) (l1Run q bi pa 4 1 0)
    bi pa 4 1 64 2176 (by decide) (by decide) pbi hd pbEnd flag tn destination returnPC
    rest hcap hactive (by decide) (by decide) hs0
  have c1 := TnCacheL1Trace.run_l1 s (UInt256.ofNat (pc+36)) (l1Run q bi pa 4 1 1)
    bi pa 4 2 32 2144 (by decide) (by decide) pbi hd pbEnd flag tn destination returnPC
    rest hcap hactive (by decide) (by decide) hs1
  have c2 := run_l1Last s (UInt256.ofNat (pc+72)) (l1Run q bi pa 4 1 2)
    bi pa pbi hd pbEnd flag tn destination returnPC
    rest hcap hactive hs2
  simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, Nat.reduceAdd] at c0 c1 c2
  have c01 := runInstructions_append_some _ _ _ _ _ c0 c1
  have c012 := runInstructions_append_some _ _ _ _ _ c01 c2
  simpa only [privateProgram3, l1Run] using c012

end Challenge.Modexp.Submission.Proofs.Fast.TnCacheL1Suffix
