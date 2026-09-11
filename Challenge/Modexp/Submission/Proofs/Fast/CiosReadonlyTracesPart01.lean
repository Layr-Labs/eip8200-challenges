import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedEntryBody
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidStore

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open CiosCachedMidMemory Monpro

theorem run_entry (s : State) (mem : ByteArray) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32*n-32)) :
    runInstructions fullEntryProgram (entryState s mem pa pb dst ret rest) =
    some (outState s (mpZeroed s mem n) pa pb n 0
      (MachineState.readWord mem 9376) (MachineState.readWord mem (32*n-32))
      (MachineState.readWord mem 9440 :: MachineState.readWord mem 96 :: MachineState.readWord mem 64 :: MachineState.readWord mem 32 :: UInt256.ofNat (pa+32*n-32) :: dst :: ret :: rest)) := by
  let tl := MachineState.readWord mem 9440
  let inv := MachineState.readWord mem 9376
  let m0 := MachineState.readWord mem (32*n-32)
  let aEnd := UInt256.ofNat (pa+32*n-32)
  let m96 := MachineState.readWord mem 96
  let m64 := MachineState.readWord mem 64
  let m32 := MachineState.readWord mem 32
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest).length ≤ 1005 := by simp only [List.length_cons]; omega
  have hc4 : rest.length+4 < 1024 := by omega
  have hc11 : rest.length+11 < 1024 := by omega
  have hlegacy := CiosCached.run_cache s mem pa pb n inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest) hcap' hact hs32
  have hskip : runInstructions [.op .JUMPDEST]
      (maskEntryState s mem pa pb inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (framed { s with memory := mem } (UInt256.ofNat 4195)
      ([UInt256.ofNat pa,UInt256.ofNat pb,inv,m0,tl,m96,m64,m32,aEnd,dst,ret] ++ rest)) := by
      simp only [runInstructions, Challenge.EvmProof.Stepper.runInstr, maskEntryState,
        entryState, framed, List.cons_append, List.nil_append, List.length_cons,
        Nat.add_assoc, Nat.reduceAdd, hc11, if_pos]
      rfl
  rw [show CiosCached.cacheProgram = [.op .JUMPDEST] ++ CiosCached.cacheProgram.drop 1 from rfl,
    runInstructions_append, hskip] at hlegacy
  have hstart : runInstructions [.op .JUMPDEST] (entryState s mem pa pb dst ret rest) =
    some (framed { s with memory := mem } (UInt256.ofNat 4164)
      ([UInt256.ofNat pa,UInt256.ofNat pb,dst,ret] ++ rest)) := by
      simp only [runInstructions, Challenge.EvmProof.Stepper.runInstr,
        entryState, framed, List.cons_append, List.nil_append, List.length_cons,
        Nat.add_assoc, Nat.reduceAdd, hc4, if_pos]
      rfl
  have hp := run_entryPrelude { s with memory := mem } (UInt256.ofNat pa)
    (UInt256.ofNat pb) dst ret n rest hcap hn32 hact hml
  have hAend : UInt256.ofNat pa + UInt256.ofNat (32*n-32) = aEnd := by
    dsimp [aEnd]
    rw [Challenge.EvmProof.Word.ofNat_add_mod]
    congr 1
    omega
  rw [hAend] at hp
  have hprefix := runInstructions_append_some _ _ _ _ _ hstart hp
  have hmasked := runInstructions_append_some _ _ _ _ _ hprefix hlegacy
  have hbody := CiosCached.run_entryBody s mem pa pb n inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest) hcap' hrun hact hn hn32 hpa hpaFit hpb hpbFit hcds hs32
  have hresult := runInstructions_append_some _ _ _ _ _ hmasked hbody
  have hprogram : fullEntryProgram =
      ((([.op .JUMPDEST] ++ entryPrelude) ++ CiosCached.cacheProgram.drop 1) ++
        CiosCached.entryBodyProgram) := by
    rfl
  exact (congrArg (fun program => runInstructions program
    (entryState s mem pa pb dst ret rest)) hprogram).trans hresult

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
