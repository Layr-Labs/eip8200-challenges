import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheL1
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheL2
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL1

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 400000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory

/-- The unchanged memory MAC accepts the larger cache frame as its caller tail. -/
theorem run_memoryL1Body (s : State) (pc : UInt256) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret pa t carry bi : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (ha : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat pa.toNat 32) = s.activeWords)
    (ht : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat t.toNat 32) = s.activeWords) :
    runInstructions (CiosCached.l1Body t)
      (framed s pc ([pa, carry, bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed
      { s with
        memory := MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded
            (macSum (MachineState.readWord s.memory pa.toNat) bi
              (MachineState.readWord s.memory t.toNat) carry).toNat 32) t.toNat }
      (pc + UInt256.ofNat 36)
      ([pa, macCarry (MachineState.readWord s.memory pa.toNat) bi
        (MachineState.readWord s.memory t.toNat) carry, bi] ++
        rowFrame c r pbi paEnd pbEnd flag dst ret rest)) := by
  let x := MachineState.readWord s.memory pa.toNat
  let v := MachineState.readWord s.memory t.toNat
  let frame := rowFrame c r pbi paEnd pbEnd flag dst ret rest
  let suffix := [c.t2, r.m0, r.z0, r.m32, r.inv, r.tl, dst, ret] ++ rest
  have hsuffix : suffix.length ≤ 1006 := by
    simp only [suffix, List.length_append, List.length_cons, List.length_nil]; omega
  have hrest : frame.length+7 < 1024 := by
    simp only [frame, rowFrame, cacheTail, List.length_append, List.length_cons, List.length_nil]; omega
  have h1 := CiosCachedL1.run_load s pc pa carry bi pbi paEnd pbEnd flag c.t0 c.t1 suffix hsuffix ha
  have h2 := L1.run_mac s (advancePC 3 pc) x bi carry pa t frame hrest ht
  have h3 := CiosCachedL1.run_store s
    (advancePC 6 (advancePC 18 (advancePC 3 pc) + UInt256.ofNat 5))
    (macSum x bi v carry) pa (macCarry x bi v carry) bi pbi paEnd pbEnd flag
    c.t0 c.t1 t suffix hsuffix ht
  have h12 := runInstructions_append_some _ _ _ _ _ h1 h2
  have h123 := runInstructions_append_some _ _ _ _ _ h12 h3
  simpa only [CiosCachedL1.body_eq, x, v, frame, suffix, rowFrame, cacheTail,
    advancePC, List.append_assoc, List.cons_append, List.nil_append, succ_eq_add,
    word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod] using h123

theorem run_memoryL2Body (s : State) (pc : UInt256) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret x tl ts carry mu bi : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hx : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat x.toNat 32) = s.activeWords)
    (htl : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tl.toNat 32) = s.activeWords)
    (hts : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat ts.toNat 32) = s.activeWords) :
    runInstructions (CiosCached.l2Program x tl ts)
      (framed s pc ([carry, mu, bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed
      { s with
        memory := MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded
            (macSum (MachineState.readWord s.memory x.toNat) mu
              (MachineState.readWord s.memory tl.toNat) carry).toNat 32) ts.toNat }
      (pc + UInt256.ofNat 38)
      ([macCarry (MachineState.readWord s.memory x.toNat) mu
        (MachineState.readWord s.memory tl.toNat) carry, mu, bi] ++
        rowFrame c r pbi paEnd pbEnd flag dst ret rest)) := by
  let v := MachineState.readWord s.memory x.toNat
  let t := MachineState.readWord s.memory tl.toNat
  let frame := rowFrame c r pbi paEnd pbEnd flag dst ret rest
  let suffix := [c.t2, r.m0, r.z0, r.m32, r.inv, r.tl, dst, ret] ++ rest
  have hsuffix : suffix.length ≤ 1006 := by
    simp only [suffix, List.length_append, List.length_cons, List.length_nil]; omega
  have hrest : ([bi] ++ frame).length+6 < 1024 := by
    simp only [frame, rowFrame, cacheTail, List.length_append, List.length_cons, List.length_nil]; omega
  have h1 := CiosCachedL2.run_load s pc x carry mu bi pbi paEnd pbEnd flag c.t0 c.t1 suffix hsuffix hx
  have h2 := L2.run_mac s (pc+UInt256.ofNat 5) v mu carry tl ([bi] ++ frame) hrest htl
  have h3 := CiosCachedL2.run_store s
    (advancePC 6 (advancePC 18 (pc+UInt256.ofNat 5) + UInt256.ofNat 5))
    (macSum v mu t carry) (macCarry v mu t carry) mu bi pbi paEnd pbEnd flag
    c.t0 c.t1 ts suffix hsuffix hts
  have h12 := runInstructions_append_some _ _ _ _ _ h1 h2
  have h123 := runInstructions_append_some _ _ _ _ _ h12 h3
  simpa only [CiosCachedL2.program_eq, v, t, frame, suffix, rowFrame, cacheTail,
    advancePC, List.append_assoc, List.cons_append, List.nil_append, succ_eq_add,
    word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod] using h123

theorem run_advance (s : State) (pc : UInt256) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret pa carry bi : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions CiosCachedL1.advanceProgram
      (framed s pc ([pa, carry, bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (advancePC 2 pc)
      ([CiosCached.negative32+pa, carry, bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) := by
  exact CiosCachedL1.run_advance s pc pa carry bi pbi paEnd pbEnd flag c.t0 c.t1
    ([c.t2, r.m0, r.z0, r.m32, r.inv, r.tl, dst, ret] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)

theorem run_drop (s : State) (pc : UInt256) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret pa carry bi : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions CiosCachedL1.dropProgram
      (framed s pc ([pa, carry, bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (advancePC 1 pc)
      ([carry, bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) := by
  exact CiosCachedL1.run_drop s pc pa carry bi pbi paEnd pbEnd flag c.t0 c.t1
    ([c.t2, r.m0, r.z0, r.m32, r.inv, r.tl, dst, ret] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.run_memoryL1Body
#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.run_memoryL2Body
