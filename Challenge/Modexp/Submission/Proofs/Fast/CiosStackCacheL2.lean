import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMacOps
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 400000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory

/-- The last two reduction MACs consume cached modulus and accumulator words. -/
def cachedL2Body (k : Fin 2) : List Instr :=
  (((sourceLoad2 k ++ L2.productProgram) ++ cacheLoad2 ⟨k.val, by omega⟩) ++
    L2.sumProgram) ++ cacheStore ⟨k.val+1, by omega⟩

theorem run_cachedL2Body (s : State) (pc : UInt256) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret : UInt256) (k : Fin 2) (carry mu bi : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions (cachedL2Body k)
      (framed s pc ([carry, mu, bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (advancePC 30 pc)
      ([macCarry (sourceWord r k) mu (word c ⟨k.val, by omega⟩) carry, mu, bi] ++
        rowFrame (c.write (addr ⟨k.val+1, by omega⟩)
          (macSum (sourceWord r k) mu (word c ⟨k.val, by omega⟩) carry))
          r pbi paEnd pbEnd flag dst ret rest)) := by
  let x := sourceWord r k
  let frame := rowFrame c r pbi paEnd pbEnd flag dst ret rest
  let kr : Fin 3 := ⟨k.val, by omega⟩
  let kw : Fin 3 := ⟨k.val+1, by omega⟩
  have hrest : ([bi] ++ frame).length+6 < 1024 := by
    simp only [frame, rowFrame, cacheTail, List.length_append, List.length_cons, List.length_nil]
    omega
  have h1 := run_sourceLoad2 s pc c r pbi paEnd pbEnd flag dst ret k carry mu bi rest hcap
  have h2 := L2.run_product s (advancePC 2 pc) x mu carry ([bi] ++ frame) hrest
  have h3 := run_cacheLoad2 s (advancePC 18 (advancePC 2 pc)) c r
    pbi paEnd pbEnd flag dst ret kr (partialCarry x mu carry) (x*mu+carry) mu bi rest hcap
  have h4 := L2.run_sum s (advancePC 2 (advancePC 18 (advancePC 2 pc)))
    (word c kr) (x*mu+carry) (partialCarry x mu carry) mu ([bi] ++ frame) hrest
  rw [carry_eq, sum_eq] at h4
  have h5 := run_cacheStore s (advancePC 6 (advancePC 2 (advancePC 18 (advancePC 2 pc))))
    c r pbi paEnd pbEnd flag dst ret kw (macSum x mu (word c kr) carry)
    (macCarry x mu (word c kr) carry) mu bi rest hcap
  have h12 := runInstructions_append_some _ _ _ _ _ h1 h2
  have h123 := runInstructions_append_some _ _ _ _ _ h12 h3
  have h1234 := runInstructions_append_some _ _ _ _ _ h123 h4
  have h12345 := runInstructions_append_some _ _ _ _ _ h1234 h5
  simpa only [cachedL2Body, x, frame, kr, kw, advancePC, List.append_assoc,
    List.cons_append, List.nil_append] using h12345

/-- The preceding reduction MAC reads the third cached accumulator word and
writes the first uncached word. -/
def partialL2Body (x ts : UInt256) : List Instr :=
  (((CiosCachedL2.loadProgram x ++ L2.productProgram) ++ cacheLoad2 ⟨2, by decide⟩) ++
    L2.sumProgram) ++ CiosCachedL2.storeProgram ts

theorem run_partialL2Body (s : State) (pc : UInt256) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret x ts carry mu bi : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hx : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat x.toNat 32) = s.activeWords)
    (ht : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat ts.toNat 32) = s.activeWords) :
    runInstructions (partialL2Body x ts)
      (framed s pc ([carry, mu, bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed
      { s with
        memory := MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded
            (macSum (MachineState.readWord s.memory x.toNat) mu c.t2 carry).toNat 32) ts.toNat }
      (pc + UInt256.ofNat 35)
      ([macCarry (MachineState.readWord s.memory x.toNat) mu c.t2 carry, mu, bi] ++
        rowFrame c r pbi paEnd pbEnd flag dst ret rest)) := by
  let v := MachineState.readWord s.memory x.toNat
  let frame := rowFrame c r pbi paEnd pbEnd flag dst ret rest
  let suffix := [c.t2, r.m0, r.z0, r.m32, r.inv, r.tl, dst, ret] ++ rest
  have hsuffix : suffix.length ≤ 1006 := by
    simp only [suffix, List.length_append, List.length_cons, List.length_nil]
    omega
  have hrest : ([bi] ++ frame).length+6 < 1024 := by
    simp only [frame, rowFrame, cacheTail, List.length_append, List.length_cons, List.length_nil]
    omega
  have h1 := CiosCachedL2.run_load s pc x carry mu bi pbi paEnd pbEnd flag
    c.t0 c.t1 suffix hsuffix hx
  have h2 := L2.run_product s (pc+UInt256.ofNat 5) v mu carry ([bi] ++ frame) hrest
  have h3 := run_cacheLoad2 s (advancePC 18 (pc+UInt256.ofNat 5)) c r
    pbi paEnd pbEnd flag dst ret ⟨2, by decide⟩ (partialCarry v mu carry) (v*mu+carry) mu bi rest hcap
  have h4 := L2.run_sum s (advancePC 2 (advancePC 18 (pc+UInt256.ofNat 5)))
    c.t2 (v*mu+carry) (partialCarry v mu carry) mu ([bi] ++ frame) hrest
  rw [carry_eq, sum_eq] at h4
  have h5 := CiosCachedL2.run_store s
    (advancePC 6 (advancePC 2 (advancePC 18 (pc+UInt256.ofNat 5))))
    (macSum v mu c.t2 carry) (macCarry v mu c.t2 carry) mu bi pbi paEnd pbEnd flag
    c.t0 c.t1 ts suffix hsuffix ht
  have h12 := runInstructions_append_some _ _ _ _ _ h1 h2
  have h123 := runInstructions_append_some _ _ _ _ _ h12 h3
  have h1234 := runInstructions_append_some _ _ _ _ _ h123 h4
  have h12345 := runInstructions_append_some _ _ _ _ _ h1234 h5
  simpa only [partialL2Body, v, frame, suffix, rowFrame, cacheTail, word, advancePC,
    List.append_assoc, List.cons_append, List.nil_append, succ_eq_add, word_add_assoc,
    Challenge.EvmProof.Word.ofNat_add_mod] using h12345

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.run_cachedL2Body
#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.run_partialL2Body
