import Challenge.Modexp.Submission.Proofs.Fast.TnCacheStoreAt
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheProductTrace
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheFrameOps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheRowTrace
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore
open CiosReadonly CiosCachedMidMemory

def middle : List Instr := TnCacheStoreAt.middle ++ TnCacheProductTrace.cachedProduct
/-- P1: the eight-limb head keeps the carry cache in the fifteenth word below the carry. -/
def middle8 : List Instr := TnCacheStoreAt.middle15 ++ TnCacheProductTrace.cachedProduct8
/-- The four-limb multiply head copy at 5494 (P1a: the inverse is the thirteenth cache word). -/
def middle4 : List Instr := TnCacheStoreAt.middle14 ++ TnCacheProductTrace.cachedProduct4
def tailShort : List Instr := TnCacheStoreAt.tail ++ TnCacheFrameOps.advanceShort

/-- P1: the row tail reads and writes the carry cache in the thirteenth frame word. -/
def tail : List Instr := TnCacheStoreAt.tail16 ++ TnCacheFrameOps.advance

theorem run_middle8 (pc0 : Nat) (s : State)
    (c bi pbi hd pb ent tn target tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : ReadonlyCache s.memory 8 tl inv m0)
    (hminv : inverseInvariant s.memory 8) :
    runInstructions middle8
      (framed s (UInt256.ofNat pc0)
        ([c,bi,pbi,hd,pb,ent,m32,allOnes,target,m64,m0,tl,m96,inv,tn,aEnd,dst,ret] ++ rest)) =
    some (framed s (UInt256.ofNat (pc0+23))
      ([rowC0 s.memory 8,rowMu s.memory 8,UInt256.lt (tn+c) c,
        pbi,hd,pb,ent,m32,allOnes,target,m64,m0,tl,m96,inv,tn+c,aEnd,dst,ret] ++ rest)) := by
  have hs := TnCacheStoreAt.run_middle15 pc0 s c bi pbi hd pb ent m32 target m64 m0 tl m96 inv tn
    (aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega)
  have hp := TnCacheProductTrace.run_cachedProduct8_model (pc0+7) s
    (UInt256.lt (tn+c) c) pbi hd pb ent m32 target tl inv m0 aEnd m96 m64 (tn+c) dst ret
    rest hcap hact hc hminv
  have both := runInstructions_append_some _ _ _ _ _ hs hp
  simpa only [middle8, TnCacheProductTrace.cacheStack, List.cons_append, List.nil_append,
    Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] using both

theorem run_middle4 (pc0 : Nat) (s : State)
    (c pbi hd pb ent tn target tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n = 4)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : ReadonlyCache s.memory n tl inv m0)
    (hm0 : m0 = MachineState.readWord s.memory (32*n-32))
    (hminv : inverseInvariant s.memory n) :
    runInstructions middle4
      (framed s (UInt256.ofNat pc0)
        ([c,pbi,hd,pb,ent,m32,allOnes,target,m64,m0,tl,m96,inv,tn,aEnd,dst,ret] ++ rest)) =
    some (framed s (UInt256.ofNat (pc0+21))
      ([rowC0 s.memory n,rowMu s.memory n,UInt256.lt (tn+c) c,
        pbi,hd,pb,ent,m32,allOnes,target,m64,m0,tl,m96,inv,tn+c,aEnd,dst,ret] ++ rest)) := by
  have hs := TnCacheStoreAt.run_middle14 pc0 s c pbi hd pb ent m32 target m64 m0 tl m96 inv tn
    (aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega)
  have hp := TnCacheProductTrace.run_cachedProduct4_model (pc0+5) s
    (UInt256.lt (tn+c) c) pbi hd pb ent m32 target tl inv m0 aEnd m96 m64 (tn+c) dst ret
    n rest hcap hn hact hc hm0 hminv
  have both := runInstructions_append_some _ _ _ _ _ hs hp
  simpa only [middle4, TnCacheProductTrace.cacheStack, List.cons_append, List.nil_append,
    Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] using both

theorem run_tail (pc0 : Nat) (s : State)
    (c f pbi hd pb ent w5 target w8 r0 r1 r2 r3 tn : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1001) (hact : 88 ≤ s.activeWords.toNat)
    (htarget : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    runInstructions tail
      (framed s (UInt256.ofNat pc0)
        ([c,f,pbi,hd,pb,ent,w5,allOnes,target,w8,r0,r1,r2,r3,tn] ++ rest)) =
    some (framed {s with memory := TnCacheMemory.put s.memory (tn+c) 2112}
      (if UInt256.isTrue (UInt256.ofNat 32+pbi) then hd else UInt256.ofNat (pc0+18))
      (TnCacheFrameOps.frame (UInt256.ofNat 32+pbi) hd pb ent w5 target w8
        (r0 :: r1 :: r2 :: r3 :: (UInt256.lt (tn+c) c+f) :: rest))) := by
  have hs := TnCacheStoreAt.run_tail16 pc0 s c f pbi hd pb ent w5 target w8 r0 r1 r2 r3 tn rest hcap hact
  have ha := TnCacheFrameOps.run_advance (pc0+12)
    {s with memory := TnCacheMemory.put s.memory (tn+c) 2112}
    pbi hd pb ent w5 target w8 (r0 :: r1 :: r2 :: r3 :: (UInt256.lt (tn+c) c+f) :: rest)
    (by simp only [List.length_cons]; omega) htarget
  have both := runInstructions_append_some _ _ _ _ _ hs ha
  simpa only [tail, TnCacheMemory.put, TnCacheFrameOps.frame, List.cons_append, List.nil_append,
    Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] using both

theorem run_tailShort (pc0 : Nat) (s : State)
    (c f pbi hd pb ent tn target inv : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat)
    (htarget : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    runInstructions tailShort
      (framed s (UInt256.ofNat pc0)
        ([c,f,pbi,hd,pb,ent,tn,allOnes,target,inv] ++ rest)) =
    some (framed {s with memory := TnCacheMemory.put s.memory (tn+c) 2112}
      (if UInt256.isTrue (UInt256.gt (negative32+pbi) pb) then hd else UInt256.ofNat (pc0+21))
      (TnCacheFrameOps.frame (negative32+pbi) hd pb ent (UInt256.lt (tn+c) c+f) target inv rest)) := by
  have hs := TnCacheStoreAt.run_tail pc0 s c f pbi hd pb ent tn target inv rest hcap hact
  have ha := TnCacheFrameOps.run_advanceShort (pc0+12)
    {s with memory := TnCacheMemory.put s.memory (tn+c) 2112}
    pbi hd pb ent (UInt256.lt (tn+c) c+f) target inv rest hcap htarget
  have both := runInstructions_append_some _ _ _ _ _ hs ha
  simpa only [tailShort, TnCacheMemory.put, TnCacheFrameOps.frame, List.cons_append, List.nil_append,
    Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] using both

#print axioms run_middle8
#print axioms run_middle4
#print axioms run_tail
#print axioms run_tailShort
end Challenge.Modexp.Submission.Proofs.Fast.TnCacheRowTrace
