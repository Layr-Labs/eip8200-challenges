import Challenge.Modexp.Submission.Proofs.Prepared.R5CacheRaw
import Challenge.Modexp.Submission.Proofs.Prepared.R5Square
namespace R5LimbCacheBridge
open EvmSemantics EvmSemantics.EVM
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
def inject (pc count : Nat) (cached : UInt256) (s : State) : State :=
  {s with pc := UInt256.ofNat pc,stack := s.stack.take count++cached::s.stack.drop count}
theorem stage0_embedding (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 cached : UInt256) (rest : List UInt256)
    (hcache : MachineState.readWord s.memory 160 = cached) :
    R5LimbCacheRaw.stage0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 cached w11 rest =
      inject 8812 13 cached (NextR5Columns.stage0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 rest) := by
  simp [inject,R5LimbCacheRaw.stage0Model,NextR5Columns.stage0Model,hcache]
theorem stage1_embedding (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 cached : UInt256) (rest : List UInt256)
    (hcache : MachineState.readWord s.memory 160 = cached) :
    R5LimbCacheRaw.stage1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 cached w13 rest =
      inject 8848 14 cached (NextR5Columns.stage1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest) := by
  simp [inject,R5LimbCacheRaw.stage1Model,NextR5Columns.stage1Model,hcache]
theorem stage2_embedding (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 cached : UInt256) (rest : List UInt256)
    (hcache : MachineState.readWord s.memory 160 = cached) :
    R5LimbCacheRaw.stage2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 cached w14 rest =
      inject 8907 15 cached (NextR5Columns.stage2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  simp [inject,R5LimbCacheRaw.stage2Model,NextR5Columns.stage2Model,hcache]
theorem stage3_embedding (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 cached : UInt256) (rest : List UInt256)
    (hcache : MachineState.readWord s.memory 160 = cached) :
    R5LimbCacheRaw.stage3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 cached w15 rest =
      inject 8972 16 cached (NextR5Columns.stage3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  simp [inject,R5LimbCacheRaw.stage3Model,NextR5Columns.stage3Model,hcache]
theorem stage4_embedding (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 cached : UInt256) (rest : List UInt256)
    (hcache : MachineState.readWord s.memory 160 = cached) :
    R5LimbCacheRaw.stage4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 cached w16 rest =
      inject 9062 16 cached (NextR5Columns.stage4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  simp [inject,R5LimbCacheRaw.stage4Model,NextR5Columns.stage4Model,hcache]
theorem stage5_embedding (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 cached : UInt256) (rest : List UInt256)
    (hcache : MachineState.readWord s.memory 160 = cached) :
    R5LimbCacheRaw.stage5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 cached w16 rest =
      inject 9164 16 cached (NextR5Columns.stage5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  simp [inject,R5LimbCacheRaw.stage5Model,NextR5Columns.stage5Model,hcache]
theorem stage6_embedding (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 cached : UInt256) (rest : List UInt256)
    (hcache : MachineState.readWord s.memory 160 = cached) :
    R5LimbCacheRaw.stage6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 cached w16 rest =
      inject 9259 16 cached (NextR5Columns.stage6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  simp [inject,R5LimbCacheRaw.stage6Model,NextR5Columns.stage6Model,hcache]
theorem stage7_embedding (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 cached : UInt256) (rest : List UInt256)
    (hcache : MachineState.readWord s.memory 160 = cached) :
    R5LimbCacheRaw.stage7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 cached w16 rest =
      inject 9331 16 cached (NextR5Columns.stage7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  simp [inject,R5LimbCacheRaw.stage7Model,NextR5Columns.stage7Model,hcache]
theorem stage8_embedding (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 cached : UInt256) (rest : List UInt256)
    (hcache : MachineState.readWord s.memory 160 = cached) :
    R5LimbCacheRaw.stage8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 cached w16 rest =
      inject 9394 16 cached (NextR5Columns.stage8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  simp [inject,R5LimbCacheRaw.stage8Model,NextR5Columns.stage8Model,hcache]
theorem stage9_embedding (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 cached : UInt256) (rest : List UInt256)
    (hcache : MachineState.readWord s.memory 160 = cached) :
    R5LimbCacheRaw.stage9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 cached w16 rest =
      inject 9405 12 cached (NextR5Columns.stage9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  simp [inject,R5LimbCacheRaw.stage9Model,NextR5Columns.stage9Model,hcache]
end R5LimbCacheBridge
