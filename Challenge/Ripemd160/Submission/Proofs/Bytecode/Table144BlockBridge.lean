import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144BlockModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144BootstrapPacking
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentTailSite
set_option warningAsError true
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144BlockBridge
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedLaneUInt256Bridge Paired144Core Paired144WordRound Paired144Algorithm Table144Prepare

theorem packed_hash (x : UInt32) :
    Table144Bootstrap.packed (Word.ofUInt32 x) = word (pack x.toBitVec x.toBitVec) := by
  apply bits_injective
  apply BitVec.eq_of_toNat_eq
  rw [bits_word,pack_toNat,bits_toNat,Table144Bootstrap.packed_ofUInt32_toNat]
  rfl

theorem ready_eq_core (s : State) (input : ByteArray) (i : Nat) (h : Compression.HashState)
    (rho : List UInt256) :
    readyState s input i h rho = Table144Core.atRound (scheduledState s i) 0 (initialLane h)
      (PersistentFrame.frame h (DriverTrace.blockOffsetWord i) (Padding.paddedWord input) rho) := by
  have hk : physicalKey 0 = Table144Bootstrap.initialKey := by decide
  change {scheduledState s i with
      pc := UInt256.ofNat 1129
      stack := Table144Bootstrap.resultStack (Word.ofUInt32 h.h0) (Word.ofUInt32 h.h1)
        (Word.ofUInt32 h.h2) (Word.ofUInt32 h.h3) (Word.ofUInt32 h.h4) (driverRest input i rho)} =
    {scheduledState s i with
      pc := UInt256.ofNat 1129
      stack := Table144CoreCommon.stack [.k,.a,.b,.c,.d,.e,.factor,.pair,.upper,.lower]
        (initialLane h) (physicalKey 0)
        (PersistentFrame.frame h (DriverTrace.blockOffsetWord i) (Padding.paddedWord input) rho)}
  simp only [Table144Bootstrap.resultStack,packed_hash,Table144CoreCommon.stack,
    List.map_cons,List.map_nil,List.cons_append,List.nil_append,Table144CoreCommon.word,
    hk,initialLane,packCrypto,PairedCompressionBridge.ofWorking,CompressionCorrect.workingOfHash,
    Table144CoreCommon.pairWord_literal,Table144CoreCommon.upperWord_literal,
    Table144CoreCommon.lowerWord_literal,Table144CoreCommon.factorWord_literal,
    Table144Bootstrap.primaryFactor,Table144Bootstrap.pairMask,Table144Bootstrap.upperMask,
    Table144Bootstrap.lowerMask,Table144Bootstrap.cache,Table144Raw.cache,
    PersistentFrame.frame,driverRest,List.append_assoc,Word.literal_eq_ofNat]

opaque gasSteps_compress (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (rho : List UInt256) (hstack : rho.length≤980)
    (hfit : input.size<2^64) (hi : i<DriverTrace.blockCount input)
    (ctx : Context s input i)
    (hcode : s.executionEnv.code=Artifact.submissionArtifact.code)
    (hfork : s.fork=.Osaka) (hrun : s.halt=.Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr=false) :
    GasSteps (Table144CallPrepare.callState s input i h rho) (resultState s input i h rho) := by
  let q := scheduledState s i
  let frame := PersistentFrame.frame h (DriverTrace.blockOffsetWord i) (Padding.paddedWord input) rho
  have hp := Table144CallPrepare.gasSteps_call_prepare s input i h rho hstack hfit hi ctx hcode hfork hrun hnp
  have hc := Table144Core.gasSteps_core q (initialLane h) frame
    (by simp only [frame,PersistentFrame.frame,List.length_cons,List.length_nil,List.length_append]; omega)
    hrun (scheduled_active s input i hfit hi) hcode hfork hnp
  have ht := PersistentTailSite.gasSteps q (DriverTrace.blockOffsetWord i) (Padding.paddedWord input) h
    (finalLane (Table144Core.message q.memory) (initialLane h)) rho hstack hrun hcode hfork hnp
  apply (hp.cast rfl (ready_eq_core s input i h rho)).trans
  apply (hc.trans ht).cast rfl
  rw [final_combine_eq_nextHash s input i h hfit hi ctx]
  rfl

#print axioms packed_hash
#print axioms ready_eq_core
#print axioms gasSteps_compress
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144BlockBridge
