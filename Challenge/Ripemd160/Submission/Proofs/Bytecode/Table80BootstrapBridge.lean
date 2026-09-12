import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Bootstrap
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Core
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80BootstrapBridge
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open PairedLaneUInt256Bridge Paired80Core Paired80WordRound Paired80Algorithm

theorem pack_mul (x : UInt32) :
    UInt256.mul (UInt256.ofNat 1208925819614629174706177) (Word.ofUInt32 x) = packed32 x x := by
  apply bits_injective
  rw [bits_mul, bits_ofNat]
  change BitVec.ofNat 256 1208925819614629174706177 * BitVec.ofNat 256 x.toNat = pack x.toBitVec x.toBitVec
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, pack_toNat]
  have hx : x.toNat < 2 ^ 32 := x.toBitVec.isLt
  have hx256 : x.toNat < 2 ^ 256 := by omega
  have hm : 1208925819614629174706177 * x.toNat < 2 ^ 256 := by omega
  norm_num only [Nat.reducePow, Nat.reduceMod]
  change 1208925819614629174706177 * (x.toNat % 2 ^ 256) % 2 ^ 256 = x.toNat + x.toNat * 2 ^ 80
  rw [Nat.mod_eq_of_lt hx256, Nat.mod_eq_of_lt hm]
  omega

def initialLane (h : Compression.HashState) : WordLane :=
  packCrypto (PairedCompressionBridge.ofWorking (CompressionCorrect.workingOfHash h))
    (PairedCompressionBridge.ofWorking (CompressionCorrect.workingOfHash h))

theorem resultStack_eq (memory : ByteArray) (h : Compression.HashState) (rho : List UInt256)
    (hh : StackMemory.hashAt memory = Compression.embedHash h) :
    Table80Bootstrap.resultStack memory rho =
      Table80CoreCommon.stack [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower]
        (initialLane h) (physicalKey 0) rho := by
  have h0 : MachineState.readWord memory 832 = Word.ofUInt32 h.h0 := congrArg Compression.EvmHashState.h0 hh
  have h1 : MachineState.readWord memory 864 = Word.ofUInt32 h.h1 := congrArg Compression.EvmHashState.h1 hh
  have h2 : MachineState.readWord memory 896 = Word.ofUInt32 h.h2 := congrArg Compression.EvmHashState.h2 hh
  have h3 : MachineState.readWord memory 928 = Word.ofUInt32 h.h3 := congrArg Compression.EvmHashState.h3 hh
  have h4 : MachineState.readWord memory 960 = Word.ofUInt32 h.h4 := congrArg Compression.EvmHashState.h4 hh
  simp only [Table80Bootstrap.resultStack, Table80Bootstrap.packedHash, h0, h1, h2, h3, h4, pack_mul]
  rfl

def gasSteps_clean (s : State) (h : Compression.HashState) (rho : List UInt256)
    (hh : StackMemory.hashAt s.memory = Compression.embedHash h)
    (hstack : rho.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 1066, stack := Table80Raw.cache ++ rho}
      (Table80Core.atRound s 0 (initialLane h) rho) := by
  have gs := Table80Bootstrap.gasSteps s rho hstack hrun hactive hcode hfork hnp
  rw [resultStack_eq s.memory h rho hh] at gs
  exact gs
#print axioms pack_mul
#print axioms resultStack_eq
#print axioms gasSteps_clean
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80BootstrapBridge
