import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13NormalTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13Memory
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentMaskEndian
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedMask32Cache PairedScheduleMemory

abbrev stk := Pair13Endian.stk
abbrev template := Pair13Endian.template
abbrev run_template := Pair13Endian.run_template
abbrev normalTemplate := Pair13NormalTrace.normalTemplate

theorem run_normal (s : State) (pc ret a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256)
    (rho : List UInt256) (p : Nat) (hstack : rho.length ≤ 880) (hrun : s.halt = .Running)
    (hp : 1056 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hq1 : off + UInt256.ofNat 1088 = UInt256.ofNat (p + 32))
    (hq0 : off + UInt256.ofNat 1056 = UInt256.ofNat p)
    (hlow : (MachineState.readWord s.memory 0).toNat % 2 ^ 144 < 2 ^ 32)
    (_hgap : PairStoreGap.GapClear s.memory) :
    runInstrSeq normalTemplate {s with pc := pc, stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} =
      some {s with
        pc := pcAfter pc normalTemplate
        stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
        memory := PoolReference.dataMemory s.memory p
        activeWords := loadedActiveWords s (UInt256.ofNat p)} := by
  exact Pair13NormalTrace.run_normal s pc ret a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho p
    hstack hrun hp hbound hq1 hq0 hlow

#print axioms run_normal
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentMaskEndian
