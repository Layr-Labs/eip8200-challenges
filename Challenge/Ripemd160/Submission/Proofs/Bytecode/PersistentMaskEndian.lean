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
    (hp : 1120 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hq1 : off + UInt256.ofNat 1152 = UInt256.ofNat (p + 32))
    (hq0 : off + UInt256.ofNat 1120 = UInt256.ofNat p)
    (hgap : PairStoreGap.GapClear s.memory) :
    runInstrSeq normalTemplate {s with pc := pc, stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} =
      some {s with
        pc := pcAfter pc normalTemplate
        stack := stk ret (UInt256.ofNat 4294967295) a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
        memory := Pair13Memory.resultMemoryJ s.memory
          (Shared32Scratch.wordsJ s.memory
            (PairedScheduleData.reversedWord (MachineState.readWord s.memory p))
            (PairedScheduleData.reversedWord (MachineState.readWord s.memory (p + 32))))
        activeWords := loadedActiveWords s (UInt256.ofNat p)} := by
  let low := PairedScheduleData.reversedWord (MachineState.readWord s.memory p)
  let high := PairedScheduleData.reversedWord (MachineState.readWord s.memory (p + 32))
  let words := Shared32Scratch.wordsJ s.memory low high
  let scratch := Shared32Scratch.fanMemory s.memory low high
  have h := Pair13NormalTrace.run_normal s pc ret a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho p
    hstack hrun hp hbound hq1 hq0
  have hm : Pair13WriterRaw.writerMemory scratch words
      = Pair13Memory.resultMemoryJ s.memory words := by
    rw [Pair13Memory.writerMemory_eq_resultMemoryJ scratch words
        (Shared32Scratch.fanMemory_gapClear s.memory _ _ hgap),
      Pair13Memory.resultMemoryJ, Pair13Memory.resultMemoryJ,
      Shared32Scratch.erase_fan s.memory (Pair13Memory.tableJ words) _ _]
  rw [← hm]
  exact h

#print axioms run_normal
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentMaskEndian
