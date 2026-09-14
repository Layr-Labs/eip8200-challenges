import Challenge.Modexp.Submission.Proofs.Fast.CsubCore
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.LazyGate
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding

/- Exact e570a487 gate instructions: PCs4727..4735, instruction indices3572..3576.
   This independent run theorem is parameterized by the code's actual4491 jump fact;
   it does not pretend the old comparison artifact contains this new gate. -/
def program : List Instr :=
  [.op .JUMPDEST, .push 2 2080, .op .MLOAD, .push 2 4491, .op .JUMPI]

def atState (s : State) (mem : ByteArray) (pc : Nat) (dst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc, stack := [dst,ret] ++ rest, memory := mem }

theorem run_gate (s : State) (mem : ByteArray) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hact : 88 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 4491 = true) :
    runInstructions program (atState s mem 4727 dst ret rest) =
      some (atState s mem
        (if (MachineState.readWord mem 2080).toNat = 0 then 4736 else 4491)
        dst ret rest) := by
  have hc2 : rest.length+2 < 1024 := by omega
  have hc3 : rest.length+3 < 1024 := by omega
  have hc4 : rest.length+4 < 1024 := by omega
  have h2080 : (2080 : UInt256).toNat = 2080 := by decide
  have h4491 : (4491 : UInt256).toNat = 4491 := by decide
  have heq4491 : (4491 : UInt256) = UInt256.ofNat 4491 := by decide
  have haN := Csub.activeWords_fix s 2080 32 (by decide) (by omega) hact
  by_cases hz : (MachineState.readWord mem 2080).toNat = 0
  · simp [program,runInstructions,Challenge.EvmProof.Stepper.runInstr,
      atState,State.activeWordsAfterUInt256,h2080,h4491,heq4491,
      haN,Nat.add_assoc,Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,hc2,hc3,hc4,UInt256.isTrue,hz]
  · simp [program,runInstructions,Challenge.EvmProof.Stepper.runInstr,
      atState,State.activeWordsAfterUInt256,h2080,h4491,heq4491,
      haN,Nat.add_assoc,Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,hc2,hc3,hc4,UInt256.isTrue,hz,hjump]

#print axioms run_gate

def copyProgram : List Instr :=
  [.op .JUMPDEST, .push 2 2112, .push 2 2688, .op .MLOAD,
   .op (.Swap ⟨1, by decide⟩), .op .MCOPY, .op .JUMP]

def returnedState (s : State) (mem : ByteArray) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := ret, stack := rest, memory := mem }

theorem run_copy (s : State) (mem : ByteArray) (n : Nat) (dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n))
    (hdstFit : dst.toNat+32*n ≤ 2816)
    (hjump : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    runInstructions copyProgram (atState s mem 4736 dst ret rest) =
      some (returnedState s
        (MachineState.writeBytes mem (MachineState.readPadded mem 2112 (32*n)) dst.toNat)
        ret rest) := by
  have hc1 : rest.length+1 < 1024 := by omega
  have hc2 : rest.length+2 < 1024 := by omega
  have hc3 : rest.length+3 < 1024 := by omega
  have hc4 : rest.length+4 < 1024 := by omega
  have hc5 : rest.length+5 < 1024 := by omega
  have h2112 : (2112 : UInt256).toNat = 2112 := by decide
  have h2688 : (2688 : UInt256).toNat = 2688 := by decide
  have hsz : 32*n % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 32*n := Nat.mod_eq_of_lt (by omega)
  have hactS := Csub.activeWords_fix s 2688 32 (by decide) (by omega) hact
  have hactD := Csub.activeWordsAfter_fix s.activeWords.toNat dst.toNat (32*n) (by omega) hdstFit hact
  have hactT := Csub.activeWords_fix s 2112 (32*n) (by omega) (by omega) hact
  simp [copyProgram,runInstructions,Challenge.EvmProof.Stepper.runInstr,
    atState,returnedState,hs32,h2112,h2688,hsz,hjump,hc2,hc3,hc4,hc5,
    State.activeWordsAfterUInt256,State.activeWordsAfterUInt256_2,hactS,hactD,hactT,hc1,Nat.add_assoc,
    Challenge.EvmProof.Word.word_toNat_ofNat,List.exchange]

#print axioms run_copy
end Challenge.Modexp.Submission.Proofs.Fast.LazyGate
