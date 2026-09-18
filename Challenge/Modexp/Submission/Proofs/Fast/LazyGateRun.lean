import Challenge.Modexp.Submission.Proofs.Fast.CsubCore
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.LazyGate
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding

/-- The lazy CSUB gate (E9, pcs 4458..4463, instruction indices 3553..3556):
`JUMPDEST DUP9 PUSH2 0x109f JUMPI`.  It branches on the carry cell (item 9 of the stack:
`rest[6]` under the call pair `[dst, ret]`) instead of the scratch word `mem[2080]`; every
caller reaches it with the cell just flushed to that word (E14 / the R4 dual park), so the
branch is still stated on `mem[2080]`. -/
def program : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨8, by decide⟩), .push 2 4255, .op .JUMPI]

def atState (s : State) (mem : ByteArray) (pc : Nat) (dst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc, stack := [dst,ret] ++ rest, memory := mem }

theorem run_gate (s : State) (mem : ByteArray) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcell : rest[6]? = some (MachineState.readWord mem 2080))
    (hjump : Decode.isValidJumpDest s.executionEnv.code 4255 = true) :
    runInstructions program (atState s mem 4458 dst ret rest) =
      some (atState s mem
        (if (MachineState.readWord mem 2080).toNat = 0 then 4464 else 4255)
        dst ret rest) := by
  have hc2 : rest.length+2 < 1024 := by omega
  have hc3 : rest.length+3 < 1024 := by omega
  have hc4 : rest.length+4 < 1024 := by omega
  have h4491 : (4255 : UInt256).toNat = 4255 := by decide
  have heq4491 : (4255 : UInt256) = UInt256.ofNat 4255 := by decide
  by_cases hz : (MachineState.readWord mem 2080).toNat = 0
  · simp [program,runInstructions,Challenge.EvmProof.Stepper.runInstr,
      atState,h4491,heq4491,hcell,
      Nat.add_assoc,Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,hc2,hc3,hc4,UInt256.isTrue,hz]
  · simp [program,runInstructions,Challenge.EvmProof.Stepper.runInstr,
      atState,h4491,heq4491,hcell,
      Nat.add_assoc,Challenge.EvmProof.Word.succ_ofNat_mod,
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
    runInstructions copyProgram (atState s mem 4464 dst ret rest) =
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
