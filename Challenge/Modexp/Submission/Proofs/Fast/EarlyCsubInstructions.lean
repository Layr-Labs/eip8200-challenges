import Challenge.Modexp.Submission.Proofs.Fast.EarlyCsubCheck
import Challenge.Modexp.Submission.Proofs.Fast.Defs
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.EarlyCsub
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding

theorem activeWordsAfter_fix (curr off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 5376) (hcurr : 168 ≤ curr) :
    MachineState.activeWordsAfter curr off sz = curr := by
  unfold MachineState.activeWordsAfter
  simp only [hsz, if_false]
  have hle : (off + sz - 1) / 32 + 1 ≤ curr := by omega
  exact Nat.max_eq_left hle

theorem activeWords_fix (s : State) (off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 5376) (hact : 168 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat off sz) =
      s.activeWords := by
  rw [activeWordsAfter_fix _ off sz hsz hoff hact]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm


def checkProgram : List Instr :=
  [.op .JUMPDEST, .push 0 0, .op .MLOAD, .push 2 4160, .op .MLOAD,
   .op .LT, .push 2 4128, .op .MLOAD, .op .ISZERO, .op .AND,
   .push 2 5165, .op .JUMPI]
def jumpProgram : List Instr := [.push 2 4925, .op .JUMP]
def copyProgram : List Instr :=
  [.op .JUMPDEST, .push 2 4160, .push 2 5248, .op .MLOAD,
   .op (.Swap ⟨1, by decide⟩), .op .MCOPY, .op .JUMP]

def checkBlock : Block Artifact.submissionArtifact .Osaka 4669 checkProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3560 12 4669 checkProgram
    (by decide) (by rfl) (by rfl) (by decide)
def jumpBlock : Block Artifact.submissionArtifact .Osaka 4687 jumpProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3572 2 4687 jumpProgram
    (by decide) (by rfl) (by rfl) (by decide)
def copyBlock : Block Artifact.submissionArtifact .Osaka 5165 copyProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3901 7 5165 copyProgram
    (by decide) (by rfl) (by rfl) (by decide)

def atState (s : State) (mem : ByteArray) (pc : Nat) (dst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc, stack := [dst,ret] ++ rest, memory := mem }

def copiedState (s : State) (mem : ByteArray) (n : Nat) (dst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := ret
    stack := rest
    memory := MachineState.writeBytes mem (MachineState.readPadded mem 4160 (32*n)) dst.toNat }

theorem run_check (s : State) (mem : ByteArray) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hact : 168 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions checkProgram (atState s mem 4669 dst ret rest) =
      some (atState s mem (if Skip mem then 5165 else 4687) dst ret rest) := by
  have hc1 : rest.length+1 < 1024 := by omega
  have hc2 : rest.length+2 < 1024 := by omega
  have hc3 : rest.length+3 < 1024 := by omega
  have hc4 : rest.length+4 < 1024 := by omega
  have hc5 : rest.length+5 < 1024 := by omega
  have h0 : ({val := 0} : UInt256).toNat = 0 := rfl
  have h8256 : (4160 : UInt256).toNat = 4160 := by decide
  have h8224 : (4128 : UInt256).toNat = 4128 := by decide
  have heq5165 : (5165 : UInt256) = UInt256.ofNat 5165 := by decide
  have h5165 : (5165 : UInt256).toNat = 5165 := by decide
  have ha0 := activeWords_fix s 0 32 (by decide) (by omega) hact
  have haT := activeWords_fix s 4160 32 (by decide) (by omega) hact
  have haN := activeWords_fix s 4128 32 (by decide) (by omega) hact
  by_cases hskip : Skip mem
  · have hz : (jumpWord mem).toNat ≠ 0 := by rw [jumpWord_toNat, if_pos hskip]; decide
    simp [checkProgram,runInstructions,Challenge.EvmProof.Stepper.runInstr,
      atState,State.activeWordsAfterUInt256,h0,h8256,h8224,h5165,
      ha0,haT,haN,Nat.add_assoc,Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod,hc2,hc3,hc4,hc5,←jumpWord_eq,UInt256.isTrue,hskip,hz,
      hcode,jumpDestEarlyCopy,heq5165]
  · have hz : (jumpWord mem).toNat = 0 := by rw [jumpWord_toNat, if_neg hskip]
    simp [checkProgram,runInstructions,Challenge.EvmProof.Stepper.runInstr,
      atState,State.activeWordsAfterUInt256,h0,h8256,h8224,h5165,
      ha0,haT,haN,Nat.add_assoc,Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod,hc2,hc3,hc4,hc5,←jumpWord_eq,UInt256.isTrue,hskip,hz]

theorem run_jump (s : State) (mem : ByteArray) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions jumpProgram (atState s mem 4687 dst ret rest) =
      some (atState s mem 4925 dst ret rest) := by
  have hc1 : rest.length+1 < 1024 := by omega
  have hc2 : rest.length+2 < 1024 := by omega
  have hc3 : rest.length+3 < 1024 := by omega
  have heq4925 : (4925 : UInt256) = UInt256.ofNat 4925 := by decide
  have h4925 : (4925 : UInt256).toNat = 4925 := by decide
  simp [jumpProgram,runInstructions,Challenge.EvmProof.Stepper.runInstr,
    atState,hc2,hc3,Nat.add_assoc,hcode,h4925,jumpDestSub,heq4925]

theorem run_copy (s : State) (mem : ByteArray) (n : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hact : 168 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hs32 : MachineState.readWord mem 5248 = UInt256.ofNat (32*n))
    (hdstFit : dst.toNat+32*n ≤ 5376)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true) :
    runInstructions copyProgram (atState s mem 5165 dst ret rest) =
      some (copiedState s mem n dst ret rest) := by
  have hc1 : rest.length+1 < 1024 := by omega
  have hc2 : rest.length+2 < 1024 := by omega
  have hc3 : rest.length+3 < 1024 := by omega
  have hc4 : rest.length+4 < 1024 := by omega
  have hc5 : rest.length+5 < 1024 := by omega
  have h8256 : (4160 : UInt256).toNat = 4160 := by decide
  have h9344 : (5248 : UInt256).toNat = 5248 := by decide
  have hsz : 32*n % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 32*n := Nat.mod_eq_of_lt (by omega)
  have hactS := activeWords_fix s 5248 32 (by decide) (by omega) hact
  have hactD := activeWordsAfter_fix s.activeWords.toNat dst.toNat (32*n) (by omega) hdstFit hact
  have hactT := activeWords_fix s 4160 (32*n) (by omega) (by omega) hact
  simp [copyProgram,runInstructions,Challenge.EvmProof.Stepper.runInstr,
    atState,copiedState,hs32,h8256,h9344,hsz,hcode,hjump,hc2,hc3,hc4,hc5,
    State.activeWordsAfterUInt256,State.activeWordsAfterUInt256_2,hactS,hactD,hactT,hc1,Nat.add_assoc,
    Challenge.EvmProof.Word.word_toNat_ofNat,List.exchange]

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256; rw [Challenge.Modexp.submissionBytecode_size]; decide,
    hcode,hfork,hrun,hnp⟩

end Challenge.Modexp.Submission.Proofs.Fast.EarlyCsub
