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
    (hoff : off + sz ≤ 9472) (hcurr : 296 ≤ curr) :
    MachineState.activeWordsAfter curr off sz = curr := by
  unfold MachineState.activeWordsAfter
  simp only [hsz, if_false]
  have hle : (off + sz - 1) / 32 + 1 ≤ curr := by omega
  exact Nat.max_eq_left hle

theorem activeWords_fix (s : State) (off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 9472) (hact : 296 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat off sz) =
      s.activeWords := by
  rw [activeWordsAfter_fix _ off sz hsz hoff hact]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm


def checkProgram : List Instr :=
  [.op .JUMPDEST, .push 0 0, .op .MLOAD, .push 2 8256, .op .MLOAD,
   .op .LT, .op .ISZERO, .push 2 8224, .op .MLOAD, .op .OR,
   .push 2 4851, .op .JUMPI]
def jumpProgram : List Instr := [.push 2 5091, .op .JUMP]
def copyProgram : List Instr :=
  [.op .JUMPDEST, .push 2 8256, .push 2 9344, .op .MLOAD,
   .op (.Swap ⟨1, by decide⟩), .op .MCOPY, .op .JUMP]

def checkBlock : Block Artifact.submissionArtifact .Osaka 4671 checkProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3564 12 4671 checkProgram
    (by decide) (by rfl) (by rfl) (by decide)
def jumpBlock : Block Artifact.submissionArtifact .Osaka 4689 jumpProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3576 2 4689 jumpProgram
    (by decide) (by rfl) (by rfl) (by decide)
def copyBlock : Block Artifact.submissionArtifact .Osaka 5091 copyProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3855 7 5091 copyProgram
    (by decide) (by rfl) (by rfl) (by decide)

def atState (s : State) (mem : ByteArray) (pc : Nat) (dst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc, stack := [dst,ret] ++ rest, memory := mem }

def copiedState (s : State) (mem : ByteArray) (n : Nat) (dst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := ret
    stack := rest
    memory := MachineState.writeBytes mem (MachineState.readPadded mem 8256 (32*n)) dst.toNat }

theorem run_check (s : State) (mem : ByteArray) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hact : 296 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions checkProgram (atState s mem 4671 dst ret rest) =
      some (atState s mem (if Skip mem then 4689 else 4851) dst ret rest) := by
  have hc1 : rest.length+1 < 1024 := by omega
  have hc2 : rest.length+2 < 1024 := by omega
  have hc3 : rest.length+3 < 1024 := by omega
  have hc4 : rest.length+4 < 1024 := by omega
  have hc5 : rest.length+5 < 1024 := by omega
  have h0 : ({val := 0} : UInt256).toNat = 0 := rfl
  have h8256 : (8256 : UInt256).toNat = 8256 := by decide
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have heq4978 : (4851 : UInt256) = UInt256.ofNat 4851 := by decide
  have h4978 : (4851 : UInt256).toNat = 4851 := by decide
  have ha0 := activeWords_fix s 0 32 (by decide) (by omega) hact
  have haT := activeWords_fix s 8256 32 (by decide) (by omega) hact
  have haN := activeWords_fix s 8224 32 (by decide) (by omega) hact
  by_cases hskip : Skip mem
  · have hz : (guardWord mem).toNat = 0 := hskip
    simp [checkProgram,runInstructions,Challenge.EvmProof.Stepper.runInstr,
      atState,State.activeWordsAfterUInt256,h0,h8256,h8224,h4978,
      ha0,haT,haN,Nat.add_assoc,Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod,hc2,hc3,hc4,hc5,←guardWord_eq,UInt256.isTrue,hskip,hz]
  · have hz : (guardWord mem).toNat ≠ 0 := hskip
    simp [checkProgram,runInstructions,Challenge.EvmProof.Stepper.runInstr,
      atState,State.activeWordsAfterUInt256,h0,h8256,h8224,h4978,
      ha0,haT,haN,Nat.add_assoc,Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod,hc2,hc3,hc4,hc5,←guardWord_eq,UInt256.isTrue,hskip,hz,
      hcode,jumpDestSub,heq4978]

theorem run_jump (s : State) (mem : ByteArray) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions jumpProgram (atState s mem 4689 dst ret rest) =
      some (atState s mem 5091 dst ret rest) := by
  have hc1 : rest.length+1 < 1024 := by omega
  have hc2 : rest.length+2 < 1024 := by omega
  have hc3 : rest.length+3 < 1024 := by omega
  have heq5219 : (5091 : UInt256) = UInt256.ofNat 5091 := by decide
  have h5219 : (5091 : UInt256).toNat = 5091 := by decide
  simp [jumpProgram,runInstructions,Challenge.EvmProof.Stepper.runInstr,
    atState,hc2,hc3,Nat.add_assoc,hcode,h5219,jumpDestEarlyCopy,heq5219]

theorem run_copy (s : State) (mem : ByteArray) (n : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n))
    (hdstFit : dst.toNat+32*n ≤ 9472)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true) :
    runInstructions copyProgram (atState s mem 5091 dst ret rest) =
      some (copiedState s mem n dst ret rest) := by
  have hc1 : rest.length+1 < 1024 := by omega
  have hc2 : rest.length+2 < 1024 := by omega
  have hc3 : rest.length+3 < 1024 := by omega
  have hc4 : rest.length+4 < 1024 := by omega
  have hc5 : rest.length+5 < 1024 := by omega
  have h8256 : (8256 : UInt256).toNat = 8256 := by decide
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  have hsz : 32*n % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 32*n := Nat.mod_eq_of_lt (by omega)
  have hactS := activeWords_fix s 9344 32 (by decide) (by omega) hact
  have hactD := activeWordsAfter_fix s.activeWords.toNat dst.toNat (32*n) (by omega) hdstFit hact
  have hactT := activeWords_fix s 8256 (32*n) (by omega) (by omega) hact
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
