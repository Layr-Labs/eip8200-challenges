import Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
import Challenge.Modexp.Submission.Proofs.Fast.SquareStagedEntry
import Challenge.Modexp.Submission.Proofs.Fast.R4Hooks
import Challenge.Modexp.Submission.Proofs.Fast.Exp

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CRTLoopEntry
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open StagedOperand

/-- The unchanged setup stages the eight-word operand and clears one scratch word. -/
def memory (mem : ByteArray) : ByteArray :=
  SquarePartialClear.memory (stage mem 2112 8)

theorem readWord (mem : ByteArray) (addr : Nat)
    (hd : addr + 32 ≤ 2048 ∨ 2624 ≤ addr) :
    MachineState.readWord (memory mem) addr = MachineState.readWord mem addr := by
  unfold memory
  rw [SquarePartialClear.readWord_outside _ addr (by omega),
    read_stage_outside mem 2112 8 addr (by omega)]

theorem represents (mem : ByteArray) (a : Nat) (ha : Model.FastRepresents mem 2112 8 a) :
    Model.FastRepresents (memory mem) 2368 8 a :=
  SquarePartialClear.fastRepresents_outside _ 2368 8 a (Or.inr (by decide))
    (SquareResult.represents_stage mem 8 a ha)

theorem keep (mem : ByteArray) (ptr n v : Nat)
    (hd : ptr + 32*n ≤ 2048 ∨ 2624 ≤ ptr) (h : Model.FastRepresents mem ptr n v) :
    Model.FastRepresents (memory mem) ptr n v := by
  refine (Model.fastRepresents_congr (a := mem) ?_ v).1 h
  intro j hj
  rw [readWord mem (ptr+32*j) (by omega)]

/-- The new kernel's initial entry; the previous-operand slot still contains
its original pointer and is deliberately not asserted to be an operand word. -/
def head (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (rest : List UInt256) : State :=
  SquareLoopBlocks.frameAt 5615 s (memory mem) 8 (SquareStagedEntry.qWord 8)
    (UInt256.ofNat 3347) (MachineState.readWord mem 224) (MachineState.readWord mem 2720)
    (MachineState.readWord mem 160) (MachineState.readWord mem 96)
    (MachineState.readWord mem 64) (MachineState.readWord mem 32)
    (UInt256.ofNat 2336) (UInt256.ofNat (k-1)) ret rest

/-- Exact existing setup and dispatcher trace up to the CRT entry block (the dispatcher
jumps past the replacement hook).
No behavior of the overwritten first row is used. -/
def gasSteps_prefix (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat 256)
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat 224)
    (hw : rest[1]? = some (UInt256.ofNat 256))
    (hn : rest[2]? = some (UInt256.ofNat 8))
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1)
    (hinv : MachineState.readWord mem 2720 ≠ UInt256.ofNat 0) :
    Challenge.EvmProof.GasSteps (Exp.sqLoopCall s mem k ret rest) (head s mem k ret rest) := by
  have g1 := Cios2Dispatch.gasSteps_commonSetupSq s mem (UInt256.ofNat 4245) 2112 512 8
    (UInt256.ofNat (k-1)) ret rest (by omega) hrun hcode hfork hnp hact (Or.inr rfl)
    (by decide) (by decide) (by decide) hcds hs32 hml hw hn SquareStagedEntry.jumpDest
    hguard hinv
  have g2 := SquareStagedEntry.gasSteps_entry s (memory mem) 8 (UInt256.ofNat 3347)
    (MachineState.readWord mem 32) (MachineState.readWord mem 64) (MachineState.readWord mem 160)
    (MachineState.readWord mem 224 :: MachineState.readWord mem 96 :: MachineState.readWord mem 2720 ::
      UInt256.ofNat 0 :: UInt256.ofNat 2336 :: UInt256.ofNat (k-1) :: ret :: rest)
    (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact
  have g3 := R4Hooks.gasSteps_h1Fall s (memory mem) (SquareStagedEntry.qWord 8)
    (UInt256.ofNat 3347) (MachineState.readWord mem 224) (MachineState.readWord mem 2720)
    (MachineState.readWord mem 160) (MachineState.readWord mem 96) (MachineState.readWord mem 64)
    (MachineState.readWord mem 32) (UInt256.ofNat 2336) (UInt256.ofNat (k-1)) ret rest
    (by omega) hrun hcode hfork hnp 8 rfl SquareStagedEntry.qWord_eight
  exact ((g1.trans g2).trans g3).cast rfl rfl

#print axioms gasSteps_prefix
end Challenge.Modexp.Submission.Proofs.Fast.CRTLoopEntry
