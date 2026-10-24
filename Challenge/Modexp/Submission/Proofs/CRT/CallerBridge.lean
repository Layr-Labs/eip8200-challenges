import Challenge.Modexp.Submission.Proofs.CRT.EntryInvariant
import Challenge.Modexp.Submission.Proofs.CRT.PureSquareInterface
import Challenge.Modexp.Submission.Proofs.CRT.CRTLoopInduction
import Challenge.Modexp.Submission.Proofs.CRT.CRTGasStepsNormalized
import Challenge.Modexp.Submission.Proofs.Fast.CRTLoopEntry
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 4096
noncomputable section

namespace HistoricalSearch.CallerBridge
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open HistoricalSearch.CRTLoopFrames HistoricalSearch.CRTAdapterMeaning
open HistoricalSearch.LoopInvariant HistoricalSearch.PureLoop

def frame (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256) : CRTLoopFrames.Frame where
  w3 := MachineState.readWord mem 192
  tl := MachineState.readWord mem 224
  inv := MachineState.readWord mem 2720
  m0 := MachineState.readWord mem 160
  m96 := MachineState.readWord mem 96
  m64 := MachineState.readWord mem 64
  m32 := MachineState.readWord mem 32
  m128 := MachineState.readWord mem 128
  aprev := UInt256.ofNat 2336
  counter := UInt256.ofNat (k-1)
  ret := ret
  rest := tail

theorem prefix_live (mem : ByteArray) : Live (CRTLoopEntry.memory mem) mem := by
  intro addr hd
  exact CRTLoopEntry.readWord mem addr (by omega)

theorem head_eq (s : State) (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256) :
    CRTLoopEntry.head s mem k ret tail = atOld s (CRTLoopEntry.memory mem) 4816
      (UInt256.ofNat 0) (SquareStagedEntry.qWord 8) (UInt256.ofNat 3347) (frame mem k ret tail) := by
  unfold CRTLoopEntry.head SquareLoopBlocks.frameAt SquareLoopBlocks.frameStack atOld
    TnM128SquareExit.frameAt TnM128SquareExit.frameStack frame
  rw [CRTLoopEntry.readWord mem 192 (Or.inl (by decide)),
    CRTLoopEntry.readWord mem 128 (Or.inl (by decide))]
  rfl

theorem static (mem : ByteArray) (k : Nat) (ret : UInt256) (tail : List UInt256)
    (bsize N mi : Nat) (hf : Exp.Frame mem 8 bsize mi)
    (hm : Model.FastRepresents mem 0 8 N) (hpos : 0<N) (hodd : N%2=1)
    (hmi : mi < 2^256) (hmiA : (N%Limbs.radix*mi+1)%2^256=0) (hguard : mi≠1) :
    Static mem (inputWord mem 0) (MachineState.readWord mem 2720) (frame mem k ret tail) N where
  s32 := hf.s32
  tlw := hf.tl
  ml := hf.ml
  w3 := rfl
  tl := rfl
  inv := rfl
  m0 := rfl
  m96 := rfl
  m64 := rfl
  m32 := rfl
  m128 := rfl
  cachedDigits := fun _ _ => rfl
  cachedInverse := rfl
  modulus := hm
  positive := hpos
  odd := Nat.odd_iff.mpr hodd
  inverse := by
    rw [hf.minvW, Exp.toNat_ofNat_self hmi]
    simpa only [Limbs.radix, Nat.add_mod, Nat.mul_mod, Nat.mod_mod] using hmiA
  inverseGuard := by
    change MachineState.readWord mem 2720 ≠ UInt256.ofNat 1
    rw [hf.minvW]
    intro he
    have hn := congrArg UInt256.toNat he
    rw [Exp.toNat_ofNat_self hmi] at hn
    exact hguard hn

/-- The concrete internal loop execution contract, kept as a parameter until
the independently checked branch/induction module is supplied. -/
abbrev LoopTrace (s : State) (N : Nat) :=
  ∀ (minv : UInt256) (n : Nat → UInt256) (k : Nat) (mem : ByteArray)
    (f : CRTLoopFrames.Frame) (A : Nat), f.rest.length ≤ 982 → Invariant mem n minv f N k A →
    GasSteps (atCache s mem 5858 n minv f)
      (CRTLoopInduction.finished s (PureLoop.memory s minv n k mem) f)

theorem positive_memory (s : State) (k : Nat) (mem : ByteArray) (hk : 1≤k) :
    PureSquareMemory.memory s k mem = PureLoop.memory s (MachineState.readWord mem 2720)
      (inputWord mem 0) k (PureSquareMemory.initial k mem) := by
  cases k with
  | zero => omega
  | succ k => rfl

def trace (s : State) (bsize N mi : Nat)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hact : 88≤s.activeWords.toNat) (hcds : s.executionEnv.calldata.size<2^256)
    (hodd : N%2=1) (hmi : mi<2^256) (hmiA : (N%Limbs.radix*mi+1)%2^256=0)
    (loop : LoopTrace s N)
    (k : Nat) (ret : UInt256) (tail : List UInt256) (mem : ByteArray) (A : Nat)
    (hguard : mi≠1) (hk : 1≤k) (hk16 : k≤16) (hcap : tail.length≤982)
    (hw : tail[1]?=some (UInt256.ofNat 256)) (hn : tail[2]?=some (UInt256.ofNat 8))
    (hf : Exp.Frame mem 8 bsize mi) (hm : Model.FastRepresents mem 0 8 N)
    (ha : Model.FastRepresents mem 2112 8 A) (hAN : A<N) :
    GasSteps (Exp.sqLoopCall s mem k ret tail)
      (Exp.retTo s (CRTLoopInterface.finished (PureSquareInterface.model s) s k mem)
        (UInt256.ofNat 690) tail) := by
  let f := frame mem k ret tail
  have hs := static mem k ret tail bsize N mi hf hm (by omega) hodd hmi hmiA hguard
  have hinv : MachineState.readWord mem 2720 ≠ UInt256.ofNat 0 := by
    intro hz
    have h := hs.inverse
    rw [hz] at h
    norm_num at h
  have g1 := CRTLoopEntry.gasSteps_prefix s mem k ret tail hcap env.running env.code env.forkEq
    env.noPrecompile hact hcds hf.s32 hf.ml hw hn hs.inverseGuard hinv
  have g2 := CRTGasStepsNormalized.entry s (CRTLoopEntry.memory mem) f (SquareStagedEntry.qWord 8)
    (UInt256.ofNat 3347) env hcap hact
  have hdigits : inputWord (CRTLoopEntry.memory mem) 0 = inputWord mem 0 :=
    funext fun i => inputWord_live (prefix_live mem) i
  rw [hdigits, (prefix_live mem) 2720 (Or.inr (by decide))] at g2
  have hi := EntryInvariant.initial mem (inputWord mem 0) (MachineState.readWord mem 2720)
    f N k A hs ha hk hk16
  have g3 := loop (MachineState.readWord mem 2720) (inputWord mem 0) k
    (PureSquareMemory.initial k mem) f A hcap hi
  have g12 := (g1.cast rfl (head_eq s mem k ret tail)).trans g2
  have g := g12.trans g3
  change GasSteps (Exp.sqLoopCall s mem k ret tail)
    (Exp.retTo s (StagedProduct.memory s (PureSquareMemory.memory s k mem) 8) (UInt256.ofNat 690) tail)
  rw [positive_memory s k mem hk]
  exact g

def implementation (s : State) (bsize N mi : Nat)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hact : 88≤s.activeWords.toNat) (hcds : s.executionEnv.calldata.size<2^256)
    (hodd : N%2=1) (hmi : mi<2^256) (hmiA : (N%Limbs.radix*mi+1)%2^256=0)
    (loop : LoopTrace s N) : CRTLoopInterface.Implementation s bsize N mi :=
  CRTLoopInterface.ofModel (PureSquareInterface.model s) s bsize N mi hodd hmi hmiA
    (trace s bsize N mi env hact hcds hodd hmi hmiA loop)

#print axioms head_eq
#print axioms static
#print axioms trace
#print axioms implementation
end HistoricalSearch.CallerBridge
