import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopSites
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopInduction
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StaggerPersistentLoopRaw

structure Ambient (s : State) : Prop where
  code : s.executionEnv.code = Artifact.submissionArtifact.code
  fork : s.fork = .Osaka
  running : s.halt = .Running
  notPrecompile : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false

def limitWord (count : Nat) : UInt256 := UInt256.ofNat (count * 64)
def offsetWord (i : Nat) : UInt256 := UInt256.ofNat (i * 64)

def loopState (s : State) (h : Compression.HashState) (i count : Nat) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 466, stack := StaggerPersistentFrame.frame h (offsetWord i) (limitWord count) rho}

def postState (s : State) (h : Compression.HashState) (i count : Nat) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 4700, stack := StaggerPersistentFrame.frame h (offsetWord i) (limitWord count) rho}

def exitState (s : State) (h : Compression.HashState) (count : Nat) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 4713, stack := StaggerPersistentFrame.frame h (limitWord count) (limitWord count) rho}

theorem next_offset (i count : Nat) (hi : i < count) (hbound : count * 64 < 2^256) :
    nextOffset (offsetWord i) = offsetWord (i + 1) := by
  change UInt256.ofNat (i * 64) + UInt256.ofNat 64 = UInt256.ofNat ((i + 1) * 64)
  rw [Word.ofNat_add_ofNat (by omega)]
  congr 1
  omega

theorem next_continue (i count : Nat) (hi : i + 1 < count)
    (hbound : count * 64 < 2^256) :
    (nextOffset (offsetWord i)).toNat ≠ (limitWord count).toNat := by
  rw [next_offset i count (by omega) hbound]
  simp only [offsetWord, limitWord, Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hbound, Nat.mod_eq_of_lt (show (i + 1) * 64 < 2^256 by omega)]
  omega

theorem next_exit (i count : Nat) (hi : i + 1 = count)
    (hbound : count * 64 < 2^256) :
    (nextOffset (offsetWord i)).toNat = (limitWord count).toNat := by
  rw [next_offset i count (by omega) hbound, hi]
  rfl

/-- The only algorithmic premise is the supplied block transition. The state
sequence may carry arbitrary memory changes; each step carries its scalar hash. -/
def run_blocks (states : Nat → State) (hashes : Nat → Compression.HashState)
    (count : Nat) (rho : List UInt256) (hcount : 0 < count)
    (hbound : count * 64 < 2^256) (hstack : rho.length ≤ 980)
    (hambient : ∀ i, i ≤ count → Ambient (states i))
    (hblock : ∀ i, i < count →
      GasSteps (loopState (states i) (hashes i) i count rho)
        (postState (states (i + 1)) (hashes (i + 1)) i count rho)) :
    GasSteps (loopState (states 0) (hashes 0) 0 count rho)
      (exitState (states count) (hashes count) count rho) := by
  let I : Nat → State := fun i =>
    if i < count then loopState (states i) (hashes i) i count rho
    else exitState (states i) (hashes i) count rho
  have hb : ∀ i, i < count → GasSteps (I i) (I (i + 1)) := by
    intro i hi
    have a := hambient (i + 1) (by omega)
    by_cases hn : i + 1 < count
    · have gp := StaggerPersistentLoopSites.gasSteps_continue (states (i + 1)) (hashes (i + 1))
        (offsetWord i) (limitWord count) rho (by omega) a.running
        (next_continue i count hn hbound) a.code a.fork a.notPrecompile
      rw [next_offset i count hi hbound] at gp
      simpa only [I, if_pos hi, if_pos hn, loopState, postState] using (hblock i hi).trans gp
    · have he : i + 1 = count := by omega
      have gp := StaggerPersistentLoopSites.gasSteps_exit (states (i + 1)) (hashes (i + 1))
        (offsetWord i) (limitWord count) rho (by omega) a.running
        (next_exit i count he hbound) a.code a.fork a.notPrecompile
      rw [next_offset i count hi hbound, he] at gp
      have gb := hblock i hi
      rw [he] at gb
      simpa only [I, if_pos hi, if_neg hn, he, if_neg (Nat.lt_irrefl count), loopState, postState, exitState,
        offsetWord, limitWord] using gb.trans gp
  have g := GasSteps.iterateBounded (I := I) count hb
  simpa only [I, if_pos hcount, if_neg (Nat.lt_irrefl count)] using g

#print axioms next_offset
#print axioms run_blocks
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopInduction
