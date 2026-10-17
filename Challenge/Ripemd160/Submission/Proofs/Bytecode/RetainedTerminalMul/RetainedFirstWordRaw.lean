import Challenge.Ripemd160.Submission.Proofs.Bytecode.ReverseLiteralRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardGrouping

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

/-! Backend model only: first-word XOR seeds a reverse fold over words 1..k.
No artifact binding or universal bytecode certificate is asserted here. -/
namespace RetainedFirstWordResearch
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace DirectLiteralModel DirectLiteralRawV4

/-- Fold k, k-1, ..., 1, retaining the already-tested word-zero accumulator. -/
def reversePositive (input : ByteArray) (a : UInt256) : Nat → UInt256
  | 0 => a
  | k+1 => reversePositive input (UInt256.lor (diff input (k+1)) a) k

theorem reversePositive_seed (input : ByteArray) (a : UInt256) (k : Nat) :
    reversePositive input (UInt256.lor (diff input 0) a) k =
      ReverseLiteralRaw.rev input a (k+1) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [reversePositive]
    have hc : UInt256.lor (diff input (k+1)) (UInt256.lor (diff input 0) a) =
        UInt256.lor (diff input 0) (UInt256.lor (diff input (k+1)) a) := by
      apply Word.word_ext
      simp only [Word.word_toNat_lor]
      ac_rfl
    rw [hc, ih]
    rfl

/-- No memory operation: consume the first word retained by the anchor check. -/
def seedTemplate : List Instr :=
  [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 0), .op .XOR]

theorem run_seed (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq seedTemplate {s with
      pc := pc
      stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} =
      some {s with
        pc := pcAfter pc seedTemplate
        stack := diff s.executionEnv.calldata 0 :: rho} := by
  have hcap0 : rho.length + 1 < 1024 := by omega
  have hcap1 : rho.length + 2 < 1024 := by omega
  simp (discharger := omega) [seedTemplate, diff, runInstrSeq,
    DataStepper.runInstr, pcAfter, hrun, hcap0, hcap1, UInt256.succ, Instr.size,
    Nat.add_assoc, Word.literal_eq_ofNat]
  repeat first | apply And.intro | rfl
  exact DirectGuard.xor_comm' _ _

#print axioms reversePositive_seed
#print axioms run_seed
end RetainedFirstWordResearch
