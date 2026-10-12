import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTemplate

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Near-dense selector certificate

The live J2 selector uses this generic prefix through RecognitionSelectorRaw;
J2Payload connects its offsets to the digest bytes in the installed artifact.
Fourteen non-overlapping twenty-byte rows fit in a 304-byte tail. Offsets count backwards
from CODESIZE, so unused gaps can contain arbitrary bytes. The arbitrary-state
execution theorem preserves every field except PC and stack.
-/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.NearDenseSelectorRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace
private theorem hadd_eq (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem hsub_eq (a b : UInt256) : a - b = UInt256.sub a b := rfl

def prefixTemplate : List Instr :=
  [ .push ⟨1, by decide⟩ (UInt256.ofNat 20),
    .push ⟨2, by decide⟩ (UInt256.ofNat 508),
    .op .CALLDATASIZE,
    .push ⟨7, by decide⟩ (UInt256.ofNat 2961358021345947),
    .op .DIV,
    .op .AND,
    .op .CODESIZE,
    .op .SUB,
    .push ⟨1, by decide⟩ (UInt256.ofNat 12) ]

def offset (size : Nat) : UInt256 :=
  UInt256.land
    (UInt256.div (UInt256.ofNat 2961358021345947) (UInt256.ofNat size))
    (UInt256.ofNat 508)

def selected (codesize : UInt256) (size : Nat) : UInt256 :=
  UInt256.sub codesize (offset size)

theorem run_prefix (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1010) (hrun : s.halt = .Running) :
    runInstrSeq prefixTemplate {s with pc := pc, stack := rho} =
      some {s with
        pc := pcAfter pc prefixTemplate
        stack := 12 :: selected (UInt256.ofNat s.executionEnv.code.size)
          s.executionEnv.calldata.size :: 20 :: rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 10) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [prefixTemplate, selected, offset, runInstrSeq,
    DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    Nat.add_assoc, hrun, hbase, hcap, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [hadd_eq, hsub_eq, RawExpressionAC.add_assoc,
    RawExpressionAC.add_comm, RawExpressionAC.add_left_comm,
    RawExpressionAC.land_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

theorem prefixTemplate_byteLength :
    (PcEncoding.assembleBytes prefixTemplate).length = 20 := by decide

theorem prefixTemplate_instructionCount : prefixTemplate.length = 9 := by decide

theorem prefixTemplate_gas : DenseScheduleTemplate.staticGas prefixTemplate = 27 := by decide

/-- (length, offset from code end), not physical row order. -/
def rows : List (Nat × Nat) :=
  [(1,152), (32,20), (64,264), (128,132), (256,64), (56,304),
   (120,176), (376,108), (1000,224), (63,40), (65,88), (55,244),
   (119,200), (31,284)]

theorem offsets_exact : ∀ row ∈ rows,
    (offset row.1).toNat = row.2 := by decide

theorem intervals_fit : ∀ row ∈ rows, 20 ≤ row.2 ∧ row.2 ≤ 304 := by decide

theorem intervals_disjoint : ∀ a ∈ rows, ∀ b ∈ rows,
    a.1 ≠ b.1 → a.2 + 20 ≤ b.2 ∨ b.2 + 20 ≤ a.2 := by decide

theorem lengths_nodup : (rows.map Prod.fst).Nodup := by decide

#print axioms run_prefix
#print axioms prefixTemplate_gas
#print axioms offsets_exact
#print axioms intervals_fit
#print axioms intervals_disjoint
end Challenge.Ripemd160.Submission.Proofs.Bytecode.NearDenseSelectorRaw
