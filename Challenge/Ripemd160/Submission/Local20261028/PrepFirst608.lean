import Challenge.Ripemd160.Submission.Local20261028.PrepFirstReady
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace RipemdSubmission20261101.First608
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof Challenge.EvmProof.Memory
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open RipemdMemoryBridge20261028
theorem read (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    MachineState.readWord (FirstTable.result5 s x rho).memory 608 =
      UInt256.ofNat 5708990770823839524233143877797980545530986752 := by
  rw [FirstMemory.actual_memory]
  apply Ordinary75.read_eq_of_bytes
  intro j hj
  simp only [FirstMemory.memory27, FirstMemory.memory26, FirstMemory.memory25,
    FirstMemory.memory24, FirstMemory.memory23, write_getD,
    if_neg (by omega : ¬ (864 ≤ 608+j ∧ 608+j < 864+32)),
    if_neg (by omega : ¬ (972 ≤ 608+j ∧ 608+j < 972+32)),
    if_neg (by omega : ¬ (814 ≤ 608+j ∧ 608+j < 814+32)),
    if_neg (by omega : ¬ (720 ≤ 608+j ∧ 608+j < 720+32)),
    if_neg (by omega : ¬ (738 ≤ 608+j ∧ 608+j < 738+32))]
  rw [FirstMemory.memory22, MachineState.writeBytes_getElem?_getD,
    readPadded_size, if_pos (by omega : 576 ≤ 608+j ∧ 608+j < 576+122)]
  have he : 608+j-576 = 32+j := by omega
  rw [he, FirstLayout.code_bytes s hc (32+j) (by omega)]
  have h : ∀ j : Fin 32, FirstLayout.value s.memory FirstLayout.literal22[32+j.val]! =
      PoolByte.byte (UInt256.ofNat 5708990770823839524233143877797980545530986752) j.val := by
    intro j; fin_cases j <;> rfl
  exact h ⟨j,hj⟩
#print axioms read
end RipemdSubmission20261101.First608
