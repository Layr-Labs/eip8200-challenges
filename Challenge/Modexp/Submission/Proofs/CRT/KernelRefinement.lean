import Challenge.Modexp.Submission.Proofs.CRT.CRTKernelExecution
import Challenge.Modexp.Submission.Proofs.CRT.MixedInput
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000

namespace HistoricalSearch.KernelRefinement
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open HistoricalSearch.GeneratedArithmetic HistoricalSearch.ConcreteArithmetic
open HistoricalSearch.ColumnMemory HistoricalSearch.ColumnSequence
open HistoricalSearch.SequenceResult HistoricalSearch.MixedMontgomery

theorem model_eq_states (s : State) (minv : UInt256) (n : Nat → UInt256) (rest : List UInt256) :
    GeneratedColumns.kernelModel s modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest =
      states s minv n rest 17 := by
  have h0 : GeneratedColumns.col0Model s modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest = states s minv n rest 1 := by rfl
  have h1 : GeneratedColumns.col1Model (states s minv n rest 1) ((states s minv n rest 1).stack.headD (UInt256.ofNat 0)) modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest = states s minv n rest 2 := by rfl
  have h2 : GeneratedColumns.col2Model (states s minv n rest 2) ((states s minv n rest 2).stack.headD (UInt256.ofNat 0)) modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest = states s minv n rest 3 := by rfl
  have h3 : GeneratedColumns.col3Model (states s minv n rest 3) ((states s minv n rest 3).stack.headD (UInt256.ofNat 0)) modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest = states s minv n rest 4 := by rfl
  have h4 : GeneratedColumns.col4Model (states s minv n rest 4) ((states s minv n rest 4).stack.headD (UInt256.ofNat 0)) modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest = states s minv n rest 5 := by rfl
  have h5 : GeneratedColumns.col5Model (states s minv n rest 5) ((states s minv n rest 5).stack.headD (UInt256.ofNat 0)) modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest = states s minv n rest 6 := by rfl
  have h6 : GeneratedColumns.col6Model (states s minv n rest 6) ((states s minv n rest 6).stack.headD (UInt256.ofNat 0)) modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest = states s minv n rest 7 := by rfl
  have h7 : GeneratedColumns.col7Model (states s minv n rest 7) ((states s minv n rest 7).stack.headD (UInt256.ofNat 0)) modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest = states s minv n rest 8 := by rfl
  have h8 : GeneratedColumns.col8Model (states s minv n rest 8) ((states s minv n rest 8).stack.headD (UInt256.ofNat 0)) modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest = states s minv n rest 9 := by rfl
  have h9 : GeneratedColumns.col9Model (states s minv n rest 9) ((states s minv n rest 9).stack.headD (UInt256.ofNat 0)) modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest = states s minv n rest 10 := by rfl
  have h10 : GeneratedColumns.col10Model (states s minv n rest 10) ((states s minv n rest 10).stack.headD (UInt256.ofNat 0)) modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest = states s minv n rest 11 := by rfl
  have h11 : GeneratedColumns.col11Model (states s minv n rest 11) ((states s minv n rest 11).stack.headD (UInt256.ofNat 0)) modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest = states s minv n rest 12 := by rfl
  have h12 : GeneratedColumns.col12Model (states s minv n rest 12) ((states s minv n rest 12).stack.headD (UInt256.ofNat 0)) modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest = states s minv n rest 13 := by rfl
  have h13 : GeneratedColumns.col13Model (states s minv n rest 13) ((states s minv n rest 13).stack.headD (UInt256.ofNat 0)) modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest = states s minv n rest 14 := by rfl
  have h14 : GeneratedColumns.col14Model (states s minv n rest 14) ((states s minv n rest 14).stack.headD (UInt256.ofNat 0)) modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest = states s minv n rest 15 := by rfl
  have h15 : GeneratedColumns.col15Model (states s minv n rest 15) ((states s minv n rest 15).stack.headD (UInt256.ofNat 0)) modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest = states s minv n rest 16 := by rfl
  have h16 : GeneratedColumns.col16Model (states s minv n rest 16) ((states s minv n rest 16).stack.headD (UInt256.ofNat 0)) modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv rest = states s minv n rest 17 := by rfl
  simp only [GeneratedColumns.kernelModel, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]

theorem run_states (s : State) (minv : UInt256) (n : Nat → UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrest : 1 ≤ rest.length) (hzero : rest.headD (UInt256.ofNat 0) = UInt256.ofNat 0)
    (hact : 88 ≤ s.activeWords.toNat)
    (hrestore0 : UInt256.land maskWord (MachineState.readWord s.memory 224) = n 0)
    (hrestore8 : UInt256.shiftRight (MachineState.readWord s.memory 0) (UInt256.ofNat 160) = n 8)
    (hrestoreInv : MachineState.readWord s.memory 2720 = minv) :
    runInstructions GeneratedColumns.kernelProgram
      {s with pc := UInt256.ofNat 5859, stack := modulusWord :: n 0 :: n 1 :: n 2 :: n 3 :: n 4 :: n 5 :: n 6 :: n 7 :: n 8 :: maskWord :: minv :: rest} =
      some (states s minv n rest 17) := by
  rw [GeneratedColumns.kernel_run s modulusWord (n 0) (n 1) (n 2) (n 3) (n 4)
    (n 5) (n 6) (n 7) (n 8) maskWord minv rest hcap hrest hzero hact rfl hrestore0 hrestore8 hrestoreInv,
    model_eq_states]

#print axioms model_eq_states
#print axioms run_states

theorem run_contract (s : State) (minv : UInt256) (n : Nat → UInt256) (rest : List UInt256) (A N : Nat)
    (hcap : rest.length ≤ 998) (hrest : 1 ≤ rest.length) (hzero : rest.headD (UInt256.ofNat 0) = UInt256.ofNat 0)
    (hact : 88 ≤ s.activeWords.toNat)
    (hrestore0 : UInt256.land maskWord (MachineState.readWord s.memory 224) = n 0)
    (hrestore8 : UInt256.shiftRight (MachineState.readWord s.memory 0) (UInt256.ofNat 160) = n 8)
    (hrestoreInv : MachineState.readWord s.memory 2720 = minv)
    (ha : ∀ i < 9, (aRead s.memory i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (ha8 : (aRead s.memory 8).toNat < 2^96) (hn8 : (n 8).toNat < 2^96)
    (hAvalue : weighted radix 9 (fun i => (aRead s.memory i).toNat) = A)
    (hNvalue : weighted radix 9 (fun i => (n i).toNat) = N)
    (hn0 : (n 0).toNat = N % radix) (hinv : (N*minv.toNat+1) % 2^256 = 0)
    (hAR : A < 2^2048) (hN : 0 < N) (hNR : N < 2^2048) (hodd : Odd N) :
    runInstructions GeneratedColumns.kernelProgram
      {s with pc := UInt256.ofNat 5859, stack := modulusWord :: n 0 :: n 1 :: n 2 :: n 3 :: n 4 :: n 5 :: n 6 :: n 7 :: n 8 :: maskWord :: minv :: rest} =
      some (states s minv n rest 17) ∧
    (∀ i < 9, (dRead (states s minv n rest 17).memory i).toNat < radix) ∧
    output s minv n rest < 2^2048+N ∧
    normalize (2^2048) N (output s minv n rest) < 2^2048 ∧
    normalize (2^2048) N (output s minv n rest) % N =
      Challenge.Modexp.Submission.Proofs.Fast.Model.montMul N (2^2048) A A := by
  exact ⟨run_states s minv n rest hcap hrest hzero hact hrestore0 hrestore8 hrestoreInv,
    KernelArithmetic.contract s minv n rest A N ha hn ha8 hn8 hAvalue hNvalue hn0 hinv hAR hN hNR hodd⟩

#print axioms run_contract

end HistoricalSearch.KernelRefinement
