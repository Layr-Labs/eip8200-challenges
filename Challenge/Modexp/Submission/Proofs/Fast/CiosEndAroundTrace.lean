import Challenge.Modexp.Submission.Proofs.Fast.CiosEndAroundCarry
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidDefs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosEndAroundTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosEndAroundCarry

/-- Stable-size form of the end-around carry row head. -/
def program : List Instr :=
  [.push 2 9440, .op .MLOAD, .op .MLOAD, .op (.Dup ⟨0, by decide⟩),
   .push 2 9376, .op .MLOAD, .op .MUL, .op (.Dup ⟨0, by decide⟩),
   .push 2 9408, .op .MLOAD, .op .MLOAD, .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨1, by decide⟩), .op .MULMOD,
   .op (.Swap ⟨0, by decide⟩), .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨1, by decide⟩), .op .GT, .op .ADD,
   .op .JUMPDEST, .op .JUMPDEST]

def loadLow : List Instr := program.take 3
def makeMu : List Instr := (program.drop 3).take 4
def loadMod : List Instr := (program.drop 7).take 4
def makeModProduct : List Instr := (program.drop 11).take 3
def finishCarry : List Instr := program.drop 14

theorem split_program : program =
    (((loadLow ++ makeMu) ++ loadMod) ++ makeModProduct) ++ finishCarry := rfl

set_option linter.unusedSimpArgs false in
theorem run_loadLow (s : State) (bi pbi paEnd pbEnd flag dst ret : UInt256) (n : Nat)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hn : n ≤ 32) (hact : 296 ≤ s.activeWords.toNat)
    (haddr : MachineState.readWord s.memory 9440 = UInt256.ofNat (8224+32*n)) :
    runInstructions loadLow
      (framed s (UInt256.ofNat 4929) (baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4930) ([MachineState.readWord s.memory (8224+32*n)] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) := by
  have hp9408 : (9408 : UInt256).toNat = 9408 := by decide
  have hp9440 : (9440 : UInt256).toNat = 9440 := by decide
  have hp9376 : (9376 : UInt256).toNat = 9376 := by decide
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length+1 < 1024 := by omega
  have h2 : rest.length+2 < 1024 := by omega
  have h3 : rest.length+3 < 1024 := by omega
  have h4 : rest.length+4 < 1024 := by omega
  have h5 : rest.length+5 < 1024 := by omega
  have h6 : rest.length+6 < 1024 := by omega
  have h7 : rest.length+7 < 1024 := by omega
  have h8 : rest.length+8 < 1024 := by omega
  have h9 : rest.length+9 < 1024 := by omega
  have h10 : rest.length+10 < 1024 := by omega
  have h11 : rest.length+11 < 1024 := by omega
  have h12 : rest.length+12 < 1024 := by omega
  have h13 : rest.length+13 < 1024 := by omega
  have h14 : rest.length+14 < 1024 := by omega
  have hmod : (8224+32*n) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 8224+32*n := Nat.mod_eq_of_lt (by omega)
  have hactP := activeWords_fix s 9440 32 (by decide) (by omega) hact
  have hactQ := activeWords_fix s (8224+32*n) 32 (by decide) (by omega) hact
  simp [loadLow, program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, baseStack, endCarry, hp9408, hp9440, hp9376, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    allOnes_value, maxWord, List.exchange, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, haddr, hmod, hactP, hactQ]

set_option linter.unusedSimpArgs false in
theorem run_makeMu (s : State) (bi pbi paEnd pbEnd flag dst ret : UInt256) (t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions makeMu
      (framed s (UInt256.ofNat 4930) ([t0] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4940) ([MachineState.readWord s.memory 9376 * t0, t0] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) := by
  have hp9408 : (9408 : UInt256).toNat = 9408 := by decide
  have hp9440 : (9440 : UInt256).toNat = 9440 := by decide
  have hp9376 : (9376 : UInt256).toNat = 9376 := by decide
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length+1 < 1024 := by omega
  have h2 : rest.length+2 < 1024 := by omega
  have h3 : rest.length+3 < 1024 := by omega
  have h4 : rest.length+4 < 1024 := by omega
  have h5 : rest.length+5 < 1024 := by omega
  have h6 : rest.length+6 < 1024 := by omega
  have h7 : rest.length+7 < 1024 := by omega
  have h8 : rest.length+8 < 1024 := by omega
  have h9 : rest.length+9 < 1024 := by omega
  have h10 : rest.length+10 < 1024 := by omega
  have h11 : rest.length+11 < 1024 := by omega
  have h12 : rest.length+12 < 1024 := by omega
  have h13 : rest.length+13 < 1024 := by omega
  have h14 : rest.length+14 < 1024 := by omega
  have hactMI := activeWords_fix s 9376 32 (by decide) (by omega) hact
  simp [makeMu, program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, baseStack, endCarry, hp9408, hp9440, hp9376, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    allOnes_value, maxWord, List.exchange, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hactMI]

set_option linter.unusedSimpArgs false in
theorem run_loadMod (s : State) (bi pbi paEnd pbEnd flag dst ret : UInt256) (n : Nat) (mu t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hn : n ≤ 32) (hact : 296 ≤ s.activeWords.toNat)
    (haddr : MachineState.readWord s.memory 9408 = UInt256.ofNat (32*n-32)) :
    runInstructions loadMod
      (framed s (UInt256.ofNat 4940) ([mu, t0] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4946) ([MachineState.readWord s.memory (32*n-32), mu, mu, t0] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) := by
  have hp9408 : (9408 : UInt256).toNat = 9408 := by decide
  have hp9440 : (9440 : UInt256).toNat = 9440 := by decide
  have hp9376 : (9376 : UInt256).toNat = 9376 := by decide
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length+1 < 1024 := by omega
  have h2 : rest.length+2 < 1024 := by omega
  have h3 : rest.length+3 < 1024 := by omega
  have h4 : rest.length+4 < 1024 := by omega
  have h5 : rest.length+5 < 1024 := by omega
  have h6 : rest.length+6 < 1024 := by omega
  have h7 : rest.length+7 < 1024 := by omega
  have h8 : rest.length+8 < 1024 := by omega
  have h9 : rest.length+9 < 1024 := by omega
  have h10 : rest.length+10 < 1024 := by omega
  have h11 : rest.length+11 < 1024 := by omega
  have h12 : rest.length+12 < 1024 := by omega
  have h13 : rest.length+13 < 1024 := by omega
  have h14 : rest.length+14 < 1024 := by omega
  have hmod : (32*n-32) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 32*n-32 := Nat.mod_eq_of_lt (by omega)
  have hactP := activeWords_fix s 9408 32 (by decide) (by omega) hact
  have hactQ := activeWords_fix s (32*n-32) 32 (by decide) (by omega) hact
  simp [loadMod, program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, baseStack, endCarry, hp9408, hp9440, hp9376, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    allOnes_value, maxWord, List.exchange, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, haddr, hmod, hactP, hactQ]

set_option linter.unusedSimpArgs false in
theorem run_makeModProduct (s : State) (bi pbi paEnd pbEnd flag dst ret : UInt256) (m0 mu t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)  :
    runInstructions makeModProduct
      (framed s (UInt256.ofNat 4946) ([m0, mu, mu, t0] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4949) ([UInt256.mulMod mu m0 maxWord, mu, t0] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) := by
  have hp9408 : (9408 : UInt256).toNat = 9408 := by decide
  have hp9440 : (9440 : UInt256).toNat = 9440 := by decide
  have hp9376 : (9376 : UInt256).toNat = 9376 := by decide
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length+1 < 1024 := by omega
  have h2 : rest.length+2 < 1024 := by omega
  have h3 : rest.length+3 < 1024 := by omega
  have h4 : rest.length+4 < 1024 := by omega
  have h5 : rest.length+5 < 1024 := by omega
  have h6 : rest.length+6 < 1024 := by omega
  have h7 : rest.length+7 < 1024 := by omega
  have h8 : rest.length+8 < 1024 := by omega
  have h9 : rest.length+9 < 1024 := by omega
  have h10 : rest.length+10 < 1024 := by omega
  have h11 : rest.length+11 < 1024 := by omega
  have h12 : rest.length+12 < 1024 := by omega
  have h13 : rest.length+13 < 1024 := by omega
  have h14 : rest.length+14 < 1024 := by omega

  simp [makeModProduct, program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, baseStack, endCarry, hp9408, hp9440, hp9376, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    allOnes_value, maxWord, List.exchange, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_finishCarry (s : State) (bi pbi paEnd pbEnd flag dst ret : UInt256) (mm mu t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)  :
    runInstructions finishCarry
      (framed s (UInt256.ofNat 4949) ([mm, mu, t0] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4955) ([endCarry mm t0, mu] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) := by
  have hp9408 : (9408 : UInt256).toNat = 9408 := by decide
  have hp9440 : (9440 : UInt256).toNat = 9440 := by decide
  have hp9376 : (9376 : UInt256).toNat = 9376 := by decide
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length+1 < 1024 := by omega
  have h2 : rest.length+2 < 1024 := by omega
  have h3 : rest.length+3 < 1024 := by omega
  have h4 : rest.length+4 < 1024 := by omega
  have h5 : rest.length+5 < 1024 := by omega
  have h6 : rest.length+6 < 1024 := by omega
  have h7 : rest.length+7 < 1024 := by omega
  have h8 : rest.length+8 < 1024 := by omega
  have h9 : rest.length+9 < 1024 := by omega
  have h10 : rest.length+10 < 1024 := by omega
  have h11 : rest.length+11 < 1024 := by omega
  have h12 : rest.length+12 < 1024 := by omega
  have h13 : rest.length+13 < 1024 := by omega
  have h14 : rest.length+14 < 1024 := by omega

  simp [finishCarry, program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, baseStack, endCarry, hp9408, hp9440, hp9376, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    allOnes_value, maxWord, List.exchange, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_program (s : State) (n : Nat) (bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32)
    (hml : MachineState.readWord s.memory 9408 = UInt256.ofNat (32*n-32))
    (htl : MachineState.readWord s.memory 9440 = UInt256.ofNat (8224+32*n))
    (hminv : ((MachineState.readWord s.memory (32*n-32)).toNat *
      (MachineState.readWord s.memory 9376).toNat + 1) % 2 ^ 256 = 0) :
    runInstructions program
      (framed s (UInt256.ofNat 4929) (baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (product s n bi pbi paEnd pbEnd flag dst ret rest) := by
  let t0 := MachineState.readWord s.memory (8224+32*n)
  let inv := MachineState.readWord s.memory 9376
  let m0 := MachineState.readWord s.memory (32*n-32)
  have h1 := run_loadLow s bi pbi paEnd pbEnd flag dst ret n rest hcap hn32 hact htl
  have h2 := run_makeMu s bi pbi paEnd pbEnd flag dst ret t0 rest hcap hact
  have h3 := run_loadMod s bi pbi paEnd pbEnd flag dst ret n (inv*t0) t0 rest hcap hn32 hact hml
  have h4 := run_makeModProduct s bi pbi paEnd pbEnd flag dst ret m0 (inv*t0) t0 rest hcap
  have h5 := run_finishCarry s bi pbi paEnd pbEnd flag dst ret
    (UInt256.mulMod (inv*t0) m0 maxWord) (inv*t0) t0 rest hcap
  have hc := row_carry m0 inv t0 hminv
  rw [mulMod_comm] at hc
  have h12 := runInstructions_append_some _ _ _ _ _ h1 h2
  have h123 := runInstructions_append_some _ _ _ _ _ h12 h3
  have h1234 := runInstructions_append_some _ _ _ _ _ h123 h4
  have h12345 := runInstructions_append_some _ _ _ _ _ h1234 h5
  rw [← split_program] at h12345
  simpa only [hc, product, rowC0, rowMu, t0, inv, m0] using h12345

end Challenge.Modexp.Submission.Proofs.Fast.CiosEndAroundTrace

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosEndAroundTrace.run_program
