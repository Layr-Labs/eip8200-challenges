import Challenge.Modexp.Submission.Proofs.Fast.CiosEndAroundCarry
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidMemory

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidProduct

open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosEndAroundCarry
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidMemory

def loadLow : List Instr := productProgram.take 3
def makeMu : List Instr := (productProgram.drop 3).take 5
def loadMod : List Instr := (productProgram.drop 8).take 3
def makeModProduct : List Instr := (productProgram.drop 11).take 4
def finishCarry : List Instr := productProgram.drop 15

theorem program_eq : productProgram =
    (((loadLow ++ makeMu) ++ loadMod) ++ makeModProduct) ++ finishCarry := rfl

theorem run_loadLow (s : State) (bi pbi paEnd pbEnd flag dst ret : UInt256) (n : Nat)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hn : n ≤ 8)
    (hact : 91 ≤ s.activeWords.toNat)
    (haddr : MachineState.readWord s.memory 2880 = UInt256.ofNat (2080+32*n)) :
    runInstructions loadLow
      (framed s (UInt256.ofNat 4560) (baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4558)
      ([MachineState.readWord s.memory (2080+32*n)] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) := by
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  have hp9440 : (2880 : UInt256).toNat = 2880 := by decide
  have hmod : (2080+32*n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      2080+32*n := Nat.mod_eq_of_lt (by omega)
  have hactP := activeWords_fix s 2880 32 (by decide) (by omega) hact
  have hactQ := activeWords_fix s (2080+32*n) 32 (by decide) (by omega) hact
  simp [loadLow, productProgram, midProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, baseStack, hp9440, hc9, hc10, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, haddr, hmod, hactP, hactQ]

theorem run_makeMu (s : State) (bi pbi paEnd pbEnd flag dst ret t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 91 ≤ s.activeWords.toNat) :
    runInstructions makeMu
      (framed s (UInt256.ofNat 4558) ([t0] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4500)
      ([t0, MachineState.readWord s.memory 2816 * t0] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) := by
  have hc10 : rest.length+10 < 1024 := by omega
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  have hp9376 : (2816 : UInt256).toNat = 2816 := by decide
  have hactMI := activeWords_fix s 2816 32 (by decide) (by omega) hact
  simp [makeMu, productProgram, midProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, baseStack, hp9376, hc10, hc11, hc12, List.exchange,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, hactMI]

theorem run_loadMod (s : State) (bi pbi paEnd pbEnd flag dst ret : UInt256)
    (n : Nat) (mu t0 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hn : n ≤ 8) (hact : 91 ≤ s.activeWords.toNat)
    (haddr : MachineState.readWord s.memory 2848 = UInt256.ofNat (32*n-32)) :
    runInstructions loadMod
      (framed s (UInt256.ofNat 4500) ([t0, mu] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4501)
      ([MachineState.readWord s.memory (32*n-32), t0, mu] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) := by
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  have hp9408 : (2848 : UInt256).toNat = 2848 := by decide
  have hmod : (32*n-32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32*n-32 := Nat.mod_eq_of_lt (by omega)
  have hactP := activeWords_fix s 2848 32 (by decide) (by omega) hact
  have hactQ := activeWords_fix s (32*n-32) 32 (by decide) (by omega) hact
  simp [loadMod, productProgram, midProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, baseStack, hp9408, hc11, hc12, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, haddr, hmod, hactP, hactQ]

theorem run_makeModProduct (s : State) (bi pbi paEnd pbEnd flag dst ret m0 mu t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions makeModProduct
      (framed s (UInt256.ofNat 4501) ([m0, t0, mu] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4507)
      ([UInt256.mulMod m0 mu maxWord, t0, mu] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) := by
  have hc12 : rest.length+12 < 1024 := by omega
  have hc13 : rest.length+13 < 1024 := by omega
  have hc14 : rest.length+14 < 1024 := by omega
  simp [makeModProduct, productProgram, midProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, baseStack, hc12, hc13, hc14, allOnes_value, maxWord, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_finishCarry (s : State) (bi pbi paEnd pbEnd flag dst ret mm mu t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions finishCarry
      (framed s (UInt256.ofNat 4507) ([mm, t0, mu] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4510)
      ([endCarry t0 mm, mu] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) := by
  have hc12 : rest.length+12 < 1024 := by omega
  have hc13 : rest.length+13 < 1024 := by omega
  simp [finishCarry, productProgram, midProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, baseStack, endCarry, hc12, hc13, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_product (s : State) (n : Nat) (bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 91 ≤ s.activeWords.toNat)
    (_hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hml : MachineState.readWord s.memory 2848 = UInt256.ofNat (32*n-32))
    (htl : MachineState.readWord s.memory 2880 = UInt256.ofNat (2080+32*n))
    (hminv : inverseInvariant s.memory n) :
    runInstructions productProgram
      (framed s (UInt256.ofNat 4560) (baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (product s n bi pbi paEnd pbEnd flag dst ret rest) := by
  let t0 := MachineState.readWord s.memory (2080+32*n)
  let inv := MachineState.readWord s.memory 2816
  let m0 := MachineState.readWord s.memory (32*n-32)
  have h1 := run_loadLow s bi pbi paEnd pbEnd flag dst ret n rest hcap hn32 hact htl
  have h2 := run_makeMu s bi pbi paEnd pbEnd flag dst ret t0 rest hcap hact
  have h3 := run_loadMod s bi pbi paEnd pbEnd flag dst ret n (inv*t0) t0 rest hcap hn32 hact hml
  have h4 := run_makeModProduct s bi pbi paEnd pbEnd flag dst ret m0 (inv*t0) t0 rest hcap
  have h5 := run_finishCarry s bi pbi paEnd pbEnd flag dst ret
    (UInt256.mulMod m0 (inv*t0) maxWord) (inv*t0) t0 rest hcap
  have hc := row_carry_swapped m0 inv t0 hminv
  have h12 := runInstructions_append_some _ _ _ _ _ h1 h2
  have h123 := runInstructions_append_some _ _ _ _ _ h12 h3
  have h1234 := runInstructions_append_some _ _ _ _ _ h123 h4
  have h12345 := runInstructions_append_some _ _ _ _ _ h1234 h5
  rw [← program_eq] at h12345
  simpa only [hc, product, rowC0, rowMu, t0, inv, m0] using h12345

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidProduct
