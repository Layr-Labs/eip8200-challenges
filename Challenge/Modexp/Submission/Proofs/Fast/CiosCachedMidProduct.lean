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

def loadLow : List Instr := productProgram.take 2
def makeMu : List Instr := (productProgram.drop 2).take 4
def loadMod : List Instr := (productProgram.drop 6).take 1
def makeModProduct : List Instr := (productProgram.drop 7).take 4
def finishCarry : List Instr := productProgram.drop 11

theorem program_eq : productProgram =
    (((loadLow ++ makeMu) ++ loadMod) ++ makeModProduct) ++ finishCarry := rfl

set_option linter.unusedSimpArgs false in
theorem run_loadLow (s : State) (bi pbi paEnd pbEnd flag dst ret : UInt256) (n : Nat)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hn : n ≤ 32)
    (hact : 296 ≤ s.activeWords.toNat)
    (haddr : MachineState.readWord s.memory 9440 = UInt256.ofNat (8224+32*n))
    (hTL : rest[1]? = some (MachineState.readWord s.memory 9440)) :
    runInstructions loadLow
      (framed s (UInt256.ofNat 4562) (baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4564)
      ([MachineState.readWord s.memory (8224+32*n)] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) := by
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  have hp9440 : (9440 : UInt256).toNat = 9440 := by decide
  have hmod : (8224+32*n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8224+32*n := Nat.mod_eq_of_lt (by omega)
  have hactP := activeWords_fix s 9440 32 (by decide) (by omega) hact
  have hactQ := activeWords_fix s (8224+32*n) 32 (by decide) (by omega) hact
  simp [loadLow, productProgram, midProgram, hTL, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, baseStack, hp9440, hc9, hc10, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, haddr, hmod, hactP, hactQ]


theorem run_makeMu (s : State) (bi pbi paEnd pbEnd flag dst ret t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hInv : rest[0]? = some (MachineState.readWord s.memory 9376)) :
    runInstructions makeMu
      (framed s (UInt256.ofNat 4564) ([t0] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4568)
      ([t0, MachineState.readWord s.memory 9376 * t0] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) := by
  have hc10 : rest.length+10 < 1024 := by omega
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  simp [makeMu, productProgram, midProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, baseStack, hInv, hc10, hc11, hc12, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod]


theorem run_loadMod (s : State) (bi pbi paEnd pbEnd flag dst ret : UInt256)
    (n : Nat) (mu t0 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (_hn : n ≤ 32) (_hact : 296 ≤ s.activeWords.toNat)
    (_haddr : MachineState.readWord s.memory 9408 = UInt256.ofNat (32*n-32))
    (hret : ret = modulusValue s.memory n) :
    runInstructions loadMod
      (framed s (UInt256.ofNat 4568) ([t0, mu] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4569)
      ([MachineState.readWord s.memory (32*n-32), t0, mu] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) := by
  have hc11 : rest.length+11 < 1024 := by omega
  simp [loadMod, productProgram, midProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, baseStack, hc11, hret, modulusValue, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_makeModProduct (s : State) (bi pbi paEnd pbEnd flag dst ret m0 mu t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions makeModProduct
      (framed s (UInt256.ofNat 4569) ([m0, t0, mu] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4573)
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
      (framed s (UInt256.ofNat 4573) ([mm, t0, mu] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4579)
      ([endCarry t0 mm, mu] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) := by
  have hc12 : rest.length+12 < 1024 := by omega
  have hc13 : rest.length+13 < 1024 := by omega
  simp [finishCarry, productProgram, midProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, baseStack, endCarry, hc12, hc13, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_product (s : State) (n : Nat) (bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat)
    (_hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hml : MachineState.readWord s.memory 9408 = UInt256.ofNat (32*n-32))
    (htl : MachineState.readWord s.memory 9440 = UInt256.ofNat (8224+32*n))
    (hminv : inverseInvariant s.memory n) (hret : ret = modulusValue s.memory n)
    (hInv : rest[0]? = some (MachineState.readWord s.memory 9376))
    (hTL : rest[1]? = some (MachineState.readWord s.memory 9440)) :
    runInstructions productProgram
      (framed s (UInt256.ofNat 4562) (baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (product s n bi pbi paEnd pbEnd flag dst ret rest) := by
  let t0 := MachineState.readWord s.memory (8224+32*n)
  let inv := MachineState.readWord s.memory 9376
  let m0 := MachineState.readWord s.memory (32*n-32)
  have h1 := run_loadLow s bi pbi paEnd pbEnd flag dst ret n rest hcap hn32 hact htl hTL
  have h2 := run_makeMu s bi pbi paEnd pbEnd flag dst ret t0 rest hcap hInv
  have h3 := run_loadMod s bi pbi paEnd pbEnd flag dst ret n (inv*t0) t0 rest hcap hn32 hact hml hret
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
