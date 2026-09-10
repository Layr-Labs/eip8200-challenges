import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidDefs
import Challenge.Modexp.Submission.Proofs.Bytecode.CiosCachedRoundedCarry

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000


namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidWords

open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

def firstProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .MUL,
   .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨1, by decide⟩), .op .MULMOD]

def highProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT,
   .op (.Dup ⟨2, by decide⟩), .op .ADD, .op (.Swap ⟨0, by decide⟩), .op .SUB]

def lowProgram : List Instr :=
  [.op (.Swap ⟨0, by decide⟩), .push 0 0, .op .LT, .op .ADD]

def roundedProgram : List Instr := CiosCachedRoundedCarry.newProgram.take 7

def program : List Instr := firstProgram ++ roundedProgram

theorem run_first (s : State) (x mu bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions firstProgram
      (framed s (UInt256.ofNat 4631) ([x, mu, mu] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4638)
      ([UInt256.mulMod x mu maxWord, x*mu, mu] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) := by
  have hc11 : rest.length+12 < 1024 := by omega
  have hc12 : rest.length+13 < 1024 := by omega
  have hc13 : rest.length+14 < 1024 := by omega
  simp [firstProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    baseStack, framed, hc11, hc12, hc13, allOnes_value, maxWord, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_high (s : State) (mm lo mu bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions highProgram
      (framed s (UInt256.ofNat 4638) ([mm, lo, mu] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4645)
      ([mm-(lo+UInt256.lt mm lo), lo, mu] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) := by
  have hc11 : rest.length+12 < 1024 := by omega
  have hc12 : rest.length+13 < 1024 := by omega
  have hc13 : rest.length+14 < 1024 := by omega
  simp [highProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    baseStack, framed, hc11, hc12, hc13, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_low (s : State) (hi lo mu bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions lowProgram
      (framed s (UInt256.ofNat 4645) ([hi, lo, mu] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4649)
      ([UInt256.isZero (UInt256.isZero lo)+hi, mu] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) := by
  have hc11 : rest.length+12 < 1024 := by omega
  have hc12 : rest.length+13 < 1024 := by omega
  simp [lowProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    baseStack, framed, hc11, hc12, zero_lt_eq_double_isZero, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_rounded (s : State) (mm lo mu bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions roundedProgram
      (framed s (UInt256.ofNat 4638) ([mm, lo, mu] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4645)
      ([UInt256.lt (UInt256.ofNat 0) lo + (mm-(lo+UInt256.lt mm lo)), mu] ++
        baseStack bi pbi paEnd pbEnd flag dst ret rest)) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  simp [roundedProgram, CiosCachedRoundedCarry.newProgram, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, baseStack, framed, ← allOnes_not,
    hc12, hc13, hc14, Nat.add_assoc, Challenge.EvmProof.Word.succ_ofNat_mod]
  exact (CiosCachedRoundedCarry.rounded_high mm lo).symm

theorem run_words (s : State) (x mu bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions program
      (framed s (UInt256.ofNat 4631) ([x, mu, mu] ++ baseStack bi pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4645)
      ([UInt256.isZero (UInt256.isZero (x*mu))+mulHi x mu, mu] ++
        baseStack bi pbi paEnd pbEnd flag dst ret rest)) := by
  have hf := run_first s x mu bi pbi paEnd pbEnd flag dst ret rest hcap
  have hr := run_rounded s (UInt256.mulMod x mu maxWord) (x*mu) mu
    bi pbi paEnd pbEnd flag dst ret rest hcap
  have hz : UInt256.ofNat 0 = ({ val := 0 } : UInt256) := by decide
  simpa only [program, hz, zero_lt_eq_double_isZero, mulHi] using
    (runInstructions_append_some _ _ _ _ _ hf hr)

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidWords
