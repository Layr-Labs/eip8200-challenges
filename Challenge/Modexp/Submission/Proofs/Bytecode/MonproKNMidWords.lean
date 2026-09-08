import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMidDefs

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMidWords

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel MonproKNCache MonproKNMidDefs
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

def firstProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .MUL,
   .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩), .op .MULMOD]

def highProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT,
   .op (.Dup ⟨2, by decide⟩), .op .ADD, .op (.Swap ⟨0, by decide⟩), .op .SUB]

def lowProgram : List Instr :=
  [.op (.Swap ⟨0, by decide⟩), .push 0 0, .op .LT, .op .ADD]

def program : List Instr := (firstProgram ++ highProgram) ++ lowProgram

theorem run_first (s : State) (x mu bi pbi paEnd pbEnd dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1007) :
    runInstructions firstProgram
      (framed s (UInt256.ofNat 2043) ([x, mu, mu] ++ baseStack bi pbi paEnd pbEnd dst ret rest)) =
    some (framed s (UInt256.ofNat 2050)
      ([UInt256.mulMod x mu maxWord, x*mu, mu] ++ baseStack bi pbi paEnd pbEnd dst ret rest)) := by
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  have hc13 : rest.length+13 < 1024 := by omega
  simp [firstProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    baseStack, framed, hc11, hc12, hc13, allOnes_value, maxWord, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_high (s : State) (mm lo mu bi pbi paEnd pbEnd dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1007) :
    runInstructions highProgram
      (framed s (UInt256.ofNat 2050) ([mm, lo, mu] ++ baseStack bi pbi paEnd pbEnd dst ret rest)) =
    some (framed s (UInt256.ofNat 2057)
      ([mm-(lo+UInt256.lt mm lo), lo, mu] ++ baseStack bi pbi paEnd pbEnd dst ret rest)) := by
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  have hc13 : rest.length+13 < 1024 := by omega
  simp [highProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    baseStack, framed, hc11, hc12, hc13, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_low (s : State) (hi lo mu bi pbi paEnd pbEnd dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1007) :
    runInstructions lowProgram
      (framed s (UInt256.ofNat 2057) ([hi, lo, mu] ++ baseStack bi pbi paEnd pbEnd dst ret rest)) =
    some (framed s (UInt256.ofNat 2061)
      ([UInt256.isZero (UInt256.isZero lo)+hi, mu] ++ baseStack bi pbi paEnd pbEnd dst ret rest)) := by
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  simp [lowProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    baseStack, framed, hc11, hc12, zero_lt_eq_double_isZero, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_words (s : State) (x mu bi pbi paEnd pbEnd dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1007) :
    runInstructions program
      (framed s (UInt256.ofNat 2043) ([x, mu, mu] ++ baseStack bi pbi paEnd pbEnd dst ret rest)) =
    some (framed s (UInt256.ofNat 2061)
      ([UInt256.isZero (UInt256.isZero (x*mu))+mulHi x mu, mu] ++
        baseStack bi pbi paEnd pbEnd dst ret rest)) := by
  exact runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _
      (run_first s x mu bi pbi paEnd pbEnd dst ret rest hcap)
      (run_high s (UInt256.mulMod x mu maxWord) (x*mu) mu
        bi pbi paEnd pbEnd dst ret rest hcap))
    (run_low s (mulHi x mu) (x*mu) mu bi pbi paEnd pbEnd dst ret rest hcap)

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMidWords
