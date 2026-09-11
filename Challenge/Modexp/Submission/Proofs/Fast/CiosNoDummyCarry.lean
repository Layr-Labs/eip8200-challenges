import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore

set_option warningAsError true
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosNoDummyCarry

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore

def multiplyProgram : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL,
   .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .MULMOD]

def highProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT,
   .op (.Dup ⟨2, by decide⟩), .op (.Swap ⟨1, by decide⟩), .op .SUB, .op .SUB]

def productProgram : List Instr := multiplyProgram ++ highProgram

theorem run_multiply (s : State) (pc x y : UInt256)
    (rest : List UInt256) (hrest : rest.length+5 < 1024) :
    runInstructions multiplyProgram (framed s pc ([maxWord,x,y] ++ rest)) =
    some (framed s (advancePC 6 pc) ([UInt256.mulMod y x maxWord,x*y,y] ++ rest)) := by
  have hc3 : rest.length+3 < 1024 := by omega
  have hc4 : rest.length+4 < 1024 := by omega
  simp [runInstructions,multiplyProgram,Challenge.EvmProof.Stepper.runInstr,framed,
    advancePC,hrest,hc3,hc4,List.exchange]

theorem run_high (s : State) (pc hi lo y : UInt256)
    (rest : List UInt256) (hrest : rest.length+5 < 1024) :
    runInstructions highProgram (framed s pc ([hi,lo,y] ++ rest)) =
    some (framed s (advancePC 7 pc) ([(hi-UInt256.lt hi lo)-lo,lo,y] ++ rest)) := by
  have hc3 : rest.length+3 < 1024 := by omega
  have hc4 : rest.length+4 < 1024 := by omega
  simp [runInstructions,highProgram,Challenge.EvmProof.Stepper.runInstr,framed,
    advancePC,hrest,hc3,hc4,List.exchange]

theorem sub_reverse (a b : UInt256) :
    a-b = UInt256.ofNat 0-(b-a) := by
  apply Challenge.EvmProof.Word.word_ext
  have ha : a.toNat < 2^256 := a.val.isLt
  have hb : b.toNat < 2^256 := b.val.isLt
  simp only [Challenge.EvmProof.Word.word_toNat_sub,
    Challenge.EvmProof.Word.word_toNat_ofNat,Nat.zero_mod]
  omega

theorem high_eq (x y : UInt256) :
    ((UInt256.mulMod y x maxWord)-UInt256.lt (UInt256.mulMod y x maxWord) (x*y))-(x*y) =
      partialCarry x y (UInt256.ofNat 0) := by
  have hz : UInt256.gt (UInt256.ofNat 0) (x*y+UInt256.ofNat 0) = UInt256.ofNat 0 := by
    simp [UInt256.gt,Challenge.EvmProof.Word.word_toNat_ofNat]
  rw [partialCarry,hz,sub_reverse (UInt256.mulMod y x maxWord)]

theorem run_product (s : State) (pc x y : UInt256)
    (rest : List UInt256) (hrest : rest.length+5 < 1024) :
    runInstructions productProgram (framed s pc ([maxWord,x,y] ++ rest)) =
    some (framed s (advancePC 13 pc) ([partialCarry x y (UInt256.ofNat 0),x*y,y] ++ rest)) := by
  have hm := run_multiply s pc x y rest hrest
  have hh := run_high s (advancePC 6 pc) (UInt256.mulMod y x maxWord) (x*y) y rest hrest
  rw [high_eq] at hh
  simpa only [productProgram,advancePC] using runInstructions_append_some _ _ _ _ _ hm hh

#print axioms run_product

end Challenge.Modexp.Submission.Proofs.Fast.CiosNoDummyCarry
