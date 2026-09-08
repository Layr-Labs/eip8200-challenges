import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTable

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTablePrelude

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def initial (template : State) (pc base modulus : UInt256) (rest : List UInt256) : State :=
  { template with
    pc := pc
    stack := [base, modulus] ++ rest
    memory := ByteArray.empty
    activeWords := UInt256.ofNat 0 }

def initProgram : List Instr :=
  [.push 1 1, .push 0 0, .op .MSTORE,
   .op (.Dup ⟨0, by decide⟩), .push 1 32, .op .MSTORE]

theorem run_init (template : State) (pc base modulus : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions initProgram (initial template pc base modulus rest) =
    some (WindowTwentyOneTable.framed template (advancePC 8 pc) base modulus 2
      ([base, modulus] ++ rest)) := by
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hpush : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  have hzero : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have hmemory : WindowTableMemory.tableMemoryThrough base modulus 2 =
      WindowTableMemory.storeWord
        (WindowTableMemory.storeWord ByteArray.empty 0 (UInt256.ofNat 1)) 32 base := rfl
  simp [runInstructions, initProgram, initial, WindowTwentyOneTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap2, hcap3, hcap4, Nat.add_assoc,
    hmemory, hzero, WindowTableMemory.storeWord,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    advancePC, succ_eq_add, hpush, word_add_assoc]

def loadProgram : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op .CALLDATALOAD, .op (.Swap ⟨1, by decide⟩)]

theorem run_load (template : State) (pc base modulus exponentOffset : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hoffset : rest[4]? = some exponentOffset) :
    runInstructions loadProgram
      (WindowTwentyOneTable.framed template pc base modulus 2 ([base, modulus] ++ rest)) =
    some (WindowTwentyOneTable.framed template (advancePC 3 pc) base modulus 2
      ([modulus, base, MachineState.readWord template.executionEnv.calldata exponentOffset.toNat] ++ rest)) := by
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  simp [runInstructions, loadProgram, WindowTwentyOneTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap2, hcap3, Nat.add_assoc,
    List.getElem?_cons_succ, hoffset, List.exchange, advancePC]

def squareProgram : List Instr :=
  [.op (.Dup ⟨14, by decide⟩), .op (.Dup ⟨15, by decide⟩), .op .MULMOD]

private theorem run_square (template : State) (pc base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions squareProgram
      (WindowTwentyOneTable.framed template pc base modulus 2
        (List.replicate 14 modulus ++ [base, exponent] ++ rest)) =
    some (WindowTwentyOneTable.framed template (advancePC 3 pc) base modulus 2
      (WindowMath.tableWord base modulus 2 :: List.replicate 13 modulus ++
        [base, exponent] ++ rest)) := by
  have hcap16 : rest.length + 16 < 1024 := by omega
  have hcap17 : rest.length + 17 < 1024 := by omega
  have hcap18 : rest.length + 18 < 1024 := by omega
  simp [runInstructions, squareProgram, WindowTwentyOneTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap16, hcap17, hcap18, Nat.add_assoc,
    List.replicate, WindowMath.tableWord, advancePC]

def stagedProgram : List Instr :=
  List.replicate 13 (.op (.Dup ⟨0, by decide⟩)) ++ squareProgram

theorem run_staged (template : State) (pc base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions stagedProgram
      (WindowTwentyOneTable.framed template pc base modulus 2 ([modulus, base, exponent] ++ rest)) =
    some (WindowTwentyOneTable.framed template (advancePC 16 pc) base modulus 2
      (WindowMath.tableWord base modulus 2 :: List.replicate 13 modulus ++
        [base, exponent] ++ rest)) := by
  let core := WindowTwentyOneTable.framed template pc base modulus 2 []
  have hd := WindowTwentyOneStage.run_topCopies core pc modulus ([base, exponent] ++ rest) 13
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hs := run_square template (advancePC 13 pc) base modulus exponent rest hrest
  have hd' : runInstructions (List.replicate 13 (.op (.Dup ⟨0, by decide⟩)))
      (WindowTwentyOneTable.framed template pc base modulus 2 ([modulus, base, exponent] ++ rest)) =
    some (WindowTwentyOneTable.framed template (advancePC 13 pc) base modulus 2
      (List.replicate 14 modulus ++ [base, exponent] ++ rest)) := by
    simpa only [core, WindowTwentyOneStage.framed, WindowTwentyOneTable.framed,
      List.cons_append, List.nil_append, List.append_assoc] using hd
  have both := runInstructions_append_some _ _ _ _ _ hd' hs
  simpa only [stagedProgram, ← advancePC_add, show 13 + 3 = 16 by decide] using both

def program : List Instr :=
  initProgram ++ loadProgram ++ stagedProgram ++ WindowTwentyOneTable.storeProgram 1 2

def endPC (pc : UInt256) : UInt256 :=
  WindowTwentyOneTable.storePC 1 (advancePC 16 (advancePC 3 (advancePC 8 pc)))

theorem run_prelude (template : State) (pc base modulus exponentOffset : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hoffset : rest[4]? = some exponentOffset) :
    runInstructions program (initial template pc base modulus rest) =
    some (WindowTwentyOneTable.state template (endPC pc) base modulus
      (MachineState.readWord template.executionEnv.calldata exponentOffset.toNat) 2 rest) := by
  let exponent := MachineState.readWord template.executionEnv.calldata exponentOffset.toNat
  have hi := run_init template pc base modulus rest hrest
  have hl := run_load template (advancePC 8 pc) base modulus exponentOffset rest hrest hoffset
  have hs := run_staged template (advancePC 3 (advancePC 8 pc)) base modulus exponent rest hrest
  have ht := WindowTwentyOneTable.run_store template (advancePC 16 (advancePC 3 (advancePC 8 pc)))
    base modulus 2 (by decide) 1 (by decide)
    (List.replicate 13 modulus ++ [base, exponent] ++ rest)
    (by simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]; omega)
  have his := runInstructions_append_some _ _ _ _ _ hi hl
  have hist := runInstructions_append_some _ _ _ _ _ his hs
  have hall := runInstructions_append_some _ _ _ _ _ hist ht
  simpa only [program, endPC, WindowTwentyOneTable.state, exponent, List.cons_append,
    List.append_assoc] using hall

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTablePrelude
