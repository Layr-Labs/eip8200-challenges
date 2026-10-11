import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTable

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTablePrelude

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel WindowTwentyOneMsize

def initial (template : State) (pc base modulus : UInt256) (rest : List UInt256) : State :=
  { template with
    pc := pc
    stack := [base, modulus] ++ rest
    memory := ByteArray.empty
    activeWords := UInt256.ofNat 0 }

def initProgram : List Instr :=
  [.push 1 1, .push 0 0, .op .MSTORE,
   .op (.Dup ⟨0, by decide⟩), .op .MSIZE, .op .MSTORE]

theorem run_init (template : State) (pc base modulus : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructionsX initProgram (initial template pc base modulus rest) =
    some (WindowTwentyOneTable.framed template (advancePC 7 pc) base modulus 2
      ([base, modulus] ++ rest)) := by
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hpush : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  have hzero : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have hmemory : WindowTableMemory.tableMemoryThrough base modulus 2 =
      WindowTableMemory.storeWord
        (WindowTableMemory.storeWord ByteArray.empty 0 (UInt256.ofNat 1)) 32 base := rfl
  simp [runInstructionsX, runInstrX_msize, initProgram, initial, WindowTwentyOneTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap2, hcap3, hcap4, Nat.add_assoc,
    hmemory, hzero, WindowTableMemory.storeWord,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    advancePC, succ_eq_add, hpush, word_add_assoc]

def liftModulusProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩)]

private theorem run_liftModulus (template : State) (pc base modulus : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions liftModulusProgram
      (WindowTwentyOneTable.framed template pc base modulus 2 ([base, modulus] ++ rest)) =
    some (WindowTwentyOneTable.framed template pc.succ base modulus 2
      ([modulus, base, modulus] ++ rest)) := by
  have hcap2 : rest.length + 2 < 1024 := by omega
  simp [runInstructions, liftModulusProgram, WindowTwentyOneTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap2, Nat.add_assoc]

def squareProgram : List Instr :=
  [.op (.Dup ⟨13, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op .MULMOD]

private theorem run_square (template : State) (pc base modulus : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions squareProgram
      (WindowTwentyOneTable.framed template pc base modulus 2
        (List.replicate 13 modulus ++ [base, modulus] ++ rest)) =
    some (WindowTwentyOneTable.framed template (advancePC 3 pc) base modulus 2
      (WindowMath.tableWord base modulus 2 :: List.replicate 12 modulus ++
        [base, modulus] ++ rest)) := by
  have hcap15 : rest.length + 15 < 1024 := by omega
  have hcap16 : rest.length + 16 < 1024 := by omega
  have hcap17 : rest.length + 17 < 1024 := by omega
  simp [runInstructions, squareProgram, WindowTwentyOneTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap15, hcap16, hcap17, Nat.add_assoc,
    List.replicate, WindowMath.tableWord, advancePC]

def stagedProgram : List Instr :=
  liftModulusProgram ++ List.replicate 12 (.op (.Dup ⟨0, by decide⟩)) ++ squareProgram

theorem run_staged (template : State) (pc base modulus : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions stagedProgram
      (WindowTwentyOneTable.framed template pc base modulus 2 ([base, modulus] ++ rest)) =
    some (WindowTwentyOneTable.framed template (advancePC 16 pc) base modulus 2
      (WindowMath.tableWord base modulus 2 :: List.replicate 12 modulus ++
        [base, modulus] ++ rest)) := by
  have hl := run_liftModulus template pc base modulus rest hrest
  let core := WindowTwentyOneTable.framed template pc.succ base modulus 2 []
  have hd := WindowTwentyOneStage.run_topCopies core pc.succ modulus ([base, modulus] ++ rest) 12
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hs := run_square template (advancePC 12 pc.succ) base modulus rest hrest
  have hd' : runInstructions (List.replicate 12 (.op (.Dup ⟨0, by decide⟩)))
      (WindowTwentyOneTable.framed template pc.succ base modulus 2 ([modulus, base, modulus] ++ rest)) =
    some (WindowTwentyOneTable.framed template (advancePC 12 pc.succ) base modulus 2
      (List.replicate 13 modulus ++ [base, modulus] ++ rest)) := by
    simpa only [core, WindowTwentyOneStage.framed, WindowTwentyOneTable.framed,
      List.cons_append, List.nil_append, List.append_assoc] using hd
  have hld := runInstructions_append_some _ _ _ _ _ hl hd'
  have both := runInstructions_append_some _ _ _ _ _ hld hs
  have hpc : advancePC 3 (advancePC 12 pc.succ) = advancePC 16 pc := rfl
  simpa only [stagedProgram, List.append_assoc, hpc] using both

def program : List Instr :=
  initProgram ++ stagedProgram ++ WindowTwentyOneTable.storeProgramM

def endPC (pc : UInt256) : UInt256 :=
  WindowTwentyOneTable.storePCM (advancePC 16 (advancePC 7 pc))

theorem run_prelude (template : State) (pc base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (_hexp : rest[1]? = some exponent) :
    runInstructionsX program (initial template pc base modulus rest) =
    some (WindowTwentyOneTable.state template (endPC pc) base modulus exponent 2 rest) := by
  have hi := run_init template pc base modulus rest hrest
  have hs : runInstructionsX stagedProgram
      (WindowTwentyOneTable.framed template (advancePC 7 pc) base modulus 2
        ([base, modulus] ++ rest)) =
      some (WindowTwentyOneTable.framed template (advancePC 16 (advancePC 7 pc)) base modulus 2
        (WindowMath.tableWord base modulus 2 :: List.replicate 12 modulus ++ [base, modulus] ++ rest)) := by
    rw [runInstructionsX_eq _ (by decide)]
    exact run_staged template (advancePC 7 pc) base modulus rest hrest
  have ht := WindowTwentyOneTable.run_storeM template (advancePC 16 (advancePC 7 pc))
    base modulus 2 (by decide)
    (List.replicate 12 modulus ++ [base, modulus] ++ rest)
    (by simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]; omega)
  have his := runInstructionsX_append_some _ _ _ _ _ hi hs
  have hall := runInstructionsX_append_some _ _ _ _ _ his ht
  simpa only [program, endPC, WindowTwentyOneTable.state, List.cons_append,
    List.append_assoc] using hall

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTablePrelude
