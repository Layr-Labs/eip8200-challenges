import Challenge.Ripemd160.Submission.Proofs.Bytecode.FoldedRound48
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullRawPaired48
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
open Challenge.Ripemd160.Submission.Proofs.Bytecode.FoldedRound48 (inputStack outputStack)
private theorem folded_key :
    UInt256.add (UInt256.ofNat 541184315)
      (UInt256.ofNat 45805601672572416830120737830960963807809187239029665) =
      UInt256.ofNat 45805601672572416830120737830960963807809187780213980 := by decide
private theorem hmul_eq_mul (x y : UInt256) : x * y = UInt256.mul x y := rfl
private theorem hadd_eq_add (x y : UInt256) : x + y = UInt256.add x y := rfl
private theorem zero_hadd (a : UInt256) : UInt256.add (UInt256.ofNat 0) a = a := by
  apply Word.word_ext; cases a; simp [UInt256.add, UInt256.ofNat, UInt256.toNat]
private theorem hadd_zero (a : UInt256) : UInt256.add a (UInt256.ofNat 0) = a := by
  apply Word.word_ext; cases a; simp [UInt256.add, UInt256.ofNat, UInt256.toNat]
private theorem zero_hadd' (a : UInt256) : UInt256.add {val := 0} a = a := zero_hadd a
private theorem hadd_zero' (a : UInt256) : UInt256.add a {val := 0} = a := hadd_zero a
def template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op .POP,
    .push ⟨22, by decide⟩ (UInt256.ofNat 45805601672572416830120737830960963807809187780213980),
    .op (.Swap ⟨0, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .OR,
    .op .XOR,
    .op (.Dup ⟨10, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .AND,
    .op (.Dup ⟨7, by decide⟩),
    .op .XOR,
    .op .AND,
    .op (.Dup ⟨10, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨2, by decide⟩),
    .op .ADD,
    .op .ADD,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .op (.Dup ⟨10, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨8, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .op (.Swap ⟨8, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .MUL,
    .op (.Dup ⟨7, by decide⟩),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND ]
def padActual (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.land x.v3 (UInt256.shiftRight (UInt256.mul x.v10 x.v9) (UInt256.ofNat 23))),
    (UInt256.add (UInt256.ofNat 541184315) (UInt256.ofNat 45805601672572416830120737830960963807809187239029665)),
    (UInt256.ofNat 0),
    x.v3,
    x.v4,
    x.v0,
    x.v6,
    (UInt256.ofNat 23),
    x.v8,
    (UInt256.land x.v3 (UInt256.add x.v8 (UInt256.shiftRight (UInt256.mul x.v10 (UInt256.land x.v3 (UInt256.add (UInt256.add (UInt256.ofNat 541184315) (UInt256.ofNat 45805601672572416830120737830960963807809187239029665)) (UInt256.add (UInt256.ofNat 0) (UInt256.add (UInt256.xor x.v9 (UInt256.land (UInt256.xor x.v0 (UInt256.land x.v4 x.v9)) (UInt256.xor (UInt256.lor x.v4 x.v9) x.v6))) x.v7))))) (UInt256.ofNat 22)))),
    x.v10,
    x.v11,
    x.v12,
    x.v13,
    x.v14,
    x.v15,
    x.v16 ] ++ rho
private theorem run_generated (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) (hz792 : MachineState.readWord s.memory 792 = UInt256.ofNat 0) (hc2 : x.v2 = UInt256.ofNat 0) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := padActual s.memory x rho} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 22) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [zero_hadd, hadd_zero, zero_hadd', hadd_zero', hz792, hc2, template, inputStack, padActual, outputStack,
    folded_key, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [hmul_eq_mul, hadd_eq_add, RawExpressionAC.add_comm,
    RawExpressionAC.add_left_comm, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
  all_goals first | assumption | trivial | (simp only [zero_hadd', hadd_zero', zero_hadd, hadd_zero])
theorem out_eq (memory : ByteArray) (x : Input) (rho : List UInt256) (hz792 : MachineState.readWord memory 792 = UInt256.ofNat 0) (hc2 : x.v2 = UInt256.ofNat 0) :
    outputStack memory x rho = padActual memory x rho := by
  simp only [Challenge.Ripemd160.Submission.Proofs.Bytecode.FoldedRound48.outputStack, padActual, hz792, hc2, zero_hadd, hadd_zero, RawExpressionAC.add_assoc, RawExpressionAC.add_comm,
    RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm,
    RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm,
    RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm,
    RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm,
    RawExpressionAC.xor_left_comm, RawExpressionAC.mulMod_comm]
theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) (hz792 : MachineState.readWord s.memory 792 = UInt256.ofNat 0) (hc2 : x.v2 = UInt256.ofNat 0) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack s.memory x rho} := by
  rw [out_eq s.memory x rho hz792 hc2]
  exact run_generated s pc x rho hstack hrun hactive hz792 hc2
#print axioms run_actual
theorem run_original (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hx : x.v5 = UInt256.ofNat 45805601672572416830120737830960963807809187239029665) (hz792 : MachineState.readWord s.memory 792 = UInt256.ofNat 0) (hc2 : x.v2 = UInt256.ofNat 0) :
    runInstrSeq template {s with pc := pc, stack := StaggerRawPaired48.inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := StaggerRawPaired48.outputStack s.memory x rho} := by
  have h := run_actual s pc x rho hstack hrun hactive hz792 hc2
  simpa only [Challenge.Ripemd160.Submission.Proofs.Bytecode.FoldedRound48.inputStack, Challenge.Ripemd160.Submission.Proofs.Bytecode.FoldedRound48.outputStack, StaggerRawPaired48.inputStack,
    StaggerRawPaired48.outputStack, hx] using h
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullRawPaired48
