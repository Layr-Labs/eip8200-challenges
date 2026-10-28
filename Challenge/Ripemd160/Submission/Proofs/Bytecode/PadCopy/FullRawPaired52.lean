import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired52Raw
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paired round 52 of the pad-only copy with its word-0 schedule read folded into the
round key: `PUSH 54; MLOAD; ADD` and the key `DUP` become one `PUSH` of key plus word. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullRawPaired52
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired52 (inputStack outputStack)
private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem neutral_hmul (a b : UInt256) : a * b = UInt256.mul a b := rfl
private theorem fold_split : UInt256.ofNat 45805604527067802242040499947532902706799460545707356 = UInt256.add (UInt256.ofNat 45805601672572416830120737830960963807809187780213980) (UInt256.ofNat 2854495385411919762116571938898990272765493376) := by decide
def template : List Instr :=
  [ .op (.Dup ⟨13, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .op (.Swap ⟨6, by decide⟩),
    .op (.Dup ⟨8, by decide⟩),
    .op (.Dup ⟨12, by decide⟩),
    .op (.Dup ⟨8, by decide⟩),
    .op .OR,
    .op .XOR,
    .op (.Dup ⟨12, by decide⟩),
    .op (.Dup ⟨8, by decide⟩),
    .op .AND,
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op .AND,
    .op (.Dup ⟨12, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨22, by decide⟩ (UInt256.ofNat 45805604527067802242040499947532902706799460545707356),
    .op .ADD,
    .op (.Dup ⟨5, by decide⟩),
    .op .AND,
    .op (.Dup ⟨12, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 19),
    .op .SHR,
    .op (.Dup ⟨10, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨5, by decide⟩),
    .op .AND,
    .op (.Swap ⟨10, by decide⟩),
    .op (.Dup ⟨12, by decide⟩),
    .op .MUL,
    .op (.Dup ⟨9, by decide⟩),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .AND ]
def padActual (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.land x.v3 (UInt256.shiftRight (UInt256.mul x.v10 x.v9) (UInt256.ofNat 23))),
    x.v13,
    x.v0,
    x.v1,
    x.v2,
    x.v3,
    x.v4,
    x.v0,
    x.v6,
    (UInt256.ofNat 23),
    x.v8,
    (UInt256.land x.v3 (UInt256.add x.v8 (UInt256.shiftRight (UInt256.mul x.v10 (UInt256.land x.v3 (UInt256.add x.v1 (UInt256.add (UInt256.ofNat 2854495385411919762116571938898990272765493376) (UInt256.add (UInt256.xor x.v9 (UInt256.land (UInt256.xor x.v0 (UInt256.land x.v4 x.v9)) (UInt256.xor (UInt256.lor x.v4 x.v9) x.v6))) x.v5))))) (UInt256.ofNat 19)))),
    x.v10,
    x.v11,
    x.v12,
    x.v13,
    x.v14,
    x.v15,
    x.v16 ] ++ rho
private theorem run_generated (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) (hk : x.v1 = UInt256.ofNat 45805601672572416830120737830960963807809187780213980) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := padActual s.memory x rho} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [hk, template, inputStack, padActual,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals simp only [fold_split, neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.mulMod_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
theorem out_eq (memory : ByteArray) (x : Input) (rho : List UInt256)
    (hm : MachineState.readWord memory 54 = UInt256.ofNat 2854495385411919762116571938898990272765493376) :
    outputStack memory x rho = padActual memory x rho := by
  simp only [Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired52.outputStack, padActual, hm]
theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) (hk : x.v1 = UInt256.ofNat 45805601672572416830120737830960963807809187780213980)
    (hm : MachineState.readWord s.memory 54 = UInt256.ofNat 2854495385411919762116571938898990272765493376) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack s.memory x rho} := by
  rw [out_eq s.memory x rho hm]
  exact run_generated s pc x rho hstack hrun hactive hk
#print axioms run_actual
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullRawPaired52
