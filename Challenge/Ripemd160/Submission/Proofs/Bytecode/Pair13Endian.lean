import Challenge.Ripemd160.Submission.Proofs.Bytecode.DeferredNormalSchedule
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScratch
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13Endian
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedMask32Cache PairedScheduleMemory

/-- The block frame seen by the endian stages: two resident words, nine further frame words,
the message offset, the limit, and the two resident byte-swap masks. -/
def stk (ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256) (rho : List UInt256) : List UInt256 :=
  ret :: mw :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: off :: lim :: mask8 :: mask16 :: rho

def stage8 (wide : Bool) : List Instr :=
  [ .op (.Dup ⟨0, by decide⟩),
    -- the LOW (1056) half carries a two-byte shift immediate; `wide` names the HIGH half
    (if wide then .push ⟨1, by decide⟩ (UInt256.ofNat 8) else .push ⟨2, by decide⟩ (UInt256.ofNat 8)),
    .op .SHR,
    .op (.Dup ⟨1, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨15, by decide⟩),
    .op .AND,
    (if wide then .push ⟨2, by decide⟩ (UInt256.ofNat 257) else .push ⟨2, by decide⟩ (UInt256.ofNat 257)),
    .op .MUL,
    .op .XOR ]

def stage16 (wide : Bool) : List Instr :=
  [ .op (.Dup ⟨15, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .op (.Dup ⟨0, by decide⟩),
    (if wide then .push ⟨1, by decide⟩ (UInt256.ofNat 16) else .push ⟨2, by decide⟩ (UInt256.ofNat 16)),
    .op .SHR,
    .op .XOR,
    .op .AND,
    .push ⟨3, by decide⟩ (UInt256.ofNat 65537),
    .op .MUL,
    .op .XOR ]

private def raw8 (v : UInt256) : UInt256 :=
  UInt256.xor (UInt256.mul (UInt256.ofNat 257) (UInt256.land mask8 (UInt256.xor v (UInt256.shiftRight v (UInt256.ofNat 8))))) v

theorem run_stage8 (s : State) (pc v ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256)
    (rho : List UInt256) (wide : Bool) (hstack : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq (stage8 wide) {s with pc := pc, stack := v :: stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} =
      some {s with
        pc := pcAfter pc (stage8 wide)
        stack := multipliedStage v 8 mask8 :: stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
  cases wide <;>
  simp (discharger := omega) [stage8, stk, multipliedStage, endianDelta, endianFactor,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size, hrun, hcap,
    Nat.add_assoc, List.getElem?_cons_zero, List.exchange, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals refine ⟨rfl, ?_⟩
  all_goals rw [RawExpressionAC.xor_comm v, RawExpressionAC.land_comm]; rfl

theorem run_stage16 (s : State) (pc v ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256)
    (rho : List UInt256) (wide : Bool) (hstack : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq (stage16 wide) {s with pc := pc, stack := v :: stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} =
      some {s with
        pc := pcAfter pc (stage16 wide)
        stack := multipliedStage v 16 mask16 :: stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
  cases wide <;>
  simp (discharger := omega) [stage16, stk, multipliedStage, endianDelta, endianFactor,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size, hrun, hcap,
    Nat.add_assoc, List.getElem?_cons_zero, List.exchange, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals exact ⟨rfl, rfl⟩

def loadTemplate (address : Nat) : List Instr :=
  [ .push ⟨if address = 1088 then 2 else 2, by split_ifs <;> decide⟩ (UInt256.ofNat address), .op (.Dup ⟨12, by decide⟩), .op .ADD, .op .MLOAD ]

theorem run_load (s : State) (pc ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256)
    (rho : List UInt256) (address q : Nat) (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hq : off + UInt256.ofNat address = UInt256.ofNat q) (hqb : q < 2 ^ 256) :
    runInstrSeq (loadTemplate address) {s with pc := pc, stack := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} =
      some {s with
        pc := pcAfter pc (loadTemplate address)
        stack := MachineState.readWord s.memory q :: stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
        activeWords := activeAfterWord s.activeWords (UInt256.ofNat q)} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
  have hwidthplus : (if address = 1088 then 2 else 2 : Nat) + 1 = 1 + (if address = 1088 then 2 else 2 : Nat) := Nat.add_comm _ _
  have hwidth : (if address = 1088 then 2 else 2 : Nat) ≠ 0 := by split_ifs <;> decide
  have hqn : (UInt256.ofNat q).toNat = q := by rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hqb]
  simp (discharger := omega) [loadTemplate, hwidth, hwidthplus, stk, activeAfterWord,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size, hrun, hcap,
    Nat.add_assoc, List.getElem?_cons_zero, List.exchange, Word.literal_eq_ofNat, State.activeWordsAfterUInt256]
  rw [hq, hqn]
  have hm : q % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = q := Nat.mod_eq_of_lt hqb
  rw [hm]
  exact ⟨rfl, rfl, rfl⟩

theorem reversed_eq (v : UInt256) :
    multipliedStage (multipliedStage v 8 mask8) 16 mask16 = PairedScheduleData.reversedWord v := by
  simp only [DenseEndianMultiply.multipliedStage8_eq_packedStage,
    DenseEndianMultiply.multipliedStage16_eq_packedStage]
  exact PairedScheduleContract.packedWord_eq_reversedWord v

theorem run_reverse (s : State) (pc v ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256)
    (rho : List UInt256) (wide : Bool) (hstack : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq (stage8 wide ++ stage16 wide) {s with pc := pc, stack := v :: stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} =
      some {s with
        pc := pcAfter (pcAfter pc (stage8 wide)) (stage16 wide)
        stack := PairedScheduleData.reversedWord v :: stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} := by
  have h1 := run_stage8 s pc v ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho wide hstack hrun
  have h2 := run_stage16 s (pcAfter pc (stage8 wide)) (multipliedStage v 8 mask8) ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho wide hstack hrun
  rw [reversed_eq] at h2
  exact DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2

def highStore : List Instr := [ .push ⟨1, by decide⟩ (UInt256.ofNat 96), .op .MSTORE ]

/-- The lower half is stored twice, eighteen bytes apart: the surviving bytes of the
`46` store duplicate the low word's own tail, which is what lets the schedule loads
below read the same thirty-two-bit field in two lanes at once. -/
def lowStore : List Instr :=
  [ .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 46),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 10),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 28),
    .op .MSTORE ]

/-- The scratch image the endian stage leaves behind. -/
def scratch3 (memory : ByteArray) (low high : UInt256) : ByteArray :=
  writeWord (writeWord (writeWord (writeWord memory 96 high) 46 low) 10 low) 28 low

theorem run_highStore (s : State) (pc value : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1022) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq highStore {s with pc := pc, stack := value :: rest} =
      some { s with
        pc := pcAfter pc highStore
        stack := rest
        memory := writeWord s.memory 96 value} :=
  by
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap : rest.length + 1 + 1 < 1024 := by omega
  have haddr : (UInt256.ofNat 96).toNat = 96 := by decide
  have hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 96 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords 96 hactive (by decide)
  simp [highStore, writeWord, runInstrSeq, Challenge.EvmProof.DataStepper.runInstr, pcAfter, hrun, hcap1, hcap,
    UInt256.succ, Instr.size, State.activeWordsAfterUInt256, haddr, hact]
  all_goals rfl

theorem run_lowStore_of_small (s : State) (pc value : UInt256) (rest : List UInt256)
    (hstack : rest.length + 3 < 1024) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq lowStore {s with pc := pc, stack := value :: rest} =
      some { s with
        pc := pcAfter pc lowStore
        stack := rest
        memory := writeWord (writeWord (writeWord s.memory 46 value) 10 value) 28 value} := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap : rest.length + 1 + 1 < 1024 := by omega
  have hcap2 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have haddr46 : (UInt256.ofNat 46).toNat = 46 := by decide
  have haddr10 : (UInt256.ofNat 10).toNat = 10 := by decide
  have haddr28 : (UInt256.ofNat 28).toNat = 28 := by decide
  have hact46 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 46 32) = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords 46 hactive (by decide)
  have hact28 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 28 32) = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords 28 hactive (by decide)
  have hact10 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 10 32) = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords 10 hactive (by decide)
  simp [lowStore, writeWord, runInstrSeq, Challenge.EvmProof.DataStepper.runInstr, pcAfter, hrun,
    hcap1, hcap, hcap2, UInt256.succ, Instr.size, State.activeWordsAfterUInt256,
    haddr46, haddr10, haddr28, hact46, hact10, hact28, List.getElem?_cons_zero]
  all_goals rfl

theorem run_lowStore (s : State) (pc value : UInt256) (rest : List UInt256)
    (hstack : rest.length + 3 < 1024) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq lowStore {s with pc := pc, stack := value :: rest} =
      some { s with
        pc := pcAfter pc lowStore
        stack := rest
        memory := writeWord (writeWord (writeWord s.memory 46 value) 10 value) 28 value} := by
  exact run_lowStore_of_small s pc value rest hstack hrun (by omega)

theorem active_swap (cur : UInt256) (p : Nat) (hbound : p + 64 < 2 ^ 256) :
    activeAfterWord (activeAfterWord cur (UInt256.ofNat p)) (UInt256.ofNat p + UInt256.ofNat 32) =
      activeAfterWord cur (UInt256.ofNat (p + 32)) := by
  have hc := cur.val.isLt
  have hcN : cur.toNat < 2 ^ 256 := hc
  have h32 := PairedScheduleContract.pointer_add32_toNat p hbound
  have hp : (UInt256.ofNat p).toNat = p := by rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hp32 : (UInt256.ofNat (p + 32)).toNat = p + 32 := by rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hin : MachineState.activeWordsAfter cur.toNat p 32 < 2 ^ 256 := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
    apply Nat.max_lt.mpr
    exact ⟨hcN, by omega⟩
  unfold activeAfterWord
  rw [h32, hp, hp32, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hin]
  congr 1
  simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
  change max (max _ _) _ = max _ _
  rw [Nat.max_assoc, Nat.max_eq_right (by omega : (p + 32 - 1) / 32 + 1 ≤ (p + 32 + 32 - 1) / 32 + 1)]

theorem active_reload (cur : UInt256) (p : Nat) (hbound : p + 64 < 2 ^ 256) :
    activeAfterWord (activeAfterWord cur (UInt256.ofNat (p + 32))) (UInt256.ofNat p) =
      activeAfterWord cur (UInt256.ofNat (p + 32)) := by
  have hcN : cur.toNat < 2 ^ 256 := cur.val.isLt
  have hp : (UInt256.ofNat p).toNat = p := by rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hp32 : (UInt256.ofNat (p + 32)).toNat = p + 32 := by rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hin : MachineState.activeWordsAfter cur.toNat (p + 32) 32 < 2 ^ 256 := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
    apply Nat.max_lt.mpr
    exact ⟨hcN, by omega⟩
  unfold activeAfterWord
  rw [hp, hp32, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hin]
  congr 1
  simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
  change max (max _ _) _ = max _ _
  rw [Nat.max_assoc, Nat.max_eq_left (by omega : (p + 32 - 1) / 32 + 1 ≤ (p + 32 + 32 - 1) / 32 + 1)]

theorem active_ge35 (cur : UInt256) (p : Nat) (hp : 1056 ≤ p) (hbound : p + 64 < 2 ^ 256) :
    35 ≤ (activeAfterWord cur (UInt256.ofNat (p + 32))).toNat := by
  have hcN : cur.toNat < 2 ^ 256 := cur.val.isLt
  have hp32 : (UInt256.ofNat (p + 32)).toNat = p + 32 := by rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hin : MachineState.activeWordsAfter cur.toNat (p + 32) 32 < 2 ^ 256 := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
    apply Nat.max_lt.mpr
    exact ⟨hcN, by omega⟩
  unfold activeAfterWord
  rw [hp32, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hin]
  simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
  apply Nat.le_trans ?_ (Nat.le_max_right _ _)
  omega

def template : List Instr :=
  loadTemplate 1088 ++ (stage8 true ++ stage16 true) ++ highStore ++ [.op .JUMPDEST] ++ loadTemplate 1056 ++ (stage8 false ++ stage16 false) ++
    lowStore

theorem run_template (s : State) (pc ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256)
    (rho : List UInt256) (p : Nat) (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hp : 1056 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hq1 : off + UInt256.ofNat 1088 = UInt256.ofNat (p + 32))
    (hq0 : off + UInt256.ofNat 1056 = UInt256.ofNat p) :
    runInstrSeq template {s with pc := pc, stack := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} =
      some {s with
        pc := pcAfter pc template
        stack := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
        memory := scratch3 s.memory
          (PairedScheduleData.reversedWord (MachineState.readWord s.memory p))
          (PairedScheduleData.reversedWord (MachineState.readWord s.memory (p + 32)))
        activeWords := loadedActiveWords s (UInt256.ofNat p)} := by
  let high := PairedScheduleData.reversedWord (MachineState.readWord s.memory (p + 32))
  let low := PairedScheduleData.reversedWord (MachineState.readWord s.memory p)
  let a1 := activeAfterWord s.activeWords (UInt256.ofNat (p + 32))
  have ha1 : 35 ≤ a1.toNat := active_ge35 s.activeWords p hp hbound
  let s1 : State := {s with activeWords := a1}
  let s2 : State := {s1 with memory := writeWord s.memory 96 high}
  let F := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
  have hF : F.length ≤ 1005 := by simp [F, stk]; omega
  have h1 := run_load s pc ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho 1088 (p + 32) hstack hrun hq1 (by omega)
  have h2 := run_reverse s1 (pcAfter pc (loadTemplate 1088)) (MachineState.readWord s.memory (p + 32))
    ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho true hstack hrun
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  have h3 := run_highStore s1 (pcAfter (pcAfter (pcAfter pc (loadTemplate 1088)) (stage8 true)) (stage16 true)) high F
    (by omega) hrun (by change 35 ≤ a1.toNat; omega)
  have h123 := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  let pcJ := pcAfter (pcAfter (pcAfter (pcAfter pc (loadTemplate 1088)) (stage8 true)) (stage16 true)) highStore
  let pc3 := pcAfter pcJ [.op .JUMPDEST]
  have hj : runInstrSeq [.op .JUMPDEST] {s2 with pc := pcJ, stack := F} =
      some {s2 with pc := pc3, stack := F} := by
    have hcap : F.length < 1024 := by omega
    simp [runInstrSeq, DataStepper.runInstr, pcAfter, pc3, Instr.size,
      UInt256.succ, hrun, hcap, s2, s1]
    rfl
  have h123j := DenseScheduleTrace.runInstrSeq_append_running h123 (by exact hrun) hj
  have h4 := run_load s2 pc3 ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho 1056 p hstack hrun hq0 (by omega)
  have hread : MachineState.readWord s2.memory p = MachineState.readWord s.memory p :=
    read_writeWord_disjoint _ _ _ _ (Or.inr (by omega))
  have hact : activeAfterWord s2.activeWords (UInt256.ofNat p) = a1 := active_reload s.activeWords p hbound
  rw [hread, hact] at h4
  have h1234 := DenseScheduleTrace.runInstrSeq_append_running h123j (by exact hrun) h4
  let pc4 := pcAfter pc3 (loadTemplate 1056)
  have h5 := run_reverse s2 pc4 (MachineState.readWord s.memory p)
    ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho false hstack hrun
  have h12345 := DenseScheduleTrace.runInstrSeq_append_running h1234 (by exact hrun) h5
  have h6 := run_lowStore s2 (pcAfter (pcAfter pc4 (stage8 false)) (stage16 false)) low F (by omega) hrun
    (by change 35 ≤ a1.toNat; omega)
  have h := DenseScheduleTrace.runInstrSeq_append_running h12345 (by exact hrun) h6
  have hloaded : loadedActiveWords s (UInt256.ofNat p) = a1 := active_swap s.activeWords p hbound
  simp only [template, DenseScheduleTrace.pcAfter_append, List.append_assoc, scratch3] at h ⊢
  rw [hloaded]
  exact h

theorem exact_bytes : assembleBytes template = [97,4,64,140,1,81,128,96,8,28,129,24,143,22,97,1,1,2,24,143,129,128,96,16,28,24,22,98,1,0,1,2,24,96,96,82,91,97,4,32,140,1,81,128,97,0,8,28,129,24,143,22,97,1,1,2,24,143,129,128,97,0,16,28,24,22,98,1,0,1,2,24,128,97,0,46,82,128,97,0,10,82,97,0,28,82] := by decide
theorem end_pc : pcAfter (UInt256.ofNat 472) template = UInt256.ofNat 558 := by decide
#print axioms run_template

/-! ### The C2 staging layout

The high word is stored once at `28` and the low word once at `616`; the pool block's four
sixteen-byte copies then duplicate each half's quartets eighteen bytes away. -/

def highStoreV2 : List Instr := [ .push ⟨1, by decide⟩ (UInt256.ofNat 28), .op .MSTORE ]

def lowStoreV2 : List Instr := [ .push ⟨2, by decide⟩ (UInt256.ofNat 616), .op .MSTORE ]

/-- The scratch image the C2 endian stage leaves behind. -/
def scratchV2 (memory : ByteArray) (low high : UInt256) : ByteArray :=
  writeWord (writeWord memory 28 high) 616 low

theorem run_highStoreV2 (s : State) (pc value : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1022) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq highStoreV2 {s with pc := pc, stack := value :: rest} =
      some { s with
        pc := pcAfter pc highStoreV2
        stack := rest
        memory := writeWord s.memory 28 value} := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap : rest.length + 1 + 1 < 1024 := by omega
  have haddr : (UInt256.ofNat 28).toNat = 28 := by decide
  have hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 28 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords 28 hactive (by decide)
  simp [highStoreV2, writeWord, runInstrSeq, Challenge.EvmProof.DataStepper.runInstr, pcAfter, hrun, hcap1, hcap,
    UInt256.succ, Instr.size, State.activeWordsAfterUInt256, haddr, hact]
  all_goals rfl

theorem run_lowStoreV2_of_small (s : State) (pc value : UInt256) (rest : List UInt256)
    (hstack : rest.length + 3 < 1024) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq lowStoreV2 {s with pc := pc, stack := value :: rest} =
      some { s with
        pc := pcAfter pc lowStoreV2
        stack := rest
        memory := writeWord s.memory 616 value} := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap : rest.length + 1 + 1 < 1024 := by omega
  have haddr : (UInt256.ofNat 616).toNat = 616 := by decide
  have hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 616 32) = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords 616 hactive (by decide)
  simp [lowStoreV2, writeWord, runInstrSeq, Challenge.EvmProof.DataStepper.runInstr, pcAfter, hrun,
    hcap1, hcap, UInt256.succ, Instr.size, State.activeWordsAfterUInt256, haddr, hact,
    List.getElem?_cons_zero]
  all_goals rfl

theorem run_lowStoreV2 (s : State) (pc value : UInt256) (rest : List UInt256)
    (hstack : rest.length + 3 < 1024) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq lowStoreV2 {s with pc := pc, stack := value :: rest} =
      some { s with
        pc := pcAfter pc lowStoreV2
        stack := rest
        memory := writeWord s.memory 616 value} := by
  exact run_lowStoreV2_of_small s pc value rest hstack hrun (by omega)

def templateV2 : List Instr :=
  loadTemplate 1088 ++ (stage8 true ++ stage16 true) ++ highStoreV2 ++ [.op .JUMPDEST] ++ loadTemplate 1056 ++ (stage8 false ++ stage16 false) ++
    lowStoreV2

theorem run_templateV2 (s : State) (pc ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim : UInt256)
    (rho : List UInt256) (p : Nat) (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hp : 1056 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hq1 : off + UInt256.ofNat 1088 = UInt256.ofNat (p + 32))
    (hq0 : off + UInt256.ofNat 1056 = UInt256.ofNat p) :
    runInstrSeq templateV2 {s with pc := pc, stack := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho} =
      some {s with
        pc := pcAfter pc templateV2
        stack := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
        memory := scratchV2 s.memory
          (PairedScheduleData.reversedWord (MachineState.readWord s.memory p))
          (PairedScheduleData.reversedWord (MachineState.readWord s.memory (p + 32)))
        activeWords := loadedActiveWords s (UInt256.ofNat p)} := by
  let high := PairedScheduleData.reversedWord (MachineState.readWord s.memory (p + 32))
  let low := PairedScheduleData.reversedWord (MachineState.readWord s.memory p)
  let a1 := activeAfterWord s.activeWords (UInt256.ofNat (p + 32))
  have ha1 : 35 ≤ a1.toNat := active_ge35 s.activeWords p hp hbound
  let s1 : State := {s with activeWords := a1}
  let s2 : State := {s1 with memory := writeWord s.memory 28 high}
  let F := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho
  have hF : F.length ≤ 1005 := by simp [F, stk]; omega
  have h1 := run_load s pc ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho 1088 (p + 32) hstack hrun hq1 (by omega)
  have h2 := run_reverse s1 (pcAfter pc (loadTemplate 1088)) (MachineState.readWord s.memory (p + 32))
    ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho true hstack hrun
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  have h3 := run_highStoreV2 s1 (pcAfter (pcAfter (pcAfter pc (loadTemplate 1088)) (stage8 true)) (stage16 true)) high F
    (by omega) hrun (by change 35 ≤ a1.toNat; omega)
  have h123 := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  let pcJ := pcAfter (pcAfter (pcAfter (pcAfter pc (loadTemplate 1088)) (stage8 true)) (stage16 true)) highStoreV2
  let pc3 := pcAfter pcJ [.op .JUMPDEST]
  have hj : runInstrSeq [.op .JUMPDEST] {s2 with pc := pcJ, stack := F} =
      some {s2 with pc := pc3, stack := F} := by
    have hcap : F.length < 1024 := by omega
    simp [runInstrSeq, DataStepper.runInstr, pcAfter, pc3, Instr.size,
      UInt256.succ, hrun, hcap, s2, s1]
    rfl
  have h123j := DenseScheduleTrace.runInstrSeq_append_running h123 (by exact hrun) hj
  have h4 := run_load s2 pc3 ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho 1056 p hstack hrun hq0 (by omega)
  have hread : MachineState.readWord s2.memory p = MachineState.readWord s.memory p :=
    read_writeWord_disjoint _ _ _ _ (Or.inr (by omega))
  have hact : activeAfterWord s2.activeWords (UInt256.ofNat p) = a1 := active_reload s.activeWords p hbound
  rw [hread, hact] at h4
  have h1234 := DenseScheduleTrace.runInstrSeq_append_running h123j (by exact hrun) h4
  let pc4 := pcAfter pc3 (loadTemplate 1056)
  have h5 := run_reverse s2 pc4 (MachineState.readWord s.memory p)
    ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 off lim rho false hstack hrun
  have h12345 := DenseScheduleTrace.runInstrSeq_append_running h1234 (by exact hrun) h5
  have h6 := run_lowStoreV2 s2 (pcAfter (pcAfter pc4 (stage8 false)) (stage16 false)) low F (by omega) hrun
    (by change 35 ≤ a1.toNat; omega)
  have h := DenseScheduleTrace.runInstrSeq_append_running h12345 (by exact hrun) h6
  have hloaded : loadedActiveWords s (UInt256.ofNat p) = a1 := active_swap s.activeWords p hbound
  simp only [templateV2, DenseScheduleTrace.pcAfter_append, List.append_assoc, scratchV2] at h ⊢
  rw [hloaded]
  exact h

theorem end_pcV2 : pcAfter (UInt256.ofNat 472) templateV2 = UInt256.ofNat 548 := by decide
#print axioms run_templateV2
#print axioms exact_bytes
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13Endian
