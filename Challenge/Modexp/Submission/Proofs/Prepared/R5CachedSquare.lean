import Challenge.Modexp.Submission.Proofs.Prepared.R5CacheRaw
import Challenge.Modexp.Submission.Proofs.Prepared.R5CacheBridge
import Challenge.Modexp.Submission.Proofs.Prepared.R5Square
namespace CachedR5Columns
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof.Word Challenge.EvmProof.Stepper
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
def history0 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W) : State := {s with pc := N 8812,stack := (CycleSubmission.R5.ExecSquare.sqCol0_o0 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt) (n0))::(CycleSubmission.R5.ExecSquare.sqCol0_o1 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt) (n0))::((a0+a0))::a1::a2::a3::a4::(n1)::(n2)::(n3)::(n4)::(p)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest}
theorem run_stage0 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    runInstructions R5LimbCacheRaw.stage0Program {s with pc := N 8786,stack := a0::a1::a2::a3::a4::(n1)::(n2)::(n3)::(n4)::(p)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} = some (history0 (s) (c) (q0) (q1) (q2) (q3) (q4) a0 a1 a2 a3 a4 (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest)) := by
  have hraw := R5LimbCacheRaw.stage0_run s a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (MachineState.readWord s.memory 160) (cnt) rest hcap hact
  have hemb := R5LimbCacheBridge.stage0_embedding s a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt) (MachineState.readWord s.memory 160) rest rfl
  have hmath := NextR5Columns.stage0_history s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest hn0 hi hp ha0 ha1 ha2 ha3 hc
  rw [hemb,hmath] at hraw
  have hend : R5LimbCacheBridge.inject 8812 13 (MachineState.readWord s.memory 160) (NextR5Columns.history0 s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest) = history0 s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest := by rfl
  exact hraw.trans (congrArg some hend)
def history1 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W) : State := {s with pc := N 8848,stack := (CycleSubmission.R5.ExecSquare.sqCol1_o0 (c) (q0) a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt) (n0))::(CycleSubmission.R5.ExecSquare.sqCol1_o1 (c) (q0) a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt) (n0))::(q0)::((a0+a0))::a1::a2::a3::a4::(n1)::(n2)::(n3)::(n4)::(p)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest}
theorem run_stage1 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    runInstructions R5LimbCacheRaw.stage1Program {s with pc := N 8812,stack := (c)::(q0)::((a0+a0))::a1::a2::a3::a4::(n1)::(n2)::(n3)::(n4)::(p)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} = some (history1 (s) (c) (q0) (q1) (q2) (q3) (q4) a0 a1 a2 a3 a4 (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest)) := by
  have hraw := R5LimbCacheRaw.stage1_run s (c) (q0) ((a0+a0)) a1 a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (MachineState.readWord s.memory 160) (cnt) rest hcap hact
  have hemb := R5LimbCacheBridge.stage1_embedding s (c) (q0) ((a0+a0)) a1 a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt) (MachineState.readWord s.memory 160) rest rfl
  have hmath := NextR5Columns.stage1_history s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest hn0 hi hp ha0 ha1 ha2 ha3 hc
  rw [hemb,hmath] at hraw
  have hend : R5LimbCacheBridge.inject 8848 14 (MachineState.readWord s.memory 160) (NextR5Columns.history1 s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest) = history1 s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest := by rfl
  exact hraw.trans (congrArg some hend)
def history2 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W) : State := {s with pc := N 8907,stack := (CycleSubmission.R5.ExecSquare.sqCol2_o0 (c) (q1) (q0) a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt) (n0))::(CycleSubmission.R5.ExecSquare.sqCol2_o1 (c) (q1) (q0) a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt) (n0))::(q1)::(q0)::((a0+a0))::((a1+a1))::a2::a3::a4::(n1)::(n2)::(n3)::(n4)::(p)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest}
theorem run_stage2 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    runInstructions R5LimbCacheRaw.stage2Program {s with pc := N 8848,stack := (c)::(q1)::(q0)::((a0+a0))::a1::a2::a3::a4::(n1)::(n2)::(n3)::(n4)::(p)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} = some (history2 (s) (c) (q0) (q1) (q2) (q3) (q4) a0 a1 a2 a3 a4 (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest)) := by
  have hraw := R5LimbCacheRaw.stage2_run s (c) (q1) (q0) ((a0+a0)) a1 a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (MachineState.readWord s.memory 160) (cnt) rest hcap hact
  have hemb := R5LimbCacheBridge.stage2_embedding s (c) (q1) (q0) ((a0+a0)) a1 a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt) (MachineState.readWord s.memory 160) rest rfl
  have hmath := NextR5Columns.stage2_history s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest hn0 hi hp ha0 ha1 ha2 ha3 hc
  rw [hemb,hmath] at hraw
  have hend : R5LimbCacheBridge.inject 8907 15 (MachineState.readWord s.memory 160) (NextR5Columns.history2 s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest) = history2 s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest := by rfl
  exact hraw.trans (congrArg some hend)
def history3 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W) : State := {s with pc := N 8972,stack := (CycleSubmission.R5.ExecSquare.sqCol3_o0 (c) (q2) (q1) (q0) a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt) (n0))::(CycleSubmission.R5.ExecSquare.sqCol3_o1 (c) (q2) (q1) (q0) a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt) (n0))::(q2)::(q1)::(q0)::((a0+a0))::((a1+a1))::a2::a3::a4::(n1)::(n2)::(n3)::(n4)::(p)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest}
theorem run_stage3 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    runInstructions R5LimbCacheRaw.stage3Program {s with pc := N 8907,stack := (c)::(q2)::(q1)::(q0)::((a0+a0))::((a1+a1))::a2::a3::a4::(n1)::(n2)::(n3)::(n4)::(p)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} = some (history3 (s) (c) (q0) (q1) (q2) (q3) (q4) a0 a1 a2 a3 a4 (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest)) := by
  have hraw := R5LimbCacheRaw.stage3_run s (c) (q2) (q1) (q0) ((a0+a0)) ((a1+a1)) a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (MachineState.readWord s.memory 160) (cnt) rest hcap hact
  have hemb := R5LimbCacheBridge.stage3_embedding s (c) (q2) (q1) (q0) ((a0+a0)) ((a1+a1)) a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt) (MachineState.readWord s.memory 160) rest rfl
  have hmath := NextR5Columns.stage3_history s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest hn0 hi hp ha0 ha1 ha2 ha3 hc
  rw [hemb,hmath] at hraw
  have hend : R5LimbCacheBridge.inject 8972 16 (MachineState.readWord s.memory 160) (NextR5Columns.history3 s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest) = history3 s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest := by rfl
  exact hraw.trans (congrArg some hend)
def history4 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W) : State := {s with pc := N 9062,stack := (CycleSubmission.R5.ExecSquare.sqCol4_o0 (c) (q3) (q2) (q1) (q0) a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt) (n0))::(q3)::(q2)::(q1)::(CycleSubmission.R5.ExecSquare.sqCol4_o4 (c) (q3) (q2) (q1) (q0) a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt) (n0))::((a0+a0))::((a1+a1))::((a2+a2))::a3::a4::(n1)::(n2)::(n3)::(n4)::(p)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest}
theorem run_stage4 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    runInstructions R5LimbCacheRaw.stage4Program {s with pc := N 8972,stack := (c)::(q3)::(q2)::(q1)::(q0)::((a0+a0))::((a1+a1))::a2::a3::a4::(n1)::(n2)::(n3)::(n4)::(p)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} = some (history4 (s) (c) (q0) (q1) (q2) (q3) (q4) a0 a1 a2 a3 a4 (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest)) := by
  have hraw := R5LimbCacheRaw.stage4_run s (c) (q3) (q2) (q1) (q0) ((a0+a0)) ((a1+a1)) a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (MachineState.readWord s.memory 160) (cnt) rest hcap hact
  have hemb := R5LimbCacheBridge.stage4_embedding s (c) (q3) (q2) (q1) (q0) ((a0+a0)) ((a1+a1)) a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt) (MachineState.readWord s.memory 160) rest rfl
  have hmath := NextR5Columns.stage4_history s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest hn0 hi hp ha0 ha1 ha2 ha3 hc
  rw [hemb,hmath] at hraw
  have hend : R5LimbCacheBridge.inject 9062 16 (MachineState.readWord s.memory 160) (NextR5Columns.history4 s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest) = history4 s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest := by rfl
  exact hraw.trans (congrArg some hend)
def history5 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W) : State := {s with pc := N 9164,stack := (CycleSubmission.R5.ExecSquare.sqCol5_o0 (c) (q3) (q2) (q1) (q4) a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt))::(q3)::(q2)::(q1)::(q4)::(CycleSubmission.R5.ExecSquare.sqCol5_o5 (c) (q3) (q2) (q1) (q4) a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt))::((a1+a1))::((a2+a2))::a3::a4::(n1)::(n2)::(n3)::(n4)::(p)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest}
theorem run_stage5 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    runInstructions R5LimbCacheRaw.stage5Program {s with pc := N 9062,stack := (c)::(q3)::(q2)::(q1)::(q4)::((a0+a0))::((a1+a1))::((a2+a2))::a3::a4::(n1)::(n2)::(n3)::(n4)::(p)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} = some (history5 (s) (c) (q0) (q1) (q2) (q3) (q4) a0 a1 a2 a3 a4 (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest)) := by
  have hraw := R5LimbCacheRaw.stage5_run s (c) (q3) (q2) (q1) (q4) ((a0+a0)) ((a1+a1)) ((a2+a2)) a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (MachineState.readWord s.memory 160) (cnt) rest hcap hact
  have hemb := R5LimbCacheBridge.stage5_embedding s (c) (q3) (q2) (q1) (q4) ((a0+a0)) ((a1+a1)) ((a2+a2)) a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt) (MachineState.readWord s.memory 160) rest rfl
  have hmath := NextR5Columns.stage5_history s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest hn0 hi hp ha0 ha1 ha2 ha3 hc
  rw [hemb,hmath] at hraw
  have hend : R5LimbCacheBridge.inject 9164 16 (MachineState.readWord s.memory 160) (NextR5Columns.history5 s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest) = history5 s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest := by rfl
  exact hraw.trans (congrArg some hend)
def history6 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W) : State := {s with pc := N 9259,stack := (CycleSubmission.R5.ExecSquare.sqCol6_o0 (c) (q3) (q2) (q1) (q4) (z0) a1 a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt))::(q3)::(q2)::(q1)::(q4)::(z0)::(CycleSubmission.R5.ExecSquare.sqCol6_o6 (c) (q3) (q2) (q1) (q4) (z0) a1 a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt))::((a2+a2))::((a3+a3))::a4::(n1)::(n2)::(n3)::(n4)::(p)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest}
theorem run_stage6 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    runInstructions R5LimbCacheRaw.stage6Program {s with pc := N 9164,stack := (c)::(q3)::(q2)::(q1)::(q4)::(z0)::((a1+a1))::((a2+a2))::a3::a4::(n1)::(n2)::(n3)::(n4)::(p)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} = some (history6 (s) (c) (q0) (q1) (q2) (q3) (q4) a0 a1 a2 a3 a4 (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest)) := by
  have hraw := R5LimbCacheRaw.stage6_run s (c) (q3) (q2) (q1) (q4) (z0) ((a1+a1)) ((a2+a2)) a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (MachineState.readWord s.memory 160) (cnt) rest hcap hact
  have hemb := R5LimbCacheBridge.stage6_embedding s (c) (q3) (q2) (q1) (q4) (z0) ((a1+a1)) ((a2+a2)) a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt) (MachineState.readWord s.memory 160) rest rfl
  have hmath := NextR5Columns.stage6_history s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest hn0 hi hp ha0 ha1 ha2 ha3 hc
  rw [hemb,hmath] at hraw
  have hend : R5LimbCacheBridge.inject 9259 16 (MachineState.readWord s.memory 160) (NextR5Columns.history6 s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest) = history6 s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest := by rfl
  exact hraw.trans (congrArg some hend)
def history7 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W) : State := {s with pc := N 9331,stack := (CycleSubmission.R5.ExecSquare.sqCol7_o0 (c) (q3) (q2) (q1) (q4) (z0) (z1) a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt))::(q3)::(q2)::(q1)::(q4)::(z0)::(z1)::(CycleSubmission.R5.ExecSquare.sqCol7_o7 (c) (q3) (q2) (q1) (q4) (z0) (z1) a2 a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt))::((a3+a3))::a4::(n1)::(n2)::(n3)::(n4)::(p)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest}
theorem run_stage7 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    runInstructions R5LimbCacheRaw.stage7Program {s with pc := N 9259,stack := (c)::(q3)::(q2)::(q1)::(q4)::(z0)::(z1)::((a2+a2))::((a3+a3))::a4::(n1)::(n2)::(n3)::(n4)::(p)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} = some (history7 (s) (c) (q0) (q1) (q2) (q3) (q4) a0 a1 a2 a3 a4 (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest)) := by
  have hraw := R5LimbCacheRaw.stage7_run s (c) (q3) (q2) (q1) (q4) (z0) (z1) ((a2+a2)) ((a3+a3)) a4 (n1) (n2) (n3) (n4) (p) (inv) (MachineState.readWord s.memory 160) (cnt) rest hcap hact
  have hemb := R5LimbCacheBridge.stage7_embedding s (c) (q3) (q2) (q1) (q4) (z0) (z1) ((a2+a2)) ((a3+a3)) a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt) (MachineState.readWord s.memory 160) rest rfl
  have hmath := NextR5Columns.stage7_history s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest hn0 hi hp ha0 ha1 ha2 ha3 hc
  rw [hemb,hmath] at hraw
  have hend : R5LimbCacheBridge.inject 9331 16 (MachineState.readWord s.memory 160) (NextR5Columns.history7 s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest) = history7 s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest := by rfl
  exact hraw.trans (congrArg some hend)
def history8 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W) : State := {s with pc := N 9394,stack := (CycleSubmission.R5.ExecSquare.sqCol8_o0 (c) (q3) (q2) (q1) (q4) (z0) (z1) (z2) a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt))::(q3)::(q2)::(q1)::(q4)::(z0)::(z1)::(z2)::(CycleSubmission.R5.ExecSquare.sqCol8_o8 (c) (q3) (q2) (q1) (q4) (z0) (z1) (z2) a3 a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt))::a4::(n1)::(n2)::(n3)::(n4)::(p)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest}
theorem run_stage8 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    runInstructions R5LimbCacheRaw.stage8Program {s with pc := N 9331,stack := (c)::(q3)::(q2)::(q1)::(q4)::(z0)::(z1)::(z2)::((a3+a3))::a4::(n1)::(n2)::(n3)::(n4)::(p)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} = some (history8 (s) (c) (q0) (q1) (q2) (q3) (q4) a0 a1 a2 a3 a4 (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest)) := by
  have hraw := R5LimbCacheRaw.stage8_run s (c) (q3) (q2) (q1) (q4) (z0) (z1) (z2) ((a3+a3)) a4 (n1) (n2) (n3) (n4) (p) (inv) (MachineState.readWord s.memory 160) (cnt) rest hcap hact
  have hemb := R5LimbCacheBridge.stage8_embedding s (c) (q3) (q2) (q1) (q4) (z0) (z1) (z2) ((a3+a3)) a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt) (MachineState.readWord s.memory 160) rest rfl
  have hmath := NextR5Columns.stage8_history s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest hn0 hi hp ha0 ha1 ha2 ha3 hc
  rw [hemb,hmath] at hraw
  have hend : R5LimbCacheBridge.inject 9394 16 (MachineState.readWord s.memory 160) (NextR5Columns.history8 s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest) = history8 s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest := by rfl
  exact hraw.trans (congrArg some hend)
def history9 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W) : State := {s with pc := N 9405,stack := (cnt)::(z0)::(z1)::(z2)::(z3)::(c)::(n1)::(n2)::(n3)::(n4)::(p)::(inv)::(MachineState.readWord s.memory 160)::(cnt-N 1)::rest}
theorem run_stage9 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    runInstructions R5LimbCacheRaw.stage9Program {s with pc := N 9394,stack := (c)::(q3)::(q2)::(q1)::(q4)::(z0)::(z1)::(z2)::(z3)::a4::(n1)::(n2)::(n3)::(n4)::(p)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} = some (history9 (s) (c) (q0) (q1) (q2) (q3) (q4) a0 a1 a2 a3 a4 (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest)) := by
  have hraw := R5LimbCacheRaw.stage9_run s (c) (q3) (q2) (q1) (q4) (z0) (z1) (z2) (z3) a4 (n1) (n2) (n3) (n4) (p) (inv) (MachineState.readWord s.memory 160) (cnt) rest hcap hact
  have hemb := R5LimbCacheBridge.stage9_embedding s (c) (q3) (q2) (q1) (q4) (z0) (z1) (z2) (z3) a4 (n1) (n2) (n3) (n4) (p) (inv) (cnt) (MachineState.readWord s.memory 160) rest rfl
  have hmath := NextR5Columns.stage9_history s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest hn0 hi hp ha0 ha1 ha2 ha3 hc
  rw [hemb,hmath] at hraw
  have hend : R5LimbCacheBridge.inject 9405 12 (MachineState.readWord s.memory 160) (NextR5Columns.history9 s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest) = history9 s c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 rest := by rfl
  exact hraw.trans (congrArg some hend)
end CachedR5Columns
namespace CycleSubmission.Prepared.R5CachedSquare
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open CycleSubmission.R5.SquareRun
def newProgram : List Instr := (R5LimbCacheRaw.stage0Program++(R5LimbCacheRaw.stage1Program++(R5LimbCacheRaw.stage2Program++(R5LimbCacheRaw.stage3Program++(R5LimbCacheRaw.stage4Program++(R5LimbCacheRaw.stage5Program++(R5LimbCacheRaw.stage6Program++(R5LimbCacheRaw.stage7Program++(R5LimbCacheRaw.stage8Program++(R5LimbCacheRaw.stage9Program))))))))))
theorem new_run (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : P = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240) :
    runInstructions newProgram {s with pc := UInt256.ofNat 8786,stack := a0::a1::a2::a3::a4::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} = some {s with pc := UInt256.ofNat 9405,stack := (cnt)::(sqV5_5 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0))::(sqV6_6 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0))::(sqV7_7 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0))::(sqV8_8 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0))::(sqV8_0 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0))::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(sqV9_12 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0))::rest} := by
  let C0 : UInt256 := sqV0_0 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let Q0 : UInt256 := sqV0_1 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let C1 : UInt256 := sqV1_0 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let Q1 : UInt256 := sqV1_1 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let C2 : UInt256 := sqV2_0 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let Q2 : UInt256 := sqV2_1 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let C3 : UInt256 := sqV3_0 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let Q3 : UInt256 := sqV3_1 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let C4 : UInt256 := sqV4_0 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let Q4 : UInt256 := sqV4_4 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let C5 : UInt256 := sqV5_0 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let Z0 : UInt256 := sqV5_5 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let C6 : UInt256 := sqV6_0 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let Z1 : UInt256 := sqV6_6 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let C7 : UInt256 := sqV7_0 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let Z2 : UInt256 := sqV7_7 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let C8 : UInt256 := sqV8_0 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let Z3 : UInt256 := sqV8_8 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let D : UInt256 := sqV9_12 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  have hp0 : 0 < P.toNat := by
    rw [hp,CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  have hc0 : C0.toNat < P.toNat := by
    change (UInt256.mulMod _ _ P).toNat < P.toNat
    exact R5SharedTools.residue_lt _ _ _ hp0
  have hc1 : C1.toNat < P.toNat := by
    change (UInt256.mulMod _ _ P).toNat < P.toNat
    exact R5SharedTools.residue_lt _ _ _ hp0
  have hc2 : C2.toNat < P.toNat := by
    change (UInt256.mulMod _ _ P).toNat < P.toNat
    exact R5SharedTools.residue_lt _ _ _ hp0
  have hc3 : C3.toNat < P.toNat := by
    change (UInt256.mulMod _ _ P).toNat < P.toNat
    exact R5SharedTools.residue_lt _ _ _ hp0
  have hc4 : C4.toNat < P.toNat := by
    change (UInt256.mulMod _ _ P).toNat < P.toNat
    exact R5SharedTools.residue_lt _ _ _ hp0
  have hc5 : C5.toNat < P.toNat := by
    change (UInt256.mulMod _ _ P).toNat < P.toNat
    exact R5SharedTools.residue_lt _ _ _ hp0
  have hc6 : C6.toNat < P.toNat := by
    change (UInt256.mulMod _ _ P).toNat < P.toNat
    exact R5SharedTools.residue_lt _ _ _ hp0
  have hc7 : C7.toNat < P.toNat := by
    change (UInt256.mulMod _ _ P).toNat < P.toNat
    exact R5SharedTools.residue_lt _ _ _ hp0
  have hc8 : C8.toNat < P.toNat := by
    change (UInt256.mulMod _ _ P).toNat < P.toNat
    exact R5SharedTools.residue_lt _ _ _ hp0
  have h0 : runInstructions R5LimbCacheRaw.stage0Program {s with pc := UInt256.ofNat 8786,stack := a0::a1::a2::a3::a4::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} = some {s with pc := UInt256.ofNat 8812,stack := (C0)::(Q0)::((a0+a0))::a1::a2::a3::a4::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} := by
    simpa only [CachedR5Columns.history0,C0,Q0,sqV0_0,sqV0_1] using CachedR5Columns.run_stage0 (s) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) a0 a1 a2 a3 a4 (n0) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (rest) (hcap) (hact) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hp0)
  have h1 : runInstructions R5LimbCacheRaw.stage1Program {s with pc := UInt256.ofNat 8812,stack := (C0)::(Q0)::((a0+a0))::a1::a2::a3::a4::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} = some {s with pc := UInt256.ofNat 8848,stack := (C1)::(Q1)::(Q0)::((a0+a0))::a1::a2::a3::a4::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} := by
    simpa only [CachedR5Columns.history1,C1,Q1,sqV1_0,sqV1_1] using CachedR5Columns.run_stage1 (s) (C0) (Q0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) a0 a1 a2 a3 a4 (n0) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (rest) (hcap) (hact) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc0)
  have h2 : runInstructions R5LimbCacheRaw.stage2Program {s with pc := UInt256.ofNat 8848,stack := (C1)::(Q1)::(Q0)::((a0+a0))::a1::a2::a3::a4::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} = some {s with pc := UInt256.ofNat 8907,stack := (C2)::(Q2)::(Q1)::(Q0)::((a0+a0))::((a1+a1))::a2::a3::a4::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} := by
    simpa only [CachedR5Columns.history2,C2,Q2,sqV2_0,sqV2_1] using CachedR5Columns.run_stage2 (s) (C1) (Q0) (Q1) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) a0 a1 a2 a3 a4 (n0) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (rest) (hcap) (hact) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc1)
  have h3 : runInstructions R5LimbCacheRaw.stage3Program {s with pc := UInt256.ofNat 8907,stack := (C2)::(Q2)::(Q1)::(Q0)::((a0+a0))::((a1+a1))::a2::a3::a4::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} = some {s with pc := UInt256.ofNat 8972,stack := (C3)::(Q3)::(Q2)::(Q1)::(Q0)::((a0+a0))::((a1+a1))::a2::a3::a4::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} := by
    simpa only [CachedR5Columns.history3,C3,Q3,sqV3_0,sqV3_1] using CachedR5Columns.run_stage3 (s) (C2) (Q0) (Q1) (Q2) (UInt256.ofNat 0) (UInt256.ofNat 0) a0 a1 a2 a3 a4 (n0) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (rest) (hcap) (hact) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc2)
  have h4 : runInstructions R5LimbCacheRaw.stage4Program {s with pc := UInt256.ofNat 8972,stack := (C3)::(Q3)::(Q2)::(Q1)::(Q0)::((a0+a0))::((a1+a1))::a2::a3::a4::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} = some {s with pc := UInt256.ofNat 9062,stack := (C4)::(Q3)::(Q2)::(Q1)::(Q4)::((a0+a0))::((a1+a1))::((a2+a2))::a3::a4::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} := by
    simpa only [CachedR5Columns.history4,C4,Q4,sqV4_0,sqV4_4] using CachedR5Columns.run_stage4 (s) (C3) (Q0) (Q1) (Q2) (Q3) (UInt256.ofNat 0) a0 a1 a2 a3 a4 (n0) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (rest) (hcap) (hact) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc3)
  have h5 : runInstructions R5LimbCacheRaw.stage5Program {s with pc := UInt256.ofNat 9062,stack := (C4)::(Q3)::(Q2)::(Q1)::(Q4)::((a0+a0))::((a1+a1))::((a2+a2))::a3::a4::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} = some {s with pc := UInt256.ofNat 9164,stack := (C5)::(Q3)::(Q2)::(Q1)::(Q4)::(Z0)::((a1+a1))::((a2+a2))::a3::a4::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} := by
    simpa only [CachedR5Columns.history5,C5,Z0,sqV5_0,sqV5_5] using CachedR5Columns.run_stage5 (s) (C4) (Q0) (Q1) (Q2) (Q3) (Q4) a0 a1 a2 a3 a4 (n0) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (rest) (hcap) (hact) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc4)
  have h6 : runInstructions R5LimbCacheRaw.stage6Program {s with pc := UInt256.ofNat 9164,stack := (C5)::(Q3)::(Q2)::(Q1)::(Q4)::(Z0)::((a1+a1))::((a2+a2))::a3::a4::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} = some {s with pc := UInt256.ofNat 9259,stack := (C6)::(Q3)::(Q2)::(Q1)::(Q4)::(Z0)::(Z1)::((a2+a2))::((a3+a3))::a4::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} := by
    simpa only [CachedR5Columns.history6,C6,Z1,sqV6_0,sqV6_6] using CachedR5Columns.run_stage6 (s) (C5) (Q0) (Q1) (Q2) (Q3) (Q4) a0 a1 a2 a3 a4 (n0) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (Z0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (rest) (hcap) (hact) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc5)
  have h7 : runInstructions R5LimbCacheRaw.stage7Program {s with pc := UInt256.ofNat 9259,stack := (C6)::(Q3)::(Q2)::(Q1)::(Q4)::(Z0)::(Z1)::((a2+a2))::((a3+a3))::a4::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} = some {s with pc := UInt256.ofNat 9331,stack := (C7)::(Q3)::(Q2)::(Q1)::(Q4)::(Z0)::(Z1)::(Z2)::((a3+a3))::a4::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} := by
    simpa only [CachedR5Columns.history7,C7,Z2,sqV7_0,sqV7_7] using CachedR5Columns.run_stage7 (s) (C6) (Q0) (Q1) (Q2) (Q3) (Q4) a0 a1 a2 a3 a4 (n0) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (Z0) (Z1) (UInt256.ofNat 0) (UInt256.ofNat 0) (rest) (hcap) (hact) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc6)
  have h8 : runInstructions R5LimbCacheRaw.stage8Program {s with pc := UInt256.ofNat 9331,stack := (C7)::(Q3)::(Q2)::(Q1)::(Q4)::(Z0)::(Z1)::(Z2)::((a3+a3))::a4::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} = some {s with pc := UInt256.ofNat 9394,stack := (C8)::(Q3)::(Q2)::(Q1)::(Q4)::(Z0)::(Z1)::(Z2)::(Z3)::a4::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} := by
    simpa only [CachedR5Columns.history8,C8,Z3,sqV8_0,sqV8_8] using CachedR5Columns.run_stage8 (s) (C7) (Q0) (Q1) (Q2) (Q3) (Q4) a0 a1 a2 a3 a4 (n0) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (Z0) (Z1) (Z2) (UInt256.ofNat 0) (rest) (hcap) (hact) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc7)
  have h9 : runInstructions R5LimbCacheRaw.stage9Program {s with pc := UInt256.ofNat 9394,stack := (C8)::(Q3)::(Q2)::(Q1)::(Q4)::(Z0)::(Z1)::(Z2)::(Z3)::a4::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(cnt)::rest} = some {s with pc := UInt256.ofNat 9405,stack := (cnt)::(Z0)::(Z1)::(Z2)::(Z3)::(C8)::(n1)::(n2)::(n3)::(n4)::(P)::(inv)::(MachineState.readWord s.memory 160)::(D)::rest} := by
    simpa only [CachedR5Columns.history9,D,sqV9_12,CycleSubmission.R5.ExecSquare.sqTail_o12] using CachedR5Columns.run_stage9 (s) (C8) (Q0) (Q1) (Q2) (Q3) (Q4) a0 a1 a2 a3 a4 (n0) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (Z0) (Z1) (Z2) (Z3) (rest) (hcap) (hact) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc8)
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 h9)))))))))
#print axioms new_run
end CycleSubmission.Prepared.R5CachedSquare
