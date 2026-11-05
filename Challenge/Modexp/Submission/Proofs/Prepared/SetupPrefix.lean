import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Prepared.SetupPrefix
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast

def oldpart0Program : List Instr :=
  [.push 0 0,
   .push 0 0,
   .push 0 0,
   .push 0 0,
   .push 0 0,
   .push 0 0,
   .push 0 0,
   .push 22 3347]

def oldpart0Model (s : State) (x0 x1 x2 x3 x4 : UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 3212, memory := s.memory, stack := (UInt256.ofNat 3347) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: x0 :: x1 :: x2 :: x3 :: x4 :: rest}

theorem oldpart0_run (s : State) (x0 x1 x2 x3 x4 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions oldpart0Program {s with pc := UInt256.ofNat 3182, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest} =
      some (oldpart0Model s x0 x1 x2 x3 x4 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  simp [hz, hzn, oldpart0Program, oldpart0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13]


def oldpart1Program : List Instr :=
  [.push 1 128,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Swap ⟨10, by decide⟩),
   .push 0 0,
   .op .NOT,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Swap ⟨10, by decide⟩)]

def oldpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := UInt256.lnot (UInt256.ofNat 0)
  {s with pc := UInt256.ofNat 3221, memory := s.memory, stack := x9 :: x10 :: x0 :: x1 :: v1 :: v0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x2 :: x3 :: x11 :: x12 :: rest}

theorem oldpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions oldpart1Program {s with pc := UInt256.ofNat 3212, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest} =
      some (oldpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, oldpart1Program, oldpart1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, ha128, hf128]


def oldpart2Program : List Instr :=
  [.push 2 2720,
   .op .MLOAD,
   .op (.Swap ⟨10, by decide⟩),
   .push 2 2688,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨2, by decide⟩)]

def oldpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 2720
  let v1 : UInt256 := MachineState.readWord s.memory 2688
  {s with pc := UInt256.ofNat 3232, memory := s.memory, stack := x0 :: v1 :: x10 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: v0 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem oldpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions oldpart2Program {s with pc := UInt256.ofNat 3221, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (oldpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have ha2688 : (2688 : UInt256).toNat = 2688 := rfl
  have hf2688 := Monpro.activeWords_fix s 2688 32 (by decide) (by norm_num) hact
  have ha2720 : (2720 : UInt256).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [oldpart2Program, oldpart2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, ha2688, hf2688, ha2720, hf2720]


def oldProgram : List Instr :=
  [.push 0 0,
   .push 0 0,
   .push 0 0,
   .push 0 0,
   .push 0 0,
   .push 0 0,
   .push 0 0,
   .push 22 3347,
   .push 1 128,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Swap ⟨10, by decide⟩),
   .push 0 0,
   .op .NOT,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Swap ⟨10, by decide⟩),
   .push 2 2720,
   .op .MLOAD,
   .op (.Swap ⟨10, by decide⟩),
   .push 2 2688,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨2, by decide⟩)]

def oldModel (s : State) (hd pa pb dst ret : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := UInt256.lnot (UInt256.ofNat 0)
  let v2 : UInt256 := MachineState.readWord s.memory 2720
  let v3 : UInt256 := MachineState.readWord s.memory 2688
  {s with pc := UInt256.ofNat 3232, memory := s.memory, stack := pa :: v3 :: hd :: v3 :: pb :: (UInt256.ofNat 3347) :: (UInt256.ofNat 0) :: v1 :: v0 :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: v2 :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: dst :: ret :: rest}

theorem old_run (s : State) (hd pa pb dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions oldProgram {s with pc := UInt256.ofNat 3182, stack := hd :: pa :: pb :: dst :: ret :: rest} =
      some (oldModel s hd pa pb dst ret rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := UInt256.lnot (UInt256.ofNat 0)
  let v2 : UInt256 := MachineState.readWord s.memory 2720
  let v3 : UInt256 := MachineState.readWord s.memory 2688
  have h0 : runInstructions oldpart0Program {s with pc := UInt256.ofNat 3182, memory := s.memory, stack := hd :: pa :: pb :: dst :: ret :: rest} = some {s with pc := UInt256.ofNat 3212, memory := s.memory, stack := (UInt256.ofNat 3347) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: hd :: pa :: pb :: dst :: ret :: rest} := by
    simpa only [oldpart0Model] using oldpart0_run (s) (hd) (pa) (pb) (dst) (ret) rest hcap hact
  have h1 : runInstructions oldpart1Program {s with pc := UInt256.ofNat 3212, memory := s.memory, stack := (UInt256.ofNat 3347) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: hd :: pa :: pb :: dst :: ret :: rest} = some {s with pc := UInt256.ofNat 3221, memory := s.memory, stack := pa :: pb :: (UInt256.ofNat 3347) :: (UInt256.ofNat 0) :: v1 :: v0 :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: hd :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: dst :: ret :: rest} := by
    simpa only [oldpart1Model, v0, v1] using oldpart1_run (s) ((UInt256.ofNat 3347)) ((UInt256.ofNat 0)) ((UInt256.ofNat 0)) ((UInt256.ofNat 0)) ((UInt256.ofNat 0)) ((UInt256.ofNat 0)) ((UInt256.ofNat 0)) ((UInt256.ofNat 0)) (hd) (pa) (pb) (dst) (ret) rest hcap hact
  have h2 : runInstructions oldpart2Program {s with pc := UInt256.ofNat 3221, memory := s.memory, stack := pa :: pb :: (UInt256.ofNat 3347) :: (UInt256.ofNat 0) :: v1 :: v0 :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: hd :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: dst :: ret :: rest} = some {s with pc := UInt256.ofNat 3232, memory := s.memory, stack := pa :: v3 :: hd :: v3 :: pb :: (UInt256.ofNat 3347) :: (UInt256.ofNat 0) :: v1 :: v0 :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: v2 :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: dst :: ret :: rest} := by
    simpa only [oldpart2Model, v2, v3] using oldpart2_run (s) (pa) (pb) ((UInt256.ofNat 3347)) ((UInt256.ofNat 0)) (v1) (v0) ((UInt256.ofNat 0)) ((UInt256.ofNat 0)) ((UInt256.ofNat 0)) ((UInt256.ofNat 0)) (hd) ((UInt256.ofNat 0)) ((UInt256.ofNat 0)) (dst) (ret) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 h2))

#print axioms old_run

private theorem directMax_eq : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 = UInt256.lnot (UInt256.ofNat 0) := by decide

def newpart0Program : List Instr :=
  [.push 0 0,
   .push 0 0,
   .push 0 0,
   .push 0 0,
   .push 1 128,
   .op .MLOAD,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935]

def newpart0Model (s : State) (x0 x1 x2 x3 x4 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := UInt256.lnot (UInt256.ofNat 0)
  {s with pc := UInt256.ofNat 3243, memory := s.memory, stack := v1 :: v0 :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: x0 :: x1 :: x2 :: x3 :: x4 :: rest}

theorem newpart0_run (s : State) (x0 x1 x2 x3 x4 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart0Program {s with pc := UInt256.ofNat 3203, stack := x0 :: x1 :: x2 :: x3 :: x4 :: rest} =
      some (newpart0Model s x0 x1 x2 x3 x4 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [directMax_eq, hz, hzn, newpart0Program, newpart0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, ha128, hf128]


def newpart1Program : List Instr :=
  [.push 0 0,
   .push 2 3347,
   .push 0 0,
   .op (.Swap ⟨10, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 3 2720,
   .op .MLOAD]

def newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 2688
  let v1 : UInt256 := MachineState.readWord s.memory 2720
  {s with pc := UInt256.ofNat 3255, memory := s.memory, stack := v1 :: v0 :: x8 :: (UInt256.ofNat 3347) :: (UInt256.ofNat 0) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: (UInt256.ofNat 0) :: x9 :: x10 :: rest}

theorem newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hw : rest[1]? = some (MachineState.readWord s.memory 2688)) :
    runInstructions newpart1Program {s with pc := UInt256.ofNat 3243, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rest} =
      some (newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 rest) := by
  rcases rest with _ | ⟨r0, _ | ⟨r1, rest⟩⟩
  · simp at hw
  · simp at hw
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hw
    subst hw
    simp only [List.length_cons] at hcap
    have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
    have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
    have hc (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
    have hc0 : rest.length + 0 < 1024 := hc 0 (by omega)
    have hc1 : rest.length + 1 < 1024 := hc 1 (by omega)
    have hc2 : rest.length + 2 < 1024 := hc 2 (by omega)
    have hc3 : rest.length + 3 < 1024 := hc 3 (by omega)
    have hc4 : rest.length + 4 < 1024 := hc 4 (by omega)
    have hc5 : rest.length + 5 < 1024 := hc 5 (by omega)
    have hc6 : rest.length + 6 < 1024 := hc 6 (by omega)
    have hc7 : rest.length + 7 < 1024 := hc 7 (by omega)
    have hc8 : rest.length + 8 < 1024 := hc 8 (by omega)
    have hc9 : rest.length + 9 < 1024 := hc 9 (by omega)
    have hc10 : rest.length + 10 < 1024 := hc 10 (by omega)
    have hc11 : rest.length + 11 < 1024 := hc 11 (by omega)
    have hc12 : rest.length + 12 < 1024 := hc 12 (by omega)
    have hc13 : rest.length + 13 < 1024 := hc 13 (by omega)
    have hc14 : rest.length + 14 < 1024 := hc 14 (by omega)
    have hc15 : rest.length + 15 < 1024 := hc 15 (by omega)
    have hc16 : rest.length + 16 < 1024 := hc 16 (by omega)
    have hc17 : rest.length + 17 < 1024 := hc 17 (by omega)
    have hc18 : rest.length + 18 < 1024 := hc 18 (by omega)
    have ha2720 : (2720 : UInt256).toNat = 2720 := rfl
    have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
    simp [hz, hzn, newpart1Program, newpart1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, ha2720, hf2720]


def newpart2Program : List Instr :=
  [.op (.Swap ⟨10, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .push 0 0,
   .op (.Swap ⟨13, by decide⟩)]

def newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 3259, memory := s.memory, stack := x12 :: x1 :: x11 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x0 :: (UInt256.ofNat 0) :: x13 :: x14 :: x15 :: rest}

theorem newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart2Program {s with pc := UInt256.ofNat 3255, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  simp [hz, hzn, newpart2Program, newpart2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18]


def newProgram : List Instr :=
  [.push 0 0,
   .push 0 0,
   .push 0 0,
   .push 0 0,
   .push 1 128,
   .op .MLOAD,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   .push 0 0,
   .push 2 3347,
   .push 0 0,
   .op (.Swap ⟨10, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 3 2720,
   .op .MLOAD,
   .op (.Swap ⟨10, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .push 0 0,
   .op (.Swap ⟨13, by decide⟩)]

def newModel (s : State) (hd pa pb dst ret : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := UInt256.lnot (UInt256.ofNat 0)
  let v2 : UInt256 := MachineState.readWord s.memory 2688
  let v3 : UInt256 := MachineState.readWord s.memory 2720
  {s with pc := UInt256.ofNat 3259, memory := s.memory, stack := pa :: v2 :: hd :: v2 :: pb :: (UInt256.ofNat 3347) :: (UInt256.ofNat 0) :: v1 :: v0 :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: v3 :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: dst :: ret :: rest}

theorem new_run (s : State) (hd pa pb dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hw : rest[1]? = some (MachineState.readWord s.memory 2688)) :
    runInstructions newProgram {s with pc := UInt256.ofNat 3203, stack := hd :: pa :: pb :: dst :: ret :: rest} =
      some (newModel s hd pa pb dst ret rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := UInt256.lnot (UInt256.ofNat 0)
  let v2 : UInt256 := MachineState.readWord s.memory 2688
  let v3 : UInt256 := MachineState.readWord s.memory 2720
  have h0 : runInstructions newpart0Program {s with pc := UInt256.ofNat 3203, memory := s.memory, stack := hd :: pa :: pb :: dst :: ret :: rest} = some {s with pc := UInt256.ofNat 3243, memory := s.memory, stack := v1 :: v0 :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: hd :: pa :: pb :: dst :: ret :: rest} := by
    simpa only [newpart0Model, v0, v1] using newpart0_run (s) (hd) (pa) (pb) (dst) (ret) rest hcap hact
  have h1 : runInstructions newpart1Program {s with pc := UInt256.ofNat 3243, memory := s.memory, stack := v1 :: v0 :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: hd :: pa :: pb :: dst :: ret :: rest} = some {s with pc := UInt256.ofNat 3255, memory := s.memory, stack := v3 :: v2 :: pb :: (UInt256.ofNat 3347) :: (UInt256.ofNat 0) :: v1 :: v0 :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: hd :: pa :: (UInt256.ofNat 0) :: dst :: ret :: rest} := by
    simpa only [newpart1Model, v2, v3] using newpart1_run (s) (v1) (v0) ((UInt256.ofNat 0)) ((UInt256.ofNat 0)) ((UInt256.ofNat 0)) ((UInt256.ofNat 0)) (hd) (pa) (pb) (dst) (ret) rest hcap hact hw
  have h2 : runInstructions newpart2Program {s with pc := UInt256.ofNat 3255, memory := s.memory, stack := v3 :: v2 :: pb :: (UInt256.ofNat 3347) :: (UInt256.ofNat 0) :: v1 :: v0 :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: hd :: pa :: (UInt256.ofNat 0) :: dst :: ret :: rest} = some {s with pc := UInt256.ofNat 3259, memory := s.memory, stack := pa :: v2 :: hd :: v2 :: pb :: (UInt256.ofNat 3347) :: (UInt256.ofNat 0) :: v1 :: v0 :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: v3 :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: dst :: ret :: rest} := by
    simpa only [newpart2Model] using newpart2_run (s) (v3) (v2) (pb) ((UInt256.ofNat 3347)) ((UInt256.ofNat 0)) (v1) (v0) ((UInt256.ofNat 0)) ((UInt256.ofNat 0)) ((UInt256.ofNat 0)) ((UInt256.ofNat 0)) (hd) (pa) ((UInt256.ofNat 0)) (dst) (ret) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 h2))

#print axioms new_run

theorem same_state (s : State) (hd pa pb dst ret : UInt256) (rest : List UInt256) :
    { oldModel s hd pa pb dst ret rest with pc := UInt256.ofNat 3259 } = newModel s hd pa pb dst ret rest := by
  simp only [oldModel, newModel]

theorem replacement_run (s : State) (hd pa pb dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hw : rest[1]? = some (MachineState.readWord s.memory 2688)) :
    runInstructions newProgram {s with pc := UInt256.ofNat 3203, stack := hd :: pa :: pb :: dst :: ret :: rest} =
    Option.map (fun state => {state with pc := UInt256.ofNat 3259})
      (runInstructions oldProgram {s with pc := UInt256.ofNat 3182, stack := hd :: pa :: pb :: dst :: ret :: rest}) := by
  rw [new_run s hd pa pb dst ret rest hcap hact hw, old_run s hd pa pb dst ret rest hcap hact]
  simp only [Option.map_some, same_state]
#print axioms replacement_run
end CycleSubmission.Prepared.SetupPrefix
