import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
open CycleSubmission.SharedStackArgs
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof.Word Challenge.EvmProof.Stepper
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
namespace OverlapPackRaw5
def part0Program : List Instr := [.op .JUMPDEST,.push 1 120,.op .MSTORE]
def part0Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f0.toNat 32) 120
  {s with pc := N 10227,memory := v0,stack := f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::rest}
theorem part0_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions part0Program {s with pc := N 10223,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::rest} = some (part0Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha120 : (120 : W).toNat = 120 := rfl
 have hf120 := Monpro.activeWords_fix s 120 32 (by decide) (by norm_num) hact
 simp [part0Program,part0Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha120,hf120]
def part1Program : List Instr := [.push 1 90,.op .MSTORE]
def part1Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f0.toNat 32) 90
  {s with pc := N 10230,memory := v0,stack := f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::rest}
theorem part1_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions part1Program {s with pc := N 10227,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::rest} = some (part1Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha90 : (90 : W).toNat = 90 := rfl
 have hf90 := Monpro.activeWords_fix s 90 32 (by decide) (by norm_num) hact
 simp [part1Program,part1Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha90,hf90]
def part2Program : List Instr := [.push 1 60,.op .MSTORE]
def part2Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f0.toNat 32) 60
  {s with pc := N 10233,memory := v0,stack := f1::f2::f3::f4::f5::f6::f7::f8::f9::rest}
theorem part2_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions part2Program {s with pc := N 10230,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::rest} = some (part2Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha60 : (60 : W).toNat = 60 := rfl
 have hf60 := Monpro.activeWords_fix s 60 32 (by decide) (by norm_num) hact
 simp [part2Program,part2Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha60,hf60]
def part3Program : List Instr := [.push 1 30,.op .MSTORE]
def part3Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f0.toNat 32) 30
  {s with pc := N 10236,memory := v0,stack := f1::f2::f3::f4::f5::f6::f7::f8::rest}
theorem part3_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions part3Program {s with pc := N 10233,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::rest} = some (part3Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha30 : (30 : W).toNat = 30 := rfl
 have hf30 := Monpro.activeWords_fix s 30 32 (by decide) (by norm_num) hact
 simp [part3Program,part3Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha30,hf30]
def part4Program : List Instr := [.push 0 0,.op .MSTORE]
def part4Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f0.toNat 32) 0
  {s with pc := N 10238,memory := v0,stack := f1::f2::f3::f4::f5::f6::f7::rest}
theorem part4_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions part4Program {s with pc := N 10236,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::rest} = some (part4Model s f0 f1 f2 f3 f4 f5 f6 f7 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha0 : (0 : W).toNat = 0 := rfl
 have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
 simp [part4Program,part4Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0]
def program : List Instr := (part0Program++(part1Program++(part2Program++(part3Program++part4Program))))
def model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f0.toNat 32) 120
  let v1 : ByteArray := MachineState.writeBytes v0 (Data.Bytes.natToBytesPadded f1.toNat 32) 90
  let v2 : ByteArray := MachineState.writeBytes v1 (Data.Bytes.natToBytesPadded f2.toNat 32) 60
  let v3 : ByteArray := MachineState.writeBytes v2 (Data.Bytes.natToBytesPadded f3.toNat 32) 30
  let v4 : ByteArray := MachineState.writeBytes v3 (Data.Bytes.natToBytesPadded f4.toNat 32) 0
  {s with pc := N 10238,memory := v4,stack := f5::f6::f7::f8::f9::f10::f11::rest}
theorem run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions program {s with pc := N 10223,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::rest} = some (model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 rest) := by
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f0.toNat 32) 120
  let v1 : ByteArray := MachineState.writeBytes v0 (Data.Bytes.natToBytesPadded f1.toNat 32) 90
  let v2 : ByteArray := MachineState.writeBytes v1 (Data.Bytes.natToBytesPadded f2.toNat 32) 60
  let v3 : ByteArray := MachineState.writeBytes v2 (Data.Bytes.natToBytesPadded f3.toNat 32) 30
  let v4 : ByteArray := MachineState.writeBytes v3 (Data.Bytes.natToBytesPadded f4.toNat 32) 0
  have h0 : runInstructions part0Program {s with pc := N 10223,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::rest} = some {s with pc := N 10227,memory := v0,stack := f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::rest} := by
    simpa only [part0Model,v0] using part0_run ({s with memory := s.memory}) f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 rest hcap hact
  have h1 : runInstructions part1Program {s with pc := N 10227,memory := v0,stack := f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::rest} = some {s with pc := N 10230,memory := v1,stack := f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::rest} := by
    simpa only [part1Model,v1] using part1_run ({s with memory := v0}) f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 rest hcap hact
  have h2 : runInstructions part2Program {s with pc := N 10230,memory := v1,stack := f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::rest} = some {s with pc := N 10233,memory := v2,stack := f3::f4::f5::f6::f7::f8::f9::f10::f11::rest} := by
    simpa only [part2Model,v2] using part2_run ({s with memory := v1}) f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 rest hcap hact
  have h3 : runInstructions part3Program {s with pc := N 10233,memory := v2,stack := f3::f4::f5::f6::f7::f8::f9::f10::f11::rest} = some {s with pc := N 10236,memory := v3,stack := f4::f5::f6::f7::f8::f9::f10::f11::rest} := by
    simpa only [part3Model,v3] using part3_run ({s with memory := v2}) f3 f4 f5 f6 f7 f8 f9 f10 f11 rest hcap hact
  have h4 : runInstructions part4Program {s with pc := N 10236,memory := v3,stack := f4::f5::f6::f7::f8::f9::f10::f11::rest} = some {s with pc := N 10238,memory := v4,stack := f5::f6::f7::f8::f9::f10::f11::rest} := by
    simpa only [part4Model,v4] using part4_run ({s with memory := v3}) f4 f5 f6 f7 f8 f9 f10 f11 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 h4))))
#print axioms run
end OverlapPackRaw5
