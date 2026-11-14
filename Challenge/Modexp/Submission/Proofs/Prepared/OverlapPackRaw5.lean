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
def part0Program : List Instr := [.op .JUMPDEST,.push 1 128,.op .MSTORE]
def part0Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f0.toNat 32) 128
  {s with pc := N 10182,memory := v0,stack := f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::rest}
theorem part0_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions part0Program {s with pc := N 10178,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::rest} = some (part0Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha128 : (128 : W).toNat = 128 := rfl
 have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
 simp [part0Program,part0Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha128,hf128]
def part1Program : List Instr := [.push 1 98,.op .MSTORE]
def part1Model (s : State) (f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f1.toNat 32) 98
  {s with pc := N 10185,memory := v0,stack := f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::rest}
theorem part1_run (s : State) (f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions part1Program {s with pc := N 10182,memory := s.memory,stack := f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::rest} = some (part1Model s f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha98 : (98 : W).toNat = 98 := rfl
 have hf98 := Monpro.activeWords_fix s 98 32 (by decide) (by norm_num) hact
 simp [part1Program,part1Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha98,hf98]
def part2Program : List Instr := [.push 1 68,.op .MSTORE]
def part2Model (s : State) (f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f2.toNat 32) 68
  {s with pc := N 10188,memory := v0,stack := f3::f4::f5::f6::f7::f8::f9::f10::f11::rest}
theorem part2_run (s : State) (f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions part2Program {s with pc := N 10185,memory := s.memory,stack := f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::rest} = some (part2Model s f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha68 : (68 : W).toNat = 68 := rfl
 have hf68 := Monpro.activeWords_fix s 68 32 (by decide) (by norm_num) hact
 simp [part2Program,part2Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha68,hf68]
def part3Program : List Instr := [.push 1 38,.op .MSTORE]
def part3Model (s : State) (f3 f4 f5 f6 f7 f8 f9 f10 f11 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f3.toNat 32) 38
  {s with pc := N 10191,memory := v0,stack := f4::f5::f6::f7::f8::f9::f10::f11::rest}
theorem part3_run (s : State) (f3 f4 f5 f6 f7 f8 f9 f10 f11 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions part3Program {s with pc := N 10188,memory := s.memory,stack := f3::f4::f5::f6::f7::f8::f9::f10::f11::rest} = some (part3Model s f3 f4 f5 f6 f7 f8 f9 f10 f11 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha38 : (38 : W).toNat = 38 := rfl
 have hf38 := Monpro.activeWords_fix s 38 32 (by decide) (by norm_num) hact
 simp [part3Program,part3Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha38,hf38]
def part4Program : List Instr := [.push 1 8,.op .MSTORE]
def part4Model (s : State) (f4 f5 f6 f7 f8 f9 f10 f11 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f4.toNat 32) 8
  {s with pc := N 10194,memory := v0,stack := f5::f6::f7::f8::f9::f10::f11::rest}
theorem part4_run (s : State) (f4 f5 f6 f7 f8 f9 f10 f11 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions part4Program {s with pc := N 10191,memory := s.memory,stack := f4::f5::f6::f7::f8::f9::f10::f11::rest} = some (part4Model s f4 f5 f6 f7 f8 f9 f10 f11 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha8 : (8 : W).toNat = 8 := rfl
 have hf8 := Monpro.activeWords_fix s 8 32 (by decide) (by norm_num) hact
 simp [part4Program,part4Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha8,hf8]
def program : List Instr := (part0Program++(part1Program++(part2Program++(part3Program++part4Program))))
def model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f0.toNat 32) 128
  let v1 : ByteArray := MachineState.writeBytes v0 (Data.Bytes.natToBytesPadded f1.toNat 32) 98
  let v2 : ByteArray := MachineState.writeBytes v1 (Data.Bytes.natToBytesPadded f2.toNat 32) 68
  let v3 : ByteArray := MachineState.writeBytes v2 (Data.Bytes.natToBytesPadded f3.toNat 32) 38
  let v4 : ByteArray := MachineState.writeBytes v3 (Data.Bytes.natToBytesPadded f4.toNat 32) 8
  {s with pc := N 10194,memory := v4,stack := f5::f6::f7::f8::f9::f10::f11::rest}
theorem run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions program {s with pc := N 10178,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::rest} = some (model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 rest) := by
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f0.toNat 32) 128
  let v1 : ByteArray := MachineState.writeBytes v0 (Data.Bytes.natToBytesPadded f1.toNat 32) 98
  let v2 : ByteArray := MachineState.writeBytes v1 (Data.Bytes.natToBytesPadded f2.toNat 32) 68
  let v3 : ByteArray := MachineState.writeBytes v2 (Data.Bytes.natToBytesPadded f3.toNat 32) 38
  let v4 : ByteArray := MachineState.writeBytes v3 (Data.Bytes.natToBytesPadded f4.toNat 32) 8
  have h0 : runInstructions part0Program {s with pc := N 10178,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::rest} = some {s with pc := N 10182,memory := v0,stack := f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::rest} := by
    simpa only [part0Model,v0] using part0_run ({s with memory := s.memory}) f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 rest hcap hact
  have h1 : runInstructions part1Program {s with pc := N 10182,memory := v0,stack := f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::rest} = some {s with pc := N 10185,memory := v1,stack := f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::rest} := by
    simpa only [part1Model,v1] using part1_run ({s with memory := v0}) f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 rest hcap hact
  have h2 : runInstructions part2Program {s with pc := N 10185,memory := v1,stack := f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::rest} = some {s with pc := N 10188,memory := v2,stack := f3::f4::f5::f6::f7::f8::f9::f10::f11::rest} := by
    simpa only [part2Model,v2] using part2_run ({s with memory := v1}) f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 rest hcap hact
  have h3 : runInstructions part3Program {s with pc := N 10188,memory := v2,stack := f3::f4::f5::f6::f7::f8::f9::f10::f11::rest} = some {s with pc := N 10191,memory := v3,stack := f4::f5::f6::f7::f8::f9::f10::f11::rest} := by
    simpa only [part3Model,v3] using part3_run ({s with memory := v2}) f3 f4 f5 f6 f7 f8 f9 f10 f11 rest hcap hact
  have h4 : runInstructions part4Program {s with pc := N 10191,memory := v3,stack := f4::f5::f6::f7::f8::f9::f10::f11::rest} = some {s with pc := N 10194,memory := v4,stack := f5::f6::f7::f8::f9::f10::f11::rest} := by
    simpa only [part4Model,v4] using part4_run ({s with memory := v3}) f4 f5 f6 f7 f8 f9 f10 f11 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 h4))))
#print axioms run
end OverlapPackRaw5
