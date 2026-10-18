import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DataStepper
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Sites
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 400000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
open Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength
open Challenge.EvmProof.DataStepper
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Sites
open YulEvmCompiler

abbrev Located := DataStepper.Located submissionArtifact .Osaka

def word0 : UInt256 := UInt256.ofNat 0x73ddde170c56696f8be0417dea23e4835ef631c760bbc9fbe962885aed87d442
def word1 : UInt256 := UInt256.ofNat 0x94cf1ae979777bb0e2637525e8cca04e9957bd786a077efc263f3336e74ad05d
def word2 : UInt256 := UInt256.ofNat 0xb5c156bbe6988df138e6aacee6745c19d3b84929745333fe641bde12e00dcb78
def digest0 : UInt256 := UInt256.ofNat 0x976132cea9a6ad960a57a65f7f0afe0b0e3a0184
def digest1 : UInt256 := UInt256.ofNat 0x39dbb2e2b89ca92e91034daac3de296393d7b8f6
def digest2 : UInt256 := UInt256.ofNat 0xfdefca32c2dac7fcbbc93ef18902f8e85b0cadbe

theorem byteLength_append (xs ys : List Instr) :
    byteLength (xs ++ ys) = byteLength xs + byteLength ys := by
  induction xs with
  | nil => simp [byteLength]
  | cons hd tl ih =>
    cases hd with
    | op _ => simp [byteLength, ih, Nat.add_assoc]
    | push _ _ => simp [byteLength, ih, Nat.add_assoc, Nat.add_left_comm]

theorem byteLength_take_succ_op (xs : List Instr) (i : Nat) (op : Operation)
    (h : xs[i]? = some (.op op)) :
    byteLength (xs.take (i + 1)) = byteLength (xs.take i) + 1 := by
  rw [List.take_add_one, show (xs[i]?).toList = [.op op] from by simp [h], byteLength_append]
  rfl

theorem byteLength_take_succ_push (xs : List Instr) (i : Nat) (w : Fin 33) (v : UInt256)
    (h : xs[i]? = some (.push w v)) :
    byteLength (xs.take (i + 1)) = byteLength (xs.take i) + (1 + w.val) := by
  rw [List.take_add_one, show (xs[i]?).toList = [.push w v] from by simp [h], byteLength_append]
  simp [byteLength]

theorem pc_succ_op (i pc : Nat) (op : Operation)
    (hget : submissionInstructions[i]? = some (.op op))
    (hpc : submissionArtifact.instructionPC i = pc) :
    submissionArtifact.instructionPC (i + 1) = pc + 1 := by
  rw [instructionPC_eq_byteLength]
  have hinst : submissionArtifact.instructions = submissionInstructions := rfl
  rw [hinst]
  rw [instructionPC_eq_byteLength, hinst] at hpc
  rw [byteLength_take_succ_op submissionInstructions i op hget, hpc]

theorem pc_succ_push (i pc : Nat) (w : Fin 33) (v : UInt256)
    (hget : submissionInstructions[i]? = some (.push w v))
    (hpc : submissionArtifact.instructionPC i = pc) :
    submissionArtifact.instructionPC (i + 1) = pc + (1 + w.val) := by
  rw [instructionPC_eq_byteLength]
  have hinst : submissionArtifact.instructions = submissionInstructions := rfl
  rw [hinst]
  rw [instructionPC_eq_byteLength, hinst] at hpc
  rw [byteLength_take_succ_push submissionInstructions i w v hget, hpc]

set_option maxRecDepth 400000 in
theorem pc_5422 : submissionArtifact.instructionPC 5422 = 9667 := by
  rw [instructionPC_eq_byteLength]
  rfl

theorem get_5422 : submissionInstructions[5422]? = some (.op .JUMPDEST) := by rfl
theorem get_5423 : submissionInstructions[5423]? = some (.push ⟨32, by decide⟩ (UInt256.ofNat 52407983597458713726083494478729836850834839133145674611439640847371528033346)) := by rfl
theorem get_5424 : submissionInstructions[5424]? = some (.push ⟨0, by decide⟩ (UInt256.ofNat 0)) := by rfl
theorem get_5425 : submissionInstructions[5425]? = some (.op .CALLDATALOAD) := by rfl
theorem get_5426 : submissionInstructions[5426]? = some (.op .EQ) := by rfl
theorem get_5427 : submissionInstructions[5427]? = some (.push ⟨2, by decide⟩ (UInt256.ofNat 9792)) := by rfl
theorem get_5428 : submissionInstructions[5428]? = some (.op .JUMPI) := by rfl
theorem get_5429 : submissionInstructions[5429]? = some (.push ⟨32, by decide⟩ (UInt256.ofNat 67308224672597080852409368528162126009170930980447052366519322622324472729693)) := by rfl
theorem get_5430 : submissionInstructions[5430]? = some (.push ⟨0, by decide⟩ (UInt256.ofNat 0)) := by rfl
theorem get_5431 : submissionInstructions[5431]? = some (.op .CALLDATALOAD) := by rfl
theorem get_5432 : submissionInstructions[5432]? = some (.op .EQ) := by rfl
theorem get_5433 : submissionInstructions[5433]? = some (.push ⟨2, by decide⟩ (UInt256.ofNat 9820)) := by rfl
theorem get_5434 : submissionInstructions[5434]? = some (.op .JUMPI) := by rfl
theorem get_5435 : submissionInstructions[5435]? = some (.push ⟨32, by decide⟩ (UInt256.ofNat 82210225693053879566223937454697223704398777913375062608144492211390645128056)) := by rfl
theorem get_5436 : submissionInstructions[5436]? = some (.push ⟨0, by decide⟩ (UInt256.ofNat 0)) := by rfl
theorem get_5437 : submissionInstructions[5437]? = some (.op .CALLDATALOAD) := by rfl
theorem get_5438 : submissionInstructions[5438]? = some (.op .EQ) := by rfl
theorem get_5439 : submissionInstructions[5439]? = some (.push ⟨2, by decide⟩ (UInt256.ofNat 9848)) := by rfl
theorem get_5440 : submissionInstructions[5440]? = some (.op .JUMPI) := by rfl
theorem get_5441 : submissionInstructions[5441]? = some (.push ⟨2, by decide⟩ (UInt256.ofNat 497)) := by rfl
theorem get_5442 : submissionInstructions[5442]? = some (.op .JUMP) := by rfl
theorem get_5443 : submissionInstructions[5443]? = some (.op .JUMPDEST) := by rfl
theorem get_5444 : submissionInstructions[5444]? = some (.push ⟨20, by decide⟩ (UInt256.ofNat 864225204616626385640043679974750823807691915652)) := by rfl
theorem get_5445 : submissionInstructions[5445]? = some (.push ⟨0, by decide⟩ (UInt256.ofNat 0)) := by rfl
theorem get_5446 : submissionInstructions[5446]? = some (.op .MSTORE) := by rfl
theorem get_5447 : submissionInstructions[5447]? = some (.push ⟨1, by decide⟩ (UInt256.ofNat 32)) := by rfl
theorem get_5448 : submissionInstructions[5448]? = some (.push ⟨0, by decide⟩ (UInt256.ofNat 0)) := by rfl
theorem get_5449 : submissionInstructions[5449]? = some (.op .RETURN) := by rfl
theorem get_5450 : submissionInstructions[5450]? = some (.op .JUMPDEST) := by rfl
theorem get_5451 : submissionInstructions[5451]? = some (.push ⟨20, by decide⟩ (UInt256.ofNat 330311920271539217756235131599613361701789350134)) := by rfl
theorem get_5452 : submissionInstructions[5452]? = some (.push ⟨0, by decide⟩ (UInt256.ofNat 0)) := by rfl
theorem get_5453 : submissionInstructions[5453]? = some (.op .MSTORE) := by rfl
theorem get_5454 : submissionInstructions[5454]? = some (.push ⟨1, by decide⟩ (UInt256.ofNat 32)) := by rfl
theorem get_5455 : submissionInstructions[5455]? = some (.push ⟨0, by decide⟩ (UInt256.ofNat 0)) := by rfl
theorem get_5456 : submissionInstructions[5456]? = some (.op .RETURN) := by rfl
theorem get_5457 : submissionInstructions[5457]? = some (.op .JUMPDEST) := by rfl
theorem get_5458 : submissionInstructions[5458]? = some (.push ⟨20, by decide⟩ (UInt256.ofNat 1449722157075762988299117569158461631583316913598)) := by rfl
theorem get_5459 : submissionInstructions[5459]? = some (.push ⟨0, by decide⟩ (UInt256.ofNat 0)) := by rfl
theorem get_5460 : submissionInstructions[5460]? = some (.op .MSTORE) := by rfl
theorem get_5461 : submissionInstructions[5461]? = some (.push ⟨1, by decide⟩ (UInt256.ofNat 32)) := by rfl
theorem get_5462 : submissionInstructions[5462]? = some (.push ⟨0, by decide⟩ (UInt256.ofNat 0)) := by rfl
theorem get_5463 : submissionInstructions[5463]? = some (.op .RETURN) := by rfl

theorem pc_chain : True := by trivial

theorem pc_5423 : submissionArtifact.instructionPC 5423 = 9668 := by
  exact pc_succ_op 5422 9667 .JUMPDEST get_5422 pc_5422
theorem pc_5424 : submissionArtifact.instructionPC 5424 = 9701 := by
  exact pc_succ_push 5423 9668 ⟨32, by decide⟩ (UInt256.ofNat 52407983597458713726083494478729836850834839133145674611439640847371528033346) get_5423 pc_5423
theorem pc_5425 : submissionArtifact.instructionPC 5425 = 9702 := by
  exact pc_succ_push 5424 9701 ⟨0, by decide⟩ (UInt256.ofNat 0) get_5424 pc_5424
theorem pc_5426 : submissionArtifact.instructionPC 5426 = 9703 := by
  exact pc_succ_op 5425 9702 .CALLDATALOAD get_5425 pc_5425
theorem pc_5427 : submissionArtifact.instructionPC 5427 = 9704 := by
  exact pc_succ_op 5426 9703 .EQ get_5426 pc_5426
theorem pc_5428 : submissionArtifact.instructionPC 5428 = 9707 := by
  exact pc_succ_push 5427 9704 ⟨2, by decide⟩ (UInt256.ofNat 9792) get_5427 pc_5427
theorem pc_5429 : submissionArtifact.instructionPC 5429 = 9708 := by
  exact pc_succ_op 5428 9707 .JUMPI get_5428 pc_5428
theorem pc_5430 : submissionArtifact.instructionPC 5430 = 9741 := by
  exact pc_succ_push 5429 9708 ⟨32, by decide⟩ (UInt256.ofNat 67308224672597080852409368528162126009170930980447052366519322622324472729693) get_5429 pc_5429
theorem pc_5431 : submissionArtifact.instructionPC 5431 = 9742 := by
  exact pc_succ_push 5430 9741 ⟨0, by decide⟩ (UInt256.ofNat 0) get_5430 pc_5430
theorem pc_5432 : submissionArtifact.instructionPC 5432 = 9743 := by
  exact pc_succ_op 5431 9742 .CALLDATALOAD get_5431 pc_5431
theorem pc_5433 : submissionArtifact.instructionPC 5433 = 9744 := by
  exact pc_succ_op 5432 9743 .EQ get_5432 pc_5432
theorem pc_5434 : submissionArtifact.instructionPC 5434 = 9747 := by
  exact pc_succ_push 5433 9744 ⟨2, by decide⟩ (UInt256.ofNat 9820) get_5433 pc_5433
theorem pc_5435 : submissionArtifact.instructionPC 5435 = 9748 := by
  exact pc_succ_op 5434 9747 .JUMPI get_5434 pc_5434
theorem pc_5436 : submissionArtifact.instructionPC 5436 = 9781 := by
  exact pc_succ_push 5435 9748 ⟨32, by decide⟩ (UInt256.ofNat 82210225693053879566223937454697223704398777913375062608144492211390645128056) get_5435 pc_5435
theorem pc_5437 : submissionArtifact.instructionPC 5437 = 9782 := by
  exact pc_succ_push 5436 9781 ⟨0, by decide⟩ (UInt256.ofNat 0) get_5436 pc_5436
theorem pc_5438 : submissionArtifact.instructionPC 5438 = 9783 := by
  exact pc_succ_op 5437 9782 .CALLDATALOAD get_5437 pc_5437
theorem pc_5439 : submissionArtifact.instructionPC 5439 = 9784 := by
  exact pc_succ_op 5438 9783 .EQ get_5438 pc_5438
theorem pc_5440 : submissionArtifact.instructionPC 5440 = 9787 := by
  exact pc_succ_push 5439 9784 ⟨2, by decide⟩ (UInt256.ofNat 9848) get_5439 pc_5439
theorem pc_5441 : submissionArtifact.instructionPC 5441 = 9788 := by
  exact pc_succ_op 5440 9787 .JUMPI get_5440 pc_5440
theorem pc_5442 : submissionArtifact.instructionPC 5442 = 9791 := by
  exact pc_succ_push 5441 9788 ⟨2, by decide⟩ (UInt256.ofNat 497) get_5441 pc_5441
theorem pc_5443 : submissionArtifact.instructionPC 5443 = 9792 := by
  exact pc_succ_op 5442 9791 .JUMP get_5442 pc_5442
theorem pc_5444 : submissionArtifact.instructionPC 5444 = 9793 := by
  exact pc_succ_op 5443 9792 .JUMPDEST get_5443 pc_5443
theorem pc_5445 : submissionArtifact.instructionPC 5445 = 9814 := by
  exact pc_succ_push 5444 9793 ⟨20, by decide⟩ (UInt256.ofNat 864225204616626385640043679974750823807691915652) get_5444 pc_5444
theorem pc_5446 : submissionArtifact.instructionPC 5446 = 9815 := by
  exact pc_succ_push 5445 9814 ⟨0, by decide⟩ (UInt256.ofNat 0) get_5445 pc_5445
theorem pc_5447 : submissionArtifact.instructionPC 5447 = 9816 := by
  exact pc_succ_op 5446 9815 .MSTORE get_5446 pc_5446
theorem pc_5448 : submissionArtifact.instructionPC 5448 = 9818 := by
  exact pc_succ_push 5447 9816 ⟨1, by decide⟩ (UInt256.ofNat 32) get_5447 pc_5447
theorem pc_5449 : submissionArtifact.instructionPC 5449 = 9819 := by
  exact pc_succ_push 5448 9818 ⟨0, by decide⟩ (UInt256.ofNat 0) get_5448 pc_5448
theorem pc_5450 : submissionArtifact.instructionPC 5450 = 9820 := by
  exact pc_succ_op 5449 9819 .RETURN get_5449 pc_5449
theorem pc_5451 : submissionArtifact.instructionPC 5451 = 9821 := by
  exact pc_succ_op 5450 9820 .JUMPDEST get_5450 pc_5450
theorem pc_5452 : submissionArtifact.instructionPC 5452 = 9842 := by
  exact pc_succ_push 5451 9821 ⟨20, by decide⟩ (UInt256.ofNat 330311920271539217756235131599613361701789350134) get_5451 pc_5451
theorem pc_5453 : submissionArtifact.instructionPC 5453 = 9843 := by
  exact pc_succ_push 5452 9842 ⟨0, by decide⟩ (UInt256.ofNat 0) get_5452 pc_5452
theorem pc_5454 : submissionArtifact.instructionPC 5454 = 9844 := by
  exact pc_succ_op 5453 9843 .MSTORE get_5453 pc_5453
theorem pc_5455 : submissionArtifact.instructionPC 5455 = 9846 := by
  exact pc_succ_push 5454 9844 ⟨1, by decide⟩ (UInt256.ofNat 32) get_5454 pc_5454
theorem pc_5456 : submissionArtifact.instructionPC 5456 = 9847 := by
  exact pc_succ_push 5455 9846 ⟨0, by decide⟩ (UInt256.ofNat 0) get_5455 pc_5455
theorem pc_5457 : submissionArtifact.instructionPC 5457 = 9848 := by
  exact pc_succ_op 5456 9847 .RETURN get_5456 pc_5456
theorem pc_5458 : submissionArtifact.instructionPC 5458 = 9849 := by
  exact pc_succ_op 5457 9848 .JUMPDEST get_5457 pc_5457
theorem pc_5459 : submissionArtifact.instructionPC 5459 = 9870 := by
  exact pc_succ_push 5458 9849 ⟨20, by decide⟩ (UInt256.ofNat 1449722157075762988299117569158461631583316913598) get_5458 pc_5458
theorem pc_5460 : submissionArtifact.instructionPC 5460 = 9871 := by
  exact pc_succ_push 5459 9870 ⟨0, by decide⟩ (UInt256.ofNat 0) get_5459 pc_5459
theorem pc_5461 : submissionArtifact.instructionPC 5461 = 9872 := by
  exact pc_succ_op 5460 9871 .MSTORE get_5460 pc_5460
theorem pc_5462 : submissionArtifact.instructionPC 5462 = 9874 := by
  exact pc_succ_push 5461 9872 ⟨1, by decide⟩ (UInt256.ofNat 32) get_5461 pc_5461
theorem pc_5463 : submissionArtifact.instructionPC 5463 = 9875 := by
  exact pc_succ_push 5462 9874 ⟨0, by decide⟩ (UInt256.ofNat 0) get_5462 pc_5462

theorem eq_zero_of_ne {a b : UInt256} (h : a ≠ b) : UInt256.eq a b = 0 := by
  unfold UInt256.eq
  have hnat : ¬ a.toNat = b.toNat := by
    intro heq
    exact h (Challenge.EvmProof.Word.word_ext heq)
  rw [if_neg hnat]
  exact (Challenge.EvmProof.Word.literal_eq_ofNat 0).symm

theorem eq_one_of_eq {a b : UInt256} (h : a = b) : UInt256.eq a b = 1 := by
  unfold UInt256.eq
  subst h
  rw [if_pos rfl]
  exact (Challenge.EvmProof.Word.literal_eq_ofNat 1).symm

theorem not_isTrue_zero : ¬ UInt256.isTrue 0 := by
  unfold UInt256.isTrue
  rw [Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  decide

theorem isTrue_one : UInt256.isTrue 1 := by
  unfold UInt256.isTrue
  rw [Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  decide

def loc (i : Nat) (instruction : Instr) (hget : submissionInstructions[i]? = some instruction)
    (hwf : WellFormed .Osaka instruction) : Located :=
  ⟨i, instruction, hget, hwf⟩

def loc_5422 : Located := ⟨5422, .op .JUMPDEST, get_5422, ⟨by decide, by trivial, by rfl⟩⟩
def loc_5423 : Located := ⟨5423, .push ⟨32, by decide⟩ (UInt256.ofNat 52407983597458713726083494478729836850834839133145674611439640847371528033346), get_5423, by decide⟩
def loc_5424 : Located := ⟨5424, .push ⟨0, by decide⟩ (UInt256.ofNat 0), get_5424, by decide⟩
def loc_5425 : Located := ⟨5425, .op .CALLDATALOAD, get_5425, ⟨by decide, by trivial, by rfl⟩⟩
def loc_5426 : Located := ⟨5426, .op .EQ, get_5426, ⟨by decide, by trivial, by rfl⟩⟩
def loc_5427 : Located := ⟨5427, .push ⟨2, by decide⟩ (UInt256.ofNat 9792), get_5427, by decide⟩
def loc_5428 : Located := ⟨5428, .op .JUMPI, get_5428, ⟨by decide, by trivial, by rfl⟩⟩
def loc_5429 : Located := ⟨5429, .push ⟨32, by decide⟩ (UInt256.ofNat 67308224672597080852409368528162126009170930980447052366519322622324472729693), get_5429, by decide⟩
def loc_5430 : Located := ⟨5430, .push ⟨0, by decide⟩ (UInt256.ofNat 0), get_5430, by decide⟩
def loc_5431 : Located := ⟨5431, .op .CALLDATALOAD, get_5431, ⟨by decide, by trivial, by rfl⟩⟩
def loc_5432 : Located := ⟨5432, .op .EQ, get_5432, ⟨by decide, by trivial, by rfl⟩⟩
def loc_5433 : Located := ⟨5433, .push ⟨2, by decide⟩ (UInt256.ofNat 9820), get_5433, by decide⟩
def loc_5434 : Located := ⟨5434, .op .JUMPI, get_5434, ⟨by decide, by trivial, by rfl⟩⟩
def loc_5435 : Located := ⟨5435, .push ⟨32, by decide⟩ (UInt256.ofNat 82210225693053879566223937454697223704398777913375062608144492211390645128056), get_5435, by decide⟩
def loc_5436 : Located := ⟨5436, .push ⟨0, by decide⟩ (UInt256.ofNat 0), get_5436, by decide⟩
def loc_5437 : Located := ⟨5437, .op .CALLDATALOAD, get_5437, ⟨by decide, by trivial, by rfl⟩⟩
def loc_5438 : Located := ⟨5438, .op .EQ, get_5438, ⟨by decide, by trivial, by rfl⟩⟩
def loc_5439 : Located := ⟨5439, .push ⟨2, by decide⟩ (UInt256.ofNat 9848), get_5439, by decide⟩
def loc_5440 : Located := ⟨5440, .op .JUMPI, get_5440, ⟨by decide, by trivial, by rfl⟩⟩
def loc_5441 : Located := ⟨5441, .push ⟨2, by decide⟩ (UInt256.ofNat 497), get_5441, by decide⟩
def loc_5442 : Located := ⟨5442, .op .JUMP, get_5442, ⟨by decide, by trivial, by rfl⟩⟩
def loc_5443 : Located := ⟨5443, .op .JUMPDEST, get_5443, ⟨by decide, by trivial, by rfl⟩⟩
def loc_5444 : Located := ⟨5444, .push ⟨20, by decide⟩ (UInt256.ofNat 864225204616626385640043679974750823807691915652), get_5444, by decide⟩
def loc_5445 : Located := ⟨5445, .push ⟨0, by decide⟩ (UInt256.ofNat 0), get_5445, by decide⟩
def loc_5446 : Located := ⟨5446, .op .MSTORE, get_5446, ⟨by decide, by trivial, by rfl⟩⟩
def loc_5447 : Located := ⟨5447, .push ⟨1, by decide⟩ (UInt256.ofNat 32), get_5447, by decide⟩
def loc_5448 : Located := ⟨5448, .push ⟨0, by decide⟩ (UInt256.ofNat 0), get_5448, by decide⟩
def loc_5449 : Located := ⟨5449, .op .RETURN, get_5449, ⟨by decide, by trivial, by rfl⟩⟩
def loc_5450 : Located := ⟨5450, .op .JUMPDEST, get_5450, ⟨by decide, by trivial, by rfl⟩⟩
def loc_5451 : Located := ⟨5451, .push ⟨20, by decide⟩ (UInt256.ofNat 330311920271539217756235131599613361701789350134), get_5451, by decide⟩
def loc_5452 : Located := ⟨5452, .push ⟨0, by decide⟩ (UInt256.ofNat 0), get_5452, by decide⟩
def loc_5453 : Located := ⟨5453, .op .MSTORE, get_5453, ⟨by decide, by trivial, by rfl⟩⟩
def loc_5454 : Located := ⟨5454, .push ⟨1, by decide⟩ (UInt256.ofNat 32), get_5454, by decide⟩
def loc_5455 : Located := ⟨5455, .push ⟨0, by decide⟩ (UInt256.ofNat 0), get_5455, by decide⟩
def loc_5456 : Located := ⟨5456, .op .RETURN, get_5456, ⟨by decide, by trivial, by rfl⟩⟩
def loc_5457 : Located := ⟨5457, .op .JUMPDEST, get_5457, ⟨by decide, by trivial, by rfl⟩⟩
def loc_5458 : Located := ⟨5458, .push ⟨20, by decide⟩ (UInt256.ofNat 1449722157075762988299117569158461631583316913598), get_5458, by decide⟩
def loc_5459 : Located := ⟨5459, .push ⟨0, by decide⟩ (UInt256.ofNat 0), get_5459, by decide⟩
def loc_5460 : Located := ⟨5460, .op .MSTORE, get_5460, ⟨by decide, by trivial, by rfl⟩⟩
def loc_5461 : Located := ⟨5461, .push ⟨1, by decide⟩ (UInt256.ofNat 32), get_5461, by decide⟩
def loc_5462 : Located := ⟨5462, .push ⟨0, by decide⟩ (UInt256.ofNat 0), get_5462, by decide⟩
def loc_5463 : Located := ⟨5463, .op .RETURN, get_5463, ⟨by decide, by trivial, by rfl⟩⟩

theorem valid_497 (s : State) (hcode : s.executionEnv.code = submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code 497 = true := by
  have h := submissionArtifact.isValidJumpDest_index 206 (by rfl)
  have hpc : submissionArtifact.instructionPC 206 = 497 := by
    rw [instructionPC_eq_byteLength]
    rfl
  rw [hpc] at h
  rw [hcode]
  exact h

theorem valid_9792 (s : State) (hcode : s.executionEnv.code = submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code 9792 = true := by
  have h := submissionArtifact.isValidJumpDest_index 5443 get_5443
  rw [pc_5443] at h
  rw [hcode]
  exact h

theorem valid_9820 (s : State) (hcode : s.executionEnv.code = submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code 9820 = true := by
  have h := submissionArtifact.isValidJumpDest_index 5450 get_5450
  rw [pc_5450] at h
  rw [hcode]
  exact h

theorem valid_9848 (s : State) (hcode : s.executionEnv.code = submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code 9848 = true := by
  have h := submissionArtifact.isValidJumpDest_index 5457 get_5457
  rw [pc_5457] at h
  rw [hcode]
  exact h

theorem valid_9667 (s : State) (hcode : s.executionEnv.code = submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code 9667 = true := by
  have h := submissionArtifact.isValidJumpDest_index 5422 get_5422
  rw [pc_5422] at h
  rw [hcode]
  exact h


theorem code_at (s : State) (pc : Nat) (stk : List UInt256) :
    (atState s pc stk).executionEnv = s.executionEnv := rfl

theorem at_pc (pc : Nat) (s : State) (stk : List UInt256) (h : pc < 2 ^ 256) :
    (atState s pc stk).pc.toNat = pc := by
  rw [atState]
  change (UInt256.ofNat pc).toNat = pc
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt h]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32
