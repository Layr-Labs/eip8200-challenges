import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

set_option warningAsError true

/-!
# Artifact-independent byte execution states

The fixed-width bytecode processes one exponent byte as a high nibble followed
by a low nibble.  These states and instruction lists factor that repeated
shape away from its four concrete bytecode locations.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowByteKernel

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open WindowNibbleKernel

def byteValue (index : Nat) (word : UInt256) : UInt256 :=
  UInt256.byteAt (UInt256.ofNat index) word

def highNibble (index : Nat) (word : UInt256) : Nat :=
  (byteValue index word).toNat / 16

def lowNibble (index : Nat) (word : UInt256) : Nat :=
  (byteValue index word).toNat % 16

def wordKernelState (template : State) (pc : UInt256)
    (base modulus word pointer accumulator : UInt256)
    (rest : List UInt256) : State :=
  { template with
    pc := pc
    stack := [word, pointer, accumulator, modulus] ++ rest
    memory := WindowTableMemory.tableMemory base modulus
    activeWords := UInt256.ofNat 16 }

def highPrepWidth (index : Nat) : Nat := if index = 0 then 0 else 1

def highPrepAdvance (index : Nat) : Nat := if index = 0 then 7 else 8

def byteAdvance (index : Nat) : Nat := highPrepAdvance index + 77

def highPrepProgram (index : Nat) : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push ⟨highPrepWidth index, by
      unfold highPrepWidth
      split <;> omega⟩ (UInt256.ofNat index), .op .BYTE,
   .op (.Dup ⟨0, by decide⟩), .push 1 4, .op .SHR]

def lowPrepProgram : List Instr :=
  [.op .POP, .op (.Dup ⟨0, by decide⟩), .push 1 15, .op .AND]

def finishProgram : List Instr := [.op .POP, .op .POP]

def highProgram (index : Nat) : List Instr :=
  highPrepProgram index ++ squareLookupProgram

def lowProgram : List Instr :=
  lowPrepProgram ++ squareLookupProgram ++ finishProgram

def byteProgram (index : Nat) : List Instr :=
  highProgram index ++ lowProgram

theorem byteValue_toNat_lt (index : Nat) (word : UInt256)
    (hindex : index < 4) :
    (byteValue index word).toNat < 256 := by
  unfold byteValue UInt256.byteAt
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (hindex.trans (by norm_num)), if_neg (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat]
  rw [show (255 : Nat) = 2 ^ 8 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  have hsmall : (word.toNat >>> (8 * (31 - index))) % 2 ^ 8 < 2 ^ 8 :=
    Nat.mod_lt _ (by norm_num)
  rw [Nat.mod_eq_of_lt (hsmall.trans (by norm_num))]
  simpa using hsmall

theorem highNibble_lt (index : Nat) (word : UInt256)
    (hindex : index < 4) : highNibble index word < 16 := by
  unfold highNibble
  have hbyte := byteValue_toNat_lt index word hindex
  omega

theorem lowNibble_lt (index : Nat) (word : UInt256) :
    lowNibble index word < 16 := by
  unfold lowNibble
  exact Nat.mod_lt _ (by norm_num)

theorem shift_highNibble (index : Nat) (word : UInt256) :
    UInt256.shiftRight (byteValue index word) (UInt256.ofNat 4) =
      UInt256.ofNat (highNibble index word) := by
  rw [Challenge.EvmProof.Word.word_eq_ofNat_toNat (byteValue index word),
    Challenge.EvmProof.Word.shiftRight_ofNat
      (value := (byteValue index word).toNat) (shift := 4)
      (byteValue index word).val.isLt (by norm_num)]
  unfold highNibble
  rw [Nat.shiftRight_eq_div_pow]

theorem mask_lowNibble (index : Nat) (word : UInt256) :
    UInt256.land (byteValue index word) (UInt256.ofNat 15) =
      UInt256.ofNat (lowNibble index word) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    show 15 % 2 ^ 256 = 15 by norm_num,
    show (15 : Nat) = 2 ^ 4 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  unfold lowNibble
  rw [Nat.mod_eq_of_lt ((Nat.mod_lt _ (by norm_num)).trans (by norm_num))]

theorem word_land_comm (left right : UInt256) :
    UInt256.land left right = UInt256.land right left := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_land, Nat.and_comm]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowByteKernel
