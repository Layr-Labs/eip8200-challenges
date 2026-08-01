import Challenge.RouteB.Memory
import Challenge.Sha256.RouteB.Main
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
/-!
# Byte-level padding model for the direct SHA-256 proof

This module states the message image produced by the reference bytecode's
`pad` function independently of its control flow.  The following execution
proof can therefore expose the same postcondition to optimized submissions.
-/

namespace Challenge.Sha256.RouteB.Padding

open EvmSemantics

def messageOffset : Nat := 0xb20

/-- `ceil ((n + 9) / 64) * 64`, in the arithmetic form emitted by the
reference bytecode. -/
def paddedLength (n : Nat) : Nat := ((n + 72) / 64) * 64

def zeroCount (n : Nat) : Nat := paddedLength n - n - 9

def zeroBytes (n : Nat) : ByteArray :=
  ByteArray.mk (Array.replicate (zeroCount n) 0)

def lengthBytes (input : ByteArray) : ByteArray :=
  Data.Bytes.natToBytesPadded (input.size * 8) 8

/-- The complete message image consumed by the reference compression loop. -/
def paddedMessage (input : ByteArray) : ByteArray :=
  input ++ ByteArray.mk #[0x80] ++ zeroBytes input.size ++ lengthBytes input

def copiedMemory (memory input : ByteArray) : ByteArray :=
  MachineState.writeBytes memory input messageOffset

def sentinelMemory (memory input : ByteArray) : ByteArray :=
  MachineState.writeBytes (copiedMemory memory input) (ByteArray.mk #[0x80])
    (messageOffset + input.size)

def paddedMemory (memory input : ByteArray) : ByteArray :=
  MachineState.writeBytes (sentinelMemory memory input) (lengthBytes input)
    (messageOffset + paddedLength input.size - 8)

theorem paddedLength_pos (n : Nat) : 0 < paddedLength n := by
  unfold paddedLength
  have : 0 < (n + 72) / 64 := by omega
  omega

theorem paddedLength_mod (n : Nat) : paddedLength n % 64 = 0 := by
  simp [paddedLength]

theorem input_and_footer_fit (n : Nat) : n + 9 ≤ paddedLength n := by
  unfold paddedLength
  have h := Nat.mod_lt (n + 72) (by omega : 0 < 64)
  have hsplit := Nat.div_add_mod (n + 72) 64
  omega

theorem paddedLength_lt (n : Nat) : paddedLength n < n + 73 := by
  unfold paddedLength
  have h := Nat.mod_lt (n + 72) (by omega : 0 < 64)
  have hsplit := Nat.div_add_mod (n + 72) 64
  omega

theorem zeroCount_add (n : Nat) : n + 1 + zeroCount n + 8 = paddedLength n := by
  unfold zeroCount
  have := input_and_footer_fit n
  omega

theorem prefix_size (n : Nat) :
    n + 1 + zeroCount n = paddedLength n - 8 := by
  have hfit := input_and_footer_fit n
  have hadd := zeroCount_add n
  omega

@[simp] theorem zeroBytes_size (n : Nat) : (zeroBytes n).size = zeroCount n := by
  simp [zeroBytes, ByteArray.size]

@[simp] theorem lengthBytes_size (input : ByteArray) :
    (lengthBytes input).size = 8 := by
  rw [lengthBytes, Challenge.RouteB.Memory.natToBytesPadded_eq_natToBE]
  change (YulEvmCompiler.natToBE (input.size * 8) 8).length = 8
  exact YulEvmCompiler.length_natToBE _ _

@[simp] theorem paddedMessage_size (input : ByteArray) :
    (paddedMessage input).size = paddedLength input.size := by
  simp only [paddedMessage, ByteArray.size_append, zeroBytes_size,
    lengthBytes_size]
  change input.size + 1 + zeroCount input.size + 8 = paddedLength input.size
  exact zeroCount_add input.size

theorem paddedLength_eq_blocks (n : Nat) :
    paddedLength n = (paddedLength n / 64) * 64 := by
  simp [paddedLength]

theorem paddedMemory_eq_write (memory input : ByteArray)
    (hmemory : memory.size ≤ messageOffset) :
    paddedMemory memory input =
      MachineState.writeBytes memory (paddedMessage input) messageOffset := by
  have hsentinel : (sentinelMemory memory input).size =
      messageOffset + input.size + 1 := by
    simp only [sentinelMemory, copiedMemory, MachineState.writeBytes_size,
      show (ByteArray.mk #[0x80]).size = 1 by rfl, one_ne_zero, if_false]
    by_cases hz : input.size = 0
    · simp [hz]
      omega
    · rw [if_neg hz]
      omega
  have hpadded : (paddedMemory memory input).size =
      messageOffset + paddedLength input.size := by
    rw [paddedMemory, MachineState.writeBytes_size, lengthBytes_size,
      if_neg (by decide : 8 ≠ 0), hsentinel]
    have hfit := input_and_footer_fit input.size
    omega
  have hwritten :
      (MachineState.writeBytes memory (paddedMessage input) messageOffset).size =
        messageOffset + paddedLength input.size := by
    rw [MachineState.writeBytes_size,
      if_neg (Nat.ne_of_gt (by simpa using paddedLength_pos input.size)),
      paddedMessage_size]
    omega
  apply ByteArray.ext_getElem
  · exact hpadded.trans hwritten.symm
  · intro i hi₁ hi₂
    have hl := MachineState.writeBytes_getElem?_getD
      (sentinelMemory memory input) (lengthBytes input)
      (messageOffset + paddedLength input.size - 8) i
    have hs := MachineState.writeBytes_getElem?_getD
      (copiedMemory memory input) (ByteArray.mk #[0x80])
      (messageOffset + input.size) i
    have hc := MachineState.writeBytes_getElem?_getD memory input messageOffset i
    have hr := MachineState.writeBytes_getElem?_getD memory
      (paddedMessage input) messageOffset i
    have hleft : (paddedMemory memory input)[i]?.getD 0 =
        (paddedMemory memory input)[i] := by
      exact Challenge.RouteB.Memory.getD0_eq_getElem _ _ hi₁
    have hright :
        (MachineState.writeBytes memory (paddedMessage input) messageOffset)[i]?.getD 0 =
          (MachineState.writeBytes memory (paddedMessage input) messageOffset)[i] := by
      exact Challenge.RouteB.Memory.getD0_eq_getElem _ _ hi₂
    rw [← hleft, ← hright]
    change (MachineState.writeBytes (sentinelMemory memory input) (lengthBytes input)
      (messageOffset + paddedLength input.size - 8))[i]?.getD 0 = _
    rw [hl, hr]
    change (sentinelMemory memory input)[i]?.getD 0 = _ at hs
    change (copiedMemory memory input)[i]?.getD 0 = _ at hc
    rw [hs, hc]
    simp only [lengthBytes_size, show (ByteArray.mk #[0x80]).size = 1 by rfl,
      paddedMessage_size]
    have hfit := input_and_footer_fit input.size
    have hprefix := prefix_size input.size
    have hlenOff : messageOffset + paddedLength input.size - 8 =
        messageOffset + input.size + 1 + zeroCount input.size := by omega
    rw [hlenOff] at hl ⊢
    have hiEnd : i < messageOffset + paddedLength input.size := by
      rw [← hpadded]
      exact hi₁
    by_cases hbefore : i < messageOffset
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
    · have hiBase : messageOffset ≤ i := by omega
      by_cases hlen : messageOffset + paddedLength input.size - 8 ≤ i
      · rw [if_pos (by omega), if_pos (by omega)]
        simp only [paddedMessage]
        rw [Challenge.RouteB.Memory.getElem?_getD_append]
        rw [if_neg (by
          simp only [ByteArray.size_append, zeroBytes_size,
            show (ByteArray.mk #[0x80]).size = 1 by rfl]
          omega)]
        apply congrArg (fun k : Nat => (lengthBytes input)[k]?.getD 0)
        simp only [ByteArray.size_append, zeroBytes_size,
          show (ByteArray.mk #[0x80]).size = 1 by rfl]
        omega
      · have hlencond' : ¬(messageOffset + input.size + 1 + zeroCount input.size ≤ i ∧
            i < messageOffset + input.size + 1 + zeroCount input.size + 8) := by omega
        rw [if_neg hlencond']
        by_cases hsentinel : i = messageOffset + input.size
        · subst i
          rw [if_pos (by omega), if_pos (by omega)]
          simp only [paddedMessage]
          rw [Challenge.RouteB.Memory.getElem?_getD_append, if_pos (by
            simp only [ByteArray.size_append, zeroBytes_size,
              show (ByteArray.mk #[0x80]).size = 1 by rfl]
            omega)]
          rw [Challenge.RouteB.Memory.getElem?_getD_append, if_pos (by
            simp only [ByteArray.size_append,
              show (ByteArray.mk #[0x80]).size = 1 by rfl]
            omega)]
          rw [Challenge.RouteB.Memory.getElem?_getD_append, if_neg (by omega)]
          apply congrArg (fun k : Nat => (ByteArray.mk #[0x80])[k]?.getD 0)
          omega
        · rw [if_neg (by omega)]
          by_cases hinput : i < messageOffset + input.size
          · rw [if_pos (by omega), if_pos (by omega)]
            simp only [paddedMessage]
            rw [Challenge.RouteB.Memory.getElem?_getD_append, if_pos (by
              simp only [ByteArray.size_append, zeroBytes_size,
                show (ByteArray.mk #[0x80]).size = 1 by rfl]
              omega)]
            rw [Challenge.RouteB.Memory.getElem?_getD_append, if_pos (by
              simp only [ByteArray.size_append,
                show (ByteArray.mk #[0x80]).size = 1 by rfl]
              omega)]
            rw [Challenge.RouteB.Memory.getElem?_getD_append, if_pos (by omega)]
          · rw [if_neg (by omega), if_pos (by omega)]
            rw [Challenge.RouteB.Memory.getElem?_getD_eq_zero_of_size_le memory i
              (by omega)]
            simp only [paddedMessage]
            rw [Challenge.RouteB.Memory.getElem?_getD_append, if_pos (by
              simp only [ByteArray.size_append, zeroBytes_size,
                show (ByteArray.mk #[0x80]).size = 1 by rfl]
              omega)]
            rw [Challenge.RouteB.Memory.getElem?_getD_append, if_neg (by
              simp only [ByteArray.size_append,
                show (ByteArray.mk #[0x80]).size = 1 by rfl]
              omega)]
            simp only [zeroBytes]
            let zeros : ByteArray :=
              ByteArray.mk (Array.replicate (zeroCount input.size) 0)
            have hzeros : zeros.size = zeroCount input.size := by
              change (Array.replicate (zeroCount input.size) 0).size = _
              exact Array.size_replicate
            change 0 = zeros[i - messageOffset - (input ++ ByteArray.mk #[0x80]).size]?.getD 0
            have hindex : i - messageOffset - (input ++ ByteArray.mk #[0x80]).size =
                i - messageOffset - (input.size + 1) := by
              simp only [ByteArray.size_append]
              rfl
            rw [hindex]
            rw [Challenge.RouteB.Memory.getD0_eq_getElem!]
            by_cases hz : i - messageOffset - (input.size + 1) < zeroCount input.size
            · rw [getElem!_pos
                zeros _ (by rw [hzeros]; exact hz)]
              dsimp only [zeros]
              have harray : i - messageOffset - (input.size + 1) <
                  (Array.replicate (zeroCount input.size) (0 : UInt8)).size := by
                rw [Array.size_replicate]
                exact hz
              exact (Array.getElem_replicate harray).symm
            · rw [getElem!_neg
                zeros _ (by rw [hzeros]; exact hz)]
              rfl

theorem readPadded_paddedMemory (memory input : ByteArray)
    (hmemory : memory.size ≤ messageOffset) :
    MachineState.readPadded (paddedMemory memory input) messageOffset
      (paddedLength input.size) = paddedMessage input := by
  calc
    _ = MachineState.readPadded
        (MachineState.writeBytes memory (paddedMessage input) messageOffset)
        messageOffset (paddedLength input.size) := by
      rw [paddedMemory_eq_write memory input hmemory]
    _ = _ := by
      simpa only [paddedMessage_size] using
        Challenge.RouteB.Memory.readPadded_writeBytes_same
          memory (paddedMessage input) messageOffset

end Challenge.Sha256.RouteB.Padding
