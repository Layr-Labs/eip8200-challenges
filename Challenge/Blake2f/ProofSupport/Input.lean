import Challenge.Blake2f.ProofSupport.Algorithm

set_option warningAsError true

/-!
# Reusable EIP-152 input and output views

These definitions factor the pinned byte-level driver into arrays of 64-bit
words. Candidate proofs can target the views without duplicating parsing and
serialization loops.
-/

namespace Challenge.Blake2f.ProofSupport.Input

open EvmSemantics

def readWords (input : ByteArray) (base count : Nat) : Array UInt64 :=
  ((List.range' 0 count).map fun i =>
    Crypto.Blake2f.readLE64 input (base + i * 8)).toArray

theorem readWords_succ (input : ByteArray) (base count : Nat) :
    readWords input base (count + 1) =
      (readWords input base count).push
        (Crypto.Blake2f.readLE64 input (base + count * 8)) := by
  simp [readWords, List.range'_1_concat]

def chaining (input : ByteArray) : Array UInt64 := readWords input 4 8

def message (input : ByteArray) : Array UInt64 := readWords input 68 16

def t0 (input : ByteArray) : UInt64 := Crypto.Blake2f.readLE64 input 196

def t1 (input : ByteArray) : UInt64 := Crypto.Blake2f.readLE64 input 204

def finalFlag (input : ByteArray) : Bool := input[212]! == 1

def writeWords (values : Array UInt64) (count : Nat) : ByteArray :=
  (List.range' 0 count).foldl
    (fun bytes i => Crypto.Blake2f.writeLE64 bytes values[i]!) ByteArray.empty

@[simp] theorem chaining_size (input : ByteArray) :
    (chaining input).size = 8 := by simp [chaining, readWords]

@[simp] theorem message_size (input : ByteArray) :
    (message input).size = 16 := by simp [message, readWords]

theorem compressBytes_eq (input : ByteArray) (rounds : Nat) :
    Crypto.Blake2f.compressBytes input rounds =
      writeWords
        (Crypto.Blake2f.compress rounds (chaining input) (message input)
          (t0 input) (t1 input) (finalFlag input)) 8 := by
  simp [Crypto.Blake2f.compressBytes, chaining, message, readWords,
    t0, t1, finalFlag, writeWords]

theorem compressBytes_eq_model (input : ByteArray) (rounds : Nat) :
    Crypto.Blake2f.compressBytes input rounds =
      writeWords
        (Algorithm.foldVector (chaining input)
          (Algorithm.rounds (message input) rounds
            (Algorithm.initialVector (chaining input) (t0 input) (t1 input)
              (finalFlag input)))) 8 := by
  rw [compressBytes_eq, Algorithm.compress_eq]

end Challenge.Blake2f.ProofSupport.Input
