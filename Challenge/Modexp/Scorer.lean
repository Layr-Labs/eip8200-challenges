import Challenge.Modexp.Spec
import EvmSemantics.EVM.StepF
import EvmSemantics.Data.Hex
set_option warningAsError true

/-!
# MODEXP executable falsification checks

The scorer compares candidate returndata with the pinned precompile-level
`spec`. It includes the EIP-198 examples, edge cases, trailing-zero input
normalization, BN254 inversion, full-width arithmetic, and a deterministic
public corpus through 2048-bit operands that exercises the multi-limb path.
-/

namespace Challenge.Modexp.Scorer

open EvmSemantics
open Challenge.Modexp

def scoringGas : Nat := 1_000_000_000_000
def scoringFuel : Nat := 500_000_000

def runEvm : Nat → EVM.State → EVM.State
  | 0, state => state
  | fuel + 1, state => if state.isDone then state else runEvm fuel (EVM.stepF state)

structure Vector where
  label : String
  input : ByteArray

private def fromHex (hex : String) : ByteArray := Hex.hexToBytes hex

private def word (n : Nat) : ByteArray :=
  EvmSemantics.Data.Bytes.natToBytesPadded n 32

private def operand (n width : Nat) : ByteArray :=
  EvmSemantics.Data.Bytes.natToBytesPadded n width

def makeInput (base exponent modulus bsize esize msize : Nat) : ByteArray :=
  word bsize ++ word esize ++ word msize ++
    operand base bsize ++ operand exponent esize ++ operand modulus msize

/-- Build a MODEXP tuple from already encoded, full-width operands. -/
def makeInputBytes (base exponent modulus : ByteArray) : ByteArray :=
  word base.size ++ word exponent.size ++ word modulus.size ++
    base ++ exponent ++ modulus

/-- Public default seed for the generated corpus. A private evaluator can
replace this single value before building to produce a different corpus. -/
def corpusSeed : Nat := 0

/-- Derive an independent 64-bit seed for a bucket and one-based case index. -/
private def vectorSeed (domain index : Nat) : Nat :=
  (corpusSeed + domain + index) % (2 ^ 64)

/-- Reproducible bytes produced by a 64-bit linear congruential generator.
This is test data generation, not a cryptographic random-number generator. -/
private def generatedBytes (seed size : Nat) : ByteArray :=
  let rec go (remaining state : Nat) (bytes : Array UInt8) : ByteArray :=
    match remaining with
    | 0 => ByteArray.mk bytes
    | n + 1 =>
        let next :=
          (state * 6364136223846793005 + 1442695040888963407) % (2 ^ 64)
        go n next (bytes.push (UInt8.ofNat (next / (2 ^ 56))))
  go size (seed % (2 ^ 64)) #[]

/-- A generated big-endian operand whose first bit is set. -/
private def generatedOperand (seed : Nat) : Nat → ByteArray
  | 0 => ByteArray.empty
  | n + 1 =>
      ByteArray.mk #[UInt8.ofNat (128 + seed % 128)] ++
        generatedBytes (seed + 0x9e3779b97f4a7c15) n

/-- A generated full-width odd modulus. -/
private def generatedModulus (seed : Nat) : Nat → ByteArray
  | 0 => ByteArray.empty
  | 1 => ByteArray.mk #[UInt8.ofNat (129 + 2 * (seed % 64))]
  | n + 2 =>
      ByteArray.mk #[UInt8.ofNat (128 + seed % 128)] ++
        generatedBytes (seed + 0xd1b54a32d192ed03) n ++
        ByteArray.mk #[UInt8.ofNat (1 + 2 * (seed % 127))]

private def generatedInput
    (seed width exponent exponentWidth : Nat) : ByteArray :=
  makeInputBytes
    (generatedOperand (3 * seed + 1) width)
    (operand exponent exponentWidth)
    (generatedModulus (3 * seed + 2) width)

private def generatedWideExponentInput
    (seed width exponentWidth : Nat) : ByteArray :=
  makeInputBytes
    (generatedOperand (3 * seed + 1) width)
    (generatedOperand (3 * seed + 3) exponentWidth)
    (generatedModulus (3 * seed + 2) width)

/-- The exponent prefix used by the Osaka/EIP-7883 precompile gas formula. -/
def exponentHead (input : ByteArray) : Nat :=
  let size := Nat.min (exponentSize input) 32
  EVM.Precompile.bytesToNatPadded input (96 + baseSize input) size

/-- Gas charged by the pinned Osaka MODEXP precompile for this tuple. -/
def precompileGas (input : ByteArray) : Nat :=
  EVM.Precompile.modexpGas .Osaka (baseSize input) (exponentSize input)
    (modulusSize input) (exponentHead input)

def eipExample1 : ByteArray := fromHex
  ("0000000000000000000000000000000000000000000000000000000000000001" ++
   "0000000000000000000000000000000000000000000000000000000000000020" ++
   "0000000000000000000000000000000000000000000000000000000000000020" ++
   "03" ++
   "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e" ++
   "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f")

def eipExample2 : ByteArray := fromHex
  ("0000000000000000000000000000000000000000000000000000000000000000" ++
   "0000000000000000000000000000000000000000000000000000000000000020" ++
   "0000000000000000000000000000000000000000000000000000000000000020" ++
   "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e" ++
   "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f")

/-- EIP-198's truncated-input example: the one supplied modulus byte is
interpreted as `0x80` followed by 31 zero bytes. -/
def truncatedModulus : ByteArray := fromHex
  ("0000000000000000000000000000000000000000000000000000000000000001" ++
   "0000000000000000000000000000000000000000000000000000000000000002" ++
   "0000000000000000000000000000000000000000000000000000000000000020" ++
   "03ffff80")

def bn254Modulus : Nat :=
  0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47

/-- A seed-derived nonzero element of the BN254 base field. -/
private def generatedBn254Base (index : Nat) : Nat :=
  let bytes := generatedBytes (vectorSeed 0x2000 index) 32
  EVM.Precompile.bytesToNatPadded bytes 0 bytes.size % (bn254Modulus - 1) + 1

/-- Inversion of a seed-derived nonzero BN254 field element: `x^(p - 2) mod p`. -/
def bn254ModularInversion : ByteArray :=
  makeInput (generatedBn254Base 1) (bn254Modulus - 2) bn254Modulus 32 32 32

/-- Fermat exponentiation of another seed-derived nonzero BN254 field element:
`x^(p - 1) mod p`. -/
def bn254Fermat : ByteArray :=
  makeInput (generatedBn254Base 2) (bn254Modulus - 1) bn254Modulus 32 32 32

theorem generatedBn254Bases_valid :
    0 < generatedBn254Base 1 ∧ generatedBn254Base 1 < bn254Modulus ∧
    0 < generatedBn254Base 2 ∧ generatedBn254Base 2 < bn254Modulus := by
  native_decide

/-- Format the one-based corpus index used in scorer output. -/
private def paddedIndex (index : Nat) : String :=
  if index < 10 then s!"0{index}" else toString index

/-- The selected RSA public exponent and its minimal byte width. -/
private def rsa1024Exponent (index : Nat) : Nat × Nat :=
  if index ≤ 3 then (3, 1)
  else if index ≤ 6 then (17, 1)
  else if index ≤ 8 then (257, 2)
  else (65537, 3)

private def rsa2048Exponent (index : Nat) : Nat × Nat :=
  if index ≤ 2 then (3, 1)
  else if index ≤ 4 then (17, 1)
  else if index = 5 then (257, 2)
  else (65537, 3)

/-- Generate an RSA-sized bucket from one domain and an exponent schedule. -/
private def generatedRsaVectors (bits width domain count : Nat)
    (exponentAt : Nat → Nat × Nat) : List Vector :=
  (List.range count).map fun offset =>
    let index := offset + 1
    let (exponent, exponentWidth) := exponentAt index
    { label := s!"generated RSA-{bits} #{paddedIndex index} e={exponent}"
    , input := generatedInput (vectorSeed domain index) width exponent exponentWidth }

/-- Forty-eight deterministic public inputs. Operand bytes come from the PRNG
above. A fixed public seed and separate bucket domains make the corpus
reproducible. The BN254 exponent and modulus remain fixed while its base is
seed-derived. -/
def generatedVectors : List Vector :=
  let generated256 := (List.range 31).map fun offset =>
    let index := offset + 2
    { label := s!"generated 256-bit #{paddedIndex index} full exponent"
    , input := generatedWideExponentInput (vectorSeed 0x1000 index) 32 32 }
  [ { label := "generated 256-bit #01 BN254 p-1", input := bn254Fermat } ] ++
    generated256 ++
    generatedRsaVectors 1024 128 0x3000 10 rsa1024Exponent ++
    generatedRsaVectors 2048 256 0x4000 6 rsa2048Exponent

theorem generatedVectors_length : generatedVectors.length = 48 := by decide

theorem firstGeneratedVector_exponentHead :
    generatedVectors[0]?.map (fun vector => exponentHead vector.input) =
      some 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd46 := by
  native_decide

def vectors : List Vector :=
  [ { label := "empty tuple", input := ByteArray.empty }
  , { label := "zero exponent", input := makeInput 42 0 97 1 0 1 }
  , { label := "zero modulus", input := makeInput 42 7 0 1 1 12 }
  , { label := "zero modulus size", input := makeInput 42 7 0 1 1 0 }
  , { label := "EIP-198 example 1", input := eipExample1 }
  , { label := "EIP-198 example 2", input := eipExample2 }
  , { label := "trailing-zero normalization", input := truncatedModulus }
  , { label := "BN254 modular inversion", input := bn254ModularInversion }
  ] ++ generatedVectors

theorem vectors_length : vectors.length = 56 := by decide

inductive Outcome where
  | ok (gas : Nat)
  | wrongResult (got expected : String) (gas : Nat)
  | badHalt (halt : String) (gas : Nat)
  | outOfFuel

def Outcome.gas? : Outcome → Option Nat
  | .ok gas | .wrongResult _ _ gas | .badHalt _ gas => some gas
  | .outOfFuel => none

def score (code input : ByteArray) : Outcome :=
  let start := initialState code input scoringGas
  let final := runEvm scoringFuel start
  if !final.isDone then .outOfFuel else
  let gas := start.gasAvailable - final.gasAvailable
  match final.halt with
  | .Returned =>
      let expected := spec input
      if final.hReturn == expected then .ok gas
      else .wrongResult (Hex.bytesToHex final.hReturn) (Hex.bytesToHex expected) gas
  | halt => .badHalt (toString (repr halt)) gas

end Challenge.Modexp.Scorer
