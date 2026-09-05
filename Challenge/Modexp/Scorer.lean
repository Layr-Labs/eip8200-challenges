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

private def makeHexInput (base exponent modulus : String) : ByteArray :=
  makeInputBytes (fromHex base) (fromHex exponent) (fromHex modulus)

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

/-- Inversion of a fixed nonzero element in the BN254 base field, computed as
`x^(p - 2) mod p`. The element is SHA-256-derived from the domain
`eip8200-challenges/modexp/bn254-inversion/base` and reduced modulo `p`. -/
def bn254ModularInversion : ByteArray := makeHexInput
  "0d2fb5ffb5b07c344bcf7640e3908737f96cce132e7e9110de36377b5d5c6289"
  "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd45"
  "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47"

/-- Fermat exponentiation of the fixed BN254 field element: `x^(p - 1) mod p`. -/
def bn254Fermat : ByteArray := makeHexInput
  "0d2fb5ffb5b07c344bcf7640e3908737f96cce132e7e9110de36377b5d5c6289"
  "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd46"
  "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47"

/-- A reproducible full-width 256-bit tuple. Each operand is derived from a
SHA-256 domain below `eip8200-challenges/modexp/random-256/`; the modulus is
forced to be odd and every operand has its high bit set. -/
def random256 : ByteArray := makeHexInput
  "a1f0b222a74b403a5a84d341cdd90fc26bf8769225b24557b64d01d7df61d9fd"
  "eca0f5ed5862646d6dc22650707a487c3436d99d7dbbba56b2f630cb682e1941"
  "afea24ccce325d471af2371241676b55270044423156c0904bb50225867f93a5"

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
reproducible. The BN254 case remains fixed because it deliberately exercises
the exponent `p - 1`. -/
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
  , { label := "2^5 mod 13", input := makeInput 2 5 13 1 1 1 }
  , { label := "zero exponent", input := makeInput 42 0 97 1 0 1 }
  , { label := "zero modulus", input := makeInput 42 7 0 1 1 12 }
  , { label := "zero modulus size", input := makeInput 42 7 0 1 1 0 }
  , { label := "EIP-198 example 1", input := eipExample1 }
  , { label := "EIP-198 example 2", input := eipExample2 }
  , { label := "trailing-zero normalization", input := truncatedModulus }
  , { label := "BN254 modular inversion", input := bn254ModularInversion }
  , { label := "random 256-bit modexp", input := random256 }
  ] ++ generatedVectors

theorem vectors_length : vectors.length = 58 := by decide

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
