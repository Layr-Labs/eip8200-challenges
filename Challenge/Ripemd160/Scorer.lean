import Challenge.Ripemd160.Spec
import EvmSemantics.EVM.StepF
import EvmSemantics.Data.Hex
set_option warningAsError true
/-! Executable falsification checks and gas measurement for RIPEMD-160. -/

namespace Challenge.Ripemd160.Scorer

open EvmSemantics
open Challenge.Ripemd160

def scoringGas : Nat := 3_000_000_000
def scoringFuel : Nat := 300_000_000

def runEvm : Nat → EVM.State → EVM.State
  | 0, state => state
  | fuel + 1, state => if state.isDone then state else runEvm fuel (EVM.stepF state)

def dirtyInitialState (code calldata : ByteArray) (gas : Nat) : EVM.State :=
  let state := initialState code calldata gas
  let account := state.accountMap deployAddress
  let account := { account with
    storage := account.storage.set 0 0xdeadbeef
    tstorage := account.tstorage.set 0 7 }
  let accounts := state.accountMap.set deployAddress account
  { state with
    accountMap := accounts
    substate := { state.substate with originalAccountMap := accounts }
    executionEnv := { state.executionEnv with weiValue := 0x1234 } }

structure Vector where
  label : String
  input : ByteArray

def patterned (n : Nat) : ByteArray := Id.run do
  let mut bs := ByteArray.empty
  for i in [:n] do
    bs := bs.push (UInt8.ofNat ((i * 37 + (i / 251) * 11 + 7) % 256))
  return bs

def repeated (n : Nat) (b : UInt8) : ByteArray := Id.run do
  let mut bs := ByteArray.empty
  for _ in [:n] do bs := bs.push b
  return bs

def vectors : List Vector :=
  [ { label := "empty", input := ByteArray.empty }
  , { label := "abc", input := "abc".toUTF8 }
  , { label := "1-byte", input := patterned 1 }
  , { label := "31-byte", input := patterned 31 }
  , { label := "32-byte", input := patterned 32 }
  , { label := "55-byte", input := patterned 55 }
  , { label := "56-byte", input := patterned 56 }
  , { label := "63-byte", input := patterned 63 }
  , { label := "64-byte", input := patterned 64 }
  , { label := "65-byte", input := patterned 65 }
  , { label := "119-byte", input := patterned 119 }
  , { label := "120-byte", input := patterned 120 }
  , { label := "128-byte", input := patterned 128 }
  , { label := "256-byte", input := patterned 256 }
  , { label := "1000-byte", input := patterned 1000 }
  , { label := "1000 a's", input := repeated 1000 0x61 } ]

/-- Published RIPEMD-160 vectors, including Ethereum's 12-byte left padding. -/
def oracleChecks : List (ByteArray × String) :=
  [ (ByteArray.empty,
      "0000000000000000000000009c1185a5c5e9fc54612808977ee8f548b2258d31")
  , ("abc".toUTF8,
      "0000000000000000000000008eb208f7e05d987a9b044a8e98c6b087f15a0bfc") ]

inductive Outcome where
  | ok (gas : Nat)
  | wrongDigest (got : String) (gas : Nat)
  | badHalt (halt : String) (gas : Nat)
  | outOfFuel

def Outcome.gas? : Outcome → Option Nat
  | .ok gas | .wrongDigest _ gas | .badHalt _ gas => some gas
  | .outOfFuel => none

def score (mkInitialState : ByteArray → ByteArray → Nat → EVM.State)
    (code calldata : ByteArray) : Outcome :=
  let start := mkInitialState code calldata scoringGas
  let final := runEvm scoringFuel start
  if !final.isDone then .outOfFuel else
  let gas := start.gasAvailable - final.gasAvailable
  match final.halt with
  | .Returned =>
      if final.hReturn == spec calldata then .ok gas
      else .wrongDigest (Hex.bytesToHex final.hReturn) gas
  | h => .badHalt (toString (repr h)) gas

def verdict (code : ByteArray) (v : Vector) : Outcome × Outcome × String :=
  let clean := score initialState code v.input
  let dirty := score dirtyInitialState code v.input
  let status :=
    match clean, dirty with
    | .ok g1, .ok g2 =>
        if g1 == g2 then "ok" else s!"ok (state-dependent gas: {g1} vs {g2})"
    | .wrongDigest got _, _ => s!"WRONG DIGEST {got}"
    | _, .wrongDigest got _ => s!"WRONG DIGEST (dirty state) {got}"
    | .badHalt h _, _ => s!"HALTED {h}"
    | _, .badHalt h _ => s!"HALTED (dirty state) {h}"
    | .outOfFuel, _ | _, .outOfFuel => "OUT OF FUEL"
  (clean, dirty, status)

end Challenge.Ripemd160.Scorer
