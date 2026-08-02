import Challenge.Sha256.Spec
import EvmSemantics.EVM.StepF
import EvmSemantics.Data.Hex
set_option warningAsError true
/-!
# Tier 1: falsification by execution

Runs a candidate implementation in the pinned *executable* EVM semantics
(`EvmSemantics.EVM.stepF`) and compares its returndata with `spec` — the
same `Crypto.Sha256.hash` that `Challenge.Sha256.Correct` is stated against,
and that the `0x02` precompile computes.

The clean starting state is `Challenge.Sha256.initialState`, exactly the state
used by `Correct`, so a Tier-1 pass is a finite sample of the Tier-2 statement.
Each vector is also run from `dirtyInitialState`, which seeds storage,
transient storage, and a nonzero call value. A faithful precompile replacement
cannot notice those contextual differences.

Passing is necessary and never sufficient. The sufficient condition is a Lean
proof of `Correct`.
-/

namespace Challenge.Sha256.Scorer

open EvmSemantics
open Challenge.Sha256

/-- Gas budget for one scored run: enough that a failing candidate fails on
its digest rather than on our budget. -/
def scoringGas : Nat := 3_000_000_000

/-- Step budget for one scored run. -/
def scoringFuel : Nat := 200_000_000

/-- Drive the executable semantics to a halt or until the fuel runs out. -/
def runEvm : Nat → EVM.State → EVM.State
  | 0, state => state
  | fuel + 1, state => if state.isDone then state else runEvm fuel (EVM.stepF state)

/-- The fixed initial state with a *dirty* world: seeded storage and transient
storage in the executing account, and a nonzero call value. Everything a
SHA-256 implementation is entitled to read (calldata) is unchanged, so a
correct candidate returns the same digest for the same gas. -/
def dirtyInitialState (code calldata : ByteArray) (gas : Nat) : EVM.State :=
  let state := initialState code calldata gas
  let account := state.accountMap deployAddress
  let account := { account with
    storage := account.storage
      |>.set (UInt256.ofNat 0) (UInt256.ofNat 0xdeadbeef)
      |>.set (UInt256.ofNat 1) (UInt256.ofNat (2 ^ 255))
      |>.set (UInt256.ofNat 0x120) (UInt256.ofNat 0xffff)
    tstorage := account.tstorage
      |>.set (UInt256.ofNat 0) (UInt256.ofNat 7)
      |>.set (UInt256.ofNat 0x20) (UInt256.ofNat 9) }
  let accounts := state.accountMap.set deployAddress account
  { state with
    accountMap := accounts
    substate := { state.substate with originalAccountMap := accounts }
    executionEnv := { state.executionEnv with weiValue := UInt256.ofNat 0x1234 } }

structure Vector where
  label : String
  input : ByteArray

/-- `n` bytes of a fixed, non-repeating pattern. -/
def patterned (n : Nat) : ByteArray := Id.run do
  let mut bs := ByteArray.empty
  for i in [:n] do
    bs := bs.push (UInt8.ofNat ((i * 37 + (i / 251) * 11 + 7) % 256))
  return bs

def repeated (n : Nat) (b : UInt8) : ByteArray := Id.run do
  let mut bs := ByteArray.empty
  for _ in [:n] do
    bs := bs.push b
  return bs

/-- The scored vectors. Lengths sit on the FIPS padding boundaries: `55` is
the largest one-block message, `56` the smallest whose length field spills
into a second block, `64` an exact block; the rest exercise the block loop. -/
def vectors : List Vector :=
  [ { label := "empty", input := ByteArray.empty }
  , { label := "abc", input := "abc".toUTF8 }
  , { label := "1-byte", input := patterned 1 }
  , { label := "31-byte", input := patterned 31 }
  , { label := "32-byte", input := patterned 32 }
  , { label := "54-byte", input := patterned 54 }
  , { label := "55-byte (last one-block)", input := patterned 55 }
  , { label := "56-byte (length spills)", input := patterned 56 }
  , { label := "fips-b2 (56-byte)"
    , input := "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8 }
  , { label := "63-byte", input := patterned 63 }
  , { label := "64-byte (exact block)", input := patterned 64 }
  , { label := "65-byte", input := patterned 65 }
  , { label := "119-byte", input := patterned 119 }
  , { label := "120-byte", input := patterned 120 }
  , { label := "127-byte", input := patterned 127 }
  , { label := "128-byte (two blocks)", input := patterned 128 }
  , { label := "256-byte", input := patterned 256 }
  , { label := "1000-byte", input := patterned 1000 }
  , { label := "1000 a's", input := repeated 1000 0x61 } ]

/-- Two FIPS 180-4 digests, hard-coded so that a scoring run also
re-validates the oracle it scores against. -/
def oracleChecks : List (ByteArray × String) :=
  [ (ByteArray.empty,
     "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
  , ("abc".toUTF8,
     "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad") ]

inductive Outcome where
  | ok (gas : Nat)
  | wrongDigest (got : String) (gas : Nat)
  | badHalt (halt : String) (gas : Nat)
  | outOfFuel

def Outcome.gas? : Outcome → Option Nat
  | .ok gas | .wrongDigest _ gas | .badHalt _ gas => some gas
  | .outOfFuel => none

/-- Run one vector from one initial state and compare with the specification. -/
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

/-- One vector's verdict from both the clean and dirty initial states. -/
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

end Challenge.Sha256.Scorer
