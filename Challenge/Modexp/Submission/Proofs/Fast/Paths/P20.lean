import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! Guarded one-byte exponent-two prefix and its Montgomery square. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2081..2097, pc 3288..3311: recognize a one-byte exponent `2`. -/
def blkExp2Guard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2081 .JUMPDEST,
   opAt 2082 (.Dup ⟨4, by decide⟩),
   pushAt 2083 1 1,
   opAt 2084 .EQ,
   pushAt 2085 1 96,
   opAt 2086 (.Dup ⟨5, by decide⟩),
   opAt 2087 .ADD,
   opAt 2088 .CALLDATALOAD,
   pushAt 2089 0 0,
   opAt 2090 .BYTE,
   pushAt 2091 1 2,
   opAt 2092 .EQ,
   opAt 2093 .AND,
   pushAt 2094 2 3312,
   opAt 2095 .JUMPI,
   pushAt 2096 2 1756,
   opAt 2097 .JUMP]

/-- Instructions 2098..2104, pc 3312..3328: `ACC := MonPro(BASE, BASE)`. -/
def blkExp2Square :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2098 .JUMPDEST,
   pushAt 2099 2 3329,
   pushAt 2100 2 2048,
   pushAt 2101 2 2048,
   pushAt 2102 2 1024,
   pushAt 2103 2 1939,
   opAt 2104 .JUMP]

/-! Instructions 2105..2108, pc 3329..3334: enter the existing final conversion. -/
def blkExp2End :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2105 .JUMPDEST,
   pushAt 2106 0 0,
   pushAt 2107 2 1850,
   opAt 2108 .JUMP]

def exp2Outer (n bsize esize msize : Nat) : List UInt256 :=
  [UInt256.ofNat (32 * n), UInt256.ofNat n, UInt256.ofNat bsize,
   UInt256.ofNat esize, UInt256.ofNat msize]

/-- The exponent-two guard entry. -/
def exp2Guard (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3288
           stack := exp2Outer n bsize esize msize
           memory := mem }

/-- The guarded square call entry. -/
def exp2Square (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3312
           stack := exp2Outer n bsize esize msize
           memory := mem }

/-- The final-conversion handoff after the square. -/
def exp2End (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3329
           stack := exp2Outer n bsize esize msize
           memory := mem }

end Challenge.Modexp.Submission.Proofs.Fast
