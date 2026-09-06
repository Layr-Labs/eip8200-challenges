import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Guarded exponent-three prefix and its two Montgomery products. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2081..2097, pc 3288..3311: recognize a one-byte exponent `3`. -/
def blk1846 :
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
   pushAt 2091 1 3,
   opAt 2092 .EQ,
   opAt 2093 .AND,
   pushAt 2094 2 3312,
   opAt 2095 .JUMPI,
   pushAt 2096 2 1756,
   opAt 2097 .JUMP]

/-- Instructions 2098..2104, pc 3312..3328: `ACC := MonPro(BASE, BASE)`. -/
def blk1863 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2098 .JUMPDEST,
   pushAt 2099 2 3329,
   pushAt 2100 2 2048,
   pushAt 2101 2 2048,
   pushAt 2102 2 1024,
   pushAt 2103 2 1939,
   opAt 2104 .JUMP]

/-- Instructions 2105..2111, pc 3329..3345: `ACC := MonPro(ACC, BASE)`. -/
def blk1870 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2105 .JUMPDEST,
   pushAt 2106 2 3346,
   pushAt 2107 2 1024,
   pushAt 2108 2 2048,
   pushAt 2109 2 1024,
   pushAt 2110 2 1939,
   opAt 2111 .JUMP]

/-! Instructions 2112..2115, pc 3346..3351: enter the existing final conversion. -/
def blk1877 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2112 .JUMPDEST,
   pushAt 2113 0 0,
   pushAt 2114 2 1850,
   opAt 2115 .JUMP]

/-- The guard entry with the persistent outer frame. -/
def smallExpGuard (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3288
           stack := outer n bsize esize msize
           memory := mem }

/-- The square call entry. -/
def smallExpSquare (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3312
           stack := outer n bsize esize msize
           memory := mem }

/-- The multiply call entry. -/
def smallExpMul (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3329
           stack := outer n bsize esize msize
           memory := mem }

/-- The final-conversion handoff. -/
def smallExpEnd (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3346
           stack := outer n bsize esize msize
           memory := mem }

end Challenge.Modexp.Submission.Proofs.Fast
