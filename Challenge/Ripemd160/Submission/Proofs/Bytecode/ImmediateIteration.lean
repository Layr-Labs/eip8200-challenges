import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateWrapper
import EvmSemantics.Crypto.Ripemd160

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateIteration

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateWrapper

/-- Width of a zero-or-one-byte immediate used by the generated wrappers. -/
def zeroOrOneWidth (n : Nat) : Fin 33 :=
  if n = 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩

def constantWidth (n : Nat) : Fin 33 :=
  if n = 0 then ⟨0, by decide⟩ else ⟨4, by decide⟩

def baseWidth (n : Nat) : Fin 33 :=
  if n = 0x160 then ⟨2, by decide⟩ else ⟨1, by decide⟩

/-- Build an H09 immediate wrapper descriptor from natural constants.
Return labels are PUSH2, non-zero RIPEMD constants are PUSH4, rotations are
PUSH1, and the two lane bases use PUSH1/PUSH2 respectively. -/
def mkImmediateSite (start ret k rotation wordIndex j base : Nat) : WrapperSite :=
  { startIndex := start
    retW := ⟨2, by decide⟩
    ret := UInt256.ofNat ret
    kW := constantWidth k
    k := UInt256.ofNat k
    rotW := ⟨1, by decide⟩
    rotation := UInt256.ofNat rotation
    wiW := zeroOrOneWidth wordIndex
    wordIndex := UInt256.ofNat wordIndex
    jW := zeroOrOneWidth j
    j := UInt256.ofNat j
    baseW := baseWidth base
    base := UInt256.ofNat base }

def instructionMatches (actual expected : YulEvmCompiler.Instr) : Bool :=
  match actual, expected with
  | .push width value, .push expectedWidth expectedValue =>
      decide (width = expectedWidth ∧ value.toNat = expectedValue.toNat)
  | .op op, .op expectedOp => decide (op = expectedOp)
  | _, _ => false

def instructionMatchesAt (index : Nat) (expected : YulEvmCompiler.Instr) : Bool :=
  match Artifact.submissionArtifact.instructions[index]? with
  | some actual => instructionMatches actual expected
  | none => false

/-- Boolean code certificate for the eight-instruction wrapper shape. -/
def wrapperCodeMatches (site : WrapperSite) : Bool :=
  instructionMatchesAt site.startIndex (.push site.retW site.ret) &&
  instructionMatchesAt (site.startIndex + 1) (.push site.kW site.k) &&
  instructionMatchesAt (site.startIndex + 2) (.push site.rotW site.rotation) &&
  instructionMatchesAt (site.startIndex + 3) (.push site.wiW site.wordIndex) &&
  instructionMatchesAt (site.startIndex + 4) (.push site.jW site.j) &&
  instructionMatchesAt (site.startIndex + 5) (.push site.baseW site.base) &&
  instructionMatchesAt (site.startIndex + 6)
    (.push ⟨2, by decide⟩ (UInt256.ofNat 0x114)) &&
  instructionMatchesAt (site.startIndex + 7) (.op .JUMP)

def leftConstant (i : Nat) : Nat :=
  [0, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e][i]!

def rightConstant (i : Nat) : Nat :=
  [0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0][i]!

def leftSite (i : Nat) : WrapperSite :=
  mkImmediateSite
    (997 + 9 * i)
    (Artifact.submissionArtifact.instructionPC (997 + 9 * i + 8))
    (leftConstant (i / 16))
    EvmSemantics.Crypto.Ripemd160.s[i]!
    EvmSemantics.Crypto.Ripemd160.r[i]!
    (i / 16) 0xc0

def rightSite (i : Nat) : WrapperSite :=
  let start := if i = 79 then 2429 else 1717 + 9 * i
  let ret := if i = 79 then 0x324 else
    Artifact.submissionArtifact.instructionPC (start + 8)
  mkImmediateSite start ret
    (rightConstant (i / 16))
    EvmSemantics.Crypto.Ripemd160.sP[i]!
    EvmSemantics.Crypto.Ripemd160.rP[i]!
    (4 - i / 16) 0x160

def leftSites : List WrapperSite := (List.range 80).map leftSite

def rightSites : List WrapperSite := (List.range 80).map rightSite

def immediateSites : List WrapperSite := leftSites ++ rightSites

def leftSiteChunk (chunk : Nat) : List WrapperSite :=
  (List.range 16).map (fun offset => leftSite (16 * chunk + offset))

def rightSiteChunk (chunk : Nat) : List WrapperSite :=
  (List.range 16).map (fun offset => rightSite (16 * chunk + offset))

def immediateSiteChunks : List (List WrapperSite) :=
  (List.range 5).map leftSiteChunk ++ (List.range 5).map rightSiteChunk

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateIteration
