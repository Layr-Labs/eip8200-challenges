import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareSteps

noncomputable section
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace CycleSubmission.Global.Fast.TnM128SquareExit
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore

/-- Eight-limb kernel exit: carry reset, row pointer `+ 0x100`, `PUSH2 5062`, then falls into the
eight-limb counter `pcC` (no `JUMPDEST`). -/
def pcM4j : Nat := 3482
/-- Eight-limb CSUB return: the next square's row-0 head. -/

def frameStack (tn m128 : UInt256) (_n : Nat)
    (pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [pbi, UInt256.ofNat 5297, w3, ent, m32, allOnes,
   m128, m64, m0, tl, m96, inv, tn,
   aprev, pdst, ret] ++ rest


def frameAt (tn m128 : UInt256) (pc : Nat) (s : State) (mem : ByteArray) (n : Nat)
    (pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : State :=
  framed {s with memory := mem} (UInt256.ofNat pc)
    (frameStack tn m128 n pbi w3 ent tl inv m0 m96 m64 m32 aprev pdst ret rest)

/-- The square counter lives in the frame's `pdst` slot (dead during the square loop; pc 3471
overwrites it).  With `[r, frame]` on the stack the block reads `pdst` (`DUP16`), stores
`pdst - 1` back (`DUP8` is `allOnes`, `SWAP16`), and calls the CSUB guard with `[2368, r]`
when the old value is nonzero. -/

def m4jProgram : List Instr :=
  [.op .JUMPDEST, .push 2 3256, .push 2 2368, .push 2 3697, .op .JUMP]


def m4jBlock : Block CycleSubmission.Artifact.artifact .Osaka 3482 m4jProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2698 5 3482 m4jProgram
    (by decide) (by rfl) (by rfl) (by decide)


theorem jumpDestM4j : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3482 = true :=
  CycleSubmission.Global.Binding.jumpDest 2698 (by rfl)


theorem jumpDestLazy : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3697 = true :=
  CycleSubmission.Global.Binding.jumpDest 2851 (by rfl)


end CycleSubmission.Global.Fast.TnM128SquareExit
