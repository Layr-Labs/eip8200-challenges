import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteTrace0
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteTrace1
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteTrace2
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteTrace3
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByte1High
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByte1Low
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByte2High
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByte2Low
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByte3High
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByte3Low

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteCorrect

open Challenge.EvmProof.Stepper
open EvmSemantics
open EvmSemantics.EVM
open WindowHitByteSlices
open WindowByteKernel
open WindowNibbleKernel

private theorem append5
    {p0 p1 p2 p3 p4 : List (Located Artifact.submissionArtifact .Osaka)}
    {s0 s1 s2 s3 s4 s5 : State}
    (h0 : runLocatedBlock p0 s0 = some s1)
    (h1 : runLocatedBlock p1 s1 = some s2)
    (h2 : runLocatedBlock p2 s2 = some s3)
    (h3 : runLocatedBlock p3 s3 = some s4)
    (h4 : runLocatedBlock p4 s4 = some s5)
    (hr1 : s1.halt = .Running) (hr2 : s2.halt = .Running)
    (hr3 : s3.halt = .Running) (hr4 : s4.halt = .Running) :
    runLocatedBlock (p0 ++ p1 ++ p2 ++ p3 ++ p4) s0 = some s5 := by
  simpa only [List.append_assoc] using
    runLocatedBlock_append p0 (p1 ++ (p2 ++ (p3 ++ p4)))
      s0 s1 s5 h0 hr1
      (runLocatedBlock_append p1 (p2 ++ (p3 ++ p4))
        s1 s2 s5 h1 hr2
        (runLocatedBlock_append p2 (p3 ++ p4) s2 s3 s5 h2 hr3
          (runLocatedBlock_append p3 p4 s3 s4 s5 h3 hr4 h4)))

/-! Opaque composition of the five first-byte artifact segments. -/
theorem run_byte0 (template : State) (base modulus word pointer accumulator : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runLocatedBlock (segmentedBytePath 0)
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3208)
        base modulus word pointer accumulator rest) =
    some (wordKernelState { template with halt := .Running } (UInt256.ofNat 3292)
      base modulus word pointer
      (WindowMath.byteWordStep modulus base accumulator
        (byteValue 0 word).toNat) rest) := by
  let high := highNibble 0 word
  let low := lowNibble 0 word
  let highAcc := WindowMath.nibbleWordStep modulus base accumulator high
  let lowAcc := WindowMath.nibbleWordStep modulus base highAcc low
  have h0 : runLocatedBlock (highPrepPath 0)
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3208)
        base modulus word pointer accumulator rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3215)
        base modulus high (byteValue 0 word) word pointer accumulator rest) := by
    simpa [high] using WindowHitByteTrace0.run_byte0_highPrep template base modulus word
      pointer accumulator rest hrest
  have h1 : runLocatedBlock (highSquareLookupPath 0)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3215)
        base modulus high (byteValue 0 word) word pointer accumulator rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3250)
        base modulus high (byteValue 0 word) word pointer highAcc rest) := by
    simpa [high, highAcc] using WindowHitByteTrace1.run_byte0_highSquareLookup
      template base modulus high (byteValue 0 word) word pointer accumulator rest
      (highNibble_lt 0 word (by decide)) hrest
  have h2 : runLocatedBlock (lowPrepPath 0)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3250)
        base modulus high (byteValue 0 word) word pointer highAcc rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3255)
        base modulus low (byteValue 0 word) word pointer highAcc rest) := by
    simpa [high, low, highAcc] using WindowHitByteTrace3.run_byte0_lowPrep template base
      modulus high word pointer highAcc rest hrest
  have h3 : runLocatedBlock (lowSquareLookupPath 0)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3255)
        base modulus low (byteValue 0 word) word pointer highAcc rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3290)
        base modulus low (byteValue 0 word) word pointer lowAcc rest) := by
    simpa [low, highAcc, lowAcc] using WindowHitByteTrace3.run_byte0_lowSquareLookup
      template base modulus low (byteValue 0 word) word pointer highAcc rest
      (lowNibble_lt 0 word) hrest
  have h4 : runLocatedBlock (finishPath 0)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3290)
        base modulus low (byteValue 0 word) word pointer lowAcc rest) =
      some (wordKernelState { template with halt := .Running } (UInt256.ofNat 3292)
        base modulus word pointer lowAcc rest) := by
    simpa [low, lowAcc] using WindowHitByteTrace3.run_byte0_finish template base modulus
      low (byteValue 0 word) word pointer lowAcc rest hrest
  have hall := append5 h0 h1 h2 h3 h4 rfl rfl rfl rfl
  simpa [segmentedBytePath, high, low, highAcc, lowAcc, WindowMath.byteWordStep,
    WindowMath.nibbleWordStep, highNibble, lowNibble] using hall

theorem run_byte1 (template : State) (base modulus word pointer accumulator : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runLocatedBlock (segmentedBytePath 1)
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3292)
        base modulus word pointer accumulator rest) =
    some (wordKernelState { template with halt := .Running } (UInt256.ofNat 3377)
      base modulus word pointer
      (WindowMath.byteWordStep modulus base accumulator
        (byteValue 1 word).toNat) rest) := by
  let high := highNibble 1 word
  let low := lowNibble 1 word
  let highAcc := WindowMath.nibbleWordStep modulus base accumulator high
  let lowAcc := WindowMath.nibbleWordStep modulus base highAcc low
  have h0 : runLocatedBlock (highPrepPath 1)
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3292)
        base modulus word pointer accumulator rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3300)
        base modulus high (byteValue 1 word) word pointer accumulator rest) := by
    simpa [high] using WindowHitByte1High.run_prep template base modulus word
      pointer accumulator rest hrest
  have h1 : runLocatedBlock (highSquareLookupPath 1)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3300)
        base modulus high (byteValue 1 word) word pointer accumulator rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3335)
        base modulus high (byteValue 1 word) word pointer highAcc rest) := by
    simpa [high, highAcc] using WindowHitByte1High.run_squareLookup template
      base modulus high (byteValue 1 word) word pointer accumulator rest
      (highNibble_lt 1 word (by decide)) hrest
  have h2 : runLocatedBlock (lowPrepPath 1)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3335)
        base modulus high (byteValue 1 word) word pointer highAcc rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3340)
        base modulus low (byteValue 1 word) word pointer highAcc rest) := by
    simpa [high, low, highAcc] using WindowHitByte1Low.run_prep template base
      modulus high word pointer highAcc rest hrest
  have h3 : runLocatedBlock (lowSquareLookupPath 1)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3340)
        base modulus low (byteValue 1 word) word pointer highAcc rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3375)
        base modulus low (byteValue 1 word) word pointer lowAcc rest) := by
    simpa [low, highAcc, lowAcc] using WindowHitByte1Low.run_squareLookup template
      base modulus low (byteValue 1 word) word pointer highAcc rest
      (lowNibble_lt 1 word) hrest
  have h4 : runLocatedBlock (finishPath 1)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3375)
        base modulus low (byteValue 1 word) word pointer lowAcc rest) =
      some (wordKernelState { template with halt := .Running } (UInt256.ofNat 3377)
        base modulus word pointer lowAcc rest) := by
    simpa [low, lowAcc] using WindowHitByte1Low.run_finish template base modulus
      low (byteValue 1 word) word pointer lowAcc rest hrest
  have hall := append5 h0 h1 h2 h3 h4 rfl rfl rfl rfl
  simpa [segmentedBytePath, high, low, highAcc, lowAcc, WindowMath.byteWordStep,
    WindowMath.nibbleWordStep, highNibble, lowNibble] using hall

theorem run_byte2 (template : State) (base modulus word pointer accumulator : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runLocatedBlock (segmentedBytePath 2)
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3377)
        base modulus word pointer accumulator rest) =
    some (wordKernelState { template with halt := .Running } (UInt256.ofNat 3462)
      base modulus word pointer
      (WindowMath.byteWordStep modulus base accumulator
        (byteValue 2 word).toNat) rest) := by
  let high := highNibble 2 word
  let low := lowNibble 2 word
  let highAcc := WindowMath.nibbleWordStep modulus base accumulator high
  let lowAcc := WindowMath.nibbleWordStep modulus base highAcc low
  have h0 : runLocatedBlock (highPrepPath 2)
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3377)
        base modulus word pointer accumulator rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3385)
        base modulus high (byteValue 2 word) word pointer accumulator rest) := by
    simpa [high] using WindowHitByte2High.run_prep template base modulus word
      pointer accumulator rest hrest
  have h1 : runLocatedBlock (highSquareLookupPath 2)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3385)
        base modulus high (byteValue 2 word) word pointer accumulator rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3420)
        base modulus high (byteValue 2 word) word pointer highAcc rest) := by
    simpa [high, highAcc] using WindowHitByte2High.run_squareLookup template
      base modulus high (byteValue 2 word) word pointer accumulator rest
      (highNibble_lt 2 word (by decide)) hrest
  have h2 : runLocatedBlock (lowPrepPath 2)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3420)
        base modulus high (byteValue 2 word) word pointer highAcc rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3425)
        base modulus low (byteValue 2 word) word pointer highAcc rest) := by
    simpa [high, low, highAcc] using WindowHitByte2Low.run_prep template base
      modulus high word pointer highAcc rest hrest
  have h3 : runLocatedBlock (lowSquareLookupPath 2)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3425)
        base modulus low (byteValue 2 word) word pointer highAcc rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3460)
        base modulus low (byteValue 2 word) word pointer lowAcc rest) := by
    simpa [low, highAcc, lowAcc] using WindowHitByte2Low.run_squareLookup template
      base modulus low (byteValue 2 word) word pointer highAcc rest
      (lowNibble_lt 2 word) hrest
  have h4 : runLocatedBlock (finishPath 2)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3460)
        base modulus low (byteValue 2 word) word pointer lowAcc rest) =
      some (wordKernelState { template with halt := .Running } (UInt256.ofNat 3462)
        base modulus word pointer lowAcc rest) := by
    simpa [low, lowAcc] using WindowHitByte2Low.run_finish template base modulus
      low (byteValue 2 word) word pointer lowAcc rest hrest
  have hall := append5 h0 h1 h2 h3 h4 rfl rfl rfl rfl
  simpa [segmentedBytePath, high, low, highAcc, lowAcc, WindowMath.byteWordStep,
    WindowMath.nibbleWordStep, highNibble, lowNibble] using hall

theorem run_byte3 (template : State) (base modulus word pointer accumulator : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runLocatedBlock (segmentedBytePath 3)
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3462)
        base modulus word pointer accumulator rest) =
    some (wordKernelState { template with halt := .Running } (UInt256.ofNat 3547)
      base modulus word pointer
      (WindowMath.byteWordStep modulus base accumulator
        (byteValue 3 word).toNat) rest) := by
  let high := highNibble 3 word
  let low := lowNibble 3 word
  let highAcc := WindowMath.nibbleWordStep modulus base accumulator high
  let lowAcc := WindowMath.nibbleWordStep modulus base highAcc low
  have h0 : runLocatedBlock (highPrepPath 3)
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3462)
        base modulus word pointer accumulator rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3470)
        base modulus high (byteValue 3 word) word pointer accumulator rest) := by
    simpa [high] using WindowHitByte3High.run_prep template base modulus word
      pointer accumulator rest hrest
  have h1 : runLocatedBlock (highSquareLookupPath 3)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3470)
        base modulus high (byteValue 3 word) word pointer accumulator rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3505)
        base modulus high (byteValue 3 word) word pointer highAcc rest) := by
    simpa [high, highAcc] using WindowHitByte3High.run_squareLookup template
      base modulus high (byteValue 3 word) word pointer accumulator rest
      (highNibble_lt 3 word (by decide)) hrest
  have h2 : runLocatedBlock (lowPrepPath 3)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3505)
        base modulus high (byteValue 3 word) word pointer highAcc rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3510)
        base modulus low (byteValue 3 word) word pointer highAcc rest) := by
    simpa [high, low, highAcc] using WindowHitByte3Low.run_prep template base
      modulus high word pointer highAcc rest hrest
  have h3 : runLocatedBlock (lowSquareLookupPath 3)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3510)
        base modulus low (byteValue 3 word) word pointer highAcc rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3545)
        base modulus low (byteValue 3 word) word pointer lowAcc rest) := by
    simpa [low, highAcc, lowAcc] using WindowHitByte3Low.run_squareLookup template
      base modulus low (byteValue 3 word) word pointer highAcc rest
      (lowNibble_lt 3 word) hrest
  have h4 : runLocatedBlock (finishPath 3)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3545)
        base modulus low (byteValue 3 word) word pointer lowAcc rest) =
      some (wordKernelState { template with halt := .Running } (UInt256.ofNat 3547)
        base modulus word pointer lowAcc rest) := by
    simpa [low, lowAcc] using WindowHitByte3Low.run_finish template base modulus
      low (byteValue 3 word) word pointer lowAcc rest hrest
  have hall := append5 h0 h1 h2 h3 h4 rfl rfl rfl rfl
  simpa [segmentedBytePath, high, low, highAcc, lowAcc, WindowMath.byteWordStep,
    WindowMath.nibbleWordStep, highNibble, lowNibble] using hall

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteCorrect
