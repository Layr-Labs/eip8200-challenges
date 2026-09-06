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

private theorem append7
    {p0 p1 p2 p3 p4 p5 p6 : List (Located Artifact.submissionArtifact .Osaka)}
    {s0 s1 s2 s3 s4 s5 s6 s7 : State}
    (h0 : runLocatedBlock p0 s0 = some s1)
    (h1 : runLocatedBlock p1 s1 = some s2)
    (h2 : runLocatedBlock p2 s2 = some s3)
    (h3 : runLocatedBlock p3 s3 = some s4)
    (h4 : runLocatedBlock p4 s4 = some s5)
    (h5 : runLocatedBlock p5 s5 = some s6)
    (h6 : runLocatedBlock p6 s6 = some s7)
    (hr1 : s1.halt = .Running) (hr2 : s2.halt = .Running)
    (hr3 : s3.halt = .Running) (hr4 : s4.halt = .Running)
    (hr5 : s5.halt = .Running) (hr6 : s6.halt = .Running) :
    runLocatedBlock (p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6) s0 = some s7 := by
  simpa only [List.append_assoc] using
    runLocatedBlock_append p0 (p1 ++ (p2 ++ (p3 ++ (p4 ++ (p5 ++ p6)))))
      s0 s1 s7 h0 hr1
      (runLocatedBlock_append p1 (p2 ++ (p3 ++ (p4 ++ (p5 ++ p6))))
        s1 s2 s7 h1 hr2
        (runLocatedBlock_append p2 (p3 ++ (p4 ++ (p5 ++ p6))) s2 s3 s7 h2 hr3
          (runLocatedBlock_append p3 (p4 ++ (p5 ++ p6)) s3 s4 s7 h3 hr4
            (runLocatedBlock_append p4 (p5 ++ p6) s4 s5 s7 h4 hr5
              (runLocatedBlock_append p5 p6 s5 s6 s7 h5 hr6 h6)))))

/-! Opaque composition of the seven first-byte artifact segments. -/
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
  let highSquared := WindowMath.squareWordAfter modulus 4 accumulator
  let highAcc := UInt256.mulMod highSquared
    (WindowMath.tableWord base modulus high) modulus
  let lowSquared := WindowMath.squareWordAfter modulus 4 highAcc
  let lowAcc := UInt256.mulMod lowSquared
    (WindowMath.tableWord base modulus low) modulus
  have h0 := WindowHitByteTrace0.run_byte0_highPrep template base modulus word
    pointer accumulator rest hrest
  have h1 := WindowHitByteTrace1.run_byte0_highSquare template base modulus high
    (byteValue 0 word) word pointer accumulator rest hrest
  have h2 := WindowHitByteTrace2.run_byte0_highLookup template base modulus high
    (byteValue 0 word) word pointer highSquared rest (highNibble_lt 0 word (by decide))
    hrest
  have h3 := WindowHitByteTrace3.run_byte0_lowPrep template base modulus high word
    pointer highAcc rest hrest
  have h4 := WindowHitByteTrace3.run_byte0_lowSquare template base modulus low
    (byteValue 0 word) word pointer highAcc rest hrest
  have h5 := WindowHitByteTrace3.run_byte0_lowLookup template base modulus low
    (byteValue 0 word) word pointer lowSquared rest (lowNibble_lt 0 word) hrest
  have h6 := WindowHitByteTrace3.run_byte0_finish template base modulus low
    (byteValue 0 word) word pointer lowAcc rest hrest
  have h56 := runLocatedBlock_append (lowLookupPath 0) (finishPath 0)
    (nibbleState { template with halt := .Running } (UInt256.ofNat 3279)
      base modulus low (byteValue 0 word) word pointer lowSquared rest)
    (nibbleState { template with halt := .Running } (UInt256.ofNat 3290)
      base modulus low (byteValue 0 word) word pointer lowAcc rest)
    (wordKernelState { template with halt := .Running } (UInt256.ofNat 3292)
      base modulus word pointer lowAcc rest)
    (by simpa [low, lowSquared, lowAcc] using h5) rfl
    (by simpa [low, lowAcc] using h6)
  have h456 := runLocatedBlock_append (lowSquarePath 0)
    (lowLookupPath 0 ++ finishPath 0)
    (nibbleState { template with halt := .Running } (UInt256.ofNat 3255)
      base modulus low (byteValue 0 word) word pointer highAcc rest)
    (nibbleState { template with halt := .Running } (UInt256.ofNat 3279)
      base modulus low (byteValue 0 word) word pointer lowSquared rest)
    (wordKernelState { template with halt := .Running } (UInt256.ofNat 3292)
      base modulus word pointer lowAcc rest)
    (by simpa [low, highAcc, lowSquared] using h4) rfl h56
  have h3456 := runLocatedBlock_append (lowPrepPath 0)
    (lowSquarePath 0 ++ lowLookupPath 0 ++ finishPath 0)
    (nibbleState { template with halt := .Running } (UInt256.ofNat 3250)
      base modulus high (byteValue 0 word) word pointer highAcc rest)
    (nibbleState { template with halt := .Running } (UInt256.ofNat 3255)
      base modulus low (byteValue 0 word) word pointer highAcc rest)
    (wordKernelState { template with halt := .Running } (UInt256.ofNat 3292)
      base modulus word pointer lowAcc rest)
    (by simpa [high, low, highAcc] using h3) rfl h456
  have h23456 := runLocatedBlock_append (highLookupPath 0)
    (lowPrepPath 0 ++ lowSquarePath 0 ++ lowLookupPath 0 ++ finishPath 0)
    (nibbleState { template with halt := .Running } (UInt256.ofNat 3239)
      base modulus high (byteValue 0 word) word pointer highSquared rest)
    (nibbleState { template with halt := .Running } (UInt256.ofNat 3250)
      base modulus high (byteValue 0 word) word pointer highAcc rest)
    (wordKernelState { template with halt := .Running } (UInt256.ofNat 3292)
      base modulus word pointer lowAcc rest)
    (by simpa [high, highSquared, highAcc] using h2) rfl h3456
  have h123456 := runLocatedBlock_append (highSquarePath 0)
    (highLookupPath 0 ++ lowPrepPath 0 ++ lowSquarePath 0 ++
      lowLookupPath 0 ++ finishPath 0)
    (nibbleState { template with halt := .Running } (UInt256.ofNat 3215)
      base modulus high (byteValue 0 word) word pointer accumulator rest)
    (nibbleState { template with halt := .Running } (UInt256.ofNat 3239)
      base modulus high (byteValue 0 word) word pointer highSquared rest)
    (wordKernelState { template with halt := .Running } (UInt256.ofNat 3292)
      base modulus word pointer lowAcc rest)
    (by simpa [high, highSquared] using h1) rfl h23456
  have hall := runLocatedBlock_append (highPrepPath 0)
    (highSquarePath 0 ++ highLookupPath 0 ++ lowPrepPath 0 ++
      lowSquarePath 0 ++ lowLookupPath 0 ++ finishPath 0)
    (wordKernelState { template with halt := .Running } (UInt256.ofNat 3208)
      base modulus word pointer accumulator rest)
    (nibbleState { template with halt := .Running } (UInt256.ofNat 3215)
      base modulus high (byteValue 0 word) word pointer accumulator rest)
    (wordKernelState { template with halt := .Running } (UInt256.ofNat 3292)
      base modulus word pointer lowAcc rest)
    (by simpa [high] using h0) rfl h123456
  simpa [segmentedBytePath, high, low, highSquared, highAcc, lowSquared,
    lowAcc, WindowMath.byteWordStep, WindowMath.nibbleWordStep,
    highNibble, lowNibble] using hall

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
  let highSquared := WindowMath.squareWordAfter modulus 4 accumulator
  let highAcc := UInt256.mulMod highSquared
    (WindowMath.tableWord base modulus high) modulus
  let lowSquared := WindowMath.squareWordAfter modulus 4 highAcc
  let lowAcc := UInt256.mulMod lowSquared
    (WindowMath.tableWord base modulus low) modulus
  have h0 : runLocatedBlock (highPrepPath 1)
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3292)
        base modulus word pointer accumulator rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3300)
        base modulus high (byteValue 1 word) word pointer accumulator rest) := by
    simpa [high] using WindowHitByte1High.run_prep template base modulus word
      pointer accumulator rest hrest
  have h1 : runLocatedBlock (highSquarePath 1)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3300)
        base modulus high (byteValue 1 word) word pointer accumulator rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3324)
        base modulus high (byteValue 1 word) word pointer highSquared rest) := by
    simpa [high, highSquared] using WindowHitByte1High.run_square template
      base modulus high (byteValue 1 word) word pointer accumulator rest hrest
  have h2 : runLocatedBlock (highLookupPath 1)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3324)
        base modulus high (byteValue 1 word) word pointer highSquared rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3335)
        base modulus high (byteValue 1 word) word pointer highAcc rest) := by
    simpa [high, highSquared, highAcc] using WindowHitByte1High.run_lookup
      template base modulus high (byteValue 1 word) word pointer highSquared rest
      (highNibble_lt 1 word (by decide)) hrest
  have h3 : runLocatedBlock (lowPrepPath 1)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3335)
        base modulus high (byteValue 1 word) word pointer highAcc rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3340)
        base modulus low (byteValue 1 word) word pointer highAcc rest) := by
    simpa [high, low, highAcc] using WindowHitByte1Low.run_prep template base
      modulus high word pointer highAcc rest hrest
  have h4 : runLocatedBlock (lowSquarePath 1)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3340)
        base modulus low (byteValue 1 word) word pointer highAcc rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3364)
        base modulus low (byteValue 1 word) word pointer lowSquared rest) := by
    simpa [low, highAcc, lowSquared] using WindowHitByte1Low.run_square template
      base modulus low (byteValue 1 word) word pointer highAcc rest hrest
  have h5 : runLocatedBlock (lowLookupPath 1)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3364)
        base modulus low (byteValue 1 word) word pointer lowSquared rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3375)
        base modulus low (byteValue 1 word) word pointer lowAcc rest) := by
    simpa [low, lowSquared, lowAcc] using WindowHitByte1Low.run_lookup template
      base modulus low (byteValue 1 word) word pointer lowSquared rest
      (lowNibble_lt 1 word) hrest
  have h6 : runLocatedBlock (finishPath 1)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3375)
        base modulus low (byteValue 1 word) word pointer lowAcc rest) =
      some (wordKernelState { template with halt := .Running } (UInt256.ofNat 3377)
        base modulus word pointer lowAcc rest) := by
    simpa [low, lowAcc] using WindowHitByte1Low.run_finish template base modulus
      low (byteValue 1 word) word pointer lowAcc rest hrest
  have hall := append7 h0 h1 h2 h3 h4 h5 h6 rfl rfl rfl rfl rfl rfl
  simpa [segmentedBytePath, high, low, highSquared, highAcc, lowSquared,
    lowAcc, WindowMath.byteWordStep, WindowMath.nibbleWordStep,
    highNibble, lowNibble] using hall

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
  let highSquared := WindowMath.squareWordAfter modulus 4 accumulator
  let highAcc := UInt256.mulMod highSquared
    (WindowMath.tableWord base modulus high) modulus
  let lowSquared := WindowMath.squareWordAfter modulus 4 highAcc
  let lowAcc := UInt256.mulMod lowSquared
    (WindowMath.tableWord base modulus low) modulus
  have h0 : runLocatedBlock (highPrepPath 2)
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3377)
        base modulus word pointer accumulator rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3385)
        base modulus high (byteValue 2 word) word pointer accumulator rest) := by
    simpa [high] using WindowHitByte2High.run_prep template base modulus word
      pointer accumulator rest hrest
  have h1 : runLocatedBlock (highSquarePath 2)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3385)
        base modulus high (byteValue 2 word) word pointer accumulator rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3409)
        base modulus high (byteValue 2 word) word pointer highSquared rest) := by
    simpa [high, highSquared] using WindowHitByte2High.run_square template
      base modulus high (byteValue 2 word) word pointer accumulator rest hrest
  have h2 : runLocatedBlock (highLookupPath 2)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3409)
        base modulus high (byteValue 2 word) word pointer highSquared rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3420)
        base modulus high (byteValue 2 word) word pointer highAcc rest) := by
    simpa [high, highSquared, highAcc] using WindowHitByte2High.run_lookup
      template base modulus high (byteValue 2 word) word pointer highSquared rest
      (highNibble_lt 2 word (by decide)) hrest
  have h3 : runLocatedBlock (lowPrepPath 2)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3420)
        base modulus high (byteValue 2 word) word pointer highAcc rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3425)
        base modulus low (byteValue 2 word) word pointer highAcc rest) := by
    simpa [high, low, highAcc] using WindowHitByte2Low.run_prep template base
      modulus high word pointer highAcc rest hrest
  have h4 : runLocatedBlock (lowSquarePath 2)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3425)
        base modulus low (byteValue 2 word) word pointer highAcc rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3449)
        base modulus low (byteValue 2 word) word pointer lowSquared rest) := by
    simpa [low, highAcc, lowSquared] using WindowHitByte2Low.run_square template
      base modulus low (byteValue 2 word) word pointer highAcc rest hrest
  have h5 : runLocatedBlock (lowLookupPath 2)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3449)
        base modulus low (byteValue 2 word) word pointer lowSquared rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3460)
        base modulus low (byteValue 2 word) word pointer lowAcc rest) := by
    simpa [low, lowSquared, lowAcc] using WindowHitByte2Low.run_lookup template
      base modulus low (byteValue 2 word) word pointer lowSquared rest
      (lowNibble_lt 2 word) hrest
  have h6 : runLocatedBlock (finishPath 2)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3460)
        base modulus low (byteValue 2 word) word pointer lowAcc rest) =
      some (wordKernelState { template with halt := .Running } (UInt256.ofNat 3462)
        base modulus word pointer lowAcc rest) := by
    simpa [low, lowAcc] using WindowHitByte2Low.run_finish template base modulus
      low (byteValue 2 word) word pointer lowAcc rest hrest
  have hall := append7 h0 h1 h2 h3 h4 h5 h6 rfl rfl rfl rfl rfl rfl
  simpa [segmentedBytePath, high, low, highSquared, highAcc, lowSquared,
    lowAcc, WindowMath.byteWordStep, WindowMath.nibbleWordStep,
    highNibble, lowNibble] using hall

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
  let highSquared := WindowMath.squareWordAfter modulus 4 accumulator
  let highAcc := UInt256.mulMod highSquared
    (WindowMath.tableWord base modulus high) modulus
  let lowSquared := WindowMath.squareWordAfter modulus 4 highAcc
  let lowAcc := UInt256.mulMod lowSquared
    (WindowMath.tableWord base modulus low) modulus
  have h0 : runLocatedBlock (highPrepPath 3)
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3462)
        base modulus word pointer accumulator rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3470)
        base modulus high (byteValue 3 word) word pointer accumulator rest) := by
    simpa [high] using WindowHitByte3High.run_prep template base modulus word
      pointer accumulator rest hrest
  have h1 : runLocatedBlock (highSquarePath 3)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3470)
        base modulus high (byteValue 3 word) word pointer accumulator rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3494)
        base modulus high (byteValue 3 word) word pointer highSquared rest) := by
    simpa [high, highSquared] using WindowHitByte3High.run_square template
      base modulus high (byteValue 3 word) word pointer accumulator rest hrest
  have h2 : runLocatedBlock (highLookupPath 3)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3494)
        base modulus high (byteValue 3 word) word pointer highSquared rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3505)
        base modulus high (byteValue 3 word) word pointer highAcc rest) := by
    simpa [high, highSquared, highAcc] using WindowHitByte3High.run_lookup
      template base modulus high (byteValue 3 word) word pointer highSquared rest
      (highNibble_lt 3 word (by decide)) hrest
  have h3 : runLocatedBlock (lowPrepPath 3)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3505)
        base modulus high (byteValue 3 word) word pointer highAcc rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3510)
        base modulus low (byteValue 3 word) word pointer highAcc rest) := by
    simpa [high, low, highAcc] using WindowHitByte3Low.run_prep template base
      modulus high word pointer highAcc rest hrest
  have h4 : runLocatedBlock (lowSquarePath 3)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3510)
        base modulus low (byteValue 3 word) word pointer highAcc rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3534)
        base modulus low (byteValue 3 word) word pointer lowSquared rest) := by
    simpa [low, highAcc, lowSquared] using WindowHitByte3Low.run_square template
      base modulus low (byteValue 3 word) word pointer highAcc rest hrest
  have h5 : runLocatedBlock (lowLookupPath 3)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3534)
        base modulus low (byteValue 3 word) word pointer lowSquared rest) =
      some (nibbleState { template with halt := .Running } (UInt256.ofNat 3545)
        base modulus low (byteValue 3 word) word pointer lowAcc rest) := by
    simpa [low, lowSquared, lowAcc] using WindowHitByte3Low.run_lookup template
      base modulus low (byteValue 3 word) word pointer lowSquared rest
      (lowNibble_lt 3 word) hrest
  have h6 : runLocatedBlock (finishPath 3)
      (nibbleState { template with halt := .Running } (UInt256.ofNat 3545)
        base modulus low (byteValue 3 word) word pointer lowAcc rest) =
      some (wordKernelState { template with halt := .Running } (UInt256.ofNat 3547)
        base modulus word pointer lowAcc rest) := by
    simpa [low, lowAcc] using WindowHitByte3Low.run_finish template base modulus
      low (byteValue 3 word) word pointer lowAcc rest hrest
  have hall := append7 h0 h1 h2 h3 h4 h5 h6 rfl rfl rfl rfl rfl rfl
  simpa [segmentedBytePath, high, low, highSquared, highAcc, lowSquared,
    lowAcc, WindowMath.byteWordStep, WindowMath.nibbleWordStep,
    highNibble, lowNibble] using hall

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteCorrect
