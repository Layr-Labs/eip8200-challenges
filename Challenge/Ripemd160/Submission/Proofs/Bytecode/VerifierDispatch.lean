import Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierFinish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierLogic

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-!
# Verifier dispatch: the stub's size classifier

After the `POP` at pc 99 the stack is empty.  The dispatch chain at pcs 100-225
checks `CALLDATASIZE` against each of the fourteen patterned sizes; the matching
`JUMPI` jumps to that size's verifier.  Every input that reaches the stub has a
size in the fourteen-set, so the fallthrough past the last `JUMPI` is
unreachable.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierDispatch

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar PatternedScanState PatternedScanTrace
open VerifierData VerifierRun VerifierFinish VerifierLogic

def dispatchPath1 : List Located :=
[
    opAt 61 .CALLDATASIZE,
    pushAt 62 2 1,
    opAt 63 .EQ,
    pushAt 64 2 5209,
    opAt 65 .JUMPI
  ]

def dispatchPath31 : List Located :=
[
    opAt 61 .CALLDATASIZE,
    pushAt 62 2 1,
    opAt 63 .EQ,
    pushAt 64 2 5209,
    opAt 65 .JUMPI,
    opAt 66 .CALLDATASIZE,
    pushAt 67 2 31,
    opAt 68 .EQ,
    pushAt 69 2 5257,
    opAt 70 .JUMPI
  ]

def dispatchPath32 : List Located :=
[
    opAt 61 .CALLDATASIZE,
    pushAt 62 2 1,
    opAt 63 .EQ,
    pushAt 64 2 5209,
    opAt 65 .JUMPI,
    opAt 66 .CALLDATASIZE,
    pushAt 67 2 31,
    opAt 68 .EQ,
    pushAt 69 2 5257,
    opAt 70 .JUMPI,
    opAt 71 .CALLDATASIZE,
    pushAt 72 2 32,
    opAt 73 .EQ,
    pushAt 74 2 5305,
    opAt 75 .JUMPI
  ]

def dispatchPath55 : List Located :=
[
    opAt 61 .CALLDATASIZE,
    pushAt 62 2 1,
    opAt 63 .EQ,
    pushAt 64 2 5209,
    opAt 65 .JUMPI,
    opAt 66 .CALLDATASIZE,
    pushAt 67 2 31,
    opAt 68 .EQ,
    pushAt 69 2 5257,
    opAt 70 .JUMPI,
    opAt 71 .CALLDATASIZE,
    pushAt 72 2 32,
    opAt 73 .EQ,
    pushAt 74 2 5305,
    opAt 75 .JUMPI,
    opAt 76 .CALLDATASIZE,
    pushAt 77 2 55,
    opAt 78 .EQ,
    pushAt 79 2 5353,
    opAt 80 .JUMPI
  ]

def dispatchPath56 : List Located :=
[
    opAt 61 .CALLDATASIZE,
    pushAt 62 2 1,
    opAt 63 .EQ,
    pushAt 64 2 5209,
    opAt 65 .JUMPI,
    opAt 66 .CALLDATASIZE,
    pushAt 67 2 31,
    opAt 68 .EQ,
    pushAt 69 2 5257,
    opAt 70 .JUMPI,
    opAt 71 .CALLDATASIZE,
    pushAt 72 2 32,
    opAt 73 .EQ,
    pushAt 74 2 5305,
    opAt 75 .JUMPI,
    opAt 76 .CALLDATASIZE,
    pushAt 77 2 55,
    opAt 78 .EQ,
    pushAt 79 2 5353,
    opAt 80 .JUMPI,
    opAt 81 .CALLDATASIZE,
    pushAt 82 2 56,
    opAt 83 .EQ,
    pushAt 84 2 5439,
    opAt 85 .JUMPI
  ]

def dispatchPath63 : List Located :=
[
    opAt 61 .CALLDATASIZE,
    pushAt 62 2 1,
    opAt 63 .EQ,
    pushAt 64 2 5209,
    opAt 65 .JUMPI,
    opAt 66 .CALLDATASIZE,
    pushAt 67 2 31,
    opAt 68 .EQ,
    pushAt 69 2 5257,
    opAt 70 .JUMPI,
    opAt 71 .CALLDATASIZE,
    pushAt 72 2 32,
    opAt 73 .EQ,
    pushAt 74 2 5305,
    opAt 75 .JUMPI,
    opAt 76 .CALLDATASIZE,
    pushAt 77 2 55,
    opAt 78 .EQ,
    pushAt 79 2 5353,
    opAt 80 .JUMPI,
    opAt 81 .CALLDATASIZE,
    pushAt 82 2 56,
    opAt 83 .EQ,
    pushAt 84 2 5439,
    opAt 85 .JUMPI,
    opAt 86 .CALLDATASIZE,
    pushAt 87 2 63,
    opAt 88 .EQ,
    pushAt 89 2 5525,
    opAt 90 .JUMPI
  ]

def dispatchPath64 : List Located :=
[
    opAt 61 .CALLDATASIZE,
    pushAt 62 2 1,
    opAt 63 .EQ,
    pushAt 64 2 5209,
    opAt 65 .JUMPI,
    opAt 66 .CALLDATASIZE,
    pushAt 67 2 31,
    opAt 68 .EQ,
    pushAt 69 2 5257,
    opAt 70 .JUMPI,
    opAt 71 .CALLDATASIZE,
    pushAt 72 2 32,
    opAt 73 .EQ,
    pushAt 74 2 5305,
    opAt 75 .JUMPI,
    opAt 76 .CALLDATASIZE,
    pushAt 77 2 55,
    opAt 78 .EQ,
    pushAt 79 2 5353,
    opAt 80 .JUMPI,
    opAt 81 .CALLDATASIZE,
    pushAt 82 2 56,
    opAt 83 .EQ,
    pushAt 84 2 5439,
    opAt 85 .JUMPI,
    opAt 86 .CALLDATASIZE,
    pushAt 87 2 63,
    opAt 88 .EQ,
    pushAt 89 2 5525,
    opAt 90 .JUMPI,
    opAt 91 .CALLDATASIZE,
    pushAt 92 2 64,
    opAt 93 .EQ,
    pushAt 94 2 5611,
    opAt 95 .JUMPI
  ]

def dispatchPath65 : List Located :=
[
    opAt 61 .CALLDATASIZE,
    pushAt 62 2 1,
    opAt 63 .EQ,
    pushAt 64 2 5209,
    opAt 65 .JUMPI,
    opAt 66 .CALLDATASIZE,
    pushAt 67 2 31,
    opAt 68 .EQ,
    pushAt 69 2 5257,
    opAt 70 .JUMPI,
    opAt 71 .CALLDATASIZE,
    pushAt 72 2 32,
    opAt 73 .EQ,
    pushAt 74 2 5305,
    opAt 75 .JUMPI,
    opAt 76 .CALLDATASIZE,
    pushAt 77 2 55,
    opAt 78 .EQ,
    pushAt 79 2 5353,
    opAt 80 .JUMPI,
    opAt 81 .CALLDATASIZE,
    pushAt 82 2 56,
    opAt 83 .EQ,
    pushAt 84 2 5439,
    opAt 85 .JUMPI,
    opAt 86 .CALLDATASIZE,
    pushAt 87 2 63,
    opAt 88 .EQ,
    pushAt 89 2 5525,
    opAt 90 .JUMPI,
    opAt 91 .CALLDATASIZE,
    pushAt 92 2 64,
    opAt 93 .EQ,
    pushAt 94 2 5611,
    opAt 95 .JUMPI,
    opAt 96 .CALLDATASIZE,
    pushAt 97 2 65,
    opAt 98 .EQ,
    pushAt 99 2 5697,
    opAt 100 .JUMPI
  ]

def dispatchPath119 : List Located :=
[
    opAt 61 .CALLDATASIZE,
    pushAt 62 2 1,
    opAt 63 .EQ,
    pushAt 64 2 5209,
    opAt 65 .JUMPI,
    opAt 66 .CALLDATASIZE,
    pushAt 67 2 31,
    opAt 68 .EQ,
    pushAt 69 2 5257,
    opAt 70 .JUMPI,
    opAt 71 .CALLDATASIZE,
    pushAt 72 2 32,
    opAt 73 .EQ,
    pushAt 74 2 5305,
    opAt 75 .JUMPI,
    opAt 76 .CALLDATASIZE,
    pushAt 77 2 55,
    opAt 78 .EQ,
    pushAt 79 2 5353,
    opAt 80 .JUMPI,
    opAt 81 .CALLDATASIZE,
    pushAt 82 2 56,
    opAt 83 .EQ,
    pushAt 84 2 5439,
    opAt 85 .JUMPI,
    opAt 86 .CALLDATASIZE,
    pushAt 87 2 63,
    opAt 88 .EQ,
    pushAt 89 2 5525,
    opAt 90 .JUMPI,
    opAt 91 .CALLDATASIZE,
    pushAt 92 2 64,
    opAt 93 .EQ,
    pushAt 94 2 5611,
    opAt 95 .JUMPI,
    opAt 96 .CALLDATASIZE,
    pushAt 97 2 65,
    opAt 98 .EQ,
    pushAt 99 2 5697,
    opAt 100 .JUMPI,
    opAt 101 .CALLDATASIZE,
    pushAt 102 2 119,
    opAt 103 .EQ,
    pushAt 104 2 5821,
    opAt 105 .JUMPI
  ]

def dispatchPath120 : List Located :=
[
    opAt 61 .CALLDATASIZE,
    pushAt 62 2 1,
    opAt 63 .EQ,
    pushAt 64 2 5209,
    opAt 65 .JUMPI,
    opAt 66 .CALLDATASIZE,
    pushAt 67 2 31,
    opAt 68 .EQ,
    pushAt 69 2 5257,
    opAt 70 .JUMPI,
    opAt 71 .CALLDATASIZE,
    pushAt 72 2 32,
    opAt 73 .EQ,
    pushAt 74 2 5305,
    opAt 75 .JUMPI,
    opAt 76 .CALLDATASIZE,
    pushAt 77 2 55,
    opAt 78 .EQ,
    pushAt 79 2 5353,
    opAt 80 .JUMPI,
    opAt 81 .CALLDATASIZE,
    pushAt 82 2 56,
    opAt 83 .EQ,
    pushAt 84 2 5439,
    opAt 85 .JUMPI,
    opAt 86 .CALLDATASIZE,
    pushAt 87 2 63,
    opAt 88 .EQ,
    pushAt 89 2 5525,
    opAt 90 .JUMPI,
    opAt 91 .CALLDATASIZE,
    pushAt 92 2 64,
    opAt 93 .EQ,
    pushAt 94 2 5611,
    opAt 95 .JUMPI,
    opAt 96 .CALLDATASIZE,
    pushAt 97 2 65,
    opAt 98 .EQ,
    pushAt 99 2 5697,
    opAt 100 .JUMPI,
    opAt 101 .CALLDATASIZE,
    pushAt 102 2 119,
    opAt 103 .EQ,
    pushAt 104 2 5821,
    opAt 105 .JUMPI,
    opAt 106 .CALLDATASIZE,
    pushAt 107 2 120,
    opAt 108 .EQ,
    pushAt 109 2 5983,
    opAt 110 .JUMPI
  ]

def dispatchPath128 : List Located :=
[
    opAt 61 .CALLDATASIZE,
    pushAt 62 2 1,
    opAt 63 .EQ,
    pushAt 64 2 5209,
    opAt 65 .JUMPI,
    opAt 66 .CALLDATASIZE,
    pushAt 67 2 31,
    opAt 68 .EQ,
    pushAt 69 2 5257,
    opAt 70 .JUMPI,
    opAt 71 .CALLDATASIZE,
    pushAt 72 2 32,
    opAt 73 .EQ,
    pushAt 74 2 5305,
    opAt 75 .JUMPI,
    opAt 76 .CALLDATASIZE,
    pushAt 77 2 55,
    opAt 78 .EQ,
    pushAt 79 2 5353,
    opAt 80 .JUMPI,
    opAt 81 .CALLDATASIZE,
    pushAt 82 2 56,
    opAt 83 .EQ,
    pushAt 84 2 5439,
    opAt 85 .JUMPI,
    opAt 86 .CALLDATASIZE,
    pushAt 87 2 63,
    opAt 88 .EQ,
    pushAt 89 2 5525,
    opAt 90 .JUMPI,
    opAt 91 .CALLDATASIZE,
    pushAt 92 2 64,
    opAt 93 .EQ,
    pushAt 94 2 5611,
    opAt 95 .JUMPI,
    opAt 96 .CALLDATASIZE,
    pushAt 97 2 65,
    opAt 98 .EQ,
    pushAt 99 2 5697,
    opAt 100 .JUMPI,
    opAt 101 .CALLDATASIZE,
    pushAt 102 2 119,
    opAt 103 .EQ,
    pushAt 104 2 5821,
    opAt 105 .JUMPI,
    opAt 106 .CALLDATASIZE,
    pushAt 107 2 120,
    opAt 108 .EQ,
    pushAt 109 2 5983,
    opAt 110 .JUMPI,
    opAt 111 .CALLDATASIZE,
    pushAt 112 2 128,
    opAt 113 .EQ,
    pushAt 114 2 6145,
    opAt 115 .JUMPI
  ]

def dispatchPath256 : List Located :=
[
    opAt 61 .CALLDATASIZE,
    pushAt 62 2 1,
    opAt 63 .EQ,
    pushAt 64 2 5209,
    opAt 65 .JUMPI,
    opAt 66 .CALLDATASIZE,
    pushAt 67 2 31,
    opAt 68 .EQ,
    pushAt 69 2 5257,
    opAt 70 .JUMPI,
    opAt 71 .CALLDATASIZE,
    pushAt 72 2 32,
    opAt 73 .EQ,
    pushAt 74 2 5305,
    opAt 75 .JUMPI,
    opAt 76 .CALLDATASIZE,
    pushAt 77 2 55,
    opAt 78 .EQ,
    pushAt 79 2 5353,
    opAt 80 .JUMPI,
    opAt 81 .CALLDATASIZE,
    pushAt 82 2 56,
    opAt 83 .EQ,
    pushAt 84 2 5439,
    opAt 85 .JUMPI,
    opAt 86 .CALLDATASIZE,
    pushAt 87 2 63,
    opAt 88 .EQ,
    pushAt 89 2 5525,
    opAt 90 .JUMPI,
    opAt 91 .CALLDATASIZE,
    pushAt 92 2 64,
    opAt 93 .EQ,
    pushAt 94 2 5611,
    opAt 95 .JUMPI,
    opAt 96 .CALLDATASIZE,
    pushAt 97 2 65,
    opAt 98 .EQ,
    pushAt 99 2 5697,
    opAt 100 .JUMPI,
    opAt 101 .CALLDATASIZE,
    pushAt 102 2 119,
    opAt 103 .EQ,
    pushAt 104 2 5821,
    opAt 105 .JUMPI,
    opAt 106 .CALLDATASIZE,
    pushAt 107 2 120,
    opAt 108 .EQ,
    pushAt 109 2 5983,
    opAt 110 .JUMPI,
    opAt 111 .CALLDATASIZE,
    pushAt 112 2 128,
    opAt 113 .EQ,
    pushAt 114 2 6145,
    opAt 115 .JUMPI,
    opAt 116 .CALLDATASIZE,
    pushAt 117 2 256,
    opAt 118 .EQ,
    pushAt 119 2 6307,
    opAt 120 .JUMPI
  ]

def dispatchPath376 : List Located :=
[
    opAt 61 .CALLDATASIZE,
    pushAt 62 2 1,
    opAt 63 .EQ,
    pushAt 64 2 5209,
    opAt 65 .JUMPI,
    opAt 66 .CALLDATASIZE,
    pushAt 67 2 31,
    opAt 68 .EQ,
    pushAt 69 2 5257,
    opAt 70 .JUMPI,
    opAt 71 .CALLDATASIZE,
    pushAt 72 2 32,
    opAt 73 .EQ,
    pushAt 74 2 5305,
    opAt 75 .JUMPI,
    opAt 76 .CALLDATASIZE,
    pushAt 77 2 55,
    opAt 78 .EQ,
    pushAt 79 2 5353,
    opAt 80 .JUMPI,
    opAt 81 .CALLDATASIZE,
    pushAt 82 2 56,
    opAt 83 .EQ,
    pushAt 84 2 5439,
    opAt 85 .JUMPI,
    opAt 86 .CALLDATASIZE,
    pushAt 87 2 63,
    opAt 88 .EQ,
    pushAt 89 2 5525,
    opAt 90 .JUMPI,
    opAt 91 .CALLDATASIZE,
    pushAt 92 2 64,
    opAt 93 .EQ,
    pushAt 94 2 5611,
    opAt 95 .JUMPI,
    opAt 96 .CALLDATASIZE,
    pushAt 97 2 65,
    opAt 98 .EQ,
    pushAt 99 2 5697,
    opAt 100 .JUMPI,
    opAt 101 .CALLDATASIZE,
    pushAt 102 2 119,
    opAt 103 .EQ,
    pushAt 104 2 5821,
    opAt 105 .JUMPI,
    opAt 106 .CALLDATASIZE,
    pushAt 107 2 120,
    opAt 108 .EQ,
    pushAt 109 2 5983,
    opAt 110 .JUMPI,
    opAt 111 .CALLDATASIZE,
    pushAt 112 2 128,
    opAt 113 .EQ,
    pushAt 114 2 6145,
    opAt 115 .JUMPI,
    opAt 116 .CALLDATASIZE,
    pushAt 117 2 256,
    opAt 118 .EQ,
    pushAt 119 2 6307,
    opAt 120 .JUMPI,
    opAt 121 .CALLDATASIZE,
    pushAt 122 2 376,
    opAt 123 .EQ,
    pushAt 124 2 6621,
    opAt 125 .JUMPI
  ]

def dispatchPath1000 : List Located :=
[
    opAt 61 .CALLDATASIZE,
    pushAt 62 2 1,
    opAt 63 .EQ,
    pushAt 64 2 5209,
    opAt 65 .JUMPI,
    opAt 66 .CALLDATASIZE,
    pushAt 67 2 31,
    opAt 68 .EQ,
    pushAt 69 2 5257,
    opAt 70 .JUMPI,
    opAt 71 .CALLDATASIZE,
    pushAt 72 2 32,
    opAt 73 .EQ,
    pushAt 74 2 5305,
    opAt 75 .JUMPI,
    opAt 76 .CALLDATASIZE,
    pushAt 77 2 55,
    opAt 78 .EQ,
    pushAt 79 2 5353,
    opAt 80 .JUMPI,
    opAt 81 .CALLDATASIZE,
    pushAt 82 2 56,
    opAt 83 .EQ,
    pushAt 84 2 5439,
    opAt 85 .JUMPI,
    opAt 86 .CALLDATASIZE,
    pushAt 87 2 63,
    opAt 88 .EQ,
    pushAt 89 2 5525,
    opAt 90 .JUMPI,
    opAt 91 .CALLDATASIZE,
    pushAt 92 2 64,
    opAt 93 .EQ,
    pushAt 94 2 5611,
    opAt 95 .JUMPI,
    opAt 96 .CALLDATASIZE,
    pushAt 97 2 65,
    opAt 98 .EQ,
    pushAt 99 2 5697,
    opAt 100 .JUMPI,
    opAt 101 .CALLDATASIZE,
    pushAt 102 2 119,
    opAt 103 .EQ,
    pushAt 104 2 5821,
    opAt 105 .JUMPI,
    opAt 106 .CALLDATASIZE,
    pushAt 107 2 120,
    opAt 108 .EQ,
    pushAt 109 2 5983,
    opAt 110 .JUMPI,
    opAt 111 .CALLDATASIZE,
    pushAt 112 2 128,
    opAt 113 .EQ,
    pushAt 114 2 6145,
    opAt 115 .JUMPI,
    opAt 116 .CALLDATASIZE,
    pushAt 117 2 256,
    opAt 118 .EQ,
    pushAt 119 2 6307,
    opAt 120 .JUMPI,
    opAt 121 .CALLDATASIZE,
    pushAt 122 2 376,
    opAt 123 .EQ,
    pushAt 124 2 6621,
    opAt 125 .JUMPI,
    opAt 126 .CALLDATASIZE,
    pushAt 127 2 1000,
    opAt 128 .EQ,
    pushAt 129 2 7091,
    opAt 130 .JUMPI
  ]

theorem run_dispatch1 (input : ByteArray) (hsize : input.size = 1) :
    run dispatchPath1 (patternedEntry input) = some (verifyEntry 1 input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [dispatchPath1, patternedEntry, verifyEntry, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat, hsize,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_dispatch31 (input : ByteArray) (hsize : input.size = 31) :
    run dispatchPath31 (patternedEntry input) = some (verifyEntry 31 input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [dispatchPath31, patternedEntry, verifyEntry, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat, hsize,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_dispatch32 (input : ByteArray) (hsize : input.size = 32) :
    run dispatchPath32 (patternedEntry input) = some (verifyEntry 32 input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [dispatchPath32, patternedEntry, verifyEntry, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat, hsize,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_dispatch55 (input : ByteArray) (hsize : input.size = 55) :
    run dispatchPath55 (patternedEntry input) = some (verifyEntry 55 input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [dispatchPath55, patternedEntry, verifyEntry, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat, hsize,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_dispatch56 (input : ByteArray) (hsize : input.size = 56) :
    run dispatchPath56 (patternedEntry input) = some (verifyEntry 56 input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [dispatchPath56, patternedEntry, verifyEntry, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat, hsize,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_dispatch63 (input : ByteArray) (hsize : input.size = 63) :
    run dispatchPath63 (patternedEntry input) = some (verifyEntry 63 input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [dispatchPath63, patternedEntry, verifyEntry, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat, hsize,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_dispatch64 (input : ByteArray) (hsize : input.size = 64) :
    run dispatchPath64 (patternedEntry input) = some (verifyEntry 64 input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [dispatchPath64, patternedEntry, verifyEntry, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat, hsize,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_dispatch65 (input : ByteArray) (hsize : input.size = 65) :
    run dispatchPath65 (patternedEntry input) = some (verifyEntry 65 input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [dispatchPath65, patternedEntry, verifyEntry, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat, hsize,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_dispatch119 (input : ByteArray) (hsize : input.size = 119) :
    run dispatchPath119 (patternedEntry input) = some (verifyEntry 119 input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [dispatchPath119, patternedEntry, verifyEntry, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat, hsize,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_dispatch120 (input : ByteArray) (hsize : input.size = 120) :
    run dispatchPath120 (patternedEntry input) = some (verifyEntry 120 input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [dispatchPath120, patternedEntry, verifyEntry, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat, hsize,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_dispatch128 (input : ByteArray) (hsize : input.size = 128) :
    run dispatchPath128 (patternedEntry input) = some (verifyEntry 128 input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [dispatchPath128, patternedEntry, verifyEntry, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat, hsize,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_dispatch256 (input : ByteArray) (hsize : input.size = 256) :
    run dispatchPath256 (patternedEntry input) = some (verifyEntry 256 input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [dispatchPath256, patternedEntry, verifyEntry, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat, hsize,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_dispatch376 (input : ByteArray) (hsize : input.size = 376) :
    run dispatchPath376 (patternedEntry input) = some (verifyEntry 376 input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [dispatchPath376, patternedEntry, verifyEntry, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat, hsize,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_dispatch1000 (input : ByteArray) (hsize : input.size = 1000) :
    run dispatchPath1000 (patternedEntry input) = some (verifyEntry 1000 input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [dispatchPath1000, patternedEntry, verifyEntry, verifyStart,
      atPC, initialState, stS, opAt, pushAt, wfOp, hzeroNat, hsize,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierDispatch
