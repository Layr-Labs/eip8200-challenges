import Challenge.Modexp.Submission.Proofs.Cycle.SquareHistory
import Challenge.Modexp.Submission.Proofs.Cycle.NormalizeMeaning
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace CycleSubmission.SquareMeaning
open EvmSemantics EvmSemantics.EVM
open CycleSubmission.WordArithmetic CycleSubmission.WordHistory
open HistoricalSearch.CRTMemoryCells Challenge.EvmProof.Memory
open CycleSubmission.NormalizeMeaning (readStore)
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

def frame0 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(n 2), (n 6), (n 4), (a 1), (a 2), (n 5), (n 7), P, (n 8), (n 1), (UInt256.ofNat (2^240-1)), (n 0), (n 3), (a 8)] ++ rest

structure Memory0 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (a 0)
  at1344 : MachineState.readWord mem 1344 = (n 0)
  at1376 : MachineState.readWord mem 1376 = (n 1)
  at2720 : MachineState.readWord mem 2720 = inv
  at1568 : MachineState.readWord mem 1568 = (n 7)
  at1600 : MachineState.readWord mem 1600 = (n 8)
  at32 : MachineState.readWord mem 32 = (a 3)
  at64 : MachineState.readWord mem 64 = (a 4)
  at96 : MachineState.readWord mem 96 = (a 5)
  at128 : MachineState.readWord mem 128 = (a 6)
  at160 : MachineState.readWord mem 160 = (a 7)

def frame1 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(n 0), P, ((UInt256.mulMod (squareQ1 inv a b n) (n 1) P) + ((UInt256.mulMod (squareQ0 inv a b n) (n 2) P) + ((UInt256.mulMod (a 1) (a 1) P) + ((squareC2 inv a b n) + ((UInt256.mulMod (a 2) (a 0) P) + (UInt256.mulMod (a 2) (a 0) P)))))), (((squareQ1 inv a b n) * (n 1)) + (((squareQ0 inv a b n) * (n 2)) + (((a 1) * (a 1)) + ((squareC2 inv a b n) + (((a 2) * (a 0)) + ((a 2) * (a 0))))))), (n 2), (n 6), (n 4), (a 1), (a 2), (n 5), (squareQ1 inv a b n), P, (squareQ0 inv a b n), (n 1), (UInt256.ofNat (2^240-1)), (n 0), (n 3), (a 8)] ++ rest

structure Memory1 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (a 0)
  at1344 : MachineState.readWord mem 1344 = (n 0)
  at1376 : MachineState.readWord mem 1376 = (n 1)
  at2720 : MachineState.readWord mem 2720 = inv
  at1568 : MachineState.readWord mem 1568 = (n 7)
  at1600 : MachineState.readWord mem 1600 = (n 8)
  at32 : MachineState.readWord mem 32 = (a 3)
  at64 : MachineState.readWord mem 64 = (a 4)
  at96 : MachineState.readWord mem 96 = (a 5)
  at128 : MachineState.readWord mem 128 = (a 6)
  at160 : MachineState.readWord mem 160 = (a 7)

def frame2 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(UInt256.mulMod (a 1) (a 3) P), (UInt256.mulMod (a 4) (a 0) P), ((((a 1) * (a 3)) + ((a 4) * (a 0))) + (((a 1) * (a 3)) + ((a 4) * (a 0)))), (squareC4 inv a b n), (n 2), (n 6), (n 4), (a 1), (a 2), (n 5), (squareQ1 inv a b n), P, (squareQ0 inv a b n), (n 1), (UInt256.ofNat (2^240-1)), (n 0), (n 3), (a 8)] ++ rest

structure Memory2 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (a 0)
  at1344 : MachineState.readWord mem 1344 = (n 0)
  at1376 : MachineState.readWord mem 1376 = (n 1)
  at2720 : MachineState.readWord mem 2720 = inv
  at1568 : MachineState.readWord mem 1568 = (n 7)
  at1600 : MachineState.readWord mem 1600 = (n 8)
  at32 : MachineState.readWord mem 32 = (a 3)
  at64 : MachineState.readWord mem 64 = (a 4)
  at96 : MachineState.readWord mem 96 = (a 5)
  at128 : MachineState.readWord mem 128 = (a 6)
  at160 : MachineState.readWord mem 160 = (a 7)
  at192 : MachineState.readWord mem 192 = (squareQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (squareQ3 inv a b n)

def frame3 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(n 5), ((squareC5 inv a b n) + ((((a 2) * (a 3)) + (((a 1) * (a 4)) + ((a 5) * (a 0)))) + (((a 2) * (a 3)) + (((a 1) * (a 4)) + ((a 5) * (a 0)))))), ((squareC5 inv a b n) + (((UInt256.mulMod (a 2) (a 3) P) + ((UInt256.mulMod (a 1) (a 4) P) + (UInt256.mulMod (a 5) (a 0) P))) + ((UInt256.mulMod (a 2) (a 3) P) + ((UInt256.mulMod (a 1) (a 4) P) + (UInt256.mulMod (a 5) (a 0) P))))), (n 2), (n 6), (n 4), (a 1), (a 2), (n 5), (squareQ1 inv a b n), P, (squareQ0 inv a b n), (n 1), (UInt256.ofNat (2^240-1)), (n 0), (n 3), (a 8)] ++ rest

structure Memory3 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (a 0)
  at1344 : MachineState.readWord mem 1344 = (n 0)
  at1376 : MachineState.readWord mem 1376 = (n 1)
  at2720 : MachineState.readWord mem 2720 = inv
  at1568 : MachineState.readWord mem 1568 = (n 7)
  at1600 : MachineState.readWord mem 1600 = (n 8)
  at32 : MachineState.readWord mem 32 = (a 3)
  at64 : MachineState.readWord mem 64 = (a 4)
  at96 : MachineState.readWord mem 96 = (a 5)
  at128 : MachineState.readWord mem 128 = (a 6)
  at160 : MachineState.readWord mem 160 = (a 7)
  at192 : MachineState.readWord mem 192 = (squareQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (squareQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (squareQ4 inv a b n)

def frame4 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(a 3), (a 3), ((squareC6 inv a b n) + ((((a 2) * (a 4)) + (((a 1) * (a 5)) + ((a 6) * (a 0)))) + (((a 2) * (a 4)) + (((a 1) * (a 5)) + ((a 6) * (a 0)))))), ((squareC6 inv a b n) + (((UInt256.mulMod (a 2) (a 4) P) + ((UInt256.mulMod (a 1) (a 5) P) + (UInt256.mulMod (a 6) (a 0) P))) + ((UInt256.mulMod (a 2) (a 4) P) + ((UInt256.mulMod (a 1) (a 5) P) + (UInt256.mulMod (a 6) (a 0) P))))), (n 2), (n 6), (n 4), (a 1), (a 2), (n 5), (squareQ1 inv a b n), P, (squareQ0 inv a b n), (n 1), (UInt256.ofNat (2^240-1)), (n 0), (n 3), (a 8)] ++ rest

structure Memory4 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (a 0)
  at1344 : MachineState.readWord mem 1344 = (n 0)
  at1376 : MachineState.readWord mem 1376 = (n 1)
  at2720 : MachineState.readWord mem 2720 = inv
  at1568 : MachineState.readWord mem 1568 = (n 7)
  at1600 : MachineState.readWord mem 1600 = (n 8)
  at32 : MachineState.readWord mem 32 = (a 3)
  at64 : MachineState.readWord mem 64 = (a 4)
  at96 : MachineState.readWord mem 96 = (a 5)
  at128 : MachineState.readWord mem 128 = (a 6)
  at160 : MachineState.readWord mem 160 = (a 7)
  at192 : MachineState.readWord mem 192 = (squareQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (squareQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (squareQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (squareQ5 inv a b n)

def frame5 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(a 2), (a 5), (((a 6) * (a 1)) + ((a 7) * (a 0))), (a 0), P, (a 7), (squareQ1 inv a b n), (squareC7 inv a b n), (n 2), (n 6), (n 4), (a 1), (a 2), (n 5), (n 7), P, (squareQ0 inv a b n), (n 1), (UInt256.ofNat (2^240-1)), (n 0), (n 3), (a 8)] ++ rest

structure Memory5 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (a 0)
  at1344 : MachineState.readWord mem 1344 = (n 0)
  at1376 : MachineState.readWord mem 1376 = (n 1)
  at2720 : MachineState.readWord mem 2720 = inv
  at1568 : MachineState.readWord mem 1568 = (n 7)
  at1600 : MachineState.readWord mem 1600 = (n 8)
  at32 : MachineState.readWord mem 32 = (a 3)
  at64 : MachineState.readWord mem 64 = (a 4)
  at96 : MachineState.readWord mem 96 = (a 5)
  at128 : MachineState.readWord mem 128 = (a 6)
  at160 : MachineState.readWord mem 160 = (a 7)
  at192 : MachineState.readWord mem 192 = (squareQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (squareQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (squareQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (squareQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (squareQ6 inv a b n)

def frame6 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(n 1), P, ((UInt256.mulMod (squareQ5 inv a b n) (n 2) P) + ((UInt256.mulMod (squareQ4 inv a b n) (n 3) P) + ((UInt256.mulMod (squareQ3 inv a b n) (n 4) P) + ((UInt256.mulMod (squareQ2 inv a b n) (n 5) P) + ((UInt256.mulMod (squareQ1 inv a b n) (n 6) P) + ((UInt256.mulMod (n 7) (squareQ0 inv a b n) P) + ((squareC7 inv a b n) + (((UInt256.mulMod (a 3) (a 4) P) + ((UInt256.mulMod (a 2) (a 5) P) + ((UInt256.mulMod (a 1) (a 6) P) + (UInt256.mulMod (a 7) (a 0) P)))) + ((UInt256.mulMod (a 3) (a 4) P) + ((UInt256.mulMod (a 2) (a 5) P) + ((UInt256.mulMod (a 1) (a 6) P) + (UInt256.mulMod (a 7) (a 0) P)))))))))))), (((squareQ6 inv a b n) * (n 1)) + (((squareQ5 inv a b n) * (n 2)) + (((squareQ4 inv a b n) * (n 3)) + (((squareQ3 inv a b n) * (n 4)) + (((squareQ2 inv a b n) * (n 5)) + (((squareQ1 inv a b n) * (n 6)) + (((n 7) * (squareQ0 inv a b n)) + ((squareC7 inv a b n) + ((((a 3) * (a 4)) + (((a 2) * (a 5)) + (((a 6) * (a 1)) + ((a 7) * (a 0))))) + (((a 3) * (a 4)) + (((a 2) * (a 5)) + (((a 6) * (a 1)) + ((a 7) * (a 0)))))))))))))), (n 2), (n 6), (n 4), (a 1), (a 2), (n 5), (n 7), P, (squareQ0 inv a b n), (n 1), (UInt256.ofNat (2^240-1)), (n 0), (n 3), (a 8)] ++ rest

structure Memory6 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (a 0)
  at1344 : MachineState.readWord mem 1344 = (n 0)
  at1376 : MachineState.readWord mem 1376 = (n 1)
  at2720 : MachineState.readWord mem 2720 = inv
  at1568 : MachineState.readWord mem 1568 = (n 7)
  at1600 : MachineState.readWord mem 1600 = (n 8)
  at32 : MachineState.readWord mem 32 = (a 3)
  at64 : MachineState.readWord mem 64 = (a 4)
  at96 : MachineState.readWord mem 96 = (a 5)
  at128 : MachineState.readWord mem 128 = (a 6)
  at160 : MachineState.readWord mem 160 = (a 7)
  at192 : MachineState.readWord mem 192 = (squareQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (squareQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (squareQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (squareQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (squareQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (squareQ1 inv a b n)

def frame7 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [((squareQ3 inv a b n) * (n 5)), (((squareQ2 inv a b n) * (n 6)) + (((n 7) * (squareQ1 inv a b n)) + (((n 8) * (squareQ0 inv a b n)) + (((a 4) * (a 4)) + ((squareC8 inv a b n) + ((((a 3) * (a 5)) + (((a 2) * (a 6)) + (((a 7) * (a 1)) + ((a 8) * (a 0))))) + (((a 3) * (a 5)) + (((a 2) * (a 6)) + (((a 7) * (a 1)) + ((a 8) * (a 0))))))))))), ((UInt256.mulMod (n 8) (squareQ0 inv a b n) P) + ((squareC8 inv a b n) + (((UInt256.mulMod (a 3) (a 5) P) + ((UInt256.mulMod (a 2) (a 6) P) + ((UInt256.mulMod (a 1) (a 7) P) + (UInt256.mulMod (a 8) (a 0) P)))) + ((UInt256.mulMod (a 3) (a 5) P) + ((UInt256.mulMod (a 2) (a 6) P) + ((UInt256.mulMod (a 1) (a 7) P) + (UInt256.mulMod (a 8) (a 0) P))))))), (n 2), (n 6), (n 4), (a 1), (a 2), (n 5), (n 7), P, (n 8), (n 1), (UInt256.ofNat (2^240-1)), (n 0), (n 3), (a 8)] ++ rest

structure Memory7 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (a 0)
  at1344 : MachineState.readWord mem 1344 = (n 0)
  at1376 : MachineState.readWord mem 1376 = (n 1)
  at2720 : MachineState.readWord mem 2720 = inv
  at1568 : MachineState.readWord mem 1568 = (n 7)
  at1600 : MachineState.readWord mem 1600 = (n 8)
  at32 : MachineState.readWord mem 32 = (a 3)
  at64 : MachineState.readWord mem 64 = (a 4)
  at96 : MachineState.readWord mem 96 = (a 5)
  at128 : MachineState.readWord mem 128 = (a 6)
  at160 : MachineState.readWord mem 160 = (a 7)
  at192 : MachineState.readWord mem 192 = (squareQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (squareQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (squareQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (squareQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (squareQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (squareQ1 inv a b n)
  at1280 : MachineState.readWord mem 1280 = (squareQ7 inv a b n)

def frame8 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(a 6), (((a 2) * (a 7)) + ((a 8) * (a 1))), (a 1), P, (a 8), (squareC9 inv a b n), (n 2), (n 6), (n 4), (squareQ6 inv a b n), (a 2), (n 5), (n 7), P, (n 8), (n 1), (UInt256.ofNat (2^240-1)), (squareQ8 inv a b n), (n 3), (a 8)] ++ rest

structure Memory8 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (a 0)
  at1344 : MachineState.readWord mem 1344 = (n 0)
  at1376 : MachineState.readWord mem 1376 = (n 1)
  at2720 : MachineState.readWord mem 2720 = inv
  at1568 : MachineState.readWord mem 1568 = (n 7)
  at1600 : MachineState.readWord mem 1600 = (n 8)
  at32 : MachineState.readWord mem 32 = (a 3)
  at64 : MachineState.readWord mem 64 = (a 4)
  at96 : MachineState.readWord mem 96 = (a 5)
  at128 : MachineState.readWord mem 128 = (a 6)
  at160 : MachineState.readWord mem 160 = (a 7)
  at192 : MachineState.readWord mem 192 = (squareQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (squareQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (squareQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (squareQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (squareQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (squareQ1 inv a b n)
  at1280 : MachineState.readWord mem 1280 = (squareQ7 inv a b n)

def frame9 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(squareQ5 inv a b n), (n 4), P, ((UInt256.mulMod (squareQ4 inv a b n) (n 5) P) + ((UInt256.mulMod (squareQ3 inv a b n) (n 6) P) + ((UInt256.mulMod (n 7) (squareQ2 inv a b n) P) + ((UInt256.mulMod (n 8) (squareQ1 inv a b n) P) + ((squareC9 inv a b n) + (((UInt256.mulMod (a 4) (a 5) P) + ((UInt256.mulMod (a 3) (a 6) P) + ((UInt256.mulMod (a 2) (a 7) P) + (UInt256.mulMod (a 8) (a 1) P)))) + ((UInt256.mulMod (a 4) (a 5) P) + ((UInt256.mulMod (a 3) (a 6) P) + ((UInt256.mulMod (a 2) (a 7) P) + (UInt256.mulMod (a 8) (a 1) P)))))))))), (((squareQ8 inv a b n) * (n 1)) + (((squareQ7 inv a b n) * (n 2)) + (((squareQ6 inv a b n) * (n 3)) + (((squareQ5 inv a b n) * (n 4)) + (((squareQ4 inv a b n) * (n 5)) + (((squareQ3 inv a b n) * (n 6)) + (((n 7) * (squareQ2 inv a b n)) + (((n 8) * (squareQ1 inv a b n)) + ((squareC9 inv a b n) + ((((a 4) * (a 5)) + (((a 3) * (a 6)) + (((a 2) * (a 7)) + ((a 8) * (a 1))))) + (((a 4) * (a 5)) + (((a 3) * (a 6)) + (((a 2) * (a 7)) + ((a 8) * (a 1))))))))))))))), (n 2), (n 6), (n 4), (squareQ6 inv a b n), (a 2), (n 5), (n 7), P, (n 8), (n 1), (UInt256.ofNat (2^240-1)), (squareQ8 inv a b n), (n 3), (a 8)] ++ rest

structure Memory9 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (a 0)
  at1344 : MachineState.readWord mem 1344 = (n 0)
  at1376 : MachineState.readWord mem 1376 = (n 1)
  at2720 : MachineState.readWord mem 2720 = inv
  at1568 : MachineState.readWord mem 1568 = (n 7)
  at1600 : MachineState.readWord mem 1600 = (n 8)
  at32 : MachineState.readWord mem 32 = (a 3)
  at64 : MachineState.readWord mem 64 = (a 4)
  at96 : MachineState.readWord mem 96 = (a 5)
  at128 : MachineState.readWord mem 128 = (a 6)
  at160 : MachineState.readWord mem 160 = (a 7)
  at192 : MachineState.readWord mem 192 = (squareQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (squareQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (squareQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (squareQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (squareQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (squareQ1 inv a b n)
  at1280 : MachineState.readWord mem 1280 = (squareQ7 inv a b n)

def frame10 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(squareQ5 inv a b n), (n 5), (((squareQ4 inv a b n) * (n 6)) + (((n 7) * (squareQ3 inv a b n)) + (((n 8) * (squareQ2 inv a b n)) + (((a 5) * (a 5)) + ((squareC10 inv a b n) + ((((a 4) * (a 6)) + (((a 3) * (a 7)) + ((a 8) * (a 2)))) + (((a 4) * (a 6)) + (((a 3) * (a 7)) + ((a 8) * (a 2)))))))))), ((squareC10 inv a b n) + (((UInt256.mulMod (a 4) (a 6) P) + ((UInt256.mulMod (a 3) (a 7) P) + (UInt256.mulMod (a 8) (a 2) P))) + ((UInt256.mulMod (a 4) (a 6) P) + ((UInt256.mulMod (a 3) (a 7) P) + (UInt256.mulMod (a 8) (a 2) P))))), (n 2), (n 6), (n 4), (squareQ6 inv a b n), (squareQ5 inv a b n), (n 5), (n 7), P, (n 8), (squareQ7 inv a b n), (UInt256.ofNat (2^240-1)), (squareQ8 inv a b n), (n 3), (a 8)] ++ rest

structure Memory10 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (squareD0 inv a b n)
  at1344 : MachineState.readWord mem 1344 = (n 0)
  at1376 : MachineState.readWord mem 1376 = (n 1)
  at2720 : MachineState.readWord mem 2720 = inv
  at1568 : MachineState.readWord mem 1568 = (n 7)
  at1600 : MachineState.readWord mem 1600 = (n 8)
  at32 : MachineState.readWord mem 32 = (a 3)
  at64 : MachineState.readWord mem 64 = (a 4)
  at96 : MachineState.readWord mem 96 = (a 5)
  at128 : MachineState.readWord mem 128 = (a 6)
  at160 : MachineState.readWord mem 160 = (a 7)
  at192 : MachineState.readWord mem 192 = (squareQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (squareQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (squareQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (squareQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (squareQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (squareQ1 inv a b n)
  at1280 : MachineState.readWord mem 1280 = (squareQ7 inv a b n)

def frame11 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(a 5), (a 6), P, ((UInt256.mulMod (a 4) (a 7) P) + (UInt256.mulMod (a 8) (a 3) P)), ((((a 5) * (a 6)) + (((a 4) * (a 7)) + ((a 8) * (a 3)))) + (((a 5) * (a 6)) + (((a 4) * (a 7)) + ((a 8) * (a 3))))), (squareC11 inv a b n), (n 2), (n 6), (n 4), (squareQ6 inv a b n), (squareQ5 inv a b n), (n 5), (n 7), P, (n 8), (squareQ7 inv a b n), (UInt256.ofNat (2^240-1)), (squareQ8 inv a b n), (n 3), (a 8)] ++ rest

structure Memory11 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (squareD0 inv a b n)
  at1344 : MachineState.readWord mem 1344 = (n 0)
  at1376 : MachineState.readWord mem 1376 = (n 1)
  at2720 : MachineState.readWord mem 2720 = inv
  at1568 : MachineState.readWord mem 1568 = (n 7)
  at1600 : MachineState.readWord mem 1600 = (n 8)
  at32 : MachineState.readWord mem 32 = (a 3)
  at64 : MachineState.readWord mem 64 = (a 4)
  at96 : MachineState.readWord mem 96 = (a 5)
  at128 : MachineState.readWord mem 128 = (a 6)
  at160 : MachineState.readWord mem 160 = (a 7)
  at192 : MachineState.readWord mem 192 = (squareQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (squareQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (squareQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (squareQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (squareQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (squareQ1 inv a b n)
  at1280 : MachineState.readWord mem 1280 = (squareQ7 inv a b n)
  at800 : MachineState.readWord mem 800 = (squareD1 inv a b n)

def frame12 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(a 6), ((squareC12 inv a b n) + ((((a 5) * (a 7)) + ((a 8) * (a 4))) + (((a 5) * (a 7)) + ((a 8) * (a 4))))), ((squareC12 inv a b n) + (((UInt256.mulMod (a 5) (a 7) P) + (UInt256.mulMod (a 8) (a 4) P)) + ((UInt256.mulMod (a 5) (a 7) P) + (UInt256.mulMod (a 8) (a 4) P)))), (n 2), (n 6), (n 4), (squareQ6 inv a b n), (squareQ5 inv a b n), (n 5), (n 7), P, (n 8), (squareQ7 inv a b n), (UInt256.ofNat (2^240-1)), (squareQ8 inv a b n), (n 3), (a 8)] ++ rest

structure Memory12 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (squareD0 inv a b n)
  at1344 : MachineState.readWord mem 1344 = (n 0)
  at1376 : MachineState.readWord mem 1376 = (n 1)
  at2720 : MachineState.readWord mem 2720 = inv
  at1568 : MachineState.readWord mem 1568 = (n 7)
  at1600 : MachineState.readWord mem 1600 = (n 8)
  at32 : MachineState.readWord mem 32 = (a 3)
  at64 : MachineState.readWord mem 64 = (a 4)
  at96 : MachineState.readWord mem 96 = (a 5)
  at128 : MachineState.readWord mem 128 = (a 6)
  at160 : MachineState.readWord mem 160 = (a 7)
  at192 : MachineState.readWord mem 192 = (squareQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (squareQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (squareQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (squareQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (squareQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (squareQ1 inv a b n)
  at1280 : MachineState.readWord mem 1280 = (squareQ7 inv a b n)
  at800 : MachineState.readWord mem 800 = (squareD1 inv a b n)
  at832 : MachineState.readWord mem 832 = (squareD2 inv a b n)

def frame13 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [((n 6) * (squareQ7 inv a b n)), (((n 7) * (squareQ6 inv a b n)) + (((n 8) * (squareQ5 inv a b n)) + ((squareC13 inv a b n) + ((((a 6) * (a 7)) + ((a 8) * (a 5))) + (((a 6) * (a 7)) + ((a 8) * (a 5))))))), ((squareC13 inv a b n) + (((UInt256.mulMod (a 6) (a 7) P) + (UInt256.mulMod (a 8) (a 5) P)) + ((UInt256.mulMod (a 6) (a 7) P) + (UInt256.mulMod (a 8) (a 5) P)))), (n 2), (n 6), (n 4), (squareQ6 inv a b n), (squareQ5 inv a b n), (n 5), (n 7), P, (n 8), (squareQ7 inv a b n), (UInt256.ofNat (2^240-1)), (squareQ8 inv a b n), (n 3), (a 8)] ++ rest

structure Memory13 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (squareD0 inv a b n)
  at1344 : MachineState.readWord mem 1344 = (n 0)
  at1376 : MachineState.readWord mem 1376 = (n 1)
  at2720 : MachineState.readWord mem 2720 = inv
  at1568 : MachineState.readWord mem 1568 = (n 7)
  at1600 : MachineState.readWord mem 1600 = (n 8)
  at32 : MachineState.readWord mem 32 = (squareD3 inv a b n)
  at64 : MachineState.readWord mem 64 = (a 4)
  at96 : MachineState.readWord mem 96 = (a 5)
  at128 : MachineState.readWord mem 128 = (a 6)
  at160 : MachineState.readWord mem 160 = (a 7)
  at192 : MachineState.readWord mem 192 = (squareQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (squareQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (squareQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (squareQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (squareQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (squareQ1 inv a b n)
  at1280 : MachineState.readWord mem 1280 = (squareQ7 inv a b n)
  at800 : MachineState.readWord mem 800 = (squareD1 inv a b n)
  at832 : MachineState.readWord mem 832 = (squareD2 inv a b n)

def frame14 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(squareC15 inv a b n), (n 2), (n 6), (n 4), (squareQ6 inv a b n), (squareD2 inv a b n), (n 5), (n 7), P, (n 8), (squareQ7 inv a b n), (UInt256.ofNat (2^240-1)), (squareQ8 inv a b n), (n 3), (a 8)] ++ rest

structure Memory14 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (squareD0 inv a b n)
  at1344 : MachineState.readWord mem 1344 = (n 0)
  at1376 : MachineState.readWord mem 1376 = (n 1)
  at2720 : MachineState.readWord mem 2720 = inv
  at1568 : MachineState.readWord mem 1568 = (n 7)
  at1600 : MachineState.readWord mem 1600 = (n 8)
  at32 : MachineState.readWord mem 32 = (squareD3 inv a b n)
  at64 : MachineState.readWord mem 64 = (squareD4 inv a b n)
  at96 : MachineState.readWord mem 96 = (squareD5 inv a b n)
  at128 : MachineState.readWord mem 128 = (a 6)
  at160 : MachineState.readWord mem 160 = (a 7)
  at192 : MachineState.readWord mem 192 = (squareQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (squareQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (squareQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (squareQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (squareQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (squareQ1 inv a b n)
  at1280 : MachineState.readWord mem 1280 = (squareQ7 inv a b n)
  at800 : MachineState.readWord mem 800 = (squareD1 inv a b n)
  at832 : MachineState.readWord mem 832 = (squareD2 inv a b n)

def frame15 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(n 2), (n 6), (n 4), (squareD1 inv a b n), (squareD2 inv a b n), (n 5), (n 7), P, (n 8), (n 1), (UInt256.ofNat (2^240-1)), (n 0), (n 3), (squareC17 inv a b n)] ++ rest

structure Memory15 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (squareD0 inv a b n)
  at1344 : MachineState.readWord mem 1344 = (n 0)
  at1376 : MachineState.readWord mem 1376 = (n 1)
  at2720 : MachineState.readWord mem 2720 = inv
  at1568 : MachineState.readWord mem 1568 = (n 7)
  at1600 : MachineState.readWord mem 1600 = (n 8)
  at32 : MachineState.readWord mem 32 = (squareD3 inv a b n)
  at64 : MachineState.readWord mem 64 = (squareD4 inv a b n)
  at96 : MachineState.readWord mem 96 = (squareD5 inv a b n)
  at128 : MachineState.readWord mem 128 = (squareD6 inv a b n)
  at160 : MachineState.readWord mem 160 = (squareD7 inv a b n)
  at192 : MachineState.readWord mem 192 = (squareQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (squareQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (squareQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (squareQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (squareQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (squareQ1 inv a b n)
  at1280 : MachineState.readWord mem 1280 = (squareQ7 inv a b n)
  at800 : MachineState.readWord mem 800 = (squareD1 inv a b n)
  at832 : MachineState.readWord mem 832 = (squareD2 inv a b n)

end CycleSubmission.SquareMeaning
