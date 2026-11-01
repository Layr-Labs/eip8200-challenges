import Challenge.Modexp.Submission.Proofs.Cycle.ProductHistory
import Challenge.Modexp.Submission.Proofs.Cycle.NormalizeMeaning
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace CycleSubmission.ProductMeaning
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
  at1792 : MachineState.readWord mem 1792 = (b 0)
  at1824 : MachineState.readWord mem 1824 = (b 1)
  at1856 : MachineState.readWord mem 1856 = (b 2)
  at1888 : MachineState.readWord mem 1888 = (b 3)
  at1920 : MachineState.readWord mem 1920 = (b 4)
  at1952 : MachineState.readWord mem 1952 = (b 5)
  at1984 : MachineState.readWord mem 1984 = (b 6)
  at2016 : MachineState.readWord mem 2016 = (b 7)
  at2048 : MachineState.readWord mem 2048 = (b 8)

def frame1 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [((UInt256.mulMod (b 1) (a 1) P) + ((UInt256.mulMod (b 2) (a 0) P) + (productC2 inv a b n))), (((b 1) * (a 1)) + (((b 2) * (a 0)) + (productC2 inv a b n))), (n 2), (n 6), (n 4), (a 1), (a 2), (n 5), (productQ1 inv a b n), P, (productQ0 inv a b n), (n 1), (UInt256.ofNat (2^240-1)), (n 0), (n 3), (a 8)] ++ rest

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
  at1792 : MachineState.readWord mem 1792 = (b 0)
  at1824 : MachineState.readWord mem 1824 = (b 1)
  at1856 : MachineState.readWord mem 1856 = (b 2)
  at1888 : MachineState.readWord mem 1888 = (b 3)
  at1920 : MachineState.readWord mem 1920 = (b 4)
  at1952 : MachineState.readWord mem 1952 = (b 5)
  at1984 : MachineState.readWord mem 1984 = (b 6)
  at2016 : MachineState.readWord mem 2016 = (b 7)
  at2048 : MachineState.readWord mem 2048 = (b 8)

def frame2 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(productQ2 inv a b n), (n 1), (((productQ1 inv a b n) * (n 2)) + (((productQ0 inv a b n) * (n 3)) + (((b 0) * (a 3)) + (((b 1) * (a 2)) + (((b 2) * (a 1)) + (((b 3) * (a 0)) + (productC3 inv a b n))))))), ((UInt256.mulMod (b 0) (a 3) P) + ((UInt256.mulMod (b 1) (a 2) P) + ((UInt256.mulMod (b 2) (a 1) P) + ((UInt256.mulMod (b 3) (a 0) P) + (productC3 inv a b n))))), (n 2), (n 6), (n 4), (a 1), (a 2), (n 5), (productQ1 inv a b n), P, (productQ0 inv a b n), (n 1), (UInt256.ofNat (2^240-1)), (n 0), (n 3), (a 8)] ++ rest

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
  at1792 : MachineState.readWord mem 1792 = (b 0)
  at1824 : MachineState.readWord mem 1824 = (b 1)
  at1856 : MachineState.readWord mem 1856 = (b 2)
  at1888 : MachineState.readWord mem 1888 = (b 3)
  at1920 : MachineState.readWord mem 1920 = (b 4)
  at1952 : MachineState.readWord mem 1952 = (b 5)
  at1984 : MachineState.readWord mem 1984 = (b 6)
  at2016 : MachineState.readWord mem 2016 = (b 7)
  at2048 : MachineState.readWord mem 2048 = (b 8)
  at192 : MachineState.readWord mem 192 = (productQ2 inv a b n)

def frame3 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(n 2), (((productQ1 inv a b n) * (n 3)) + (((productQ0 inv a b n) * (n 4)) + (((b 0) * (a 4)) + (((b 1) * (a 3)) + (((b 2) * (a 2)) + (((b 3) * (a 1)) + (((b 4) * (a 0)) + (productC4 inv a b n)))))))), ((UInt256.mulMod (b 0) (a 4) P) + ((UInt256.mulMod (b 1) (a 3) P) + ((UInt256.mulMod (b 2) (a 2) P) + ((UInt256.mulMod (b 3) (a 1) P) + ((UInt256.mulMod (b 4) (a 0) P) + (productC4 inv a b n)))))), (n 2), (n 6), (n 4), (a 1), (a 2), (n 5), (productQ1 inv a b n), P, (productQ0 inv a b n), (n 1), (UInt256.ofNat (2^240-1)), (n 0), (n 3), (a 8)] ++ rest

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
  at1792 : MachineState.readWord mem 1792 = (b 0)
  at1824 : MachineState.readWord mem 1824 = (b 1)
  at1856 : MachineState.readWord mem 1856 = (b 2)
  at1888 : MachineState.readWord mem 1888 = (b 3)
  at1920 : MachineState.readWord mem 1920 = (b 4)
  at1952 : MachineState.readWord mem 1952 = (b 5)
  at1984 : MachineState.readWord mem 1984 = (b 6)
  at2016 : MachineState.readWord mem 2016 = (b 7)
  at2048 : MachineState.readWord mem 2048 = (b 8)
  at192 : MachineState.readWord mem 192 = (productQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (productQ3 inv a b n)

def frame4 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(b 1), (a 4), (((b 2) * (a 3)) + (((b 3) * (a 2)) + (((b 4) * (a 1)) + (((b 5) * (a 0)) + (productC5 inv a b n))))), (a 4), P, ((UInt256.mulMod (b 2) (a 3) P) + ((UInt256.mulMod (b 3) (a 2) P) + ((UInt256.mulMod (b 4) (a 1) P) + ((UInt256.mulMod (b 5) (a 0) P) + (productC5 inv a b n))))), (b 1), (n 2), (n 6), (n 4), (a 1), (a 2), (n 5), (productQ1 inv a b n), P, (productQ0 inv a b n), (n 1), (UInt256.ofNat (2^240-1)), (n 0), (n 3), (a 8)] ++ rest

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
  at1792 : MachineState.readWord mem 1792 = (b 0)
  at1824 : MachineState.readWord mem 1824 = (b 1)
  at1856 : MachineState.readWord mem 1856 = (b 2)
  at1888 : MachineState.readWord mem 1888 = (b 3)
  at1920 : MachineState.readWord mem 1920 = (b 4)
  at1952 : MachineState.readWord mem 1952 = (b 5)
  at1984 : MachineState.readWord mem 1984 = (b 6)
  at2016 : MachineState.readWord mem 2016 = (b 7)
  at2048 : MachineState.readWord mem 2048 = (b 8)
  at192 : MachineState.readWord mem 192 = (productQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (productQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (productQ4 inv a b n)

def frame5 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [((b 5) * (a 1)), (((b 6) * (a 0)) + (productC6 inv a b n)), (a 1), P, ((UInt256.mulMod (b 6) (a 0) P) + (productC6 inv a b n)), (b 5), (n 2), (n 6), (n 4), (a 1), (a 2), (n 5), (productQ1 inv a b n), P, (productQ0 inv a b n), (n 1), (UInt256.ofNat (2^240-1)), (n 0), (n 3), (a 8)] ++ rest

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
  at1792 : MachineState.readWord mem 1792 = (b 0)
  at1824 : MachineState.readWord mem 1824 = (b 1)
  at1856 : MachineState.readWord mem 1856 = (b 2)
  at1888 : MachineState.readWord mem 1888 = (b 3)
  at1920 : MachineState.readWord mem 1920 = (b 4)
  at1952 : MachineState.readWord mem 1952 = (b 5)
  at1984 : MachineState.readWord mem 1984 = (b 6)
  at2016 : MachineState.readWord mem 2016 = (b 7)
  at2048 : MachineState.readWord mem 2048 = (b 8)
  at192 : MachineState.readWord mem 192 = (productQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (productQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (productQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (productQ5 inv a b n)

def frame6 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(n 4), P, ((UInt256.mulMod (productQ1 inv a b n) (n 5) P) + ((UInt256.mulMod (productQ0 inv a b n) (n 6) P) + ((UInt256.mulMod (b 0) (a 6) P) + ((UInt256.mulMod (b 1) (a 5) P) + ((UInt256.mulMod (b 2) (a 4) P) + ((UInt256.mulMod (b 3) (a 3) P) + ((UInt256.mulMod (b 4) (a 2) P) + ((UInt256.mulMod (b 5) (a 1) P) + ((UInt256.mulMod (b 6) (a 0) P) + (productC6 inv a b n)))))))))), (((productQ5 inv a b n) * (n 1)) + (((productQ4 inv a b n) * (n 2)) + (((productQ3 inv a b n) * (n 3)) + (((productQ2 inv a b n) * (n 4)) + (((productQ1 inv a b n) * (n 5)) + (((productQ0 inv a b n) * (n 6)) + (((b 0) * (a 6)) + (((b 1) * (a 5)) + (((b 2) * (a 4)) + (((b 3) * (a 3)) + (((b 4) * (a 2)) + (((b 5) * (a 1)) + (((b 6) * (a 0)) + (productC6 inv a b n)))))))))))))), (n 2), (n 6), (n 4), (a 1), (a 2), (n 5), (productQ1 inv a b n), P, (productQ0 inv a b n), (n 1), (UInt256.ofNat (2^240-1)), (n 0), (n 3), (a 8)] ++ rest

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
  at1792 : MachineState.readWord mem 1792 = (b 0)
  at1824 : MachineState.readWord mem 1824 = (b 1)
  at1856 : MachineState.readWord mem 1856 = (b 2)
  at1888 : MachineState.readWord mem 1888 = (b 3)
  at1920 : MachineState.readWord mem 1920 = (b 4)
  at1952 : MachineState.readWord mem 1952 = (b 5)
  at1984 : MachineState.readWord mem 1984 = (b 6)
  at2016 : MachineState.readWord mem 2016 = (b 7)
  at2048 : MachineState.readWord mem 2048 = (b 8)
  at192 : MachineState.readWord mem 192 = (productQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (productQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (productQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (productQ5 inv a b n)

def frame7 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(((b 3) * (a 4)) + (((b 4) * (a 3)) + (((b 5) * (a 2)) + (((b 6) * (a 1)) + (((b 7) * (a 0)) + (productC7 inv a b n)))))), (a 4), P, ((UInt256.mulMod (b 4) (a 3) P) + ((UInt256.mulMod (b 5) (a 2) P) + ((UInt256.mulMod (b 6) (a 1) P) + ((UInt256.mulMod (b 7) (a 0) P) + (productC7 inv a b n))))), (productQ1 inv a b n), (b 3), (n 2), (n 6), (n 4), (a 1), (a 2), (n 5), (n 7), P, (productQ0 inv a b n), (n 1), (UInt256.ofNat (2^240-1)), (n 0), (n 3), (a 8)] ++ rest

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
  at1792 : MachineState.readWord mem 1792 = (b 0)
  at1824 : MachineState.readWord mem 1824 = (b 1)
  at1856 : MachineState.readWord mem 1856 = (b 2)
  at1888 : MachineState.readWord mem 1888 = (b 3)
  at1920 : MachineState.readWord mem 1920 = (b 4)
  at1952 : MachineState.readWord mem 1952 = (b 5)
  at1984 : MachineState.readWord mem 1984 = (b 6)
  at2016 : MachineState.readWord mem 2016 = (b 7)
  at2048 : MachineState.readWord mem 2048 = (b 8)
  at192 : MachineState.readWord mem 192 = (productQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (productQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (productQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (productQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (productQ6 inv a b n)

def frame8 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [P, ((UInt256.mulMod (productQ4 inv a b n) (n 3) P) + ((UInt256.mulMod (productQ3 inv a b n) (n 4) P) + ((UInt256.mulMod (productQ2 inv a b n) (n 5) P) + ((UInt256.mulMod (productQ1 inv a b n) (n 6) P) + ((UInt256.mulMod (n 7) (productQ0 inv a b n) P) + ((UInt256.mulMod (b 0) (a 7) P) + ((UInt256.mulMod (b 1) (a 6) P) + ((UInt256.mulMod (b 2) (a 5) P) + ((UInt256.mulMod (b 3) (a 4) P) + ((UInt256.mulMod (b 4) (a 3) P) + ((UInt256.mulMod (b 5) (a 2) P) + ((UInt256.mulMod (b 6) (a 1) P) + ((UInt256.mulMod (b 7) (a 0) P) + (productC7 inv a b n)))))))))))))), (((productQ6 inv a b n) * (n 1)) + (((productQ5 inv a b n) * (n 2)) + (((productQ4 inv a b n) * (n 3)) + (((productQ3 inv a b n) * (n 4)) + (((productQ2 inv a b n) * (n 5)) + (((productQ1 inv a b n) * (n 6)) + (((n 7) * (productQ0 inv a b n)) + (((b 0) * (a 7)) + (((b 1) * (a 6)) + (((b 2) * (a 5)) + (((b 3) * (a 4)) + (((b 4) * (a 3)) + (((b 5) * (a 2)) + (((b 6) * (a 1)) + (((b 7) * (a 0)) + (productC7 inv a b n)))))))))))))))), (n 2), (n 6), (n 4), (a 1), (a 2), (n 5), (n 7), P, (productQ0 inv a b n), (n 1), (UInt256.ofNat (2^240-1)), (n 0), (n 3), (a 8)] ++ rest

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
  at1792 : MachineState.readWord mem 1792 = (b 0)
  at1824 : MachineState.readWord mem 1824 = (b 1)
  at1856 : MachineState.readWord mem 1856 = (b 2)
  at1888 : MachineState.readWord mem 1888 = (b 3)
  at1920 : MachineState.readWord mem 1920 = (b 4)
  at1952 : MachineState.readWord mem 1952 = (b 5)
  at1984 : MachineState.readWord mem 1984 = (b 6)
  at2016 : MachineState.readWord mem 2016 = (b 7)
  at2048 : MachineState.readWord mem 2048 = (b 8)
  at192 : MachineState.readWord mem 192 = (productQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (productQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (productQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (productQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (productQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (productQ1 inv a b n)

def frame9 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(a 5), (((b 4) * (a 4)) + (((b 5) * (a 3)) + (((b 6) * (a 2)) + (((b 7) * (a 1)) + (((b 8) * (a 0)) + (productC8 inv a b n)))))), (a 5), P, ((UInt256.mulMod (b 4) (a 4) P) + ((UInt256.mulMod (b 5) (a 3) P) + ((UInt256.mulMod (b 6) (a 2) P) + ((UInt256.mulMod (b 7) (a 1) P) + ((UInt256.mulMod (b 8) (a 0) P) + (productC8 inv a b n)))))), (b 3), (a 8), (n 6), (n 4), (a 1), (a 2), (n 5), (n 7), P, (productQ0 inv a b n), (n 1), (UInt256.ofNat (2^240-1)), (n 0), (n 3), (n 2)] ++ rest

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
  at1792 : MachineState.readWord mem 1792 = (b 0)
  at1824 : MachineState.readWord mem 1824 = (b 1)
  at1856 : MachineState.readWord mem 1856 = (b 2)
  at1888 : MachineState.readWord mem 1888 = (b 3)
  at1920 : MachineState.readWord mem 1920 = (b 4)
  at1952 : MachineState.readWord mem 1952 = (b 5)
  at1984 : MachineState.readWord mem 1984 = (b 6)
  at2016 : MachineState.readWord mem 2016 = (b 7)
  at2048 : MachineState.readWord mem 2048 = (b 8)
  at192 : MachineState.readWord mem 192 = (productQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (productQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (productQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (productQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (productQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (productQ1 inv a b n)
  at1280 : MachineState.readWord mem 1280 = (productQ7 inv a b n)

def frame10 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(UInt256.mulMod (n 6) (productQ2 inv a b n) P), ((UInt256.mulMod (n 7) (productQ1 inv a b n) P) + ((UInt256.mulMod (n 8) (productQ0 inv a b n) P) + ((UInt256.mulMod (b 0) (a 8) P) + ((UInt256.mulMod (b 1) (a 7) P) + ((UInt256.mulMod (b 2) (a 6) P) + ((UInt256.mulMod (b 3) (a 5) P) + ((UInt256.mulMod (b 4) (a 4) P) + ((UInt256.mulMod (b 5) (a 3) P) + ((UInt256.mulMod (b 6) (a 2) P) + ((UInt256.mulMod (b 7) (a 1) P) + ((UInt256.mulMod (b 8) (a 0) P) + (productC8 inv a b n)))))))))))), (((n 1) * (productQ7 inv a b n)) + (((productQ6 inv a b n) * (n 2)) + (((n 3) * (productQ5 inv a b n)) + (((n 4) * (productQ4 inv a b n)) + (((n 5) * (productQ3 inv a b n)) + (((n 6) * (productQ2 inv a b n)) + (((n 7) * (productQ1 inv a b n)) + (((n 8) * (productQ0 inv a b n)) + (((b 0) * (a 8)) + (((b 1) * (a 7)) + (((b 2) * (a 6)) + (((b 3) * (a 5)) + (((b 4) * (a 4)) + (((b 5) * (a 3)) + (((b 6) * (a 2)) + (((b 7) * (a 1)) + (((b 8) * (a 0)) + (productC8 inv a b n)))))))))))))))))), (a 8), (n 6), (n 4), (a 1), (a 2), (n 5), (n 7), P, (n 8), (n 1), (UInt256.ofNat (2^240-1)), (n 0), (n 3), (n 2)] ++ rest

structure Memory10 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
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
  at1792 : MachineState.readWord mem 1792 = (b 0)
  at1824 : MachineState.readWord mem 1824 = (b 1)
  at1856 : MachineState.readWord mem 1856 = (b 2)
  at1888 : MachineState.readWord mem 1888 = (b 3)
  at1920 : MachineState.readWord mem 1920 = (b 4)
  at1952 : MachineState.readWord mem 1952 = (b 5)
  at1984 : MachineState.readWord mem 1984 = (b 6)
  at2016 : MachineState.readWord mem 2016 = (b 7)
  at2048 : MachineState.readWord mem 2048 = (b 8)
  at192 : MachineState.readWord mem 192 = (productQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (productQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (productQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (productQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (productQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (productQ1 inv a b n)
  at1280 : MachineState.readWord mem 1280 = (productQ7 inv a b n)

def frame11 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(b 4), (a 5), P, ((UInt256.mulMod (b 5) (a 4) P) + ((UInt256.mulMod (b 6) (a 3) P) + ((UInt256.mulMod (b 7) (a 2) P) + ((UInt256.mulMod (b 8) (a 1) P) + (productC9 inv a b n))))), (((b 5) * (a 4)) + (((b 6) * (a 3)) + (((b 7) * (a 2)) + (((b 8) * (a 1)) + (productC9 inv a b n))))), (a 8), (n 6), (n 4), (productQ6 inv a b n), (a 2), (n 5), (n 7), P, (n 8), (n 1), (UInt256.ofNat (2^240-1)), (productQ8 inv a b n), (n 3), (n 2)] ++ rest

structure Memory11 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
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
  at1792 : MachineState.readWord mem 1792 = (b 0)
  at1824 : MachineState.readWord mem 1824 = (b 1)
  at1856 : MachineState.readWord mem 1856 = (b 2)
  at1888 : MachineState.readWord mem 1888 = (b 3)
  at1920 : MachineState.readWord mem 1920 = (b 4)
  at1952 : MachineState.readWord mem 1952 = (b 5)
  at1984 : MachineState.readWord mem 1984 = (b 6)
  at2016 : MachineState.readWord mem 2016 = (b 7)
  at2048 : MachineState.readWord mem 2048 = (b 8)
  at192 : MachineState.readWord mem 192 = (productQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (productQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (productQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (productQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (productQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (productQ1 inv a b n)
  at1280 : MachineState.readWord mem 1280 = (productQ7 inv a b n)

def frame12 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(n 5), (productQ4 inv a b n), P, ((UInt256.mulMod (n 6) (productQ3 inv a b n) P) + ((UInt256.mulMod (n 7) (productQ2 inv a b n) P) + ((UInt256.mulMod (n 8) (productQ1 inv a b n) P) + ((UInt256.mulMod (b 1) (a 8) P) + ((UInt256.mulMod (b 2) (a 7) P) + ((UInt256.mulMod (b 3) (a 6) P) + ((UInt256.mulMod (b 4) (a 5) P) + ((UInt256.mulMod (b 5) (a 4) P) + ((UInt256.mulMod (b 6) (a 3) P) + ((UInt256.mulMod (b 7) (a 2) P) + ((UInt256.mulMod (b 8) (a 1) P) + (productC9 inv a b n)))))))))))), (((n 1) * (productQ8 inv a b n)) + (((productQ7 inv a b n) * (n 2)) + (((n 3) * (productQ6 inv a b n)) + (((n 4) * (productQ5 inv a b n)) + (((n 5) * (productQ4 inv a b n)) + (((n 6) * (productQ3 inv a b n)) + (((n 7) * (productQ2 inv a b n)) + (((n 8) * (productQ1 inv a b n)) + (((b 1) * (a 8)) + (((b 2) * (a 7)) + (((b 3) * (a 6)) + (((b 4) * (a 5)) + (((b 5) * (a 4)) + (((b 6) * (a 3)) + (((b 7) * (a 2)) + (((b 8) * (a 1)) + (productC9 inv a b n))))))))))))))))), (a 8), (n 6), (n 4), (productQ6 inv a b n), (a 2), (n 5), (n 7), P, (n 8), (n 1), (UInt256.ofNat (2^240-1)), (productQ8 inv a b n), (n 3), (n 2)] ++ rest

structure Memory12 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
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
  at1792 : MachineState.readWord mem 1792 = (b 0)
  at1824 : MachineState.readWord mem 1824 = (b 1)
  at1856 : MachineState.readWord mem 1856 = (b 2)
  at1888 : MachineState.readWord mem 1888 = (b 3)
  at1920 : MachineState.readWord mem 1920 = (b 4)
  at1952 : MachineState.readWord mem 1952 = (b 5)
  at1984 : MachineState.readWord mem 1984 = (b 6)
  at2016 : MachineState.readWord mem 2016 = (b 7)
  at2048 : MachineState.readWord mem 2048 = (b 8)
  at192 : MachineState.readWord mem 192 = (productQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (productQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (productQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (productQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (productQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (productQ1 inv a b n)
  at1280 : MachineState.readWord mem 1280 = (productQ7 inv a b n)

def frame13 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(a 6), P, ((UInt256.mulMod (b 5) (a 5) P) + ((UInt256.mulMod (b 6) (a 4) P) + ((UInt256.mulMod (b 7) (a 3) P) + ((UInt256.mulMod (a 2) (b 8) P) + (productC10 inv a b n))))), (((b 5) * (a 5)) + (((b 6) * (a 4)) + (((b 7) * (a 3)) + (((a 2) * (b 8)) + (productC10 inv a b n))))), (a 8), (n 6), (n 4), (productQ6 inv a b n), (productQ5 inv a b n), (n 5), (n 7), P, (n 8), (productQ7 inv a b n), (UInt256.ofNat (2^240-1)), (productQ8 inv a b n), (n 3), (n 2)] ++ rest

structure Memory13 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (productD0 inv a b n)
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
  at1792 : MachineState.readWord mem 1792 = (b 0)
  at1824 : MachineState.readWord mem 1824 = (b 1)
  at1856 : MachineState.readWord mem 1856 = (b 2)
  at1888 : MachineState.readWord mem 1888 = (b 3)
  at1920 : MachineState.readWord mem 1920 = (b 4)
  at1952 : MachineState.readWord mem 1952 = (b 5)
  at1984 : MachineState.readWord mem 1984 = (b 6)
  at2016 : MachineState.readWord mem 2016 = (b 7)
  at2048 : MachineState.readWord mem 2048 = (b 8)
  at192 : MachineState.readWord mem 192 = (productQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (productQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (productQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (productQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (productQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (productQ1 inv a b n)
  at1280 : MachineState.readWord mem 1280 = (productQ7 inv a b n)

def frame14 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [((UInt256.mulMod (productQ8 inv a b n) (n 2) P) + ((UInt256.mulMod (productQ7 inv a b n) (n 3) P) + ((UInt256.mulMod (n 4) (productQ6 inv a b n) P) + ((UInt256.mulMod (n 5) (productQ5 inv a b n) P) + ((UInt256.mulMod (n 6) (productQ4 inv a b n) P) + ((UInt256.mulMod (n 7) (productQ3 inv a b n) P) + ((UInt256.mulMod (n 8) (productQ2 inv a b n) P) + ((UInt256.mulMod (b 2) (a 8) P) + ((UInt256.mulMod (b 3) (a 7) P) + ((UInt256.mulMod (b 4) (a 6) P) + ((UInt256.mulMod (b 5) (a 5) P) + ((UInt256.mulMod (b 6) (a 4) P) + ((UInt256.mulMod (b 7) (a 3) P) + ((UInt256.mulMod (a 2) (b 8) P) + (productC10 inv a b n))))))))))))))), (((productQ8 inv a b n) * (n 2)) + (((n 3) * (productQ7 inv a b n)) + (((n 4) * (productQ6 inv a b n)) + (((n 5) * (productQ5 inv a b n)) + (((n 6) * (productQ4 inv a b n)) + (((n 7) * (productQ3 inv a b n)) + (((n 8) * (productQ2 inv a b n)) + (((b 2) * (a 8)) + (((b 3) * (a 7)) + (((b 4) * (a 6)) + (((b 5) * (a 5)) + (((b 6) * (a 4)) + (((b 7) * (a 3)) + (((a 2) * (b 8)) + (productC10 inv a b n))))))))))))))), (a 8), (n 6), (n 4), (productQ6 inv a b n), (productQ5 inv a b n), (n 5), (n 7), P, (n 8), (productQ7 inv a b n), (UInt256.ofNat (2^240-1)), (productQ8 inv a b n), (n 3), (n 2)] ++ rest

structure Memory14 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (productD0 inv a b n)
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
  at1792 : MachineState.readWord mem 1792 = (b 0)
  at1824 : MachineState.readWord mem 1824 = (b 1)
  at1856 : MachineState.readWord mem 1856 = (b 2)
  at1888 : MachineState.readWord mem 1888 = (b 3)
  at1920 : MachineState.readWord mem 1920 = (b 4)
  at1952 : MachineState.readWord mem 1952 = (b 5)
  at1984 : MachineState.readWord mem 1984 = (b 6)
  at2016 : MachineState.readWord mem 2016 = (b 7)
  at2048 : MachineState.readWord mem 2048 = (b 8)
  at192 : MachineState.readWord mem 192 = (productQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (productQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (productQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (productQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (productQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (productQ1 inv a b n)
  at1280 : MachineState.readWord mem 1280 = (productQ7 inv a b n)

def frame15 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(productQ7 inv a b n), (((n 5) * (productQ6 inv a b n)) + (((n 6) * (productQ5 inv a b n)) + (((n 7) * (productQ4 inv a b n)) + (((n 8) * (productQ3 inv a b n)) + (((b 3) * (a 8)) + (((b 4) * (a 7)) + (((b 5) * (a 6)) + (((b 6) * (a 5)) + (((b 7) * (a 4)) + (((b 8) * (a 3)) + (productC11 inv a b n))))))))))), ((UInt256.mulMod (b 3) (a 8) P) + ((UInt256.mulMod (b 4) (a 7) P) + ((UInt256.mulMod (b 5) (a 6) P) + ((UInt256.mulMod (b 6) (a 5) P) + ((UInt256.mulMod (b 7) (a 4) P) + ((UInt256.mulMod (b 8) (a 3) P) + (productC11 inv a b n))))))), (a 8), (n 6), (n 4), (productQ6 inv a b n), (productQ5 inv a b n), (n 5), (n 7), P, (n 8), (productQ7 inv a b n), (UInt256.ofNat (2^240-1)), (productQ8 inv a b n), (n 3), (n 2)] ++ rest

structure Memory15 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (productD0 inv a b n)
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
  at1792 : MachineState.readWord mem 1792 = (b 0)
  at1824 : MachineState.readWord mem 1824 = (b 1)
  at1856 : MachineState.readWord mem 1856 = (b 2)
  at1888 : MachineState.readWord mem 1888 = (b 3)
  at1920 : MachineState.readWord mem 1920 = (b 4)
  at1952 : MachineState.readWord mem 1952 = (b 5)
  at1984 : MachineState.readWord mem 1984 = (b 6)
  at2016 : MachineState.readWord mem 2016 = (b 7)
  at2048 : MachineState.readWord mem 2048 = (b 8)
  at192 : MachineState.readWord mem 192 = (productQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (productQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (productQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (productQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (productQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (productQ1 inv a b n)
  at1280 : MachineState.readWord mem 1280 = (productQ7 inv a b n)
  at800 : MachineState.readWord mem 800 = (productD1 inv a b n)

def frame16 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [((UInt256.mulMod (b 5) (a 7) P) + ((UInt256.mulMod (b 6) (a 6) P) + ((UInt256.mulMod (b 7) (a 5) P) + ((UInt256.mulMod (b 8) (a 4) P) + (productC12 inv a b n))))), (((b 5) * (a 7)) + (((b 6) * (a 6)) + (((b 7) * (a 5)) + (((b 8) * (a 4)) + (productC12 inv a b n))))), (a 8), (n 6), (n 4), (productQ6 inv a b n), (productQ5 inv a b n), (n 5), (n 7), P, (n 8), (productQ7 inv a b n), (UInt256.ofNat (2^240-1)), (productQ8 inv a b n), (n 3), (n 2)] ++ rest

structure Memory16 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (productD0 inv a b n)
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
  at1792 : MachineState.readWord mem 1792 = (b 0)
  at1824 : MachineState.readWord mem 1824 = (b 1)
  at1856 : MachineState.readWord mem 1856 = (b 2)
  at1888 : MachineState.readWord mem 1888 = (b 3)
  at1920 : MachineState.readWord mem 1920 = (b 4)
  at1952 : MachineState.readWord mem 1952 = (b 5)
  at1984 : MachineState.readWord mem 1984 = (b 6)
  at2016 : MachineState.readWord mem 2016 = (b 7)
  at2048 : MachineState.readWord mem 2048 = (b 8)
  at192 : MachineState.readWord mem 192 = (productQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (productQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (productQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (productQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (productQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (productQ1 inv a b n)
  at1280 : MachineState.readWord mem 1280 = (productQ7 inv a b n)
  at800 : MachineState.readWord mem 800 = (productD1 inv a b n)
  at832 : MachineState.readWord mem 832 = (productD2 inv a b n)

def frame17 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(((b 7) * (a 6)) + (((b 8) * (a 5)) + (productC13 inv a b n))), (a 7), P, ((UInt256.mulMod (b 7) (a 6) P) + ((UInt256.mulMod (b 8) (a 5) P) + (productC13 inv a b n))), (b 6), (a 8), (n 6), (n 4), (productQ6 inv a b n), (productQ5 inv a b n), (n 5), (n 7), P, (n 8), (productQ7 inv a b n), (UInt256.ofNat (2^240-1)), (productQ8 inv a b n), (n 3), (n 2)] ++ rest

structure Memory17 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (productD0 inv a b n)
  at1344 : MachineState.readWord mem 1344 = (n 0)
  at1376 : MachineState.readWord mem 1376 = (n 1)
  at2720 : MachineState.readWord mem 2720 = inv
  at1568 : MachineState.readWord mem 1568 = (n 7)
  at1600 : MachineState.readWord mem 1600 = (n 8)
  at32 : MachineState.readWord mem 32 = (productD3 inv a b n)
  at64 : MachineState.readWord mem 64 = (a 4)
  at96 : MachineState.readWord mem 96 = (a 5)
  at128 : MachineState.readWord mem 128 = (a 6)
  at160 : MachineState.readWord mem 160 = (a 7)
  at1792 : MachineState.readWord mem 1792 = (b 0)
  at1824 : MachineState.readWord mem 1824 = (b 1)
  at1856 : MachineState.readWord mem 1856 = (b 2)
  at1888 : MachineState.readWord mem 1888 = (b 3)
  at1920 : MachineState.readWord mem 1920 = (b 4)
  at1952 : MachineState.readWord mem 1952 = (b 5)
  at1984 : MachineState.readWord mem 1984 = (b 6)
  at2016 : MachineState.readWord mem 2016 = (b 7)
  at2048 : MachineState.readWord mem 2048 = (b 8)
  at192 : MachineState.readWord mem 192 = (productQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (productQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (productQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (productQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (productQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (productQ1 inv a b n)
  at1280 : MachineState.readWord mem 1280 = (productQ7 inv a b n)
  at800 : MachineState.readWord mem 800 = (productD1 inv a b n)
  at832 : MachineState.readWord mem 832 = (productD2 inv a b n)

def frame18 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(b 6), (a 8), (((b 7) * (a 7)) + (((b 8) * (a 6)) + (productC14 inv a b n))), (a 8), P, ((UInt256.mulMod (b 7) (a 7) P) + ((UInt256.mulMod (b 8) (a 6) P) + (productC14 inv a b n))), (b 6), (a 8), (n 6), (n 4), (productQ6 inv a b n), (productD2 inv a b n), (n 5), (n 7), P, (n 8), (productQ7 inv a b n), (UInt256.ofNat (2^240-1)), (productQ8 inv a b n), (n 3), (n 2)] ++ rest

structure Memory18 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (productD0 inv a b n)
  at1344 : MachineState.readWord mem 1344 = (n 0)
  at1376 : MachineState.readWord mem 1376 = (n 1)
  at2720 : MachineState.readWord mem 2720 = inv
  at1568 : MachineState.readWord mem 1568 = (n 7)
  at1600 : MachineState.readWord mem 1600 = (n 8)
  at32 : MachineState.readWord mem 32 = (productD3 inv a b n)
  at64 : MachineState.readWord mem 64 = (productD4 inv a b n)
  at96 : MachineState.readWord mem 96 = (a 5)
  at128 : MachineState.readWord mem 128 = (a 6)
  at160 : MachineState.readWord mem 160 = (a 7)
  at1792 : MachineState.readWord mem 1792 = (b 0)
  at1824 : MachineState.readWord mem 1824 = (b 1)
  at1856 : MachineState.readWord mem 1856 = (b 2)
  at1888 : MachineState.readWord mem 1888 = (b 3)
  at1920 : MachineState.readWord mem 1920 = (b 4)
  at1952 : MachineState.readWord mem 1952 = (b 5)
  at1984 : MachineState.readWord mem 1984 = (b 6)
  at2016 : MachineState.readWord mem 2016 = (b 7)
  at2048 : MachineState.readWord mem 2048 = (b 8)
  at192 : MachineState.readWord mem 192 = (productQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (productQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (productQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (productQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (productQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (productQ1 inv a b n)
  at1280 : MachineState.readWord mem 1280 = (productQ7 inv a b n)
  at800 : MachineState.readWord mem 800 = (productD1 inv a b n)
  at832 : MachineState.readWord mem 832 = (productD2 inv a b n)

def frame19 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(productC16 inv a b n), (b 8), (a 8), (n 6), (n 4), (productD1 inv a b n), (productD2 inv a b n), (n 5), (n 7), P, (n 8), (productQ7 inv a b n), (UInt256.ofNat (2^240-1)), (productQ8 inv a b n), (n 3), (n 2)] ++ rest

structure Memory19 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (productD0 inv a b n)
  at1344 : MachineState.readWord mem 1344 = (n 0)
  at1376 : MachineState.readWord mem 1376 = (n 1)
  at2720 : MachineState.readWord mem 2720 = inv
  at1568 : MachineState.readWord mem 1568 = (n 7)
  at1600 : MachineState.readWord mem 1600 = (n 8)
  at32 : MachineState.readWord mem 32 = (productD3 inv a b n)
  at64 : MachineState.readWord mem 64 = (productD4 inv a b n)
  at96 : MachineState.readWord mem 96 = (productD5 inv a b n)
  at128 : MachineState.readWord mem 128 = (productD6 inv a b n)
  at160 : MachineState.readWord mem 160 = (a 7)
  at1792 : MachineState.readWord mem 1792 = (b 0)
  at1824 : MachineState.readWord mem 1824 = (b 1)
  at1856 : MachineState.readWord mem 1856 = (b 2)
  at1888 : MachineState.readWord mem 1888 = (b 3)
  at1920 : MachineState.readWord mem 1920 = (b 4)
  at1952 : MachineState.readWord mem 1952 = (b 5)
  at1984 : MachineState.readWord mem 1984 = (b 6)
  at2016 : MachineState.readWord mem 2016 = (b 7)
  at2048 : MachineState.readWord mem 2048 = (b 8)
  at192 : MachineState.readWord mem 192 = (productQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (productQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (productQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (productQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (productQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (productQ1 inv a b n)
  at1280 : MachineState.readWord mem 1280 = (productQ7 inv a b n)
  at800 : MachineState.readWord mem 800 = (productD1 inv a b n)
  at832 : MachineState.readWord mem 832 = (productD2 inv a b n)

def frame20 (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : List UInt256 :=
  [(n 2), (n 6), (n 4), (productD1 inv a b n), (productD2 inv a b n), (n 5), (n 7), P, (n 8), (productQ7 inv a b n), (UInt256.ofNat (2^240-1)), (productQ8 inv a b n), (n 3), (productC17 inv a b n)] ++ rest

structure Memory20 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
  at768 : MachineState.readWord mem 768 = (productD0 inv a b n)
  at1344 : MachineState.readWord mem 1344 = (n 0)
  at1376 : MachineState.readWord mem 1376 = (n 1)
  at2720 : MachineState.readWord mem 2720 = inv
  at1568 : MachineState.readWord mem 1568 = (n 7)
  at1600 : MachineState.readWord mem 1600 = (n 8)
  at32 : MachineState.readWord mem 32 = (productD3 inv a b n)
  at64 : MachineState.readWord mem 64 = (productD4 inv a b n)
  at96 : MachineState.readWord mem 96 = (productD5 inv a b n)
  at128 : MachineState.readWord mem 128 = (productD6 inv a b n)
  at160 : MachineState.readWord mem 160 = (productD7 inv a b n)
  at1792 : MachineState.readWord mem 1792 = (b 0)
  at1824 : MachineState.readWord mem 1824 = (b 1)
  at1856 : MachineState.readWord mem 1856 = (b 2)
  at1888 : MachineState.readWord mem 1888 = (b 3)
  at1920 : MachineState.readWord mem 1920 = (b 4)
  at1952 : MachineState.readWord mem 1952 = (b 5)
  at1984 : MachineState.readWord mem 1984 = (b 6)
  at2016 : MachineState.readWord mem 2016 = (b 7)
  at2048 : MachineState.readWord mem 2048 = (b 8)
  at192 : MachineState.readWord mem 192 = (productQ2 inv a b n)
  at0 : MachineState.readWord mem 0 = (productQ3 inv a b n)
  at224 : MachineState.readWord mem 224 = (productQ4 inv a b n)
  at1216 : MachineState.readWord mem 1216 = (productQ5 inv a b n)
  at1248 : MachineState.readWord mem 1248 = (productQ6 inv a b n)
  at1088 : MachineState.readWord mem 1088 = (productQ1 inv a b n)
  at1280 : MachineState.readWord mem 1280 = (productQ7 inv a b n)
  at800 : MachineState.readWord mem 800 = (productD1 inv a b n)
  at832 : MachineState.readWord mem 832 = (productD2 inv a b n)

end CycleSubmission.ProductMeaning
