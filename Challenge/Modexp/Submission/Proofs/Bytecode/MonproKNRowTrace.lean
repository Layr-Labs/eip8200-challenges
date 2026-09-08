import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowGas
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNL1Run
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNL2Run
import Challenge.Modexp.Submission.Proofs.Fast.MonproPreserveModel

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowTrace

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof WindowNineBinding MonproKNRowPaths MonproKNLoopPaths
open MonproKNRowFrames MonproKNCache
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

def l1Gas {artifact : ProgramArtifact} {fork : Fork}
    (paths : RowPaths artifact fork) (l1paths : L1Paths artifact fork)
    (s : State) (mem : ByteArray) (bi : UInt256) (pa pb n i : Nat)
    (dst ret : UInt256) (rest : List UInt256) (env : Environment artifact fork s)
    (hcap : rest.length ≤ 1007) (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 9472) :
    GasSteps (l1 s mem bi pa pb n i 0 2003 dst ret rest)
      (l1 s mem bi pa pb n i n 2008 dst ret rest) :=
  (MonproKNRowGas.stubGas paths s mem bi pa pb n i 0 dst ret rest env hcap).trans
    (MonproKNL1Run.run l1paths s mem bi pa n
      (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pb-32))
      dst ret rest env hcap hact hn32 hn hpa hpaFit)

def l2Gas {artifact : ProgramArtifact} {fork : Fork} (paths : L2Paths artifact fork)
    (s : State) (mem : ByteArray) (bi mu c0 : UInt256) (pa pb n i : Nat)
    (dst ret : UInt256) (rest : List UInt256) (env : Environment artifact fork s)
    (hcap : rest.length ≤ 1007) (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) :
    GasSteps (l2 s mem bi mu c0 pa pb n i 0 2077 dst ret rest)
      (l2 s mem bi mu c0 pa pb n i (n-1) 2435 dst ret rest) :=
  MonproKNL2Run.run paths s mem bi mu c0 n
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa-32))
    (UInt256.ofNat (pb-32)) dst ret rest env hcap hact hn32 hn

/-- One complete row, with exactly n L1 MACs and n-1 L2 MACs, before its tail. -/
def rowToTail {artifact : ProgramArtifact} {fork : Fork}
    (paths : RowPaths artifact fork) (l1paths : L1Paths artifact fork)
    (l2paths : L2Paths artifact fork)
    (s : State) (mem : ByteArray) (pa pb n i : Nat) (dst ret : UInt256)
    (rest : List UInt256) (env : Environment artifact fork s)
    (hcap : rest.length ≤ 1007) (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hi : i < n)
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224+32*n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32*n-32)) :
    GasSteps (outer s mem pa pb n i dst ret rest)
      (tail s (rowL2 mem pa pb n i).memory
        (UInt256.ofNat (ptrAt (32*n-64) (n-1)))
        (UInt256.ofNat (ptrAt (8192+32*n) (n-1)))
        (rowL2 mem pa pb n i).carry (rowMu (rowL1 mem pa pb n i).memory n)
        (rowBi mem pb n i) pa pb n i dst ret rest) :=
  (MonproKNRowGas.outGas paths s mem pa pb n i dst ret rest env hcap hact
      hn hn32 hi hpa hpaFit hpb hpbFit hs32 htl).trans <|
  (l1Gas paths l1paths s mem (rowBi mem pb n i) pa pb n i dst ret rest
      env hcap hact hn hn32 hpa hpaFit).trans <|
  (MonproKNRowGas.middleGas paths s (rowL1 mem pa pb n i).memory
      (UInt256.ofNat (ptrAt (pa+32*n-32) n))
      (UInt256.ofNat (ptrAt (8224+32*n) n)) (rowL1 mem pa pb n i).carry
      (rowBi mem pb n i) pa pb n i dst ret rest env hcap hact hn hn32
      ((readWord_l1Step mem (rowBi mem pb n i) pa n 9408 n hn32 (by omega)).trans hml)
      ((readWord_l1Step mem (rowBi mem pb n i) pa n 9440 n hn32 (by omega)).trans htl)).trans
  (l2Gas l2paths s (rowMid mem pa pb n i) (rowBi mem pb n i)
      (rowMu (rowL1 mem pa pb n i).memory n)
      (rowC0 (rowL1 mem pa pb n i).memory n) pa pb n i dst ret rest
      env hcap hact hn hn32)

def rowNext {artifact : ProgramArtifact} {fork : Fork}
    (paths : RowPaths artifact fork) (l1paths : L1Paths artifact fork)
    (l2paths : L2Paths artifact fork)
    (s : State) (mem : ByteArray) (pa pb n i : Nat) (dst ret : UInt256)
    (rest : List UInt256) (env : Environment artifact fork s)
    (hcap : rest.length ≤ 1007) (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hi : i+1 < n)
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224+32*n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32*n-32)) :
    GasSteps (outer s mem pa pb n i dst ret rest)
      (outer s (rowMem mem pa pb n i) pa pb n (i+1) dst ret rest) :=
  (rowToTail paths l1paths l2paths s mem pa pb n i dst ret rest env hcap hact
      hn hn32 (by omega) hpa hpaFit hpb hpbFit hs32 htl hml).trans
    (MonproKNRowGas.tailNextGas paths s (rowL2 mem pa pb n i).memory
      (UInt256.ofNat (ptrAt (32*n-64) (n-1)))
      (UInt256.ofNat (ptrAt (8192+32*n) (n-1)))
      (rowL2 mem pa pb n i).carry (rowMu (rowL1 mem pa pb n i).memory n)
      (rowBi mem pb n i) pa pb n i dst ret rest env hcap hact hpb hpbFit hi)

def rowLast {artifact : ProgramArtifact} {fork : Fork}
    (paths : RowPaths artifact fork) (l1paths : L1Paths artifact fork)
    (l2paths : L2Paths artifact fork)
    (s : State) (mem : ByteArray) (pa pb n i : Nat) (dst ret : UInt256)
    (rest : List UInt256) (env : Environment artifact fork s)
    (hcap : rest.length ≤ 1007) (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hi : i+1 = n)
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224+32*n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32*n-32)) :
    GasSteps (outer s mem pa pb n i dst ret rest)
      (csub s (rowMem mem pa pb n i) dst ret rest) :=
  (rowToTail paths l1paths l2paths s mem pa pb n i dst ret rest env hcap hact
      hn hn32 (by omega) hpa hpaFit hpb hpbFit hs32 htl hml).trans <|
  (MonproKNRowGas.tailLastGas paths s (rowL2 mem pa pb n i).memory
      (UInt256.ofNat (ptrAt (32*n-64) (n-1)))
      (UInt256.ofNat (ptrAt (8192+32*n) (n-1)))
      (rowL2 mem pa pb n i).carry (rowMu (rowL1 mem pa pb n i).memory n)
      (rowBi mem pb n i) pa pb n i dst ret rest env hcap hact hpb hpbFit hi).trans
  (MonproKNRowGas.exitGas paths s (rowMem mem pa pb n i)
      (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) pa pb dst ret rest env hcap)

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowTrace
