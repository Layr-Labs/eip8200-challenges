import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowTrace

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNWhole

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof WindowNineBinding MonproKNRowPaths MonproKNLoopPaths
open MonproKNRowFrames MonproKNCache
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

/-- The first n-1 complete rows, leaving the final row for its different exit. -/
def rows {artifact : ProgramArtifact} {fork : Fork}
    (paths : RowPaths artifact fork) (l1paths : L1Paths artifact fork)
    (l2paths : L2Paths artifact fork)
    (s : State) (mem : ByteArray) (pa pb n : Nat) (dst ret : UInt256)
    (rest : List UInt256) (env : Environment artifact fork s)
    (hcap : rest.length ≤ 1007) (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224+32*n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32*n-32)) :
    GasSteps (outer s mem pa pb n 0 dst ret rest)
      (outer s (rowsMem mem pa pb n (n-1)) pa pb n (n-1) dst ret rest) :=
  GasSteps.iterateBounded
    (I := fun i => outer s (rowsMem mem pa pb n i) pa pb n i dst ret rest) (n-1)
    (fun i hi => MonproKNRowTrace.rowNext paths l1paths l2paths
      s (rowsMem mem pa pb n i) pa pb n i dst ret rest env hcap hact
      hn hn32 (by omega) hpa hpaFit hpb hpbFit
      ((readWord_rowsMem mem pa pb n 9344 hn32 (by omega) i).trans hs32)
      ((readWord_rowsMem mem pa pb n 9440 hn32 (by omega) i).trans htl)
      ((readWord_rowsMem mem pa pb n 9408 hn32 (by omega) i).trans hml))

/-- The real EVM relation from entry through every row to the unchanged CSUB frame. -/
def toCsub {artifact : ProgramArtifact} {fork : Fork}
    (paths : RowPaths artifact fork) (l1paths : L1Paths artifact fork)
    (l2paths : L2Paths artifact fork)
    (s : State) (mem : ByteArray) (pa pb n : Nat) (dst ret : UInt256)
    (rest : List UInt256) (env : Environment artifact fork s)
    (hcap : rest.length ≤ 1007) (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224+32*n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32*n-32)) :
    GasSteps (entry s mem pa pb dst ret rest)
      (csub s (rowsMem (mpZeroed s mem n) pa pb n n) dst ret rest) := by
  let zeroed := mpZeroed s mem n
  have hsZ : MachineState.readWord zeroed 9344 = UInt256.ofNat (32*n) :=
    (readWord_mpZeroed s mem n 9344 hn32 (by omega)).trans hs32
  have htZ : MachineState.readWord zeroed 9440 = UInt256.ofNat (8224+32*n) :=
    (readWord_mpZeroed s mem n 9440 hn32 (by omega)).trans htl
  have hmZ : MachineState.readWord zeroed 9408 = UInt256.ofNat (32*n-32) :=
    (readWord_mpZeroed s mem n 9408 hn32 (by omega)).trans hml
  have last := MonproKNRowTrace.rowLast paths l1paths l2paths
    s (rowsMem zeroed pa pb n (n-1)) pa pb n (n-1) dst ret rest env hcap hact
    hn hn32 (by omega) hpa hpaFit hpb hpbFit
    ((readWord_rowsMem zeroed pa pb n 9344 hn32 (by omega) (n-1)).trans hsZ)
    ((readWord_rowsMem zeroed pa pb n 9440 hn32 (by omega) (n-1)).trans htZ)
    ((readWord_rowsMem zeroed pa pb n 9408 hn32 (by omega) (n-1)).trans hmZ)
  change GasSteps (outer s (rowsMem zeroed pa pb n (n-1)) pa pb n (n-1) dst ret rest)
    (csub s (rowsMem zeroed pa pb n ((n-1)+1)) dst ret rest) at last
  rw [show n-1+1 = n by omega] at last
  exact (MonproKNRowGas.entryGas paths s mem pa pb n dst ret rest env hcap hact hn32
    hpa hpaFit hpb hpbFit hcds hs32).trans
    ((rows paths l1paths l2paths s zeroed pa pb n dst ret rest env hcap hact
      hn hn32 hpa hpaFit hpb hpbFit hsZ htZ hmZ).trans last)

/-- Existing Exp callers have the stronger 1000-slot tail bound; no public
input restriction is introduced by the internal cache-bearing frame. -/
def fromExp {artifact : ProgramArtifact} {fork : Fork}
    (paths : RowPaths artifact fork) (l1paths : L1Paths artifact fork)
    (l2paths : L2Paths artifact fork)
    (s : State) (mem : ByteArray) (pa pb n : Nat) (dst ret : UInt256)
    (rest : List UInt256) (env : Environment artifact fork s)
    (hcap : rest.length ≤ 1000) (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224+32*n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32*n-32)) :
    GasSteps (entry s mem pa pb dst ret rest)
      (csub s (rowsMem (mpZeroed s mem n) pa pb n n) dst ret rest) :=
  toCsub paths l1paths l2paths s mem pa pb n dst ret rest env (by omega)
    hact hn hn32 hpa hpaFit hpb hpbFit hcds hs32 htl hml

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNWhole
