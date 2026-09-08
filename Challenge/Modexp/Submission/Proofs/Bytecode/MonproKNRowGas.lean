import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNEntry
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMid
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNTailRows

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowGas

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof WindowNineBinding MonproKNRowPaths
open MonproKNRowFrames MonproKNCache
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

def entryGas {artifact : ProgramArtifact} {fork : Fork} (paths : RowPaths artifact fork)
    (s : State) (mem : ByteArray) (pa pb n : Nat) (dst ret : UInt256) (rest : List UInt256)
    (env : Environment artifact fork s) (hcap : rest.length ≤ 1007)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n)) :
    GasSteps (entry s mem pa pb dst ret rest)
      (outer s (mpZeroed s mem n) pa pb n 0 dst ret rest) :=
  paths.entry.steps (env.transfer (t := entry s mem pa pb dst ret rest) rfl rfl) rfl
    (MonproKNEntry.run_entry s mem pa pb n dst ret rest hcap hact hn32
      hpa hpaFit hpb hpbFit hcds hs32)

def outGas {artifact : ProgramArtifact} {fork : Fork} (paths : RowPaths artifact fork)
    (s : State) (mem : ByteArray) (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (env : Environment artifact fork s) (hcap : rest.length ≤ 1007)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32) (hi : i < n)
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224+32*n)) :
    GasSteps (outer s mem pa pb n i dst ret rest)
      (l1 s mem (rowBi mem pb n i) pa pb n i 0 2003 dst ret rest) :=
  paths.out.steps (env.transfer (t := outer s mem pa pb n i dst ret rest) rfl rfl) rfl
    (MonproKNEntryOut.run_out s mem pa pb n i dst ret rest hcap hact hn hn32 hi
      hpa hpaFit hpb hpbFit hs32 htl)

def stubGas {artifact : ProgramArtifact} {fork : Fork} (paths : RowPaths artifact fork)
    (s : State) (mem : ByteArray) (bi : UInt256) (pa pb n i j : Nat)
    (dst ret : UInt256) (rest : List UInt256) (env : Environment artifact fork s)
    (hcap : rest.length ≤ 1007) :
    GasSteps (l1 s mem bi pa pb n i j 2003 dst ret rest)
      (l1 s mem bi pa pb n i j 4070 dst ret rest) := by
  let st := l1 s mem bi pa pb n i j 2003 dst ret rest
  have hstack : st.stack.length+1 < 1024 := by
    simp only [st, l1, List.length_append, List.length_cons, List.length_nil]
    omega
  have ht : Decode.isValidJumpDest st.executionEnv.code 4070 = true := by
    change Decode.isValidJumpDest s.executionEnv.code 4070 = true
    rw [env.code]
    exact paths.l1Jump
  exact paths.stub.steps (env.transfer (t := st) rfl rfl) rfl
    (MonproKNExit.run_stub st st.stack hstack ht)

def middleGas {artifact : ProgramArtifact} {fork : Fork} (paths : RowPaths artifact fork)
    (s : State) (mem : ByteArray) (paj ptj c bi : UInt256) (pa pb n i : Nat)
    (dst ret : UInt256) (rest : List UInt256) (env : Environment artifact fork s)
    (hcap : rest.length ≤ 1007) (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32*n-32))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224+32*n)) :
    GasSteps (middle s mem paj ptj c bi pa pb n i dst ret rest)
      (l2 s (midMem mem c) bi (rowMu mem n) (rowC0 mem n) pa pb n i 0 2077 dst ret rest) :=
  paths.middle.steps
    (env.transfer (t := middle s mem paj ptj c bi pa pb n i dst ret rest) rfl rfl) rfl
    (MonproKNMid.run_middle s mem paj ptj c bi pa pb n i dst ret rest hcap hact hn hn32 hml htl)

def tailNextGas {artifact : ProgramArtifact} {fork : Fork} (paths : RowPaths artifact fork)
    (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256) (pa pb n i : Nat)
    (dst ret : UInt256) (rest : List UInt256) (env : Environment artifact fork s)
    (hcap : rest.length ≤ 1007) (hact : 296 ≤ s.activeWords.toNat)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472) (hi : i+1 < n) :
    GasSteps (tail s mem pmj ptj c mu bi pa pb n i dst ret rest)
      (outer s (tailMem mem c) pa pb n (i+1) dst ret rest) := by
  have ht : Decode.isValidJumpDest s.executionEnv.code 1982 = true := by
    rw [env.code]
    exact paths.outerJump
  exact paths.tail.steps
    (env.transfer (t := tail s mem pmj ptj c mu bi pa pb n i dst ret rest) rfl rfl) rfl
    (MonproKNTailRows.run_next s mem pmj ptj c mu bi pa pb n i dst ret rest
      hcap hact hpb hpbFit hi ht)

def tailLastGas {artifact : ProgramArtifact} {fork : Fork} (paths : RowPaths artifact fork)
    (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256) (pa pb n i : Nat)
    (dst ret : UInt256) (rest : List UInt256) (env : Environment artifact fork s)
    (hcap : rest.length ≤ 1007) (hact : 296 ≤ s.activeWords.toNat)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472) (hi : i+1 = n) :
    GasSteps (tail s mem pmj ptj c mu bi pa pb n i dst ret rest)
      (exit s (tailMem mem c) (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) pa pb dst ret rest) := by
  have ht : Decode.isValidJumpDest s.executionEnv.code 1982 = true := by
    rw [env.code]
    exact paths.outerJump
  exact paths.tail.steps
    (env.transfer (t := tail s mem pmj ptj c mu bi pa pb n i dst ret rest) rfl rfl) rfl
    (MonproKNTailRows.run_last s mem pmj ptj c mu bi pa pb n i dst ret rest
      hcap hact hpb hpbFit hi ht)

def exitGas {artifact : ProgramArtifact} {fork : Fork} (paths : RowPaths artifact fork)
    (s : State) (mem : ByteArray) (pbi : UInt256) (pa pb : Nat)
    (dst ret : UInt256) (rest : List UInt256) (env : Environment artifact fork s)
    (hcap : rest.length ≤ 1007) :
    GasSteps (exit s mem pbi pa pb dst ret rest) (csub s mem dst ret rest) := by
  have ht : Decode.isValidJumpDest s.executionEnv.code 2655 = true := by
    rw [env.code]
    exact paths.csubJump
  exact paths.exit.steps (env.transfer (t := exit s mem pbi pa pb dst ret rest) rfl rfl) rfl
    (MonproKNExit.run_exit { s with memory := mem } pbi
      (UInt256.ofNat (pa-32)) (UInt256.ofNat (pb-32)) dst ret rest hcap ht)

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowGas
