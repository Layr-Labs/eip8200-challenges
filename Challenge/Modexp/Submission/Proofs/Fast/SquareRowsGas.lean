import Challenge.Modexp.Submission.Proofs.Fast.SquareProductGas
import Challenge.Modexp.Submission.Proofs.Fast.SquareReductionGas
import Challenge.Modexp.Submission.Proofs.Fast.SquareRowsModel
import Challenge.Modexp.Submission.Proofs.Fast.CarryTailRows
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyTraces

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareRowsGas
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore SquareInit
open SquareRowModel SquareRowsModel CiosCachedMidMemory
open _root_.Challenge.Modexp.Submission.Proofs.Fast.SquareDiagonal (base)

def tag : Nat → UInt256
  | 0 => l1Target 8
  | i+1 => SquareParts.delta i

def state (s : State) (mem : ByteArray) (pa i : Nat)
    (tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256) : State :=
  stateAt s mem (if i < 8 then 5190 else 4794)
    (base (UInt256.ofNat (ptrAt (pa+32*8-32) i)) (UInt256.ofNat pa) (UInt256.ofNat (pa-32))
      (tag i) (UInt256.ofNat 4509) inv
      (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))

def gasSteps_row (s : State) (mem : ByteArray) (pa i : Nat)
    (tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpafit : pa+256 ≤ 8192) (hi : i < 8)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hinv : inverseInvariant mem 8)
    (hroute : MachineState.readWord mem 9280 = UInt256.ofNat 5190)
    (hhigh : SquareWords.clearBit (MachineState.readWord mem 8928) = UInt256.ofNat 0)
    (env : Environment Artifact.submissionArtifact .Osaka s) :
    Challenge.EvmProof.GasSteps (state s mem pa i tl inv m0 aEnd m96 m64 m32 dst ret rest)
      (state s (row mem (digit mem pa i) i) pa (i+1) tl inv m0 aEnd m96 m64 m32 dst ret rest) := by
  let ai := digit mem pa i
  let pbi := UInt256.ofNat (ptrAt (pa+32*8-32) i)
  let midmem := mid mem ai i
  have hp : pbi.toNat = pa+32*(7-i) := by
    change (UInt256.ofNat (ptrAt (pa+32*8-32) i)).toNat = _
    rw [ptrAt_toNat _ _ (by omega) (by omega)]
    omega
  have hpword : pbi = UInt256.ofNat (pa+32*(7-i)) := by
    apply Challenge.EvmProof.Word.word_ext
    rw [hp, Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hdelta : pbi-UInt256.ofNat pa = SquareParts.delta i := by
    rw [hpword, Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)]
    congr 1
    omega
  have hpbi : pbi.toNat+32 ≤ 9472 := by rw [hp]; omega
  have hh : i = 7 → SquareCoefficients.coefficient mem ai i 8 = UInt256.ofNat 0 := by
    intro h
    subst i
    simpa only [SquareCoefficients.coefficient, Nat.reduceEqDiff, if_false, ite_true,
      SquareCoefficients.dWord, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] using hhigh
  have hpdt := SquareProductGas.gasSteps_product s mem ai i pbi (UInt256.ofNat pa)
    (UInt256.ofNat (pa-32)) (tag i) (UInt256.ofNat 4509) inv
    (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact hi hpbi hdelta (by rw [hp]; rfl) hh env
  have hread (addr : Nat) (hd : addr+32 ≤ 8224 ∨ 8512 ≤ addr) :
      MachineState.readWord midmem addr = MachineState.readWord mem addr :=
    read_mid_outside mem ai i addr (by omega) hd
  have hcm := hc.of_preserved (hread 9376 (Or.inr (by decide))) (hread 224 (Or.inl (by decide)))
  have hem := he.of_preserved (hread 96 (Or.inl (by decide)))
    (hread 64 (Or.inl (by decide))) (hread 32 (Or.inl (by decide)))
  have him : inverseInvariant midmem 8 := by
    simpa only [inverseInvariant, hread 224 (Or.inl (by decide)),
      hread 9376 (Or.inr (by decide))] using hinv
  have hr := SquareReductionGas.gasSteps_reduce s midmem (flag mem ai i) pbi (UInt256.ofNat pa)
    (UInt256.ofNat (pa-32)) (SquareParts.delta i) tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact hcm hem him
    ((hread 9280 (Or.inr (by decide))).trans hroute) env
  have hnext := CarryTailRows.pointer_next (pa+32*8-32) i
  have hcond := CiosCachedPointers.l1_condition pa 8 (i+1) hpa (by omega) (by omega)
  simpa only [state, if_pos hi, tag, midmem, row, ai, pbi, hnext, hcond] using hpdt.trans hr

def gasSteps_rows (s : State) (mem : ByteArray) (pa : Nat)
    (tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpafit : pa+256 ≤ 8192)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hinv : inverseInvariant mem 8)
    (hroute : MachineState.readWord mem 9280 = UInt256.ofNat 5190)
    (hhigh : SquareWords.clearBit (MachineState.readWord mem 8928) = UInt256.ofNat 0)
    (env : Environment Artifact.submissionArtifact .Osaka s) :
    Challenge.EvmProof.GasSteps (state s mem pa 0 tl inv m0 aEnd m96 m64 m32 dst ret rest)
      (mpCsubState s (rows mem pa 8) dst ret rest) := by
  have hloop : Challenge.EvmProof.GasSteps
      (state s mem pa 0 tl inv m0 aEnd m96 m64 m32 dst ret rest)
      (state s (rows mem pa 8) pa 8 tl inv m0 aEnd m96 m64 m32 dst ret rest) := by
    apply Challenge.EvmProof.GasSteps.iterateBounded
      (I := fun i => state s (rows mem pa i) pa i tl inv m0 aEnd m96 m64 m32 dst ret rest) 8
    intro i hi
    have hread (addr : Nat) (hd : addr+32 ≤ 8224 ∨ 8512 ≤ addr) :
        MachineState.readWord (rows mem pa i) addr = MachineState.readWord mem addr :=
      read_rows_outside mem pa addr hd i (by omega)
    exact gasSteps_row s (rows mem pa i) pa i tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact hpa hpafit hi
      (hc.of_preserved (hread 9376 (Or.inr (by decide))) (hread 224 (Or.inl (by decide))))
      (he.of_preserved (hread 96 (Or.inl (by decide))) (hread 64 (Or.inl (by decide))) (hread 32 (Or.inl (by decide))))
      (by simpa only [inverseInvariant, hread 224 (Or.inl (by decide)), hread 9376 (Or.inr (by decide))] using hinv)
      ((hread 9280 (Or.inr (by decide))).trans hroute)
      (by rw [hread 8928 (Or.inr (by decide))]; exact hhigh) env
  refine hloop.trans ?_
  apply CarryRowBlocks.exitBlock.steps (s := state s (rows mem pa 8) pa 8 tl inv m0 aEnd m96 m64 m32 dst ret rest)
    (env.transfer rfl rfl) rfl
  exact CiosReadonly.run_exit {s with memory := rows mem pa 8}
    (UInt256.ofNat (ptrAt (pa+32*8-32) 8)) (UInt256.ofNat pa) (UInt256.ofNat (pa-32)) (tag 8)
    (UInt256.ofNat 4509) tl inv m0 aEnd m96 m64 m32 dst ret rest hcap
    (by change Decode.isValidJumpDest s.executionEnv.code 4902 = true
        rw [env.code]; exact Artifact.isValidJumpDest_index 3740 (by rfl))

end Challenge.Modexp.Submission.Proofs.Fast.SquareRowsGas
