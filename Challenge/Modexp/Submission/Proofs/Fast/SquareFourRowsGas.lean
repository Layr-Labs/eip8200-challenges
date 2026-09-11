import Challenge.Modexp.Submission.Proofs.Fast.SquareFourProductGas
import Challenge.Modexp.Submission.Proofs.Fast.SquareFourReductionGas
import Challenge.Modexp.Submission.Proofs.Fast.SquareFourRowsModel
import Challenge.Modexp.Submission.Proofs.Fast.CarryTailRows
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyTraces

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareFourRowsGas
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore SquareInit
open SquareFourRowModel SquareFourRowsModel CiosCachedMidMemory
open _root_.Challenge.Modexp.Submission.Proofs.Fast.SquareDiagonal (base)

def tag : Nat → UInt256
  | 0 => l1Target 4
  | i+1 => SquareParts.delta (i+4)

def state (s : State) (mem : ByteArray) (pa i : Nat)
    (tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256) : State :=
  stateAt s mem (if i < 4 then 5191 else 4794)
    (base (UInt256.ofNat (ptrAt (pa+32*4-32) i)) (UInt256.ofNat pa) (UInt256.ofNat (pa-32))
      (tag i) (UInt256.ofNat 4661) inv
      (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))

def gasSteps_row (s : State) (mem : ByteArray) (pa i : Nat)
    (tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 91 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpafit : pa+128 ≤ 2048) (hi : i < 4)
    (hc : CiosReadonly.ReadonlyCache mem 4 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hinv : inverseInvariant mem 4)
    (hroute : MachineState.readWord mem 2720 = UInt256.ofNat 5191)
    (hhigh : SquareWords.clearBit (MachineState.readWord mem 2368) = UInt256.ofNat 0)
    (env : Environment Artifact.submissionArtifact .Osaka s) :
    Challenge.EvmProof.GasSteps (state s mem pa i tl inv m0 aEnd m96 m64 m32 dst ret rest)
      (state s (row mem (digit mem pa i) i) pa (i+1) tl inv m0 aEnd m96 m64 m32 dst ret rest) := by
  let ai := digit mem pa i
  let pbi := UInt256.ofNat (ptrAt (pa+32*4-32) i)
  let midmem := mid mem ai i
  have hp : pbi.toNat = pa+32*(3-i) := by
    change (UInt256.ofNat (ptrAt (pa+32*4-32) i)).toNat = _
    rw [ptrAt_toNat _ _ (by omega) (by omega)]
    omega
  have hpword : pbi = UInt256.ofNat (pa+32*(3-i)) := by
    apply Challenge.EvmProof.Word.word_ext
    rw [hp, Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hdelta : pbi-UInt256.ofNat pa = SquareParts.delta (i+4) := by
    rw [hpword, Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)]
    congr 1
    omega
  have hpbi : pbi.toNat+32 ≤ 2912 := by rw [hp]; omega
  have hpdt := SquareFourProductGas.gasSteps_product s mem ai i pbi (UInt256.ofNat pa)
    (UInt256.ofNat (pa-32)) (tag i) (UInt256.ofNat 4661) inv
    (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact hi hpbi hdelta (by rw [hp]; rfl) hhigh env
  have hread (addr : Nat) (hd : addr+32 ≤ 2080 ∨ 2240 ≤ addr) :
      MachineState.readWord midmem addr = MachineState.readWord mem addr :=
    read_mid_outside mem ai i addr (by omega) hd
  have hcm := hc.of_preserved (hread 2816 (Or.inr (by decide))) (hread 96 (Or.inl (by decide)))
  have hem := he.of_preserved (hread 96 (Or.inl (by decide)))
    (hread 64 (Or.inl (by decide))) (hread 32 (Or.inl (by decide)))
  have him : inverseInvariant midmem 4 := by
    simpa only [inverseInvariant, hread 96 (Or.inl (by decide)),
      hread 2816 (Or.inr (by decide))] using hinv
  have hr := SquareFourReductionGas.gasSteps_reduce s midmem (flag mem ai i) pbi (UInt256.ofNat pa)
    (UInt256.ofNat (pa-32)) (SquareParts.delta (i+4)) tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact hcm hem him
    ((hread 2720 (Or.inr (by decide))).trans hroute) env
  have hnext := CarryTailRows.pointer_next (pa+32*4-32) i
  have hcond := CiosCachedPointers.l1_condition pa 4 (i+1) hpa (by omega) (by omega)
  simpa only [state, if_pos hi, tag, midmem, row, ai, pbi, hnext, hcond] using hpdt.trans hr

def gasSteps_rows (s : State) (mem : ByteArray) (pa : Nat)
    (tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 91 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpafit : pa+128 ≤ 2048)
    (hc : CiosReadonly.ReadonlyCache mem 4 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hinv : inverseInvariant mem 4)
    (hroute : MachineState.readWord mem 2720 = UInt256.ofNat 5191)
    (hhigh : SquareWords.clearBit (MachineState.readWord mem 2368) = UInt256.ofNat 0)
    (env : Environment Artifact.submissionArtifact .Osaka s) :
    Challenge.EvmProof.GasSteps (state s mem pa 0 tl inv m0 aEnd m96 m64 m32 dst ret rest)
      (mpCsubState s (rows mem pa 4) dst ret rest) := by
  have hloop : Challenge.EvmProof.GasSteps
      (state s mem pa 0 tl inv m0 aEnd m96 m64 m32 dst ret rest)
      (state s (rows mem pa 4) pa 4 tl inv m0 aEnd m96 m64 m32 dst ret rest) := by
    apply Challenge.EvmProof.GasSteps.iterateBounded
      (I := fun i => state s (rows mem pa i) pa i tl inv m0 aEnd m96 m64 m32 dst ret rest) 4
    intro i hi
    have hread (addr : Nat) (hd : addr+32 ≤ 2080 ∨ 2240 ≤ addr) :
        MachineState.readWord (rows mem pa i) addr = MachineState.readWord mem addr :=
      read_rows_outside mem pa addr hd i (by omega)
    exact gasSteps_row s (rows mem pa i) pa i tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact hpa hpafit hi
      (hc.of_preserved (hread 2816 (Or.inr (by decide))) (hread 96 (Or.inl (by decide))))
      (he.of_preserved (hread 96 (Or.inl (by decide))) (hread 64 (Or.inl (by decide))) (hread 32 (Or.inl (by decide))))
      (by simpa only [inverseInvariant, hread 96 (Or.inl (by decide)), hread 2816 (Or.inr (by decide))] using hinv)
      ((hread 2720 (Or.inr (by decide))).trans hroute)
      (by rw [hread 2368 (Or.inr (by decide))]; exact hhigh) env
  refine hloop.trans ?_
  apply CarryRowBlocks.exitBlock.steps (s := state s (rows mem pa 4) pa 4 tl inv m0 aEnd m96 m64 m32 dst ret rest)
    (env.transfer rfl rfl) rfl
  exact CiosReadonly.run_exit {s with memory := rows mem pa 4}
    (UInt256.ofNat (ptrAt (pa+32*4-32) 4)) (UInt256.ofNat pa) (UInt256.ofNat (pa-32)) (tag 4)
    (UInt256.ofNat 4661) tl inv m0 aEnd m96 m64 m32 dst ret rest hcap
    (by change Decode.isValidJumpDest s.executionEnv.code 4902 = true
        rw [env.code]; exact Artifact.isValidJumpDest_index 3745 (by rfl))

end Challenge.Modexp.Submission.Proofs.Fast.SquareFourRowsGas
