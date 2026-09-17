import Challenge.Modexp.Submission.Proofs.Fast.CarryRowGas
import Challenge.Modexp.Submission.Proofs.Fast.CarryFullBase
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowLemmas
import Challenge.Modexp.Submission.Proofs.Fast.FusedEntry

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.UnrolledRows

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore
open CarryRowModel CiosCachedMidMemory

def dispatcherPC : Nat := 5339
def r4PC : Nat := 5349
def r8PC : Nat := 6205

def dispatcherProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨3, by decide⟩), .push 2 3549,
   .op .EQ, .push 2 r8PC, .op .JUMPI]

def tailAdvanceProgram : List Instr :=
  CarryRowPrograms.tailStore ++ [.op (.Dup ⟨4, by decide⟩), .op .ADD]

def r4RowProgram : List Instr :=
  (((CiosCached.outProgram ++ CiosReadonly.commonFirstProgram) ++
      ((StagedOperand.stepProgram 64 2176 ++ StagedOperand.stepProgram 32 2144) ++
        StagedOperand.stepProgram 0 2112)) ++ CarryRowPrograms.middleBlock) ++
    (((CiosCached.joinProgram ++ CiosReadonlyExtra.extraProgram 1 2176 2208) ++
       CiosReadonlyExtra.extraProgram 2 2144 2176) ++
      CiosCachedLast.l2LastProgram 0 0 2112 2144)) ++ tailAdvanceProgram

def r8RowProgram : List Instr :=
  (((CiosCached.outProgram ++ CiosReadonly.commonFirstProgram) ++
      ((((((StagedOperand.stepProgram 192 2304 ++ StagedOperand.stepProgram 160 2272) ++
        StagedOperand.stepProgram 128 2240) ++ StagedOperand.stepProgram 96 2208) ++
        StagedOperand.stepProgram 64 2176) ++ StagedOperand.stepProgram 32 2144) ++
        StagedOperand.stepProgram 0 2112)) ++ CarryRowPrograms.middleBlock) ++
    ((((((((CiosCached.joinProgram ++ CiosCached.l2Program 10 192 2304 2336) ++
      CiosCached.l2Program 1 160 2272 2304) ++ CiosCached.l2Program 1 128 2240 2272) ++
      CiosReadonlyExtra.extraProgram 0 2208 2240) ++ CiosCached.joinProgram) ++
      CiosReadonlyExtra.extraProgram 1 2176 2208) ++
      CiosReadonlyExtra.extraProgram 2 2144 2176) ++
      CiosCachedLast.l2LastProgram 0 0 2112 2144)) ++ tailAdvanceProgram

def finalJumpProgram : List Instr := [.push 2 4109, .op .JUMP]

def dispatcherBlock : Block Artifact.submissionArtifact .Osaka dispatcherPC dispatcherProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4110 6 dispatcherPC dispatcherProgram
    (by decide) (by rfl) (by rfl) (by decide)

def r4Block0 : Block Artifact.submissionArtifact .Osaka 5349 r4RowProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4116 244 5349 r4RowProgram
    (by decide) (by rfl) (by rfl) (by decide)
def r4Block1 : Block Artifact.submissionArtifact .Osaka 5633 r4RowProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4360 244 5633 r4RowProgram
    (by decide) (by rfl) (by rfl) (by decide)
def r4Block2 : Block Artifact.submissionArtifact .Osaka 5917 r4RowProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4604 244 5917 r4RowProgram
    (by decide) (by rfl) (by rfl) (by decide)

def r8Block0 : Block Artifact.submissionArtifact .Osaka 6205 r8RowProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4850 487 6205 r8RowProgram
    (by decide) (by rfl) (by rfl) (by decide)
def r8Block1 : Block Artifact.submissionArtifact .Osaka 6785 r8RowProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5337 487 6785 r8RowProgram
    (by decide) (by rfl) (by rfl) (by decide)
def r8Block2 : Block Artifact.submissionArtifact .Osaka 7365 r8RowProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 5824 487 7365 r8RowProgram
    (by decide) (by rfl) (by rfl) (by decide)
def r8Block3 : Block Artifact.submissionArtifact .Osaka 7945 r8RowProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6311 487 7945 r8RowProgram
    (by decide) (by rfl) (by rfl) (by decide)
def r8Block4 : Block Artifact.submissionArtifact .Osaka 8525 r8RowProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 6798 487 8525 r8RowProgram
    (by decide) (by rfl) (by rfl) (by decide)
def r8Block5 : Block Artifact.submissionArtifact .Osaka 9105 r8RowProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7285 487 9105 r8RowProgram
    (by decide) (by rfl) (by rfl) (by decide)
def r8Block6 : Block Artifact.submissionArtifact .Osaka 9685 r8RowProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 7772 487 9685 r8RowProgram
    (by decide) (by rfl) (by rfl) (by decide)

def finalJump4 : Block Artifact.submissionArtifact .Osaka 6201 finalJumpProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4848 2 6201 finalJumpProgram
    (by decide) (by rfl) (by rfl) (by decide)
def finalJump8 : Block Artifact.submissionArtifact .Osaka 10265 finalJumpProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 8259 2 10265 finalJumpProgram
    (by decide) (by rfl) (by rfl) (by decide)

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  CarryRowBlocks.environment s hcode hfork hrun hnp

theorem jumpDest_dispatcher :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode dispatcherPC = true :=
  Artifact.isValidJumpDest_index 4110 (by rfl)

theorem jumpDest_r8 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode r8PC = true :=
  Artifact.isValidJumpDest_index 4850 (by rfl)

def privateStart (pc : Nat) (s : State) (mem : ByteArray) (pb n i : Nat)
    (ent pdst ret : UInt256) (rest : List UInt256) : State :=
  { outState s mem pb n i (UInt256.ofNat dispatcherPC) ent pdst ret rest with
    pc := UInt256.ofNat pc }

theorem run_dispatch4 (s : State) (mem : ByteArray) (pb i : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions dispatcherProgram
      (outState s mem pb 4 i (UInt256.ofNat dispatcherPC) (l1Target 4) pdst ret rest) =
    some (privateStart r4PC s mem pb 4 i (l1Target 4) pdst ret rest) := by
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  simp [dispatcherProgram, privateStart, outState, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, hc9, hc10, l1Target_four,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_dispatch8 (s : State) (mem : ByteArray) (pb i : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions dispatcherProgram
      (outState s mem pb 8 i (UInt256.ofNat dispatcherPC) (l1Target 8) pdst ret rest) =
    some (privateStart r8PC s mem pb 8 i (l1Target 8) pdst ret rest) := by
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hj : Decode.isValidJumpDest s.executionEnv.code r8PC = true := by
    rw [hcode]; exact jumpDest_r8
  simp [dispatcherProgram, privateStart, outState, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, hc9, hc10, l1Target_eight, hj,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_outAt (pc : Nat) (s : State) (mem : ByteArray) (pb n i : Nat)
    (ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hact : 88 ≤ s.activeWords.toNat)
    (_hn : 2 ≤ n) (_hn32 : n ≤ 8) (hi : i < n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 2816) :
    runInstructions CiosCached.outProgram (privateStart pc s mem pb n i ent pdst ret rest) =
      some (firstAt (pc+3) s mem (rowBi mem pb n i) pb n i
        (UInt256.ofNat dispatcherPC) ent pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hpbi : ptrAt (pb + 32 * n - 32) i % 2^256 = pb + 32 * (n - 1 - i) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hactB : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pb + 32 * (n - 1 - i)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14,
      CiosCached.outProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      privateStart, outState, firstAt, rowBi, hc8, hc9, hc10, hc11, hzero, hpbi, hactB,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

theorem run_commonFirstAt (pc : Nat) (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i : Nat) (ent tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hpos : 0 < n)
    (hpaFit : pa+32*n ≤ 2816)
    (htl : tl = UInt256.ofNat (2080+32*n))
    (hAend : aEnd = UInt256.ofNat (pa+32*n-32)) :
    runInstructions CiosReadonly.commonFirstProgram
      (firstAt pc s mem bi pb n i (UInt256.ofNat dispatcherPC) ent inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (l1At (pc+24) s mem bi pa pb n i 1 (UInt256.ofNat dispatcherPC) ent inv m0
      (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  have ha : aEnd.toNat = pa+32*(n-1) := by
    rw [hAend,Challenge.EvmProof.Word.word_toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  have ht : tl.toNat = 2112+32*(n-1) := by
    rw [htl,Challenge.EvmProof.Word.word_toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  let st : State := {s with memory := mem}
  have hA : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat aEnd.toNat 32) =
      st.activeWords := by
    rw [ha]
    exact activeWords_fix st _ 31 (by decide) (by omega) hact
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat tl.toNat 32) =
      st.activeWords := by
    rw [ht]
    exact activeWords_fix st _ 31 (by decide) (by omega) hact
  let pbi := UInt256.ofNat (ptrAt (pb+32*n-32) i)
  let frame := CiosCommonFirst.tail pbi (UInt256.ofNat dispatcherPC) (UInt256.ofNat (pb-32))
    ent (l2Target n) tl inv m0 aEnd m96 m64 m32 dst ret rest
  have hl := CiosCommonFirst.run_load st (UInt256.ofNat pc) bi pbi
    (UInt256.ofNat dispatcherPC) (UInt256.ofNat (pb-32)) ent (l2Target n) tl inv m0
    aEnd m96 m64 m32 dst ret rest hcap hA
  have hm := CiosNoDummyCarry.run_multiply st (advancePC 3 (UInt256.ofNat pc))
    (MachineState.readWord mem aEnd.toNat) bi frame
    (by simp only [frame,CiosCommonFirst.tail,List.length_append,List.length_cons,List.length_nil]; omega)
  have hf := CiosCommonFirst.run_fused st (advancePC 6 (advancePC 3 (UInt256.ofNat pc)))
    (MachineState.readWord mem aEnd.toNat) bi pbi (UInt256.ofNat dispatcherPC)
    (UInt256.ofNat (pb-32)) ent (l2Target n) tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hT
  have both := runInstructions_append_some _ _ _ _ _ hl hm
  have hall := runInstructions_append_some _ _ _ _ _ both hf
  have hpc : advancePC 6 (advancePC 3 (UInt256.ofNat pc))+UInt256.ofNat 15 =
      UInt256.ofNat (pc+24) := by
    simp [advancePC, Challenge.EvmProof.Word.ofNat_add_mod, word_add_assoc]
  simpa only [CiosReadonly.commonFirstProgram,st,frame,pbi,CiosCommonFirst.tail,
    firstAt,l1At,l1Q,l1Step,framed,ha,ht,hpc,Nat.sub_zero,List.cons_append,List.nil_append]
    using hall

theorem run_middleStoreAt (pc : Nat) (s : State) (c bi pbi hd pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.middleStore
      (framed s (UInt256.ofNat pc)
        ([c,bi,pbi,hd,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := midMem1 s.memory c} (UInt256.ofNat (pc+14))
      ([overflow s.memory c,pbi,hd,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hactN := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have haddr : (2080 : UInt256).toNat = 2080 := by decide
  simp (config := {maxSteps := 100000}) [CarryRowPrograms.middleStore, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, hc13, midMem1, overflow,
    haddr, hactN, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_cachedProductAt (pc : Nat) (s : State)
    (bi pbi hd pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n ≤ 8)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : CiosReadonly.ReadonlyCache s.memory n tl inv m0)
    (hminv : inverseInvariant s.memory n) :
    runInstructions CiosReadonly.cachedProduct
      (framed s (UInt256.ofNat pc)
        (CiosReadonly.cacheStack bi pbi hd pb flag target2 tl inv m0 aEnd
          m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat (pc+12))
      ([rowC0 s.memory n,rowMu s.memory n] ++
        CiosReadonly.cacheStack bi pbi hd pb flag target2 tl inv m0 aEnd
          m96 m64 m32 dst ret rest)) := by
  rw [hc.lowAddress, hc.inverse, hc.modulusLow]
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hmod : (2080+32*n) % 2^256 = 2080+32*n := Nat.mod_eq_of_lt (by omega)
  have hmul : MachineState.readWord s.memory (2080+32*n) *
      MachineState.readWord s.memory 2720 =
      MachineState.readWord s.memory 2720 * MachineState.readWord s.memory (2080+32*n) := by
    apply Challenge.EvmProof.Word.word_ext
    change ((MachineState.readWord s.memory (2080+32*n)).val *
      (MachineState.readWord s.memory 2720).val).val =
      ((MachineState.readWord s.memory 2720).val *
      (MachineState.readWord s.memory (2080+32*n)).val).val
    rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]
  have hactQ := activeWords_fix s (2080+32*n) 32 (by decide) (by omega) hact
  have hguard : MachineState.readWord s.memory 2720 ≠ UInt256.ofNat 1 := by
    rw [← hc.inverse]; exact hc.inverseGuard
  have hcarry := N0Carry.addMod_row_carry (MachineState.readWord s.memory (32*n-32))
    (MachineState.readWord s.memory 2720) (MachineState.readWord s.memory (2080+32*n))
    hminv hguard
  simp (config := { maxSteps := 400000 }) [CiosReadonly.cachedProduct, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, CiosReadonly.cacheStack,
    CiosCachedMidDefs.baseStack, Nat.add_assoc, hc17, hc18, hc19, hc20, hc21, hc22,
    hmul, allOnes_value, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    hmod, hactQ, List.exchange, N0Carry.addMod_comm, hcarry, rowC0, rowMu,
    Challenge.EvmProof.Word.ofNat_add_mod]

def midAt (pc : Nat) (s : State) (mem : ByteArray) (c bi : UInt256)
    (pb n i : Nat) (ent pdst ret : UInt256) (rest : List UInt256) : State :=
  { midState s mem c bi pb n i (UInt256.ofNat dispatcherPC) ent pdst ret rest with
    pc := UInt256.ofNat pc }

theorem run_middleAt (pc : Nat) (s : State) (mem : ByteArray) (c bi : UInt256)
    (pb n i : Nat) (ent tl inv m0 aEnd m96 m64 m32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0) (hminv : inverseInvariant mem n) :
    runInstructions CarryRowPrograms.middleBlock
      (midAt pc s mem c bi pb n i ent inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (l2At (pc+27) s (midMem1 mem c) (overflow mem c)
      (rowMu mem n) (rowC0 mem n) pb n i 0 (UInt256.ofNat dispatcherPC) ent inv m0
      (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  have hmem := middle_agree mem mem (refl mem) c
  have hmu : rowMu (midMem1 mem c) n = rowMu mem n :=
    (CarryRowModel.rowMu_eq _ _ hmem n).trans (rowMu_mid mem c n hn)
  have hc0 : rowC0 (midMem1 mem c) n = rowC0 mem n :=
    (CarryRowModel.rowC0_eq _ _ hmem n hn32).trans (rowC0_mid mem c n hn hn32)
  have hcache : CiosReadonly.ReadonlyCache (midMem1 mem c) n tl inv m0 :=
    hc.of_preserved (readWord_midMem1 mem c 2720 (Or.inr (by decide)))
      (readWord_midMem1 mem c (32*n-32) (Or.inl (by omega)))
  have hminv' : inverseInvariant (midMem1 mem c) n := by
    unfold inverseInvariant
    rw [readWord_midMem1 mem c (32*n-32) (Or.inl (by omega)),
      readWord_midMem1 mem c 2720 (Or.inr (by decide))]
    exact hminv
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hjd : runInstructions [.op .JUMPDEST]
      (midAt pc s mem c bi pb n i ent inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
      some (framed {s with memory := mem} (UInt256.ofNat (pc+1))
        ([c,bi,UInt256.ofNat (ptrAt (pb+32*n-32) i),UInt256.ofNat dispatcherPC,
          UInt256.ofNat (pb-32),ent,negative32,allOnes,l2Target n,inv] ++
          (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) := by
    simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, midAt, midState, framed,
      hc18, hc17, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  have hs := run_middleStoreAt (pc+1) {s with memory := mem} c bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat dispatcherPC)
    (UInt256.ofNat (pb-32)) ent (l2Target n) inv
    (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact
  have hp := run_cachedProductAt (pc+15) {s with memory := midMem1 mem c}
    (overflow mem c) (UInt256.ofNat (ptrAt (pb+32*n-32) i))
    (UInt256.ofNat dispatcherPC) (UInt256.ofNat (pb-32)) ent (l2Target n)
    tl inv m0 aEnd m96 m64 m32 dst ret n rest hcap hn32 hact hcache hminv'
  have h := runInstructions_append_some _ _ _ _ _ hs hp
  have h2 := runInstructions_append_some _ _ _ _ _ hjd h
  simpa only [CarryRowPrograms.middleBlock, CarryRowPrograms.middle,
    CiosReadonly.fullMidProgram, l2At, l2Step, CiosReadonly.cacheStack,
    CiosCachedMidDefs.baseStack, framed, hmu, hc0, List.append_assoc,
    List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd] using h2

def tailAt (pc : Nat) (s : State) (mem : ByteArray) (c mu bi : UInt256)
    (pb n i : Nat) (ent pdst ret : UInt256) (rest : List UInt256) : State :=
  { tailState s mem c mu bi pb n i (UInt256.ofNat dispatcherPC) ent pdst ret rest with
    pc := UInt256.ofNat pc }

theorem run_tailStoreAt (pc : Nat) (s : State) (c f pbi hd pb flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions CarryRowPrograms.tailStore
      (framed s (UInt256.ofNat pc)
        ([c,f,pbi,hd,pb,flag,negative32,allOnes,dst,ret] ++ rest)) =
    some (framed {s with memory := tailCarry s.memory c f} (UInt256.ofNat (pc+17))
      ([pbi,hd,pb,flag,negative32,allOnes,dst,ret] ++ rest)) := by
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hactN := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have hactT := activeWords_fix s 2112 32 (by decide) (by omega) hact
  have hn : (2080 : UInt256).toNat = 2080 := by decide
  have ht : (2112 : UInt256).toNat = 2112 := by decide
  simp (config := {maxSteps := 100000}) [CarryRowPrograms.tailStore, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11, hc12, hc13,
    tailCarry, tailMem1, hn, ht, hactN, hactT, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_tailAdvanceAt (pc : Nat) (s : State) (mem : ByteArray) (c mu bi : UInt256)
    (pb n i : Nat) (ent dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions tailAdvanceProgram
      (tailAt pc s mem c mu bi pb n i ent dst ret rest) =
    some (privateStart (pc+19) s (tailCarry mem c bi) pb n (i+1) ent dst ret rest) := by
  have hs := run_tailStoreAt pc {s with memory := mem} c bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat dispatcherPC)
    (UInt256.ofNat (pb-32)) ent (l2Target n) dst (ret :: rest)
    (by simp only [List.length_cons]; omega) hact
  have hp := CarryTailRows.pointer_next (pb+32*n-32) i
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have ha : runInstructions [.op (.Dup ⟨4, by decide⟩), .op .ADD]
      (framed {s with memory := tailCarry mem c bi} (UInt256.ofNat (pc+17))
        ([UInt256.ofNat (ptrAt (pb+32*n-32) i),UInt256.ofNat dispatcherPC,
          UInt256.ofNat (pb-32),ent,negative32,allOnes,l2Target n,dst,ret] ++ rest)) =
      some (privateStart (pc+19) s (tailCarry mem c bi) pb n (i+1) ent dst ret rest) := by
    simp [runInstructions, Challenge.EvmProof.Stepper.runInstr, framed, privateStart, outState,
      hc8, hc9, hp, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange]
  have h := runInstructions_append_some _ _ _ _ _ hs ha
  simpa only [tailAdvanceProgram, tailAt, tailState, framed,
    List.cons_append, List.nil_append] using h

theorem run_extraAt (slot : Fin 3) (pc : Nat) (x loadAddr storeAddr : UInt256)
    (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hk : k+1 < n)
    (hx : x.toNat = 32*(n-2-k)) (hselect : x.toNat = CiosReadonlyExtra.cacheAddress slot)
    (hload : loadAddr.toNat = 2112+32*(n-2-k))
    (hstore : storeAddr.toNat = 2112+32*(n-1-k))
    (hc : CiosReadonlyExtra.ExtraCache mem m96 m64 m32) :
    runInstructions (CiosReadonlyExtra.extraProgram slot loadAddr storeAddr)
      (l2At pc s mem bi mu c0 pb n i k (UInt256.ofNat dispatcherPC) ent inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) =
    some (l2At (pc+33) s mem bi mu c0 pb n i (k+1) (UInt256.ofNat dispatcherPC) ent inv m0
      (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) := by
  have h := CiosReadonlyExtra.run_extraStep slot s (UInt256.ofNat pc) mem
    bi mu c0 n k x loadAddr storeAddr hx hselect hload hstore
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat dispatcherPC)
    (UInt256.ofNat (pb-32)) ent (l2Target n) tl inv m0 aEnd m96 m64 m32 pdst ret rest
    hcap hact hn hk hc
  simpa only [CiosCachedL2.state,l2At,Challenge.EvmProof.Word.ofNat_add_mod,
    List.cons_append,List.nil_append] using h

theorem run_lastAt (pc : Nat) (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb n i : Nat) (ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hact : 88 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 8) (hn : 2 ≤ n) :
    runInstructions (CiosCachedLast.l2LastProgram 0 0 2112 2144)
      (l2At pc s mid bi mu c0 pb n i (n-2) (UInt256.ofNat dispatcherPC) ent pdst ret rest) =
    some (tailAt (pc+33) s (l2Step mid mu c0 n (n-1)).memory
      (l2Step mid mu c0 n (n-1)).carry mu bi pb n i ent pdst ret rest) := by
  have h := CiosCachedLast.run_stepLast 0 s (UInt256.ofNat pc) mid bi mu c0 n (n-2)
    0 2112 2144
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 1 - (n - 2) = 1 by omega]; decide)
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat dispatcherPC)
    (UInt256.ofNat (pb-32)) ent (l2Target n) pdst (ret :: rest)
    (by simp only [List.length_cons]; omega) hact hn32 (by omega) (by decide)
  have hnn : n - 2 + 1 = n - 1 := by omega
  rw [hnn] at h
  simpa only [List.cons_append, List.nil_append, CiosCachedL2.state,
    CiosCachedLast.lastState, l2At, tailAt, tailState,
    Challenge.EvmProof.Word.ofNat_add_mod] using h

theorem run_l1FourAt (pc : Nat) (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb i : Nat) (ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hact : 88 ≤ s.activeWords.toNat)
    (hpaFit : pa + 32 * 4 ≤ 2048 ∨ pa = 2368)
    (hsnapshot : StagedOperand.Snapshot mem pa 4) :
    runInstructions
      ((StagedOperand.stepProgram 64 2176 ++ StagedOperand.stepProgram 32 2144) ++
        StagedOperand.stepProgram 0 2112)
      (l1At pc s mem bi pa pb 4 i 1 (UInt256.ofNat dispatcherPC) ent pdst ret rest) =
    some (midAt (pc+111) s (l1Step mem bi pa 4 4).memory
      (l1Step mem bi pa 4 4).carry bi pb 4 i ent pdst ret rest) := by
  have h1 := StagedOperand.run_stepQ pc 64 2176 s (l1Step mem bi pa 4 1) bi
    pa pb 4 i 1 (UInt256.ofNat dispatcherPC) ent pdst ret rest hcap hact
    (by decide) (by decide) (by decide) (by decide)
    (hsnapshot.l1_stage bi 1 (by decide) hpaFit)
  rw [SquareModel.l1Step_succ_eq] at h1
  have h2 := StagedOperand.run_stepQ (pc+37) 32 2144 s (l1Step mem bi pa 4 2) bi
    pa pb 4 i 2 (UInt256.ofNat dispatcherPC) ent pdst ret rest hcap hact
    (by decide) (by decide) (by decide) (by decide)
    (hsnapshot.l1_stage bi 2 (by decide) hpaFit)
  rw [SquareModel.l1Step_succ_eq] at h2
  have h3 := StagedOperand.run_stepQ (pc+74) 0 2112 s (l1Step mem bi pa 4 3) bi
    pa pb 4 i 3 (UInt256.ofNat dispatcherPC) ent pdst ret rest hcap hact
    (by decide) (by decide) (by decide) (by decide)
    (hsnapshot.l1_stage bi 3 (by decide) hpaFit)
  rw [SquareModel.l1Step_succ_eq] at h3
  have h := runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _ h1 h2) h3
  simpa only [midAt, midState, l1At, l1Q, Nat.add_assoc, Nat.reduceAdd] using h

theorem run_l1EightAt (pc : Nat) (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb i : Nat) (ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hact : 88 ≤ s.activeWords.toNat)
    (hpaFit : pa + 32 * 8 ≤ 2048 ∨ pa = 2368)
    (hsnapshot : StagedOperand.Snapshot mem pa 8) :
    runInstructions
      ((((((StagedOperand.stepProgram 192 2304 ++ StagedOperand.stepProgram 160 2272) ++
        StagedOperand.stepProgram 128 2240) ++ StagedOperand.stepProgram 96 2208) ++
        StagedOperand.stepProgram 64 2176) ++ StagedOperand.stepProgram 32 2144) ++
        StagedOperand.stepProgram 0 2112)
      (l1At pc s mem bi pa pb 8 i 1 (UInt256.ofNat dispatcherPC) ent pdst ret rest) =
    some (midAt (pc+259) s (l1Step mem bi pa 8 8).memory
      (l1Step mem bi pa 8 8).carry bi pb 8 i ent pdst ret rest) := by
  have hsnap (j : Nat) (hj : j ≤ 8) := hsnapshot.l1_stage bi j (by decide) hpaFit
  have h1 := StagedOperand.run_stepQ pc 192 2304 s (l1Step mem bi pa 8 1) bi
    pa pb 8 i 1 (UInt256.ofNat dispatcherPC) ent pdst ret rest hcap hact
    (by decide) (by decide) (by decide) (by decide) (hsnap 1 (by decide))
  rw [SquareModel.l1Step_succ_eq] at h1
  have h2 := StagedOperand.run_stepQ (pc+37) 160 2272 s (l1Step mem bi pa 8 2) bi
    pa pb 8 i 2 (UInt256.ofNat dispatcherPC) ent pdst ret rest hcap hact
    (by decide) (by decide) (by decide) (by decide) (hsnap 2 (by decide))
  rw [SquareModel.l1Step_succ_eq] at h2
  have h3 := StagedOperand.run_stepQ (pc+74) 128 2240 s (l1Step mem bi pa 8 3) bi
    pa pb 8 i 3 (UInt256.ofNat dispatcherPC) ent pdst ret rest hcap hact
    (by decide) (by decide) (by decide) (by decide) (hsnap 3 (by decide))
  rw [SquareModel.l1Step_succ_eq] at h3
  have h4 := StagedOperand.run_stepQ (pc+111) 96 2208 s (l1Step mem bi pa 8 4) bi
    pa pb 8 i 4 (UInt256.ofNat dispatcherPC) ent pdst ret rest hcap hact
    (by decide) (by decide) (by decide) (by decide) (hsnap 4 (by decide))
  rw [SquareModel.l1Step_succ_eq] at h4
  have h5 := StagedOperand.run_stepQ (pc+148) 64 2176 s (l1Step mem bi pa 8 5) bi
    pa pb 8 i 5 (UInt256.ofNat dispatcherPC) ent pdst ret rest hcap hact
    (by decide) (by decide) (by decide) (by decide) (hsnap 5 (by decide))
  rw [SquareModel.l1Step_succ_eq] at h5
  have h6 := StagedOperand.run_stepQ (pc+185) 32 2144 s (l1Step mem bi pa 8 6) bi
    pa pb 8 i 6 (UInt256.ofNat dispatcherPC) ent pdst ret rest hcap hact
    (by decide) (by decide) (by decide) (by decide) (hsnap 6 (by decide))
  rw [SquareModel.l1Step_succ_eq] at h6
  have h7 := StagedOperand.run_stepQ (pc+222) 0 2112 s (l1Step mem bi pa 8 7) bi
    pa pb 8 i 7 (UInt256.ofNat dispatcherPC) ent pdst ret rest hcap hact
    (by decide) (by decide) (by decide) (by decide) (hsnap 7 (by decide))
  rw [SquareModel.l1Step_succ_eq] at h7
  have h12 := runInstructions_append_some _ _ _ _ _ h1 h2
  have h123 := runInstructions_append_some _ _ _ _ _ h12 h3
  have h1234 := runInstructions_append_some _ _ _ _ _ h123 h4
  have h12345 := runInstructions_append_some _ _ _ _ _ h1234 h5
  have h123456 := runInstructions_append_some _ _ _ _ _ h12345 h6
  have h := runInstructions_append_some _ _ _ _ _ h123456 h7
  simpa only [midAt, midState, l1At, l1Q, Nat.add_assoc, Nat.reduceAdd] using h

theorem run_joinAt (pc : Nat) (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) :
    runInstructions CiosCached.joinProgram
      (l2At pc s mem bi mu c0 pb n i k (UInt256.ofNat dispatcherPC) ent pdst ret rest) =
    some (l2At (pc+1) s mem bi mu c0 pb n i k
      (UInt256.ofNat dispatcherPC) ent pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc : rest.length+11 < 1024 := by omega
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14,
    CiosCached.joinProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    l2At, hc, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

opaque run_r4RowAt (pc : Nat) (s : State) (mem : ByteArray) (pa pb i : Nat)
    (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hact : 88 ≤ s.activeWords.toNat) (hi : i < 4)
    (hpaFit : pa + 32 * 4 ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 4 ≤ 2816)
    (hminv : inverseInvariant mem 4)
    (hc : CiosReadonly.ReadonlyCache mem 4 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*4-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 4) :
    runInstructions r4RowProgram
      (privateStart pc s mem pb 4 i (l1Target 4) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) =
    some (privateStart (pc+284) s (rowCarry mem pa pb 4 i) pb 4 (i+1)
      (l1Target 4) inv m0
      (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  have h1 := run_outAt pc s mem pb 4 i (l1Target 4) inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
    hcap' hrun hact (by decide) (by decide) hi hpb hpbFit
  have h2 := run_commonFirstAt (pc+3) s mem (rowBi mem pb 4 i) pa pb 4 i
    (l1Target 4) tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact
    (by decide) (by decide) (by omega) hc.lowAddress hAend
  have h3 := run_l1FourAt (pc+27) s mem (rowBi mem pb 4 i) pa pb i
    (l1Target 4) inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
    hcap' hact hpaFit hsnapshot
  have hminv4 := inverse_l1Step mem (rowBi mem pb 4 i) pa 4 4 (by decide) hminv
  have h4 := run_middleAt (pc+138) s
    (l1Step mem (rowBi mem pb 4 i) pa 4 4).memory
    (l1Step mem (rowBi mem pb 4 i) pa 4 4).carry (rowBi mem pb 4 i)
    pb 4 i (l1Target 4) tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact
    (by decide) (by decide) (hc.l1 (by decide) (rowBi mem pb 4 i) pa 4) hminv4
  let mid := midMem1 (l1Step mem (rowBi mem pb 4 i) pa 4 4).memory
    (l1Step mem (rowBi mem pb 4 i) pa 4 4).carry
  let bi := rowOverflow mem pa pb 4 i
  let mu := rowMu (rowL1 mem pa pb 4 i).memory 4
  let c0 := rowC0 (rowL1 mem pa pb 4 i).memory 4
  have h5 := run_joinAt (pc+165) s mid bi mu c0 pb 4 i 0
    (l1Target 4) inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap'
  have he' : CiosReadonlyExtra.ExtraCache mid m96 m64 m32 := by
    exact (he.l1 (rowBi mem pb 4 i) pa 4 4 (by decide)).of_preserved
      (readWord_midMem1 _ _ 96 (Or.inl (by decide)))
      (readWord_midMem1 _ _ 64 (Or.inl (by decide)))
      (readWord_midMem1 _ _ 32 (Or.inl (by decide)))
  have h6 := run_extraAt 1 (pc+166) 64 2176 2208 s mid bi mu c0 pb 4 i 0
    (l1Target 4) tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact
    (by decide) (by decide) (by decide) (by decide) (by decide) he'
  have h7 := run_extraAt 2 (pc+199) 32 2144 2176 s mid bi mu c0 pb 4 i 1
    (l1Target 4) tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact
    (by decide) (by decide) (by decide) (by decide) (by decide) he'
  have h8 := run_lastAt (pc+232) s mid bi mu c0 pb 4 i (l1Target 4) inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hact
    (by decide) (by decide)
  have h9 := run_tailAdvanceAt (pc+265) s
    (l2Step mid mu c0 4 3).memory (l2Step mid mu c0 4 3).carry mu bi
    pb 4 i (l1Target 4) inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hact
  have h12 := runInstructions_append_some _ _ _ _ _ h1 h2
  have h123 := runInstructions_append_some _ _ _ _ _ h12 h3
  have h1234 := runInstructions_append_some _ _ _ _ _ h123 h4
  have h12345 := runInstructions_append_some _ _ _ _ _ h1234 h5
  have h123456 := runInstructions_append_some _ _ _ _ _ h12345 h6
  have h1234567 := runInstructions_append_some _ _ _ _ _ h123456 h7
  have h12345678 := runInstructions_append_some _ _ _ _ _ h1234567 h8
  have hall := runInstructions_append_some _ _ _ _ _ h12345678 h9
  simpa only [r4RowProgram, mid, bi, mu, c0, rowL1, rowMidCarry, rowL2Carry,
    rowOverflow, rowCarry, Nat.add_assoc, Nat.reduceAdd] using hall

opaque run_r8RowAt (pc : Nat) (s : State) (mem : ByteArray) (pa pb i : Nat)
    (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hact : 88 ≤ s.activeWords.toNat) (hi : i < 8)
    (hpaFit : pa + 32 * 8 ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 8 ≤ 2816)
    (hminv : inverseInvariant mem 8)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*8-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 8) :
    runInstructions r8RowProgram
      (privateStart pc s mem pb 8 i (l1Target 8) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) =
    some (privateStart (pc+580) s (rowCarry mem pa pb 8 i) pb 8 (i+1)
      (l1Target 8) inv m0
      (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  have h1 := run_outAt pc s mem pb 8 i (l1Target 8) inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
    hcap' hrun hact (by decide) (by decide) hi hpb hpbFit
  have h2 := run_commonFirstAt (pc+3) s mem (rowBi mem pb 8 i) pa pb 8 i
    (l1Target 8) tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact
    (by decide) (by decide) (by omega) hc.lowAddress hAend
  have h3 := run_l1EightAt (pc+27) s mem (rowBi mem pb 8 i) pa pb i
    (l1Target 8) inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
    hcap' hact hpaFit hsnapshot
  have hminv8 := inverse_l1Step mem (rowBi mem pb 8 i) pa 8 8 (by decide) hminv
  have h4 := run_middleAt (pc+286) s
    (l1Step mem (rowBi mem pb 8 i) pa 8 8).memory
    (l1Step mem (rowBi mem pb 8 i) pa 8 8).carry (rowBi mem pb 8 i)
    pb 8 i (l1Target 8) tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact
    (by decide) (by decide) (hc.l1 (by decide) (rowBi mem pb 8 i) pa 8) hminv8
  let mid := midMem1 (l1Step mem (rowBi mem pb 8 i) pa 8 8).memory
    (l1Step mem (rowBi mem pb 8 i) pa 8 8).carry
  let bi := rowOverflow mem pa pb 8 i
  let mu := rowMu (rowL1 mem pa pb 8 i).memory 8
  let c0 := rowC0 (rowL1 mem pa pb 8 i).memory 8
  have h5 := run_joinAt (pc+313) s mid bi mu c0 pb 8 i 0
    (l1Target 8) inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap'
  have h6 := CiosCached.run_l2Mac (pc+314) 10 192 2304 2336 s mid bi mu c0
    pb 8 i 0 (UInt256.ofNat dispatcherPC) (l1Target 8) inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hact
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h7 := CiosCached.run_l2Mac (pc+358) 1 160 2272 2304 s mid bi mu c0
    pb 8 i 1 (UInt256.ofNat dispatcherPC) (l1Target 8) inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hact
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h8 := CiosCached.run_l2Mac (pc+393) 1 128 2240 2272 s mid bi mu c0
    pb 8 i 2 (UInt256.ofNat dispatcherPC) (l1Target 8) inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hact
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have he' : CiosReadonlyExtra.ExtraCache mid m96 m64 m32 := by
    exact (he.l1 (rowBi mem pb 8 i) pa 8 8 (by decide)).of_preserved
      (readWord_midMem1 _ _ 96 (Or.inl (by decide)))
      (readWord_midMem1 _ _ 64 (Or.inl (by decide)))
      (readWord_midMem1 _ _ 32 (Or.inl (by decide)))
  have h9 := run_extraAt 0 (pc+428) 96 2208 2240 s mid bi mu c0 pb 8 i 3
    (l1Target 8) tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact
    (by decide) (by decide) (by decide) (by decide) (by decide) he'
  have h10 := run_joinAt (pc+461) s mid bi mu c0 pb 8 i 4
    (l1Target 8) inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap'
  have h11 := run_extraAt 1 (pc+462) 64 2176 2208 s mid bi mu c0 pb 8 i 4
    (l1Target 8) tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact
    (by decide) (by decide) (by decide) (by decide) (by decide) he'
  have h12 := run_extraAt 2 (pc+495) 32 2144 2176 s mid bi mu c0 pb 8 i 5
    (l1Target 8) tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact
    (by decide) (by decide) (by decide) (by decide) (by decide) he'
  have h13 := run_lastAt (pc+528) s mid bi mu c0 pb 8 i (l1Target 8) inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hact
    (by decide) (by decide)
  have h14 := run_tailAdvanceAt (pc+561) s
    (l2Step mid mu c0 8 7).memory (l2Step mid mu c0 8 7).carry mu bi
    pb 8 i (l1Target 8) inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hact
  have h12' := runInstructions_append_some _ _ _ _ _ h1 h2
  have h123 := runInstructions_append_some _ _ _ _ _ h12' h3
  have h1234 := runInstructions_append_some _ _ _ _ _ h123 h4
  have h12345 := runInstructions_append_some _ _ _ _ _ h1234 h5
  have h123456 := runInstructions_append_some _ _ _ _ _ h12345 h6
  have h1234567 := runInstructions_append_some _ _ _ _ _ h123456 h7
  have h12345678 := runInstructions_append_some _ _ _ _ _ h1234567 h8
  have h123456789 := runInstructions_append_some _ _ _ _ _ h12345678 h9
  have h12345678910 := runInstructions_append_some _ _ _ _ _ h123456789 h10
  have h1234567891011 := runInstructions_append_some _ _ _ _ _ h12345678910 h11
  have h123456789101112 := runInstructions_append_some _ _ _ _ _ h1234567891011 h12
  have h12345678910111213 := runInstructions_append_some _ _ _ _ _ h123456789101112 h13
  have hall := runInstructions_append_some _ _ _ _ _ h12345678910111213 h14
  simpa only [r8RowProgram, mid, bi, mu, c0, rowL1, rowMidCarry, rowL2Carry,
    rowOverflow, rowCarry, Nat.add_assoc, Nat.reduceAdd] using hall

opaque gasSteps_firstFour (L : CarryIface.RowLemmas) (s : State) (mem : ByteArray)
    (pa pb : Nat) (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hpaFit : pa + 32 * 4 ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 4 ≤ 2816)
    (hminv : inverseInvariant mem 4)
    (hc : CiosReadonly.ReadonlyCache mem 4 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*4-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 4) :
    Challenge.EvmProof.GasSteps
      (privateStart 3520 s mem pb 4 0 (l1Target 4) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (privateStart dispatcherPC s (rowCarry mem pa pb 4 0) pb 4 1
        (l1Target 4) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  have g1 : Challenge.EvmProof.GasSteps
      (privateStart 3520 s mem pb 4 0 (l1Target 4) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (firstAt 3523 s mem (rowBi mem pb 4 0) pb 4 0 (UInt256.ofNat dispatcherPC)
        (l1Target 4) inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) :=
    CarryRowBlocks.out.steps (environment _ hcode hfork hrun hnp) rfl
      (run_outAt 3520 s mem pb 4 0 (l1Target 4) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
        hcap' hrun hact (by decide) (by decide) (by decide) hpb hpbFit)
  have hminv4 := inverse_l1Step mem (rowBi mem pb 4 0) pa 4 4 (by decide) hminv
  refine g1.trans (L.gasSteps_commonFirst s mem (rowBi mem pb 4 0) pa pb 4 0
    (UInt256.ofNat dispatcherPC) (l1Target 4) tl inv m0 aEnd m96 m64 m32 pdst ret rest
    hcap hrun hcode hfork hnp hact (by decide) (by decide) (by omega)
    hc.lowAddress hAend) |>.trans ?_
  refine (L.gasSteps_l1MulFour s mem (rowBi mem pb 4 0) pa pb 0
    (UInt256.ofNat dispatcherPC) inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp
    hact hpaFit hsnapshot).trans ?_
  refine (L.gasSteps_mid s (l1Step mem (rowBi mem pb 4 0) pa 4 4).memory
    (l1Step mem (rowBi mem pb 4 0) pa 4 4).carry (rowBi mem pb 4 0) pb 4 0
    (UInt256.ofNat dispatcherPC) (l1Target 4) tl inv m0 aEnd m96 m64 m32 pdst ret rest
    hcap hrun hcode hfork hnp hact (by decide) (by decide) hminv4
    (hc.l1 (by decide) (rowBi mem pb 4 0) pa 4)).trans ?_
  refine (by simpa only [rowL1, rowMidCarry, rowL2Carry, rowOverflow] using
    L.gasSteps_l2Four s
      (midMem1 (l1Step mem (rowBi mem pb 4 0) pa 4 4).memory
        (l1Step mem (rowBi mem pb 4 0) pa 4 4).carry)
      (rowOverflow mem pa pb 4 0) (rowMu (rowL1 mem pa pb 4 0).memory 4)
      (rowC0 (rowL1 mem pa pb 4 0).memory 4) pb 0 (UInt256.ofNat dispatcherPC)
      (l1Target 4) tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact
      ((he.l1 (rowBi mem pb 4 0) pa 4 4 (by decide)).of_preserved
        (readWord_midMem1 _ _ 96 (Or.inl (by decide)))
        (readWord_midMem1 _ _ 64 (Or.inl (by decide)))
        (readWord_midMem1 _ _ 32 (Or.inl (by decide))))).trans ?_
  simpa only [privateStart, rowCarry, rowOverflow] using
    L.gasSteps_tailNext s (rowL2Carry mem pa pb 4 0).memory
      (rowL2Carry mem pa pb 4 0).carry (rowMu (rowL1 mem pa pb 4 0).memory 4)
      (rowOverflow mem pa pb 4 0) pb 4 0 (UInt256.ofNat dispatcherPC) (l1Target 4)
      inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap'
      hrun hcode hfork hnp hact (by decide) hpb hpbFit jumpDest_dispatcher

opaque gasSteps_firstEight (L : CarryIface.RowLemmas) (s : State) (mem : ByteArray)
    (pa pb : Nat) (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hpaFit : pa + 32 * 8 ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 8 ≤ 2816)
    (hminv : inverseInvariant mem 8)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*8-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 8) :
    Challenge.EvmProof.GasSteps
      (privateStart 3520 s mem pb 8 0 (l1Target 8) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (privateStart dispatcherPC s (rowCarry mem pa pb 8 0) pb 8 1
        (l1Target 8) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  have g1 : Challenge.EvmProof.GasSteps
      (privateStart 3520 s mem pb 8 0 (l1Target 8) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (firstAt 3523 s mem (rowBi mem pb 8 0) pb 8 0 (UInt256.ofNat dispatcherPC)
        (l1Target 8) inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) :=
    CarryRowBlocks.out.steps (environment _ hcode hfork hrun hnp) rfl
      (run_outAt 3520 s mem pb 8 0 (l1Target 8) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
        hcap' hrun hact (by decide) (by decide) (by decide) hpb hpbFit)
  have hminv8 := inverse_l1Step mem (rowBi mem pb 8 0) pa 8 8 (by decide) hminv
  refine g1.trans (L.gasSteps_commonFirst s mem (rowBi mem pb 8 0) pa pb 8 0
    (UInt256.ofNat dispatcherPC) (l1Target 8) tl inv m0 aEnd m96 m64 m32 pdst ret rest
    hcap hrun hcode hfork hnp hact (by decide) (by decide) (by omega)
    hc.lowAddress hAend) |>.trans ?_
  refine (L.gasSteps_l1MulEight s mem (rowBi mem pb 8 0) pa pb 0
    (UInt256.ofNat dispatcherPC) inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp
    hact hpaFit hsnapshot).trans ?_
  refine (L.gasSteps_mid s (l1Step mem (rowBi mem pb 8 0) pa 8 8).memory
    (l1Step mem (rowBi mem pb 8 0) pa 8 8).carry (rowBi mem pb 8 0) pb 8 0
    (UInt256.ofNat dispatcherPC) (l1Target 8) tl inv m0 aEnd m96 m64 m32 pdst ret rest
    hcap hrun hcode hfork hnp hact (by decide) (by decide) hminv8
    (hc.l1 (by decide) (rowBi mem pb 8 0) pa 8)).trans ?_
  refine (by simpa only [rowL1, rowMidCarry, rowL2Carry, rowOverflow] using
    L.gasSteps_l2Eight s
      (midMem1 (l1Step mem (rowBi mem pb 8 0) pa 8 8).memory
        (l1Step mem (rowBi mem pb 8 0) pa 8 8).carry)
      (rowOverflow mem pa pb 8 0) (rowMu (rowL1 mem pa pb 8 0).memory 8)
      (rowC0 (rowL1 mem pa pb 8 0).memory 8) pb 0 (UInt256.ofNat dispatcherPC)
      (l1Target 8) tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact
      ((he.l1 (rowBi mem pb 8 0) pa 8 8 (by decide)).of_preserved
        (readWord_midMem1 _ _ 96 (Or.inl (by decide)))
        (readWord_midMem1 _ _ 64 (Or.inl (by decide)))
        (readWord_midMem1 _ _ 32 (Or.inl (by decide))))).trans ?_
  simpa only [privateStart, rowCarry, rowOverflow] using
    L.gasSteps_tailNext s (rowL2Carry mem pa pb 8 0).memory
      (rowL2Carry mem pa pb 8 0).carry (rowMu (rowL1 mem pa pb 8 0).memory 8)
      (rowOverflow mem pa pb 8 0) pb 8 0 (UInt256.ofNat dispatcherPC) (l1Target 8)
      inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap'
      hrun hcode hfork hnp hact (by decide) hpb hpbFit jumpDest_dispatcher

opaque gasSteps_r4Row (pc : Nat)
    (block : Block Artifact.submissionArtifact .Osaka pc r4RowProgram)
    (s : State) (mem : ByteArray) (pa pb i : Nat)
    (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hi : i < 4)
    (hpaFit : pa + 32 * 4 ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 4 ≤ 2816)
    (hminv : inverseInvariant mem 4)
    (hc : CiosReadonly.ReadonlyCache mem 4 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*4-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 4) :
    Challenge.EvmProof.GasSteps
      (privateStart pc s mem pb 4 i (l1Target 4) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (privateStart (pc+284) s (rowCarry mem pa pb 4 i) pb 4 (i+1)
        (l1Target 4) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) :=
  block.steps (environment _ hcode hfork hrun hnp) rfl
    (run_r4RowAt pc s mem pa pb i tl inv m0 aEnd m96 m64 m32 pdst ret rest
      hcap hrun hact hi hpaFit hpb hpbFit hminv hc he hAend hsnapshot)

opaque gasSteps_r8Row (pc : Nat)
    (block : Block Artifact.submissionArtifact .Osaka pc r8RowProgram)
    (s : State) (mem : ByteArray) (pa pb i : Nat)
    (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hi : i < 8)
    (hpaFit : pa + 32 * 8 ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 8 ≤ 2816)
    (hminv : inverseInvariant mem 8)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*8-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 8) :
    Challenge.EvmProof.GasSteps
      (privateStart pc s mem pb 8 i (l1Target 8) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (privateStart (pc+580) s (rowCarry mem pa pb 8 i) pb 8 (i+1)
        (l1Target 8) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) :=
  block.steps (environment _ hcode hfork hrun hnp) rfl
    (run_r8RowAt pc s mem pa pb i tl inv m0 aEnd m96 m64 m32 pdst ret rest
      hcap hrun hact hi hpaFit hpb hpbFit hminv hc he hAend hsnapshot)

opaque gasSteps_dispatch4 (s : State) (mem : ByteArray) (pb i : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (privateStart dispatcherPC s mem pb 4 i (l1Target 4) pdst ret rest)
      (privateStart r4PC s mem pb 4 i (l1Target 4) pdst ret rest) :=
  dispatcherBlock.steps (environment _ hcode hfork hrun hnp) rfl
    (run_dispatch4 s mem pb i pdst ret rest hcap)

opaque gasSteps_dispatch8 (s : State) (mem : ByteArray) (pb i : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (privateStart dispatcherPC s mem pb 8 i (l1Target 8) pdst ret rest)
      (privateStart r8PC s mem pb 8 i (l1Target 8) pdst ret rest) :=
  dispatcherBlock.steps (environment _ hcode hfork hrun hnp) rfl
    (run_dispatch8 s mem pb i pdst ret rest hcap hcode)

theorem jumpDest_exit :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4109 = true :=
  Artifact.isValidJumpDest_index 3115 (by rfl)

theorem run_finalJumpAt (pc : Nat) (s : State) (mem : ByteArray) (pb n : Nat)
    (ent pdst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions finalJumpProgram
      (privateStart pc s mem pb n n ent pdst ret rest) =
    some (CiosCachedTailDefs.exitState s mem
      (UInt256.ofNat (ptrAt (pb+32*n-32) n)) pb n (UInt256.ofNat dispatcherPC)
      ent pdst ret rest) := by
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hj : Decode.isValidJumpDest s.executionEnv.code 4109 = true := by
    rw [hcode]; exact jumpDest_exit
  simp [finalJumpProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    privateStart, outState, CiosCachedTailDefs.exitState, framed, hc9, hc10, hj,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

opaque gasSteps_finalJump (pc : Nat)
    (block : Block Artifact.submissionArtifact .Osaka pc finalJumpProgram)
    (s : State) (mem : ByteArray) (pb n : Nat)
    (ent pdst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (privateStart pc s mem pb n n ent pdst ret rest)
      (CiosCachedTailDefs.exitState s mem
        (UInt256.ofNat (ptrAt (pb+32*n-32) n)) pb n (UInt256.ofNat dispatcherPC)
        ent pdst ret rest) :=
  block.steps (environment _ hcode hfork hrun hnp) rfl
    (run_finalJumpAt pc s mem pb n ent pdst ret rest hcap hcode)

opaque gasSteps_exit (s : State) (mem : ByteArray) (pb n : Nat)
    (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (CiosCachedTailDefs.exitState s mem (UInt256.ofNat (ptrAt (pb+32*n-32) n))
        pb n (UInt256.ofNat dispatcherPC) (l1Target n) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (mpCsubState s mem pdst ret rest) := by
  let pbi := UInt256.ofNat (ptrAt (pb+32*n-32) n)
  let frameRest := tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest
  have hcap' : frameRest.length ≤ 1005 := by
    simp only [frameRest, List.length_cons]; omega
  have g1 := CarryRowGas.gasSteps_dispatchMul {s with memory := mem} mem pbi pb n
    (UInt256.ofNat dispatcherPC) (l1Target n) inv m0 frameRest hcap'
    hrun hcode hfork hnp (by decide)
  have g2 := CarryRowGas.gasSteps_nxJd {s with memory := mem} mem pbi pb n
    (UInt256.ofNat dispatcherPC) (l1Target n) inv m0 frameRest hcap'
    hrun hcode hfork hnp
  have g3 : Challenge.EvmProof.GasSteps
      (CiosCachedTailDefs.nxState s mem pbi pb n (UInt256.ofNat dispatcherPC)
        (l1Target n) inv m0 frameRest)
      (mpCsubState s mem pdst ret rest) :=
    CarryRowBlocks.exitBlock.steps (environment _ hcode hfork hrun hnp) rfl
      (CiosReadonly.run_exit {s with memory := mem} pbi (UInt256.ofNat dispatcherPC)
        (UInt256.ofNat (pb-32)) (l1Target n) (l2Target n) tl inv m0 aEnd
        m96 m64 m32 pdst ret rest hcap)
  exact (g1.trans g2).trans g3

opaque gasSteps_rowsFour (L : CarryIface.RowLemmas) (s : State) (mem : ByteArray)
    (pa pb : Nat) (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hpaFit : pa + 32 * 4 ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 4 ≤ 2816)
    (hminv : inverseInvariant mem 4)
    (hc : CiosReadonly.ReadonlyCache mem 4 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*4-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 4) :
    Challenge.EvmProof.GasSteps
      (privateStart 3520 s (mpZeroed s mem 4) pb 4 0 (l1Target 4) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (mpCsubState s (rowsCarry (mpZeroed s mem 4) pa pb 4 4) pdst ret rest) := by
  let base := mpZeroed s mem 4
  let frameRest := tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest
  have hcap' : frameRest.length ≤ 1005 := by
    simp only [frameRest, List.length_cons]; omega
  have hsz := hsnapshot.zeroed_stage s (by decide) hpaFit
  have hminvz := inverse_mpZeroed s mem 4 (by decide) hminv
  have hcz := hc.zeroed (by decide) s
  have hez := he.zeroed s 4 (by decide)
  have g0 := gasSteps_firstFour L s base pa pb tl inv m0 aEnd m96 m64 m32 pdst ret rest
    hcap hrun hcode hfork hnp hact hpaFit hpb hpbFit hminvz hcz hez hAend hsz
  have gd := gasSteps_dispatch4 s (rowsCarry base pa pb 4 1) pb 1 inv m0 frameRest
    hcap' hrun hcode hfork hnp
  have g1 := gasSteps_r4Row 5349 r4Block0 s (rowsCarry base pa pb 4 1) pa pb 1
    tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide)
    hpaFit hpb hpbFit
    (CarryFull.inverse_rowsCarry base pa pb 4 1 (by decide) hminvz)
    (CarryFull.readonlyCache_rowsCarry hcz (by decide) pa pb 1)
    (CarryFull.extraCache_rowsCarry hez pa pb 4 1 (by decide)) hAend
    (hsz.rows_stage pb 1 (by decide) hpaFit)
  have g2 := gasSteps_r4Row 5633 r4Block1 s (rowsCarry base pa pb 4 2) pa pb 2
    tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide)
    hpaFit hpb hpbFit
    (CarryFull.inverse_rowsCarry base pa pb 4 2 (by decide) hminvz)
    (CarryFull.readonlyCache_rowsCarry hcz (by decide) pa pb 2)
    (CarryFull.extraCache_rowsCarry hez pa pb 4 2 (by decide)) hAend
    (hsz.rows_stage pb 2 (by decide) hpaFit)
  have g3 := gasSteps_r4Row 5917 r4Block2 s (rowsCarry base pa pb 4 3) pa pb 3
    tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide)
    hpaFit hpb hpbFit
    (CarryFull.inverse_rowsCarry base pa pb 4 3 (by decide) hminvz)
    (CarryFull.readonlyCache_rowsCarry hcz (by decide) pa pb 3)
    (CarryFull.extraCache_rowsCarry hez pa pb 4 3 (by decide)) hAend
    (hsz.rows_stage pb 3 (by decide) hpaFit)
  have gf := gasSteps_finalJump 6201 finalJump4 s (rowsCarry base pa pb 4 4) pb 4
    (l1Target 4) inv m0 frameRest hcap' hrun hcode hfork hnp
  have gx := gasSteps_exit s (rowsCarry base pa pb 4 4) pb 4 tl inv m0 aEnd m96 m64 m32
    pdst ret rest hcap hrun hcode hfork hnp
  have g0' : Challenge.EvmProof.GasSteps
      (privateStart 3520 s base pb 4 0 (l1Target 4) inv m0 frameRest)
      (privateStart dispatcherPC s (rowsCarry base pa pb 4 1) pb 4 1
        (l1Target 4) inv m0 frameRest) := by
    simpa only [frameRest, base, rowsCarry] using g0
  have gd' : Challenge.EvmProof.GasSteps
      (privateStart dispatcherPC s (rowsCarry base pa pb 4 1) pb 4 1
        (l1Target 4) inv m0 frameRest)
      (privateStart r4PC s (rowsCarry base pa pb 4 1) pb 4 1
        (l1Target 4) inv m0 frameRest) := gd
  have g1' := g1
  have g2' : Challenge.EvmProof.GasSteps
      (privateStart 5633 s (rowsCarry base pa pb 4 2) pb 4 2 (l1Target 4) inv m0 frameRest)
      (privateStart 5917 s (rowsCarry base pa pb 4 3) pb 4 3 (l1Target 4) inv m0 frameRest) := by
    simpa only [frameRest, rowsCarry] using g2
  have g3' : Challenge.EvmProof.GasSteps
      (privateStart 5917 s (rowsCarry base pa pb 4 3) pb 4 3 (l1Target 4) inv m0 frameRest)
      (privateStart 6201 s (rowsCarry base pa pb 4 4) pb 4 4 (l1Target 4) inv m0 frameRest) := by
    simpa only [frameRest, rowsCarry] using g3
  have g1'' : Challenge.EvmProof.GasSteps
      (privateStart r4PC s (rowsCarry base pa pb 4 1) pb 4 1 (l1Target 4) inv m0 frameRest)
      (privateStart 5633 s (rowsCarry base pa pb 4 2) pb 4 2 (l1Target 4) inv m0 frameRest) := by
    simpa only [frameRest, rowsCarry] using g1'
  exact ((((((g0'.trans gd').trans g1'').trans g2').trans g3').trans gf).trans gx)

opaque gasSteps_rowsEight (L : CarryIface.RowLemmas) (s : State) (mem : ByteArray)
    (pa pb : Nat) (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hpaFit : pa + 32 * 8 ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 8 ≤ 2816)
    (hminv : inverseInvariant mem 8)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*8-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 8) :
    Challenge.EvmProof.GasSteps
      (privateStart 3520 s (mpZeroed s mem 8) pb 8 0 (l1Target 8) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (mpCsubState s (rowsCarry (mpZeroed s mem 8) pa pb 8 8) pdst ret rest) := by
  let base := mpZeroed s mem 8
  let frameRest := tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest
  have hcap' : frameRest.length ≤ 1005 := by
    simp only [frameRest, List.length_cons]; omega
  have hsz := hsnapshot.zeroed_stage s (by decide) hpaFit
  have hminvz := inverse_mpZeroed s mem 8 (by decide) hminv
  have hcz := hc.zeroed (by decide) s
  have hez := he.zeroed s 8 (by decide)
  have g0 := gasSteps_firstEight L s base pa pb tl inv m0 aEnd m96 m64 m32 pdst ret rest
    hcap hrun hcode hfork hnp hact hpaFit hpb hpbFit hminvz hcz hez hAend hsz
  have gd := gasSteps_dispatch8 s (rowsCarry base pa pb 8 1) pb 1 inv m0 frameRest
    hcap' hrun hcode hfork hnp
  have g1 := gasSteps_r8Row 6205 r8Block0 s (rowsCarry base pa pb 8 1) pa pb 1
    tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide)
    hpaFit hpb hpbFit (CarryFull.inverse_rowsCarry base pa pb 8 1 (by decide) hminvz)
    (CarryFull.readonlyCache_rowsCarry hcz (by decide) pa pb 1)
    (CarryFull.extraCache_rowsCarry hez pa pb 8 1 (by decide)) hAend
    (hsz.rows_stage pb 1 (by decide) hpaFit)
  have g2 := gasSteps_r8Row 6785 r8Block1 s (rowsCarry base pa pb 8 2) pa pb 2
    tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide)
    hpaFit hpb hpbFit (CarryFull.inverse_rowsCarry base pa pb 8 2 (by decide) hminvz)
    (CarryFull.readonlyCache_rowsCarry hcz (by decide) pa pb 2)
    (CarryFull.extraCache_rowsCarry hez pa pb 8 2 (by decide)) hAend
    (hsz.rows_stage pb 2 (by decide) hpaFit)
  have g3 := gasSteps_r8Row 7365 r8Block2 s (rowsCarry base pa pb 8 3) pa pb 3
    tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide)
    hpaFit hpb hpbFit (CarryFull.inverse_rowsCarry base pa pb 8 3 (by decide) hminvz)
    (CarryFull.readonlyCache_rowsCarry hcz (by decide) pa pb 3)
    (CarryFull.extraCache_rowsCarry hez pa pb 8 3 (by decide)) hAend
    (hsz.rows_stage pb 3 (by decide) hpaFit)
  have g4 := gasSteps_r8Row 7945 r8Block3 s (rowsCarry base pa pb 8 4) pa pb 4
    tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide)
    hpaFit hpb hpbFit (CarryFull.inverse_rowsCarry base pa pb 8 4 (by decide) hminvz)
    (CarryFull.readonlyCache_rowsCarry hcz (by decide) pa pb 4)
    (CarryFull.extraCache_rowsCarry hez pa pb 8 4 (by decide)) hAend
    (hsz.rows_stage pb 4 (by decide) hpaFit)
  have g5 := gasSteps_r8Row 8525 r8Block4 s (rowsCarry base pa pb 8 5) pa pb 5
    tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide)
    hpaFit hpb hpbFit (CarryFull.inverse_rowsCarry base pa pb 8 5 (by decide) hminvz)
    (CarryFull.readonlyCache_rowsCarry hcz (by decide) pa pb 5)
    (CarryFull.extraCache_rowsCarry hez pa pb 8 5 (by decide)) hAend
    (hsz.rows_stage pb 5 (by decide) hpaFit)
  have g6 := gasSteps_r8Row 9105 r8Block5 s (rowsCarry base pa pb 8 6) pa pb 6
    tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide)
    hpaFit hpb hpbFit (CarryFull.inverse_rowsCarry base pa pb 8 6 (by decide) hminvz)
    (CarryFull.readonlyCache_rowsCarry hcz (by decide) pa pb 6)
    (CarryFull.extraCache_rowsCarry hez pa pb 8 6 (by decide)) hAend
    (hsz.rows_stage pb 6 (by decide) hpaFit)
  have g7 := gasSteps_r8Row 9685 r8Block6 s (rowsCarry base pa pb 8 7) pa pb 7
    tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide)
    hpaFit hpb hpbFit (CarryFull.inverse_rowsCarry base pa pb 8 7 (by decide) hminvz)
    (CarryFull.readonlyCache_rowsCarry hcz (by decide) pa pb 7)
    (CarryFull.extraCache_rowsCarry hez pa pb 8 7 (by decide)) hAend
    (hsz.rows_stage pb 7 (by decide) hpaFit)
  have gf := gasSteps_finalJump 10265 finalJump8 s (rowsCarry base pa pb 8 8) pb 8
    (l1Target 8) inv m0 frameRest hcap' hrun hcode hfork hnp
  have gx := gasSteps_exit s (rowsCarry base pa pb 8 8) pb 8 tl inv m0 aEnd m96 m64 m32
    pdst ret rest hcap hrun hcode hfork hnp
  have g0' : Challenge.EvmProof.GasSteps
      (privateStart 3520 s base pb 8 0 (l1Target 8) inv m0 frameRest)
      (privateStart dispatcherPC s (rowsCarry base pa pb 8 1) pb 8 1
        (l1Target 8) inv m0 frameRest) := by
    simpa only [frameRest, base, rowsCarry] using g0
  have gd' : Challenge.EvmProof.GasSteps
      (privateStart dispatcherPC s (rowsCarry base pa pb 8 1) pb 8 1
        (l1Target 8) inv m0 frameRest)
      (privateStart r8PC s (rowsCarry base pa pb 8 1) pb 8 1
        (l1Target 8) inv m0 frameRest) := gd
  have g1' : Challenge.EvmProof.GasSteps
      (privateStart 6205 s (rowsCarry base pa pb 8 1) pb 8 1 (l1Target 8) inv m0 frameRest)
      (privateStart 6785 s (rowsCarry base pa pb 8 2) pb 8 2 (l1Target 8) inv m0 frameRest) := by
    simpa only [frameRest, rowsCarry] using g1
  have g2' : Challenge.EvmProof.GasSteps
      (privateStart 6785 s (rowsCarry base pa pb 8 2) pb 8 2 (l1Target 8) inv m0 frameRest)
      (privateStart 7365 s (rowsCarry base pa pb 8 3) pb 8 3 (l1Target 8) inv m0 frameRest) := by
    simpa only [frameRest, rowsCarry] using g2
  have g3' : Challenge.EvmProof.GasSteps
      (privateStart 7365 s (rowsCarry base pa pb 8 3) pb 8 3 (l1Target 8) inv m0 frameRest)
      (privateStart 7945 s (rowsCarry base pa pb 8 4) pb 8 4 (l1Target 8) inv m0 frameRest) := by
    simpa only [frameRest, rowsCarry] using g3
  have g4' : Challenge.EvmProof.GasSteps
      (privateStart 7945 s (rowsCarry base pa pb 8 4) pb 8 4 (l1Target 8) inv m0 frameRest)
      (privateStart 8525 s (rowsCarry base pa pb 8 5) pb 8 5 (l1Target 8) inv m0 frameRest) := by
    simpa only [frameRest, rowsCarry] using g4
  have g5' : Challenge.EvmProof.GasSteps
      (privateStart 8525 s (rowsCarry base pa pb 8 5) pb 8 5 (l1Target 8) inv m0 frameRest)
      (privateStart 9105 s (rowsCarry base pa pb 8 6) pb 8 6 (l1Target 8) inv m0 frameRest) := by
    simpa only [frameRest, rowsCarry] using g5
  have g6' : Challenge.EvmProof.GasSteps
      (privateStart 9105 s (rowsCarry base pa pb 8 6) pb 8 6 (l1Target 8) inv m0 frameRest)
      (privateStart 9685 s (rowsCarry base pa pb 8 7) pb 8 7 (l1Target 8) inv m0 frameRest) := by
    simpa only [frameRest, rowsCarry] using g6
  have g7' : Challenge.EvmProof.GasSteps
      (privateStart 9685 s (rowsCarry base pa pb 8 7) pb 8 7 (l1Target 8) inv m0 frameRest)
      (privateStart 10265 s (rowsCarry base pa pb 8 8) pb 8 8 (l1Target 8) inv m0 frameRest) := by
    simpa only [frameRest, rowsCarry] using g7
  exact ((((((((((g0'.trans gd').trans g1').trans g2').trans g3').trans g4').trans g5').trans
    g6').trans g7').trans gf).trans gx)

end Challenge.Modexp.Submission.Proofs.Fast.UnrolledRows
