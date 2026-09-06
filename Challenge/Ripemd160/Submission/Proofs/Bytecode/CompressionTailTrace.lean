import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionRightLoopTrace
import Challenge.EvmProof.Memory

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

/-!
# Direct trace of the RIPEMD-160 compression tail

The 82-instruction cross-combination is split at its natural stack seams:
compute `h0`, compute/store `h1` through `h4`, store the retained `h0`, then
clean up and return.  Keeping each direct execution proof below 21
instructions bounds elaboration while retaining one artifact-pinned path.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionTailTrace

open EvmSemantics
open EvmSemantics.EVM
open CompressionTrace
open CompressionRightTrace

def combination0Located := combinationLocated.take 10
def combination1Located := (combinationLocated.drop 10).take 15
def combination2Located := (combinationLocated.drop 25).take 15
def combination3Located := (combinationLocated.drop 40).take 15
def combination4Located := (combinationLocated.drop 55).take 20
def combinationCleanupLocated := combinationLocated.drop 75
def combinationPopsLocated := combinationCleanupLocated.take 6
def combinationJumpLocated := combinationCleanupLocated.drop 6

@[simp] private theorem combination0PC (j : Nat) (hlo : 565 ≤ j)
    (hhi : j ≤ 574) :
    Artifact.submissionArtifact.instructionPC j =
      [806, 811, 814, 815, 818, 819, 822, 823, 824, 825][j - 565]! := by
  interval_cases j <;> rfl

@[simp] private theorem combination1PC (j : Nat) (hlo : 575 ≤ j)
    (hhi : j ≤ 589) :
    Artifact.submissionArtifact.instructionPC j =
      [826, 831, 834, 835, 838, 839, 842, 843, 844, 845, 846, 851,
       852, 853, 855][j - 575]! := by
  interval_cases j <;> rfl

@[simp] private theorem combination2PC (j : Nat) (hlo : 590 ≤ j)
    (hhi : j ≤ 604) :
    Artifact.submissionArtifact.instructionPC j =
      [856, 861, 864, 865, 868, 869, 872, 873, 874, 875, 876, 881,
       882, 883, 885][j - 590]! := by
  interval_cases j <;> rfl

@[simp] private theorem combination3PC (j : Nat) (hlo : 605 ≤ j)
    (hhi : j ≤ 619) :
    Artifact.submissionArtifact.instructionPC j =
      [886, 891, 894, 895, 897, 898, 901, 902, 903, 904, 905, 910,
       911, 912, 914][j - 605]! := by
  interval_cases j <;> rfl

@[simp] private theorem combination4PC (j : Nat) (hlo : 620 ≤ j)
    (hhi : j ≤ 639) :
    Artifact.submissionArtifact.instructionPC j =
      [915, 920, 923, 924, 926, 927, 930, 931, 932, 933, 934, 939,
       940, 941, 943, 944, 949, 950, 951, 953][j - 620]! := by
  interval_cases j <;> rfl

@[simp] theorem combinationCleanupPC (j : Nat) (hlo : 640 ≤ j)
    (hhi : j ≤ 646) :
    Artifact.submissionArtifact.instructionPC j =
      [954, 955, 956, 957, 958, 959, 960][j - 640]! := by
  interval_cases j <;> rfl

def storeWordMemory (memory : ByteArray) (offset : Nat)
    (value : UInt256) : ByteArray :=
  MachineState.writeBytes memory
    (Data.Bytes.natToBytesPadded value.toNat 32) offset

@[simp] private theorem readWord_storeWordMemory_after (memory : ByteArray)
    (writeStart readStart : Nat) (value : UInt256)
    (hbefore : writeStart + 32 ≤ readStart) :
    MachineState.readWord (storeWordMemory memory writeStart value) readStart =
      MachineState.readWord memory readStart := by
  unfold storeWordMemory
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  right
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hbefore

@[simp] private theorem readWord_writePadded32_after (memory : ByteArray)
    (writeStart readStart : Nat) (value : UInt256)
    (hbefore : writeStart + 32 ≤ readStart) :
    MachineState.readWord
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value.toNat 32) writeStart)
        readStart = MachineState.readWord memory readStart := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  right
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hbefore

def touchWord (s : State) (offset : Nat) : State :=
  { s with activeWords := s.activeWordsAfterUInt256 offset 32 }

def touched0 (s : State) : State :=
  touchWord (touchWord (touchWord s 448) 256) 544

def touched1 (s : State) : State :=
  touchWord (touchWord (touchWord (touchWord (touched0 s) 480) 288) 576) 64

def touched2 (s : State) : State :=
  touchWord (touchWord (touchWord (touchWord (touched1 s) 352) 320) 608) 96

def touched3 (s : State) : State :=
  touchWord (touchWord (touchWord (touchWord (touched2 s) 384) 192) 640) 128

def touched4 (s : State) : State :=
  touchWord
    (touchWord (touchWord (touchWord (touchWord (touched3 s) 416) 224) 512) 160)
    32

def combination0 (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  let t := touched0 s
  { t with pc := UInt256.ofNat 826
           stack := (tailCombination s).h0 :: messageOffset :: returnDest :: rest }

def combination1 (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  let out := tailCombination s
  let t := touched1 s
  { t with pc := UInt256.ofNat 856
           stack := out.h1 :: out.h0 :: messageOffset :: returnDest :: rest
           memory := storeWordMemory s.memory 64 out.h1 }

def combination2 (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  let out := tailCombination s
  let t := touched2 s
  { t with pc := UInt256.ofNat 886
           stack := out.h2 :: out.h1 :: out.h0 ::
             messageOffset :: returnDest :: rest
           memory := storeWordMemory (storeWordMemory s.memory 64 out.h1)
             96 out.h2 }

def combination3 (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  let out := tailCombination s
  let t := touched3 s
  { t with pc := UInt256.ofNat 915
           stack := out.h3 :: out.h2 :: out.h1 :: out.h0 ::
             messageOffset :: returnDest :: rest
           memory := storeWordMemory
             (storeWordMemory (storeWordMemory s.memory 64 out.h1) 96 out.h2)
             128 out.h3 }

def combination4 (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  let out := tailCombination s
  let m1 := storeWordMemory s.memory 64 out.h1
  let m2 := storeWordMemory m1 96 out.h2
  let m3 := storeWordMemory m2 128 out.h3
  let m4 := storeWordMemory m3 160 out.h4
  let m5 := storeWordMemory m4 32 out.h0
  let t := touched4 s
  { t with pc := UInt256.ofNat 954
           stack := out.h4 :: out.h3 :: out.h2 :: out.h1 :: out.h0 ::
             messageOffset :: returnDest :: rest
           memory := m5 }

theorem activeWords_unchanged (s : State)
    (hactive : 21 ≤ s.activeWords.toNat) (off : Nat) (hoff : off ≤ 640) :
    s.activeWordsAfterUInt256 off 32 = s.activeWords := by
  have hn : MachineState.activeWordsAfter s.activeWords.toNat off 32 =
      s.activeWords.toNat := by
    simp [MachineState.activeWordsAfter]
    omega
  unfold State.activeWordsAfterUInt256
  rw [hn]
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt s.activeWords.val.isLt

@[simp] private theorem land_eq_and (x y : UInt256) :
    UInt256.land x y = x &&& y := by rfl

@[simp] private theorem land_mask_idem (x : UInt256) :
    UInt256.land (UInt256.land x (UInt256.ofNat 0xffffffff))
      (UInt256.ofNat 0xffffffff) =
        UInt256.land x (UInt256.ofNat 0xffffffff) := by
  rw [land_eq_and, land_eq_and]
  simpa [Challenge.EvmProof.Word.mask32] using
    Challenge.EvmProof.Word.mask32_idem x

@[simp] private theorem and_mask_idem (x : UInt256) :
    (x &&& UInt256.ofNat 0xffffffff) &&& UInt256.ofNat 0xffffffff =
      x &&& UInt256.ofNat 0xffffffff := by
  simpa [Challenge.EvmProof.Word.mask32] using
    Challenge.EvmProof.Word.mask32_idem x

set_option linter.unusedSimpArgs false in
theorem run_combination0 (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 970)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock combination0Located
      (combinationEntry s messageOffset returnDest rest) =
        some (combination0 s messageOffset returnDest rest) := by
  have hcap (m : Nat) (hm : m ≤ 12) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 250000 })
    [combination0Located, combinationLocated,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      combinationEntry, combination0, touched0, touchWord, tailCombination,
      Compression.evmCombine,
      savedHashAt512, workingAt, wordAt, Challenge.EvmProof.Word.mask32,
      State.activeWordsAfterUInt256, hrun, hcap,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_combination1 (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 970)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock combination1Located
      (combination0 s messageOffset returnDest rest) =
        some (combination1 s messageOffset returnDest rest) := by
  have hcap (m : Nat) (hm : m ≤ 13) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 300000 })
    [combination1Located, combinationLocated,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      combination0, combination1, touched0, touched1, touchWord,
      storeWordMemory, tailCombination, Compression.evmCombine,
      savedHashAt512, workingAt, wordAt, Challenge.EvmProof.Word.mask32,
      Challenge.EvmProof.Word.mask32_idem,
      State.activeWordsAfterUInt256, hrun, hcap,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_combination2 (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 970)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock combination2Located
      (combination1 s messageOffset returnDest rest) =
        some (combination2 s messageOffset returnDest rest) := by
  have hcap (m : Nat) (hm : m ≤ 14) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 350000 })
    [combination2Located, combinationLocated,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      combination1, combination2, touched0, touched1, touched2, touchWord,
      storeWordMemory, tailCombination, Compression.evmCombine,
      savedHashAt512, workingAt, wordAt, Challenge.EvmProof.Word.mask32,
      Challenge.EvmProof.Word.mask32_idem,
      Challenge.EvmProof.Memory.readWord_writeBytes_disjoint,
      State.activeWordsAfterUInt256, hrun, hcap,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_combination3 (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 970)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock combination3Located
      (combination2 s messageOffset returnDest rest) =
        some (combination3 s messageOffset returnDest rest) := by
  have hcap (m : Nat) (hm : m ≤ 15) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 400000 })
    [combination3Located, combinationLocated,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      combination2, combination3, touched0, touched1, touched2, touched3,
      touchWord, storeWordMemory, tailCombination, Compression.evmCombine,
      savedHashAt512, workingAt, wordAt, Challenge.EvmProof.Word.mask32,
      Challenge.EvmProof.Word.mask32_idem,
      Challenge.EvmProof.Memory.readWord_writeBytes_disjoint,
      State.activeWordsAfterUInt256, hrun, hcap,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_combination4 (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 970)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock combination4Located
      (combination3 s messageOffset returnDest rest) =
        some (combination4 s messageOffset returnDest rest) := by
  have hcap (m : Nat) (hm : m ≤ 16) : rest.length + m < 1024 := by omega
  simp (config := { maxSteps := 500000 })
    [combination4Located, combinationLocated,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      combination3, combination4, touched0, touched1, touched2, touched3,
      touched4, touchWord, storeWordMemory, tailCombination,
      Compression.evmCombine, savedHashAt512, workingAt, wordAt,
      Challenge.EvmProof.Word.mask32, Challenge.EvmProof.Word.mask32_idem,
      Challenge.EvmProof.Memory.readWord_writeBytes_disjoint,
      State.activeWordsAfterUInt256, hrun, hcap,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.add_assoc]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionTailTrace
