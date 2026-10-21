import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.LocatedBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.EarlySerializeFallback

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-! Exact candidate cleanup-to-copy join. The target is a code-parametric generic
copy state, not the root image's state. No whole-image correctness is claimed. -/
namespace RetainedFallback114
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace StackRoundTemplate RetainedIntegration105 RetainedResultEdge112

/-- Include the generic destination and all eight setup/copy instructions. -/
def copyTemplate : List Instr :=
  [.op .JUMPDEST,
   .push ⟨30, by decide⟩ (UInt256.ofNat 1766820105243087041267848467410591083712559083657179364930612997358944255),
   .push ⟨31, by decide⟩ (UInt256.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455),
   .op .CALLDATASIZE, .push ⟨0, by decide⟩ 0,
   .push ⟨2, by decide⟩ (UInt256.ofNat 1056), .op .CALLDATACOPY,
   .op .CALLDATASIZE, .push ⟨2, by decide⟩ (UInt256.ofNat 1056)]

theorem actual_copy_slice :
    (RetainedBridge111.Candidate.instructions.drop 125).take copyTemplate.length = copyTemplate := by rfl

def copySite : GenericRoundSite RetainedBridge111.Candidate.artifact .Osaka copyTemplate :=
  StackSiteBuilder.ofSlice copyTemplate 125 actual_copy_slice
    (by change 125 + copyTemplate.length ≤ RetainedBridge111.Candidate.instructions.length
        rw [RetainedBridge111.Candidate.instruction_count]; decide)
    RetainedLocated113.code_bound
    (StackRoundData.templateWellFormed_mem (by decide)) (by decide)

theorem copySite_pc : copySite.startPC = UInt256.ofNat 245 := by
  change UInt256.ofNat (RetainedBridge111.Candidate.artifact.instructionPC 125) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem copy_advances : ∀ i ∈ copyTemplate.dropLast, RecognitionLift.Advances i := by
  apply RecognitionLift.advancesAll_sound
  decide

/-- The ordinary nonempty calldata copy state, with the candidate environment
and arbitrary untouched persistent fields. Stack head is shown first. -/
def copied (s : State) (rho : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 319
    stack := [UInt256.ofNat 1056, UInt256.ofNat s.executionEnv.calldata.size,
      DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16] ++ rho
    memory := MachineState.writeBytes ByteArray.empty
      (MachineState.readPadded s.executionEnv.calldata 0 s.executionEnv.calldata.size) 1056
    activeWords := State.activeWordsAfterUInt256
      {s with activeWords := UInt256.ofNat 0} 1056 s.executionEnv.calldata.size }

private theorem active_absorb (n : Nat) (hpos : 0 < n) :
    MachineState.activeWordsAfter 1 1056 n = MachineState.activeWordsAfter 0 1056 n := by
  simp only [MachineState.activeWordsAfter, if_neg (by omega : n ≠ 0)]
  have h : 1 ≤ (1056 + n - 1) / 32 + 1 := by omega
  change max 1 _ = max 0 _
  rw [Nat.max_eq_right h, Nat.max_eq_right (Nat.zero_le _)]

theorem run_copy (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hpos : 0 < s.executionEnv.calldata.size)
    (hm : s.memory.size = 32) :
    runInstrSeq copyTemplate (cleared s rho) = some (copied s rho) := by
  have hcap (n : Nat) (hn : n ≤ 7) : rho.length + n < 1024 := by omega
  have hsize : s.executionEnv.calldata.size % 2 ^ 256 = s.executionEnv.calldata.size :=
    Nat.mod_eq_of_lt hfit
  have hm8 : UInt256.ofNat
      450552876409790643671482431940419874915447411150352389258589821042463539455 =
      DenseScheduleTemplate.mask8 := by decide
  have hm16 : UInt256.ofNat
      1766820105243087041267848467410591083712559083657179364930612997358944255 =
      DenseScheduleTemplate.mask16 := by decide
  simp (discharger := omega) [copyTemplate, cleared, copied, runInstrSeq, DataStepper.runInstr,
    hrun, show rho.length < 1024 by omega, hcap, UInt256.succ, Instr.size,
    Nat.add_assoc, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    show ({val := 0} : UInt256).toNat = 0 by rfl, hsize, hm8, hm16,
    State.activeWordsAfterUInt256, EarlySerializeFallback.clear_word s.memory hm,
    EarlySerializeFallback.calldata_absorb_zero32 s.executionEnv.calldata hpos,
    active_absorb s.executionEnv.calldata.size hpos]
  have hsize2 := hsize
  norm_num only [Nat.reducePow] at hsize2
  rw [hsize2]
  simp only [active_absorb _ hpos, EarlySerializeFallback.calldata_absorb_zero32 _ hpos]
  decide

def gasSteps_copy (s : State) (rho : List UInt256) (e : RetainedLocated113.Env s)
    (hs : rho.length ≤ 980) (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hpos : 0 < s.executionEnv.calldata.size) (hm : s.memory.size = 32) :
    GasSteps (cleared s rho) (copied s rho) :=
  RecognitionLift.gasSteps_of_raw copySite _ _ e.code e.fork e.run e.np
    (by simpa only [cleared] using copySite_pc.symm) copy_advances
    (run_copy s rho hs e.run hfit hpos hm)

/-- Full literal miss through the *candidate's* cleanup and generic copy.
This removes both the speculative digest bytes and the one-word high-water
mark, while preserving the original arbitrary stack tail. -/
def gasSteps_miss_copy (s : State) (rho : List UInt256) (e : RetainedLocated113.Env s)
    (hs : rho.length ≤ 980) (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hpos : 0 < s.executionEnv.calldata.size) (ha : s.activeWords = UInt256.ofNat 0)
    (hm : s.memory.size = 0) (hn : retainedResult s.executionEnv.calldata ≠ 0) :
    GasSteps {s with
      pc := UInt256.ofNat 8157
      stack := MachineState.readWord s.executionEnv.calldata 0 :: rho}
      (copied s rho) := by
  let w := stored s ExactBindings.digest
  have ew : RetainedLocated113.Env w := ⟨e.code, e.fork, e.run, e.np⟩
  have hwm : w.memory.size = 32 := by
    simp [w, stored, MachineState.writeBytes_size, BytesLemmas.natToBytesPadded_size, hm]
  have hc : copied w rho = copied s rho := by
    simp only [copied, w, stored]
    rfl
  exact (RetainedLocated113.gasSteps_miss s rho e hs ha hn).trans
    (GasSteps.cast (gasSteps_copy w rho ew hs hfit hpos hwm) rfl hc)

#print axioms actual_copy_slice
#print axioms gasSteps_copy
#print axioms gasSteps_miss_copy
end RetainedFallback114
