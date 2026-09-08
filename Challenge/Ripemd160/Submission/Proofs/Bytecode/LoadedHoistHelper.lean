import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShiftedHoistHelper

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-!
# Loaded-word helper templates

The quad caller now loads the four schedule words itself (`PUSH1 off; MLOAD`
in place of `PUSH2 ptr`), so each four-round helper block starts without its
leading `MLOAD`, and rounds 1-3 lose the seam `SWAP1` that used to bring the
next pointer to the top for loading: the two `ADD`s after the Boolean function
take the message word and the working `A` in either order.  The helper entry
therefore carries the loaded words and the memory expansion the caller already
paid for; the block itself never touches memory or `activeWords`, and its
endpoint is the unchanged `quadAfterHelperBeforeJump`.

The templates are the shifted-factor templates with the loads hoisted out, and
the traces are proved by running both templates symbolically.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.LoadedHoistHelper

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundState QuadRoundTemplate
open PairRoundTemplate QuadGapTemplate

abbrev shiftedFactor := ShiftedHoistHelper.shiftedFactor
abbrev controlPush := ShiftedHoistHelper.controlPush

/-- Helper entry: the caller has loaded the words at `p0 … p3` and expanded
memory over them. -/
def quadHelperEntry (s : State) (startPC p0 p1 p2 p3 returnPC : UInt256)
    (r0 r1 r2 r3 : Nat) (working : Compression.EvmWorking)
    (rho : List UInt256) : State :=
  { s with
    pc := startPC
    stack := [MachineState.readWord s.memory p0.toNat, working.a, shiftedFactor r0,
      MachineState.readWord s.memory p1.toNat, shiftedFactor r1,
      MachineState.readWord s.memory p2.toNat, shiftedFactor r2,
      MachineState.readWord s.memory p3.toNat, shiftedFactor r3, returnPC,
      working.b, working.c, working.d, working.e] ++
      [QuadRoundTemplate.factor] ++ rho
    activeWords := quadActiveWordsAfterUInt256_4 s p0.toNat p1.toNat p2.toNat p3.toNat }

/-- Drop the block's leading `MLOAD` and every seam `SWAP1; MLOAD`. -/
def hoistLoads : List Instr → List Instr
  | .op .JUMPDEST :: .op .MLOAD :: rest => .op .JUMPDEST :: hoistLoads rest
  | .op (.Swap ⟨0, _⟩) :: .op .MLOAD :: rest => hoistLoads rest
  | instruction :: rest => instruction :: hoistLoads rest
  | [] => []

def leftTemplate (j : Nat) (constant : UInt256) : List Instr :=
  hoistLoads (ShiftedHoistHelper.leftTemplate j constant)

def rightTemplate (j : Nat) (constant : UInt256) : List Instr :=
  hoistLoads (ShiftedHoistHelper.rightTemplate j constant)

set_option linter.unusedSimpArgs false in
theorem left_equiv (j : Nat) (hj : j < 5)
    (s : State) (startPC p0 p1 p2 p3 returnPC : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running) :
    runInstrSeq (leftTemplate j constant)
      (quadHelperEntry s startPC p0 p1 p2 p3 returnPC
        r0 r1 r2 r3 working (mask :: rho)) =
    Option.map (fun out => {out with
        pc := pcAfter startPC (leftTemplate j constant)
        activeWords := quadActiveWordsAfterUInt256_4 s p0.toNat p1.toNat p2.toNat p3.toNat})
      (runInstrSeq (ShiftedHoistHelper.leftTemplate j constant)
        (ShiftedHoistHelper.quadHelperEntry s startPC p0 p1 p2 p3 returnPC
          r0 r1 r2 r3 working (mask :: rho))) := by
  have hmul (u v : UInt256) : u.mul v = u * v := rfl
  have hcap (m : Nat) (hm : m ≤ 18) : rho.length + m < 1024 := by omega
  have hadd (u v : UInt256) : u.add v = u + v := rfl
  have hassoc (u v w : UInt256) : (u + v) + w = u + (v + w) := by
    apply Word.word_ext
    change ((u.val + v.val) + w.val).val = (u.val + (v.val + w.val)).val
    simp [Fin.add_def, Nat.add_assoc]
  -- the seam: the word and the working `A` are added in the other order
  have hseam (f a : UInt256) (p : Nat) :
      (f + a) + MachineState.readWord s.memory p =
        (f + MachineState.readWord s.memory p) + a := by
    rw [hassoc, Word.word_add_comm a, ← hassoc]
  have hpc (u : UInt256) (a b : Nat) :
      (u + UInt256.ofNat a) + UInt256.ofNat b =
        u + UInt256.ofNat (a + b) := by
    rw [hassoc, Word.ofNat_add_mod]
  interval_cases j <;>
    dsimp only [leftTemplate, ShiftedHoistHelper.leftTemplate,
      CachedMaskHoistHelper.leftTemplate,
      CachedMaskHoistHelper.leftTemplate0, CachedMaskHoistHelper.leftTemplate1,
      CachedMaskHoistHelper.leftTemplate2, CachedMaskHoistHelper.leftTemplate3,
      CachedMaskHoistHelper.leftTemplate4, ShiftedHoistHelper.shiftRotations,
      ShiftedHoistHelper.removeEntryShuffle, hoistLoads] <;>
    simp only [ShiftedHoistHelper.shiftRotations, ShiftedHoistHelper.removeEntryShuffle,
      hoistLoads] <;>
    simp (config := { maxSteps := 5000000 })
      [quadHelperEntry, ShiftedHoistHelper.quadHelperEntry, roundWords,
       runInstrSeq, Stepper.runInstr, pcAfter, List.exchange,
       hrun, hcap, hmul, UInt256.succ, Instr.size, Instr.size_op, Instr.size_push,
       State.activeWordsAfterUInt256, hadd, hseam, hpc,
       Word.ofNat_add_mod, Word.word_toNat_ofNat, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem right_equiv (j : Nat) (hj : j < 5)
    (s : State) (startPC p0 p1 p2 p3 returnPC : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256)
    (working : Compression.EvmWorking) (a b c d e : UInt256)
    (rho : List UInt256)
    (hstack : rho.length < 1001) (hrun : s.halt = .Running) :
    runInstrSeq (rightTemplate j constant)
      (quadHelperEntry s startPC p0 p1 p2 p3 returnPC
        r0 r1 r2 r3 working (a :: b :: c :: d :: e :: mask :: rho)) =
    Option.map (fun out => {out with
        pc := pcAfter startPC (rightTemplate j constant)
        activeWords := quadActiveWordsAfterUInt256_4 s p0.toNat p1.toNat p2.toNat p3.toNat})
      (runInstrSeq (ShiftedHoistHelper.rightTemplate j constant)
        (ShiftedHoistHelper.quadHelperEntry s startPC p0 p1 p2 p3 returnPC
          r0 r1 r2 r3 working (a :: b :: c :: d :: e :: mask :: rho))) := by
  have hmul (u v : UInt256) : u.mul v = u * v := rfl
  have hcap (m : Nat) (hm : m ≤ 23) : rho.length + m < 1024 := by omega
  have hadd (u v : UInt256) : u.add v = u + v := rfl
  have hassoc (u v w : UInt256) : (u + v) + w = u + (v + w) := by
    apply Word.word_ext
    change ((u.val + v.val) + w.val).val = (u.val + (v.val + w.val)).val
    simp [Fin.add_def, Nat.add_assoc]
  -- the seam: the word and the working `A` are added in the other order
  have hseam (f a : UInt256) (p : Nat) :
      (f + a) + MachineState.readWord s.memory p =
        (f + MachineState.readWord s.memory p) + a := by
    rw [hassoc, Word.word_add_comm a, ← hassoc]
  have hpc (u : UInt256) (a b : Nat) :
      (u + UInt256.ofNat a) + UInt256.ofNat b =
        u + UInt256.ofNat (a + b) := by
    rw [hassoc, Word.ofNat_add_mod]
  interval_cases j <;>
    dsimp only [rightTemplate, ShiftedHoistHelper.rightTemplate,
      CachedMaskHoistHelper.rightTemplate,
      CachedMaskHoistHelper.rightTemplate0, CachedMaskHoistHelper.rightTemplate1,
      CachedMaskHoistHelper.rightTemplate2, CachedMaskHoistHelper.rightTemplate3,
      CachedMaskHoistHelper.rightTemplate4, ShiftedHoistHelper.shiftRotations,
      ShiftedHoistHelper.removeEntryShuffle, hoistLoads] <;>
    simp only [ShiftedHoistHelper.shiftRotations, ShiftedHoistHelper.removeEntryShuffle,
      hoistLoads] <;>
    simp (config := { maxSteps := 5000000 })
      [quadHelperEntry, ShiftedHoistHelper.quadHelperEntry, roundWords,
       runInstrSeq, Stepper.runInstr, pcAfter, List.exchange,
       hrun, hcap, hmul, UInt256.succ, Instr.size, Instr.size_op, Instr.size_push,
       State.activeWordsAfterUInt256, hadd, hseam, hpc,
       Word.ofNat_add_mod, Word.word_toNat_ofNat, Nat.add_assoc]

theorem run_left (j : Nat) (hj : j < 5)
    (s : State) (startPC p0 p1 p2 p3 returnPC : UInt256)
    (r0 r1 r2 r3 : Nat) (working : Compression.EvmWorking)
    (constant : UInt256) (rho : List UInt256)
    (hzero : j = 0 → constant = 0)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hrot0 : 0 < r0) (hrot0' : r0 < 32) (hrot1 : 0 < r1) (hrot1' : r1 < 32)
    (hrot2 : 0 < r2) (hrot2' : r2 < 32) (hrot3 : 0 < r3) (hrot3' : r3 < 32) :
    runInstrSeq (leftTemplate j constant)
      (quadHelperEntry s startPC p0 p1 p2 p3 returnPC
        r0 r1 r2 r3 working (mask :: rho)) =
      some (quadAfterHelperBeforeJump s (pcAfter startPC (leftTemplate j constant))
        returnPC j working p0 p1 p2 p3 r0 r1 r2 r3 constant (mask :: rho)) := by
  rw [left_equiv j hj s startPC p0 p1 p2 p3 returnPC r0 r1 r2 r3
    constant working rho hstack hrun]
  rw [ShiftedHoistHelper.run_left j hj s startPC p0 p1 p2 p3 returnPC
    r0 r1 r2 r3 working constant rho hzero hstack hrun
    hrot0 hrot0' hrot1 hrot1' hrot2 hrot2' hrot3 hrot3']
  rfl

theorem run_right (j : Nat) (hj : j < 5)
    (s : State) (startPC p0 p1 p2 p3 returnPC : UInt256)
    (r0 r1 r2 r3 : Nat) (working : Compression.EvmWorking)
    (constant a b c d e : UInt256) (rho : List UInt256)
    (hzero : j = 0 → constant = 0)
    (hstack : rho.length < 1001) (hrun : s.halt = .Running)
    (hrot0 : 0 < r0) (hrot0' : r0 < 32) (hrot1 : 0 < r1) (hrot1' : r1 < 32)
    (hrot2 : 0 < r2) (hrot2' : r2 < 32) (hrot3 : 0 < r3) (hrot3' : r3 < 32) :
    runInstrSeq (rightTemplate j constant)
      (quadHelperEntry s startPC p0 p1 p2 p3 returnPC
        r0 r1 r2 r3 working (a :: b :: c :: d :: e :: mask :: rho)) =
      some (quadAfterHelperBeforeJump s (pcAfter startPC (rightTemplate j constant))
        returnPC j working p0 p1 p2 p3 r0 r1 r2 r3 constant
          (a :: b :: c :: d :: e :: mask :: rho)) := by
  rw [right_equiv j hj s startPC p0 p1 p2 p3 returnPC r0 r1 r2 r3
    constant working a b c d e rho hstack hrun]
  rw [ShiftedHoistHelper.run_right j hj s startPC p0 p1 p2 p3 returnPC
    r0 r1 r2 r3 working constant a b c d e rho hzero hstack hrun
    hrot0 hrot0' hrot1 hrot1' hrot2 hrot2' hrot3 hrot3']
  rfl

set_option linter.unusedSimpArgs false in
theorem left_advances (j : Nat) (hj : j < 5) (constant : UInt256) :
    ∀ instruction ∈ leftTemplate j constant,
      PairMultiplyLift.Advances instruction := by
  intro instruction hmem
  interval_cases j <;>
    dsimp only [leftTemplate, ShiftedHoistHelper.leftTemplate,
      CachedMaskHoistHelper.leftTemplate,
      CachedMaskHoistHelper.leftTemplate0, CachedMaskHoistHelper.leftTemplate1,
      CachedMaskHoistHelper.leftTemplate2, CachedMaskHoistHelper.leftTemplate3,
      CachedMaskHoistHelper.leftTemplate4, ShiftedHoistHelper.shiftRotations,
      ShiftedHoistHelper.removeEntryShuffle, hoistLoads] at hmem <;>
    simp only [ShiftedHoistHelper.shiftRotations, ShiftedHoistHelper.removeEntryShuffle,
      hoistLoads] at hmem <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem <;>
    simp_all [PairMultiplyLift.Advances, SharedCallTrace.Advances] <;>
    aesop (add safe constructors StraightLine)

set_option linter.unusedSimpArgs false in
theorem right_advances (j : Nat) (hj : j < 5) (constant : UInt256) :
    ∀ instruction ∈ rightTemplate j constant,
      PairMultiplyLift.Advances instruction := by
  intro instruction hmem
  interval_cases j <;>
    dsimp only [rightTemplate, ShiftedHoistHelper.rightTemplate,
      CachedMaskHoistHelper.rightTemplate,
      CachedMaskHoistHelper.rightTemplate0, CachedMaskHoistHelper.rightTemplate1,
      CachedMaskHoistHelper.rightTemplate2, CachedMaskHoistHelper.rightTemplate3,
      CachedMaskHoistHelper.rightTemplate4, ShiftedHoistHelper.shiftRotations,
      ShiftedHoistHelper.removeEntryShuffle, hoistLoads] at hmem <;>
    simp only [ShiftedHoistHelper.shiftRotations, ShiftedHoistHelper.removeEntryShuffle,
      hoistLoads] at hmem <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem <;>
    simp_all [PairMultiplyLift.Advances, SharedCallTrace.Advances] <;>
    aesop (add safe constructors StraightLine)

/-- Exact located execution for any certified pure helper implementation. -/
theorem runLocated_of_raw {artifact : ProgramArtifact} {fork : Fork}
    (helperCode : List Instr)
    (hform : ∀ i ∈ helperCode, PairMultiplyLift.Advances i)
    (j : Nat) (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (constant : UInt256) (site : GenericRoundSite artifact fork helperCode)
    (s : State) (returnPC : UInt256) (working : Compression.EvmWorking)
    (rho : List UInt256)
    (hraw : runInstrSeq helperCode
      (quadHelperEntry s site.startPC p0 p1 p2 p3 returnPC r0 r1 r2 r3 working rho) =
      some (quadAfterHelperBeforeJump s (pcAfter site.startPC helperCode)
        returnPC j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho)) :
    Stepper.runLocatedBlock site.path
      (quadHelperEntry s site.startPC p0 p1 p2 p3 returnPC r0 r1 r2 r3 working rho) =
      some (quadAfterHelperBeforeJump s site.endPC
        returnPC j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho) := by
  have hend : site.endPC = pcAfter site.startPC helperCode := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [PairMultiplyLift.runLocatedBlock_eq_raw site hform
    (quadHelperEntry s site.startPC p0 p1 p2 p3 returnPC r0 r1 r2 r3 working rho) rfl]
  rw [hraw, ← hend]

def gasSteps_of_raw {artifact : ProgramArtifact} {fork : Fork}
    (helperCode : List Instr)
    (hform : ∀ i ∈ helperCode, PairMultiplyLift.Advances i)
    (j : Nat) (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (constant : UInt256) (site : GenericRoundSite artifact fork helperCode)
    (s : State) (returnPC : UInt256) (working : Compression.EvmWorking)
    (rho : List UInt256)
    (hraw : runInstrSeq helperCode
      (quadHelperEntry s site.startPC p0 p1 p2 p3 returnPC r0 r1 r2 r3 working rho) =
      some (quadAfterHelperBeforeJump s (pcAfter site.startPC helperCode)
        returnPC j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho))
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (quadHelperEntry s site.startPC p0 p1 p2 p3 returnPC r0 r1 r2 r3 working rho)
      (quadAfterHelperBeforeJump s site.endPC
        returnPC j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho) := by
  exact Stepper.runLocatedBlock_sound artifact fork site.path hcode hfork
    (runLocated_of_raw helperCode hform j p0 p1 p2 p3 r0 r1 r2 r3
      constant site s returnPC working rho hraw) hrun hnp

#print axioms run_left
#print axioms run_right

end Challenge.Ripemd160.Submission.Proofs.Bytecode.LoadedHoistHelper

