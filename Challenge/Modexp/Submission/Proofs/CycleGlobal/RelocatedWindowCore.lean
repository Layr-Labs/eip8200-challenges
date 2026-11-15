import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasCore
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOnePositive
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.RelocatedWindowCore
open Challenge.Modexp Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof WindowNibbleKernel WindowTwentyOneBinding WindowTwentyOneMsize
namespace Table
def tablePC (power : Nat) : Nat := 1197 + 5 * power
private theorem updatePC (power : Nat) (hlo : 2 ≤ power) (hhi : power < 14) :
    WindowTwentyOneTable.storePCM (advancePC 2 (UInt256.ofNat (tablePC power))) =
      UInt256.ofNat (tablePC (power + 1)) := by
  interval_cases power <;> decide
theorem run_one (template : State) (base modulus exponent : UInt256)
    (power : Nat) (hlo : 2 ≤ power) (hhi : power < 14)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructionsX (WindowTwentyOneTable.updateProgramM power hlo)
      (WindowTwentyOneTable.state template (UInt256.ofNat (tablePC power)) base modulus exponent power rest) =
    some (WindowTwentyOneTable.state template (UInt256.ofNat (tablePC (power + 1)))
      base modulus exponent (power + 1) rest) := by
  have h := WindowTwentyOneTable.run_updateM template (UInt256.ofNat (tablePC power))
    base modulus exponent power hlo hhi rest hrest
  simpa only [updatePC power hlo hhi] using h
def buildProgram : Nat → List Instr
  | 0 => []
  | count + 1 => buildProgram count ++
      WindowTwentyOneTable.updateProgramM (count + 2) (by omega)
theorem run_build (template : State) (base modulus exponent : UInt256)
    (count : Nat) (hcount : count ≤ 12)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructionsX (buildProgram count)
      (WindowTwentyOneTable.state template (UInt256.ofNat 1207) base modulus exponent 2 rest) =
    some (WindowTwentyOneTable.state template (UInt256.ofNat (tablePC (count + 2)))
      base modulus exponent (count + 2) rest) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have h := run_one template base modulus exponent (count + 2) (by omega) (by omega) rest hrest
      have both := runInstructionsX_append_some _ _ _ _ _ (ih (by omega)) h
      simpa only [buildProgram,show count + 2 + 1 = count + 1 + 2 by omega] using both
def program : List Instr :=
  WindowTwentyOneTablePrelude.program++buildProgram 12++WindowTwentyOneTable.lastUpdateProgramM
theorem run_all (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hexp : rest[1]? = some exponent) :
    runInstructionsX program
      (WindowTwentyOneTablePrelude.initial template (UInt256.ofNat 1181) base modulus rest) =
    some (WindowTwentyOneTable.framed template (UInt256.ofNat 1270) base modulus 16 rest) := by
  have hp := WindowTwentyOneTablePrelude.run_prelude template (UInt256.ofNat 1181)
    base modulus exponent rest hrest hexp
  have hpc : WindowTwentyOneTablePrelude.endPC (UInt256.ofNat 1181) = UInt256.ofNat 1207 := by decide
  rw [hpc] at hp
  have hb := run_build template base modulus exponent 12 (by decide) rest hrest
  have hl := WindowTwentyOneTable.run_last_updateM template (UInt256.ofNat (tablePC 14))
    base modulus exponent rest hrest
  have hlastPC : WindowTwentyOneTable.lastStorePCM (UInt256.ofNat (tablePC 14)).succ =
      UInt256.ofNat 1270 := by decide
  rw [hlastPC] at hl
  exact runInstructionsX_append_some _ _ _ _ _ (runInstructionsX_append_some _ _ _ _ _ hp hb) hl
end Table
namespace Route
open WindowPrecopyRoute
def returnedState (template : State) (base modulus exponent : UInt256) (rest : List UInt256) :
    State :=
  WindowTwentyOneReturn.returned
    (routeState template 2739 base modulus exponent
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63::exponent::rest))
    (UInt256.ofNat 2744) (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63) 18
    (exponent::rest)
theorem run_setupAt (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 600) :
    runInstructions setupProgram
      (WindowTwentyOneTable.framed template (UInt256.ofNat 1270) base modulus 16
        (modulus::exponent::rest)) =
    some (WindowTwentyOneTable.framed template (UInt256.ofNat 1274) base modulus 16
      (UInt256.shiftRight exponent (UInt256.ofNat 3)::frame modulus exponent rest)) := by
  have h := run_setup template (UInt256.ofNat 1270) base modulus exponent rest (by omega)
  rw [advancePC_ofNat] at h
  exact h
theorem run_copyAt (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 600) :
    runInstructionsX copyProgram
      (WindowTwentyOneTable.framed template (UInt256.ofNat 1274) base modulus 16
        (UInt256.shiftRight exponent (UInt256.ofNat 3)::frame modulus exponent rest)) =
    some (routeState template 1282 base modulus exponent (frame modulus exponent rest)) := by
  have h := run_copy template (UInt256.ofNat 1274) base modulus exponent
    (UInt256.shiftRight exponent (UInt256.ofNat 3)) rest (by omega)
  rw [advancePC_ofNat] at h
  exact h
theorem run_poolAt (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 600) :
    runInstructions poolProgram (routeState template 1282 base modulus exponent
      (frame modulus exponent rest)) =
    some (routeState template 1596 base modulus exponent
      (List.replicate 314 modulus++frame modulus exponent rest)) := by
  have h := run_pool template (UInt256.ofNat 1282) (routeMem base modulus exponent) 18
    modulus (exponent::rest)
    (by simp only [List.length_cons]; omega)
  rw [advancePC_ofNat] at h
  exact h
theorem run_firstAt (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 600) :
    runInstructions firstProgram (routeState template 1596 base modulus exponent
      (List.replicate 314 modulus++frame modulus exponent rest)) =
    some (routeState template 1605 base modulus exponent
      (WindowTwentyOneMath.initialAccumulator base modulus exponent.toNat ::
        List.replicate 314 modulus++frame modulus exponent rest)) := by
  have hd := WindowTwentyOneMath.nibble_lt exponent.toNat 0
  have h := run_first template (UInt256.ofNat 1596) (routeMem base modulus exponent) base modulus
    (WindowTwentyOneMath.nibble exponent.toNat 0) hd (routeMem_table base modulus exponent _ hd)
    (first_address _ exponent) (List.replicate 314 modulus++frame modulus exponent rest)
    (by simp only [frame,List.length_append,List.length_replicate,List.length_cons]; omega)
  rw [advancePC_ofNat] at h
  exact h
theorem run_headAt (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 600) :
    runInstructions (routeWindows 0 60) (routeState template 1605 base modulus exponent
      (WindowTwentyOneMath.initialAccumulator base modulus exponent.toNat ::
        List.replicate 314 modulus++frame modulus exponent rest)) =
    some (routeState template 2685 base modulus exponent
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 60 ::
        List.replicate 14 modulus++frame modulus exponent rest)) := by
  have h := run_routeWindows template (routeMem base modulus exponent) base modulus exponent
    (frame modulus exponent rest) (routeMem_table base modulus exponent)
    (fun i hi => precopy_address _ exponent i hi) 60 0 (by omega) (UInt256.ofNat 1605)
    (WindowTwentyOneMath.initialAccumulator base modulus exponent.toNat) 14
    (by simp only [frame,List.length_cons]; omega)
  rw [advancePC_ofNat] at h
  exact h
theorem run_tailAt (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 600) :
    runInstructions tailProgram (routeState template 2685 base modulus exponent
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 60 ::
        List.replicate 14 modulus++frame modulus exponent rest)) =
    some (returnedState template base modulus exponent rest) := by
  have h1 : runInstructions (routeWindows 60 1) (routeState template 2685 base modulus exponent
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 60 ::
        List.replicate 14 modulus++frame modulus exponent rest)) =
      some (routeState template 2703 base modulus exponent
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat 61 ::
          List.replicate 9 modulus++frame modulus exponent rest)) := by
    have h := run_routeWindows template (routeMem base modulus exponent) base modulus exponent
      (frame modulus exponent rest) (routeMem_table base modulus exponent)
      (fun i hi => precopy_address _ exponent i hi) 1 60 (by omega) (UInt256.ofNat 2685)
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 60) 9
      (by simp only [frame,List.length_cons]; omega)
    have h61 : WindowTwentyOneMath.advance base modulus exponent.toNat (1 + 60) 1
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat 60) =
        WindowTwentyOneMath.accumulator base modulus exponent.toNat 61 :=
      (WindowTwentyOneMath.advance_add base modulus exponent.toNat 1 60 1 _).symm
    rw [advancePC_ofNat,h61] at h
    exact h
  have h2a : runInstructions (WindowSixteenBlock.Block.squares 4)
      (routeState template 2703 base modulus exponent
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat 61 ::
          List.replicate 9 modulus++frame modulus exponent rest)) =
      some (routeState template 2711 base modulus exponent
        (WindowMath.squareWordAfter modulus 4
          (WindowTwentyOneMath.accumulator base modulus exponent.toNat 61) ::
          List.replicate 5 modulus++frame modulus exponent rest)) := by
    have h := WindowSixteenBlock.Block.run_squares template (UInt256.ofNat 2703)
      (routeMem base modulus exponent) 18 modulus
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 61)
      (List.replicate 5 modulus++frame modulus exponent rest) 4 (by decide)
      (by simp only [frame,List.length_append,List.length_replicate,List.length_cons]; omega)
    have hstack : WindowTwentyOneMath.accumulator base modulus exponent.toNat 61 ::
          List.replicate 9 modulus++frame modulus exponent rest =
        WindowTwentyOneMath.accumulator base modulus exponent.toNat 61 ::
          List.replicate 4 modulus++(List.replicate 5 modulus++frame modulus exponent rest) := by
      simp only [List.cons_append,← List.append_assoc,← List.replicate_add]
    rw [advancePC_ofNat] at h
    rw [hstack]
    exact h
  have hd62 := WindowTwentyOneMath.nibble_lt exponent.toNat 62
  have h2b : runInstructions stackLookupProgram
      (routeState template 2711 base modulus exponent
        (WindowMath.squareWordAfter modulus 4
          (WindowTwentyOneMath.accumulator base modulus exponent.toNat 61) ::
          List.replicate 5 modulus++frame modulus exponent rest)) =
      some (routeState template 2721 base modulus exponent
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat 62 ::
          List.replicate 4 modulus++frame modulus exponent rest)) := by
    have h := run_stackLookup template (UInt256.ofNat 2711) (routeMem base modulus exponent)
      base modulus
      (WindowMath.squareWordAfter modulus 4
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat 61))
      exponent (WindowTwentyOneMath.nibble exponent.toNat 62)
      hd62 (routeMem_table base modulus exponent _ hd62) (stack62_address exponent)
      rest (by omega)
    have h62 : WindowTwentyOneMath.accumulator base modulus exponent.toNat 62 =
        UInt256.mulMod
          (WindowMath.tableWord base modulus (WindowTwentyOneMath.nibble exponent.toNat 62))
          (WindowMath.squareWordAfter modulus 4
            (WindowTwentyOneMath.accumulator base modulus exponent.toNat 61)) modulus := by
      rw [mulMod_comm]
      rfl
    rw [advancePC_ofNat] at h
    rw [h62]
    exact h
  have h3 : runInstructions (WindowSixteenBlock.Block.squares 4)
      (routeState template 2721 base modulus exponent
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat 62 ::
          List.replicate 4 modulus++frame modulus exponent rest)) =
      some (routeState template 2729 base modulus exponent
        (WindowMath.squareWordAfter modulus 4
          (WindowTwentyOneMath.accumulator base modulus exponent.toNat 62) ::
          frame modulus exponent rest)) := by
    have h := WindowSixteenBlock.Block.run_squares template (UInt256.ofNat 2721)
      (routeMem base modulus exponent) 18 modulus
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 62)
      (frame modulus exponent rest) 4 (by decide)
      (by simp only [frame,List.length_cons]; omega)
    rw [advancePC_ofNat] at h
    exact h
  have hd := WindowTwentyOneMath.nibble_lt exponent.toNat 63
  have h4 : runInstructions finalProgram
      (routeState template 2729 base modulus exponent
        (WindowMath.squareWordAfter modulus 4
          (WindowTwentyOneMath.accumulator base modulus exponent.toNat 62) ::
          frame modulus exponent rest)) =
      some (WindowTwentyOneReturn.framed
        (routeState template 2739 base modulus exponent
          (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63 ::
            exponent::rest))
        (UInt256.ofNat 2739)
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63 ::
          exponent::rest)) := by
    have h := run_final template (UInt256.ofNat 2729) (routeMem base modulus exponent) base modulus
      (WindowMath.squareWordAfter modulus 4
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat 62))
      exponent (WindowTwentyOneMath.nibble exponent.toNat 63)
      hd (routeMem_table base modulus exponent _ hd) (last_address exponent)
      rest (by omega)
    rw [advancePC_ofNat,
      mulMod_comm (WindowMath.tableWord base modulus (WindowTwentyOneMath.nibble exponent.toNat 63))
        (WindowMath.squareWordAfter modulus 4
          (WindowTwentyOneMath.accumulator base modulus exponent.toNat 62)) modulus] at h
    exact h
  have h5 := WindowTwentyOneReturn.run_return
    (routeState template 2739 base modulus exponent
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63::exponent::rest))
    (UInt256.ofNat 2739) (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63) 18
    (by decide) rfl (exponent::rest) (by simp only [List.length_cons]; omega)
  rw [advancePC_ofNat] at h5
  have h012 := runInstructions_append_some _ _ _ _ _ h1 h2a
  have h0123 := runInstructions_append_some _ _ _ _ _ h012 h2b
  have h01234 := runInstructions_append_some _ _ _ _ _ h0123 h3
  have h012345 := runInstructions_append_some _ _ _ _ _ h01234 h4
  have hall := runInstructions_append_some _ _ _ _ _ h012345 h5
  exact hall
end Route
structure Paths (artifact : ProgramArtifact) (fork : Fork) where
  table : Block artifact fork 1181 Table.program
  setup : Block artifact fork 1270 WindowPrecopyRoute.setupProgram
  copy : Block artifact fork 1274 WindowPrecopyRoute.copyProgram
  pool : Block artifact fork 1282 WindowPrecopyRoute.poolProgram
  first : Block artifact fork 1596 WindowPrecopyRoute.firstProgram
  head : Block artifact fork 1605 (WindowPrecopyRoute.routeWindows 0 60)
  tail : Block artifact fork 2685 WindowPrecopyRoute.tailProgram
def steps_core {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 600)
    (he : rest[1]? = some exponent) (hm : rest[0]? = some modulus) :
    GasSteps (WindowTwentyOneTablePrelude.initial template (UInt256.ofNat 1181) base modulus rest)
      (Route.returnedState template base modulus exponent (rest.drop 2)) := by
  have ht := Block.stepsX paths.table
    (s := WindowTwentyOneTablePrelude.initial template (UInt256.ofNat 1181) base modulus rest)
    (env.transfer rfl rfl) rfl
    (Table.run_all template base modulus exponent rest (by omega) he)
  have hrest_eq : rest = modulus::exponent::rest.drop 2 := by
    rcases rest with _ | ⟨x0,_ | ⟨x1,tail⟩⟩
    · simp at hm
    · simp at he
    · simp only [List.getElem?_cons_zero] at hm
      simp only [List.getElem?_cons_succ,List.getElem?_cons_zero] at he
      cases hm; cases he; rfl
  have hdrop : (rest.drop 2).length ≤ 600 := by simp [List.length_drop]; omega
  have hs := Route.run_setupAt template base modulus exponent (rest.drop 2) hdrop
  rw [← hrest_eq] at hs
  have gs := paths.setup.steps
    (s := WindowTwentyOneTable.framed template (UInt256.ofNat 1270) base modulus 16 rest)
    (env.transfer rfl rfl) rfl hs
  have gc := Block.stepsX paths.copy
    (s := WindowTwentyOneTable.framed template (UInt256.ofNat 1274) base modulus 16
      (UInt256.shiftRight exponent (UInt256.ofNat 3) ::
        WindowPrecopyRoute.frame modulus exponent (rest.drop 2)))
    (env.transfer rfl rfl) rfl
    (Route.run_copyAt template base modulus exponent (rest.drop 2) hdrop)
  have gp := paths.pool.steps
    (s := WindowPrecopyRoute.routeState template 1282 base modulus exponent
      (WindowPrecopyRoute.frame modulus exponent (rest.drop 2)))
    (env.transfer rfl rfl) rfl
    (Route.run_poolAt template base modulus exponent (rest.drop 2) hdrop)
  have gf := paths.first.steps
    (s := WindowPrecopyRoute.routeState template 1596 base modulus exponent
      (List.replicate 314 modulus++WindowPrecopyRoute.frame modulus exponent (rest.drop 2)))
    (env.transfer rfl rfl) rfl
    (Route.run_firstAt template base modulus exponent (rest.drop 2) hdrop)
  have gh := paths.head.steps
    (s := WindowPrecopyRoute.routeState template 1605 base modulus exponent
      (WindowTwentyOneMath.initialAccumulator base modulus exponent.toNat ::
        List.replicate 314 modulus++WindowPrecopyRoute.frame modulus exponent (rest.drop 2)))
    (env.transfer rfl rfl) rfl
    (Route.run_headAt template base modulus exponent (rest.drop 2) hdrop)
  have gt := paths.tail.steps
    (s := WindowPrecopyRoute.routeState template 2685 base modulus exponent
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 60 ::
        List.replicate 14 modulus++WindowPrecopyRoute.frame modulus exponent (rest.drop 2)))
    (env.transfer rfl rfl) rfl
    (Route.run_tailAt template base modulus exponent (rest.drop 2) hdrop)
  exact (((((ht.trans gs).trans gc).trans gp).trans gf).trans gh).trans gt
namespace Entry
open WindowTwentyOneEntry
abbrev baseProgram := WindowTwentyOneEntry.baseProgram
abbrev modulusProgram := WindowTwentyOneEntry.modulusProgram
theorem run_base (template : State) (value : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions baseProgram (framed template (UInt256.ofNat 1178) (value::rest)) =
    some (framed template (UInt256.ofNat 1179) (value::rest)) := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  simp [runInstructions,baseProgram,WindowTwentyOneEntry.baseProgram,framed,Challenge.EvmProof.Stepper.runInstr,
    hcap1,Challenge.EvmProof.Word.succ_ofNat_mod]
theorem run_modulus (template : State)
    (value base : UInt256) (rest : List UInt256) (hrest : rest.length ≤ 999)
    (hbase : rest[1]? = some base) :
    runInstructions modulusProgram (framed template (UInt256.ofNat 1179) (value::rest)) =
    some (framed template (UInt256.ofNat 1181)
      (base::value::value::rest)) := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  simp [runInstructions,modulusProgram,WindowTwentyOneEntry.modulusProgram,framed,Challenge.EvmProof.Stepper.runInstr,
    hcap1,hcap2,hbase,Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]
end Entry
end CycleSubmission.Global.RelocatedWindowCore
