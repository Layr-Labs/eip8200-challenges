import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.Local20261028.CoreGas
import Challenge.Ripemd160.Submission.Local20261028.RecHoistedStoreEntryRaw
import Challenge.Ripemd160.Submission.Local20261028.RecHoistedStoreAnchorRaw

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

/-! Exact decoded guards for the hoisted image. This closes the entry-to-return
success path; generic and alternate-recognizer paths remain separate obligations. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.HoistedStoreEntry
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTrace StackRoundTemplate
open HoistedStoreEntryRaw

inductive Piece | filter | size | anchor

def template : Piece → List Instr
  | .filter => filterTemplate
  | .size => sizeTemplate
  | .anchor => HoistedStoreAnchorRaw.anchorTemplate

def index : Piece → Nat | .filter => 0 | .size => 6 | .anchor => 11
def pc : Piece → Nat | .filter => 0 | .size => 12 | .anchor => 21

theorem actual_slice (p : Piece) :
    (HoistedStoreArtifact.instructions.drop (index p)).take (template p).length = template p := by
  cases p <;> rfl

theorem bounds (p : Piece) :
    index p + (template p).length ≤ HoistedStoreArtifact.instructions.length := by
  rw [HoistedStoreArtifact.instruction_count]
  cases p <;> decide

theorem wellFormed (p : Piece) : (template p).all CoreGas.wellFormedCheck = true := by
  cases p <;> decide

def site (p : Piece) : GenericRoundSite HoistedStoreArtifact.artifact .Osaka (template p) :=
  StackSiteBuilder.ofSlice (template p) (index p) (actual_slice p) (bounds p)
    (by change HoistedStoreArtifact.code.size < 2 ^ 256; rw [HoistedStoreArtifact.code_size]; norm_num)
    (CoreGas.wellFormed_of_check _ (wellFormed p)) (by cases p <;> decide)

theorem site_pc (p : Piece) : (site p).startPC = UInt256.ofNat (pc p) := by
  change UInt256.ofNat (HoistedStoreArtifact.artifact.instructionPC (index p)) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  cases p <;> decide

theorem form (p : Piece) : ∀ i ∈ (template p).dropLast, RecognitionLift.Advances i := by
  apply RecognitionLift.advancesAll_sound
  cases p <;> decide

def lift (p : Piece) (s t : State) (e : HoistedStoreSites.Env s) (rho : List UInt256)
    (h : runInstrSeq (template p) {s with pc := UInt256.ofNat (pc p), stack := rho} = some t) :
    GasSteps {s with pc := UInt256.ofNat (pc p), stack := rho} t :=
  RecognitionLift.gasSteps_of_raw (site p) _ _ e.code e.fork e.run e.np
    (site_pc p).symm (form p) h

def to_seed (s : State) (rho : List UInt256) (e : HoistedStoreSites.Env s)
    (hs : rho.length ≤ 976)
    (hfilter : condition s.executionEnv.calldata = 0)
    (hsize : s.executionEnv.calldata.size = 1000)
    (hanchor : Low64RepeatMath.condition s.executionEnv.calldata = 0) :
    GasSteps {s with pc := 0, stack := rho}
      {s with pc := UInt256.ofNat 48, stack := (MachineState.readWord s.executionEnv.calldata 0 :: rho)} := by
  have hf := lift .filter s _ e rho (run_filter_fall s rho hs e.run hfilter)
  have hz := lift .size s _ e rho (run_size_fall s rho hs e.run hsize)
  have ha := lift .anchor s _ e rho
    (HoistedStoreAnchorRaw.run_anchor_low_fall s rho (by omega) e.run hanchor)
  exact hf.trans (hz.trans ha)

def success (s : State) (rho : List UInt256) (e : HoistedStoreSites.Env s)
    (hs : rho.length ≤ 976) (ha : s.activeWords = 0)
    (hfilter : condition s.executionEnv.calldata = 0)
    (hsize : s.executionEnv.calldata.size = 1000)
    (hanchor : Low64RepeatMath.condition s.executionEnv.calldata = 0)
    (hm : PcSeedRaw.mismatch s.executionEnv.calldata = 0) :
    GasSteps {s with pc := UInt256.ofNat 0, stack := rho}
      {(HoistedStoreResearch.stored s) with pc := UInt256.ofNat 9940, stack := rho, halt := .Returned, hReturn := spec s.executionEnv.calldata} :=
  (to_seed s rho e hs hfilter hsize hanchor).trans
    (HoistedStoreComposed.success s rho e hs ha hsize hanchor hm)

/-- From the actual entry, every rejected scanner value clears the speculative
store and rejoins the ordinary copy state, preserving its environment. -/
def miss (s : State) (rho : List UInt256) (e : HoistedStoreSites.Env s)
    (hs : rho.length ≤ 975) (ha : s.activeWords = 0) (hmem : s.memory.size = 0)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hfilter : condition s.executionEnv.calldata = 0)
    (hsize : s.executionEnv.calldata.size = 1000)
    (hanchor : Low64RepeatMath.condition s.executionEnv.calldata = 0)
    (hm : PcSeedRaw.mismatch s.executionEnv.calldata ≠ 0) :
    GasSteps {s with pc := UInt256.ofNat 0, stack := rho}
      (RetainedFallback114.copied s (0 :: rho)) :=
  (to_seed s rho e (by omega) hfilter hsize hanchor).trans
    (HoistedStoreComposed.miss s rho e hs ha hmem hfit (by omega) hm)

/-- Sufficient-gas evaluation from the actual program entry for any input meeting
all scanner guards; no finite-vector restriction occurs in this theorem. -/
theorem eval_success (input : ByteArray)
    (hfilter : condition input = 0) (hsize : input.size = 1000)
    (hanchor : Low64RepeatMath.condition input = 0)
    (hm : PcSeedRaw.mismatch input = 0) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState HoistedStoreArtifact.code input gas) (.returned (spec input)) := by
  let s := initialState HoistedStoreArtifact.code input 0
  have e : HoistedStoreSites.Env s := ⟨rfl, rfl, rfl, by exact deployAddress_not_precompile⟩
  let trace := success s [] e (by simp) rfl hfilter hsize hanchor hm
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have heval := eval_of_steps (trace.trace gas hgas) (by
    simp [withGas, State.isDone, State.isHalted, State.isRunning,
      HoistedStoreResearch.stored, s, initialState])
  rw [State.toResult_returned _ (by rfl)] at heval
  simpa only [withGas, s, initialState, HoistedStoreResearch.stored,
    show UInt256.ofNat 0 = (0 : UInt256) from rfl] using heval

#print axioms to_seed
#print axioms success
#print axioms miss
#print axioms eval_success
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.HoistedStoreEntry
