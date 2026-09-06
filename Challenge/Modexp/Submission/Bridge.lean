import Challenge.Modexp.Spec
import Challenge.Modexp.ProofSupport.InitialState
import YulEvmCompiler.LowerCorrect
import YulEvmCompiler.StackScalable
import Challenge.Modexp.Submission.Lowering
set_option warningAsError true

/-!
# Bridge: from an Asm-level halting run to `Challenge.Modexp.Correct`

The verified Yul compiler's phase-B theorem (`YulEvmCompiler.arun_halt_sim`)
lifts an Asm-machine execution to the EVM small-step semantics on the lowered
bytecode. This module packages the challenge-specific plumbing:

* `initYst` — the Yul-side state matching the challenge's fixed initial EVM
  state, with its `StateMatch` proof;
* `correct_of_asm` — the end-to-end reduction: from the lowering fact
  (`lowerProg prog = some is`, produced kernel-checkably via `lowerProg'` from
  `Submission/Lowering.lean`), the stack certificate (`checkCert`, decided),
  and an Asm-level halting computation of `spec calldata`, conclude
  `Correct (assemble is)`.
-/

namespace Challenge.Modexp.Submission

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics (Block)
open YulSemantics.EVM (EvmState ExecEnv U256 HaltKind ExternalCalls ExternalCreates
  byteFrom)
open YulEvmCompiler
open Challenge.Modexp

/-- The local (no external calls or creates) model the program runs in. -/
instance localModel : ExternalModel :=
  { calls := ExternalCalls.none, creates := ExternalCreates.none }

/-- The Yul-side initial state matching `initialState code calldata gas` for
every gas budget. The program's code is visible through `extCodeOf` at the
deployment address so the target account's `codeHash` agrees; every other
projection is empty. -/
def initYst (code calldata : ByteArray) : EvmState :=
  { EvmState.init with
    env := { (default : ExecEnv) with
      address := BitVec.ofNat 256 deployAddress.toNat
      code := code.toList
      calldata := calldata.toList
      keccakOf := targetKeccakOracle
      extCodeOf := fun a =>
        if AccountAddress.ofUInt256 (conv a) = deployAddress then code.toList else [] } }

/-- Calldata/code agreement of a byte array with its own list view. -/
theorem memMatch_byteFrom_toList (b : ByteArray) :
    MemMatch (byteFrom b.toList) b := by
  intro a
  have hsize : b.data.toList.length = b.size := by
    rw [Array.length_toList]; rfl
  simp only [byteFrom, List.getD]
  rw [ByteArray.toList_eq_data]
  by_cases h : a < b.size
  · rw [dif_pos h]
    rw [List.getElem?_eq_getElem (by rw [hsize]; exact h)]
    rw [Array.getElem_toList]
    rfl
  · rw [dif_neg h, List.getElem?_eq_none (by rw [hsize]; omega)]
    rfl

/-- The initial `StateMatch`. Requires nonempty code (the challenge artifact
always is) so that the self-code `codeHash` projection is the Keccak hash. -/
theorem initYst_stateMatch (code calldata : ByteArray) (gas : Nat)
    (hne : code.size ≠ 0) :
    StateMatch (initYst code calldata) (initialState code calldata gas) where
  mem := MemMatch.init
  stor := by
    intro k
    show (⟨0⟩ : UInt256) = _
    show (⟨0⟩ : UInt256) = ((AccountMap.empty.set deployAddress { Account.empty with code })
        deployAddress).storage.get (conv k)
    rw [AccountMap.get_set_same]
    show (⟨0⟩ : UInt256) = (Account.empty.storage).get (conv k)
    simp [Storage.get, Account.empty, Storage.empty]
  tstor := by
    intro k
    show (⟨0⟩ : UInt256) = _
    show (⟨0⟩ : UInt256) = ((AccountMap.empty.set deployAddress { Account.empty with code })
        deployAddress).tstorage.get (conv k)
    rw [AccountMap.get_set_same]
    show (⟨0⟩ : UInt256) = (Account.empty.tstorage).get (conv k)
    simp [Storage.get, Account.empty, Storage.empty]
  cd := memMatch_byteFrom_toList calldata
  env := by
    refine { calldataLen := ?_, keccak := ?_, address := ?_, origin := ?_, caller := ?_, callvalue := ?_, gasprice := ?_, static := ?_, coinbase := ?_, timestamp := ?_, number := ?_, prevrandao := ?_, gaslimit := ?_, chainid := ?_, basefee := ?_, blobbasefee := ?_, blobHash := ?_, blockHash := ?_ }
    · show calldata.toList.length = calldata.size
      rw [ByteArray.toList_eq_data, Array.length_toList]
      rfl
    · exact targetKeccakOracle_agrees
    · show conv (BitVec.ofNat 256 deployAddress.toNat) = deployAddress.toUInt256
      rw [conv_ofNat']
      rfl
    · show conv (0 : U256) = _; rw [conv_zero]; rfl
    · show conv (0 : U256) = _; rw [conv_zero]; rfl
    · show conv (0 : U256) = _; rw [conv_zero]; rfl
    · show conv (0 : U256) = _; rw [conv_zero]; rfl
    · rfl
    · show conv (0 : U256) = _; rw [conv_zero]; rfl
    · show conv (0 : U256) = _; rw [conv_zero]; rfl
    · show conv (0 : U256) = _; rw [conv_zero]; rfl
    · show conv (0 : U256) = _; rw [conv_zero]; rfl
    · show conv (0 : U256) = _; rw [conv_zero]; rfl
    · show conv (0 : U256) = _; rw [conv_zero]; rfl
    · show conv (0 : U256) = _; rw [conv_zero]; rfl
    · show conv (0 : U256) = _; rw [conv_zero]; rfl
    · intro i
      show conv (0 : U256) = _
      rw [conv_zero]
      show (⟨0⟩ : UInt256) = ((#[] : Array UInt256))[(conv i).toNat]?.getD 0
      simp
      rfl
    · intro n
      show conv (0 : U256) = _
      rw [conv_zero]
      rfl
  codeBytes := memMatch_byteFrom_toList code
  codeLen := by
    show code.toList.length = code.size
    rw [ByteArray.toList_eq_data, Array.length_toList]
    rfl
  selfBalance := by
    show (⟨0⟩ : UInt256) = _
    show (⟨0⟩ : UInt256) = ((AccountMap.empty.set deployAddress { Account.empty with code })
        deployAddress).balance
    rw [AccountMap.get_set_same]
    rfl
  balanceOf := by
    intro a
    show (⟨0⟩ : UInt256) = _
    show (⟨0⟩ : UInt256) = ((AccountMap.empty.set deployAddress { Account.empty with code })
        (AccountAddress.ofUInt256 (conv a))).balance
    by_cases h : AccountAddress.ofUInt256 (conv a) = deployAddress
    · rw [h, AccountMap.get_set_same]
      rfl
    · rw [AccountMap.get_set_other _ _ _ _ h, AccountMap.get_empty]
      rfl
  activeWords := by
    show conv (0 : U256) = _
    rw [conv_zero]
    rfl
  retData := MemMatch.init
  retDataLen := rfl
  externalCode := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a
      show MemMatch (byteFrom (if AccountAddress.ofUInt256 (conv a) = deployAddress
          then code.toList else []))
          (((AccountMap.empty.set deployAddress { Account.empty with code })
            (AccountAddress.ofUInt256 (conv a))).code)
      by_cases h : AccountAddress.ofUInt256 (conv a) = deployAddress
      · rw [if_pos h, h, AccountMap.get_set_same]
        exact memMatch_byteFrom_toList code
      · rw [if_neg h, AccountMap.get_set_other _ _ _ _ h, AccountMap.get_empty]
        exact MemMatch.init
    · intro a
      show (if AccountAddress.ofUInt256 (conv a) = deployAddress
          then code.toList else []).length =
          (((AccountMap.empty.set deployAddress { Account.empty with code })
            (AccountAddress.ofUInt256 (conv a))).code).size
      by_cases h : AccountAddress.ofUInt256 (conv a) = deployAddress
      · rw [if_pos h, h, AccountMap.get_set_same]
        show code.toList.length = code.size
        rw [ByteArray.toList_eq_data, Array.length_toList]
        rfl
      · rw [if_neg h, AccountMap.get_set_other _ _ _ _ h, AccountMap.get_empty]
        rfl
    · intro a
      show conv (YulSemantics.EVM.projectedCodeHash (initYst code calldata).env
          (initYst code calldata).env.balanceOf a) =
          (((AccountMap.empty.set deployAddress { Account.empty with code })
            (AccountAddress.ofUInt256 (conv a))).codeHash)
      by_cases h : AccountAddress.ofUInt256 (conv a) = deployAddress
      · have hext : (initYst code calldata).env.extCodeOf a = code.toList := if_pos h
        rw [h, AccountMap.get_set_same]
        rw [YulSemantics.EVM.projectedCodeHash, hext]
        rw [if_neg]
        · show conv (targetKeccakOracle code.toList) = _
          rw [targetKeccakOracle_agrees, mkCode_toList]
          show keccak256 code = Account.codeHash { Account.empty with code }
          rw [Account.codeHash, if_neg]
          simp [Account.isEmpty, hne]
        · intro hcond
          obtain ⟨_, _, hlen⟩ := hcond
          rw [ByteArray.toList_eq_data, Array.length_toList] at hlen
          exact hne hlen
      · have hext : (initYst code calldata).env.extCodeOf a = [] := if_neg h
        rw [AccountMap.get_set_other _ _ _ _ h, AccountMap.get_empty]
        rw [YulSemantics.EVM.projectedCodeHash, hext]
        rw [if_pos ⟨rfl, rfl, rfl⟩]
        rfl
    · intro a
      show (⟨0⟩ : UInt256) = (((AccountMap.empty.set deployAddress { Account.empty with code })
          (AccountAddress.ofUInt256 (conv a))).nonce)
      by_cases h : AccountAddress.ofUInt256 (conv a) = deployAddress
      · rw [h, AccountMap.get_set_same]
        rfl
      · rw [AccountMap.get_set_other _ _ _ _ h, AccountMap.get_empty]
        rfl
    · intro a k
      show (⟨0⟩ : UInt256) = (((AccountMap.empty.set deployAddress { Account.empty with code })
          (AccountAddress.ofUInt256 (conv a))).storage.get (conv k))
      by_cases h : AccountAddress.ofUInt256 (conv a) = deployAddress
      · rw [h, AccountMap.get_set_same]
        show (⟨0⟩ : UInt256) = (Account.empty.storage).get (conv k)
        simp [Storage.get, Account.empty, Storage.empty]
      · rw [AccountMap.get_set_other _ _ _ _ h, AccountMap.get_empty]
        show (⟨0⟩ : UInt256) = (Account.empty.storage).get (conv k)
        simp [Storage.get, Account.empty, Storage.empty]
    · intro a k
      show (⟨0⟩ : UInt256) = (((AccountMap.empty.set deployAddress { Account.empty with code })
          (AccountAddress.ofUInt256 (conv a))).tstorage.get (conv k))
      by_cases h : AccountAddress.ofUInt256 (conv a) = deployAddress
      · rw [h, AccountMap.get_set_same]
        show (⟨0⟩ : UInt256) = (Account.empty.tstorage).get (conv k)
        simp [Storage.get, Account.empty, Storage.empty]
      · rw [AccountMap.get_set_other _ _ _ _ h, AccountMap.get_empty]
        show (⟨0⟩ : UInt256) = (Account.empty.tstorage).get (conv k)
        simp [Storage.get, Account.empty, Storage.empty]
  logs := List.Forall₂.nil
  selfdestructs := List.Forall₂.nil
  createdThisTx := by
    show (false : Bool) = !((AccountMap.empty.set deployAddress { Account.empty with code })
        deployAddress).isContract
    rw [AccountMap.get_set_same]
    simp [Account.isContract, hne]

/-- The initial `FrameOK`. -/
theorem initYst_frameOK {code calldata : ByteArray} {gas : Nat}
    (hsize : code.size < 2 ^ 256) : FrameOK code (initialState code calldata gas) where
  hcode := rfl
  codeSmall := hsize
  fork := rfl
  noPrecompile := deployAddress_not_precompile
  callStack := rfl
  running := rfl

/-- The end-to-end reduction. -/
theorem correct_of_asm {prog : List Asm} {is : List Instr} {d : CertData}
    (hlow : lowerProg prog = some is)
    (hsmall : codeSize prog < 256 ^ labelWidth)
    (hcert : checkCert prog d = true)
    (hne : (assemble is).size ≠ 0)
    (hrun : ∀ calldata : ByteArray, ValidInput calldata →
      ∃ (b : AConf) (yst' : EvmState),
        ASteps prog ⟨prog, [], initYst (assemble is) calldata⟩ b ∧
        AHalt prog b yst' ∧
        yst'.halted = some (.ret, (spec calldata).toList))
    : Challenge.Modexp.Correct (assemble is) := by
  intro calldata hvalid
  obtain ⟨b, yst', hsteps, hhalt, hres⟩ := hrun calldata hvalid
  obtain ⟨bnd, H⟩ := arun_halt_sim ExternalsRealized.none
    hlow hsmall hsteps hhalt (List.suffix_refl _)
    (checkCert_run_bound hcert _)
  have hsize : (assemble is).size < 2 ^ 256 := by
    have hlen : (assemble is).size = codeSize prog := by
      rw [assemble_eq_mkCode, size_mkCode, lowerFrag_length hlow]
    have hsmall' : codeSize prog < 65536 := by simpa [labelWidth] using hsmall
    have h2 : (65536 : Nat) < 2 ^ 256 := by norm_num
    omega
  refine ⟨bnd, fun g hg => ?_⟩
  obtain ⟨s', hstep, hsm, hcs, hhm⟩ := H (initialState (assemble is) calldata g)
    ⟨by rw [assembleWithPayload_nil]; exact initYst_frameOK hsize, initYst_stateMatch _ _ _ hne,
     by simp [initialState_pc], by simp [initialState_stack]⟩ hg
  obtain ⟨hk, hhalted, hmatch⟩ := hhm
  rw [hres] at hhalted
  obtain rfl := Option.some.inj hhalted
  obtain ⟨hhalt_ret, hretdata⟩ := hmatch
  apply Eval.iff_steps_halted.mpr
  exact ⟨s', hstep, by rw [hhalt_ret]; exact HaltKind.noConfusion, hcs, by
    rw [State.toResult_returned _ hhalt_ret]
    have hretdata' : s'.hReturn.toList = (spec calldata).toList := hretdata
    have hfin : s'.hReturn = spec calldata := by
      have hc := congrArg mkCode hretdata'
      rwa [mkCode_toList, mkCode_toList] at hc
    rw [hfin]⟩

end Challenge.Modexp.Submission
