import Challenge.Modexp.Submission.Bridge
import Challenge.Modexp.Submission.CertProc
import Challenge.Modexp.Submission.Lowering
import Challenge.Modexp.Submission.Proof.HeaderProc
import Challenge.Modexp.Submission.Proof.WordPathProc
import Challenge.Modexp.Submission.Proof.BigExpProc

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-!
# The full Asm-level run of the MODEXP submission

Assembles the three header outcomes of `Proof/HeaderProc.lean` into the
full-run theorem `program_correct` that `Bridge.correct_of_asm` consumes:
executing `programAsm` from the challenge's fixed initial state halts
returning `spec calldata` for every valid input.

* `modulusSize = 0` — `header_retEmpty` halts inside the header with the
  empty return, which is `spec calldata` there;
* `0 < modulusSize ≤ 32` — `header_word` falls through to the word path
  with the exit state `hst6`, whose `WordEntry` frame
  (`hst6_cells`/`hst6_activeWords`/`hst6_env`) `wordPath_correct` consumes;
* `32 < modulusSize` — `bigExp_correct` is already a full-run theorem.

Also packages the facts `correct_of_asm` needs next to the run: the
structural lowering fact `hlow` (via `lowerProg_of_lowerProg'`, exactly as
the smoke test `Scratch.lean` does it), the certificate and label-width
facts, and the nonempty-artifact fact `hne` (list-level, after
`assemble_eq_mkCode`/`size_mkCode`).
-/

namespace Challenge.Modexp.Submission.Proof.Top

open YulEvmCompiler
open YulSemantics.EVM (EvmState)
open Challenge.Modexp.Submission (programAsm programInstrs initYst localModel certData
  checkCert_ok codeSize_ok lowerProg_of_lowerProg')
open Challenge.Modexp.Submission.Proof.WordPath
open Challenge.Modexp.Submission.Proof.Header
open Challenge.Modexp.Submission.Proof.BigExpProc (bigExp_correct)
open Challenge.Modexp (spec ValidInput baseSize exponentSize modulusSize)

/-- The lowering fact `correct_of_asm` consumes: kernel-checked through the
structural `lowerProg'` mirror of the pinned compiler's `lowerProg`. -/
theorem hlow : lowerProg programAsm = some programInstrs :=
  lowerProg_of_lowerProg' (by decide)

/-- The kernel-checked stack-safety certificate. -/
theorem hcert : checkCert programAsm certData = true := checkCert_ok

/-- The artifact fits the two-byte label addressing. -/
theorem hsmall : codeSize programAsm < 256 ^ labelWidth := codeSize_ok

/-- The artifact is nonempty: the assembled byte list is (much) longer than
zero. Stated at the list level (`assemble_eq_mkCode`/`size_mkCode`) so the
kernel never builds a byte array here. -/
theorem hne : (assemble programInstrs).size ≠ 0 := by
  rw [assemble_eq_mkCode, size_mkCode]
  decide

/-- The sectioned spelling of the initial configuration: `programAsm` is its
four sections, and the two compute sections continue into the halt
sections and procedure bodies. -/
theorem start_conf_eq (calldata : ByteArray) :
    (⟨programAsm, [], initYst (assemble programInstrs) calldata⟩ : AConf) =
      ⟨secHeader programLabels ++ (secWordPath programLabels ++
        (secBigPath programLabels ++ progTail)), [],
        initYst (assemble programInstrs) calldata⟩ := by
  rw [programAsm_eq]
  rfl

/-- The program's full run: every valid input halts returning `spec
calldata`. -/
theorem program_correct (calldata : ByteArray) (hvalid : ValidInput calldata) :
    ∃ (b : AConf) (yst' : EvmState),
      ASteps programAsm ⟨programAsm, [], initYst (assemble programInstrs) calldata⟩ b ∧
      AHalt programAsm b yst' ∧
      yst'.halted = some (.ret, (spec calldata).toList) := by
  have hbs : baseSize calldata ≤ 1024 := hvalid.2.1
  have hes : exponentSize calldata ≤ 1024 := hvalid.2.2.1
  have hstart := start_conf_eq calldata
  rcases Nat.lt_or_ge (modulusSize calldata) 1 with hm0 | hmpos
  · -- `modulusSize = 0`: the header returns empty, which is the spec here
    obtain ⟨b, yst', hS, hH, hD⟩ :=
      header_retEmpty calldata hvalid (by omega)
        (rest := secWordPath programLabels ++ (secBigPath programLabels ++ progTail))
    have hS' : ASteps programAsm
        ⟨programAsm, [], initYst (assemble programInstrs) calldata⟩ b :=
      hstart.symm ▸ hS
    exact ⟨b, yst', hS', hH, hD⟩
  · rcases Nat.lt_or_ge 32 (modulusSize calldata) with hmbig | hm32
    · -- `32 < modulusSize`: the big path is a full-run theorem already
      exact bigExp_correct calldata hvalid hmbig
    · -- `0 < modulusSize ≤ 32`: header, then the word path
      have hA : ASteps programAsm
          ⟨programAsm, [], initYst (assemble programInstrs) calldata⟩
          ⟨secWordPath programLabels ++ (secBigPath programLabels ++ progTail), [],
            hst6 calldata⟩ :=
        hstart.symm ▸ (header_word calldata hvalid (by omega) hm32
          (rest := secWordPath programLabels ++ (secBigPath programLabels ++ progTail)))
      have h6 := hst6_cells calldata
      have hent : WordEntry (hst6 calldata) calldata (baseSize calldata)
          (exponentSize calldata) (modulusSize calldata) 96 (96 + baseSize calldata)
          (96 + baseSize calldata + exponentSize calldata) :=
        ⟨by rw [hst6_activeWords]; norm_num, hst6_env calldata,
          h6.1, h6.2.1, h6.2.2.1, h6.2.2.2.1, h6.2.2.2.2.1, h6.2.2.2.2.2.1⟩
      obtain ⟨b, yst', hS, hH, hD⟩ :=
        wordPath_correct (calldata := calldata) (bs := baseSize calldata)
          (es := exponentSize calldata) (ms := modulusSize calldata) (bo := 96)
          (eo := 96 + baseSize calldata) (mo := 96 + baseSize calldata + exponentSize calldata)
          hbs hes (by omega) hm32 rfl rfl rfl rfl rfl rfl
          (lt_two_pow_256_of_lt_pow256 hm32
            (bytesToNatPadded_lt_pow calldata _ _)) hent
      exact ⟨b, yst', hA.trans hS, hH, hD⟩

end Challenge.Modexp.Submission.Proof.Top
