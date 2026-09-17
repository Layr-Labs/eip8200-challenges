import Challenge.Modexp.Submission.LocalPatch.StaticDomain
import Challenge.Modexp.Submission.LocalPatch.JumpDestLayout

set_option warningAsError true
set_option linter.unusedSimpArgs false

/-! All-target scanner semantics for different local PUSH layouts.
Unlike `JumpDestLayout.check`, the two certified walks may have different
instruction counts. Nothing here assumes equality of jump predicates. -/
namespace Challenge.Modexp.Submission.LocalPatch.ScannerTargets
open EvmSemantics EvmSemantics.EVM
open StaticDomain

/-- The jump destinations in an explicit scanner path. -/
def targets (code : ByteArray) (pcs : List Nat) : List Nat :=
  pcs.filter (JumpDestLayout.boundaryIsJumpDest code)

theorem targets_append (code : ByteArray) (left right : List Nat) :
    targets code (left ++ right) = targets code left ++ targets code right := by
  simp only [targets, List.filter_append]

theorem path_lower {code : ByteArray} {start stop : Nat} {pcs : List Nat}
    (hpath : ScanPath code start pcs stop) :
    ∀ q, q ∈ pcs → start ≤ q := by
  induction pcs generalizing start with
  | nil => intro q hq; simp at hq
  | cons pc rest ih =>
    rcases hpath with ⟨rfl, _, htail⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Nat.le_refl _
    · have h := ih htail q hq
      dsimp [scanNext] at h
      omega

theorem path_length {code : ByteArray} {start stop : Nat} {pcs : List Nat}
    (hpath : ScanPath code start pcs stop) : start + pcs.length ≤ stop := by
  induction pcs generalizing start with
  | nil => simpa only [ScanPath, List.length_nil, Nat.add_zero] using
      (show start ≤ stop from Nat.le_of_eq hpath)
  | cons pc rest ih =>
    rcases hpath with ⟨rfl, _, htail⟩
    have h := ih htail
    simp only [List.length_cons]
    dsimp [scanNext] at h
    omega

/-- Full semantics, not just the forward implication for known targets. -/
theorem validFrom_iff {code : ByteArray} {pcs : List Nat} {start fuel target : Nat}
    (hpath : ScanPath code start pcs code.size) (hfuel : pcs.length < fuel) :
    Decode.validJumpDestFrom code target start fuel = true ↔
      target ∈ targets code pcs := by
  induction pcs generalizing start fuel with
  | nil =>
    have hs : start = code.size := hpath
    subst start
    cases fuel with
    | zero => simp [targets, Decode.validJumpDestFrom]
    | succ fuel =>
      by_cases he : code.size = target <;>
        simp [Decode.validJumpDestFrom, he, targets]
  | cons pc rest ih =>
    rcases hpath with ⟨hstart, hpc, htail⟩
    subst start
    cases fuel with
    | zero => simp at hfuel
    | succ fuel =>
      have hf : rest.length < fuel := by simp only [List.length_cons] at hfuel; omega
      have hn : pc ∉ rest := by
        intro hm
        have hl := path_lower htail pc hm
        dsimp [scanNext] at hl
        omega
      by_cases he : pc = target
      · subst target
        simp [Decode.validJumpDestFrom, targets, List.mem_filter,
          JumpDestLayout.boundaryIsJumpDest, hpc]
      · by_cases hgt : pc > target
        · have hnall : target ∉ pc :: rest := by
            intro hm
            have hl := path_lower (show ScanPath code pc (pc :: rest) code.size from
              ⟨rfl, hpc, htail⟩) target hm
            omega
          simp [Decode.validJumpDestFrom, he, hgt, targets, List.mem_filter, hnall]
        · have hstop : ¬ (pc > target ∨ pc ≥ code.size) := by omega
          rw [Decode.validJumpDestFrom, if_neg he, if_neg hstop]
          have hrec := ih htail hf
          change Decode.validJumpDestFrom code target (scanNext code pc) fuel = true ↔ _
          rw [hrec]
          simp only [targets, List.mem_filter, List.mem_cons]
          simp [Ne.symm he]

/-- A complete path gives the complete predicate, including out-of-range and
PUSH-payload targets. -/
theorem valid_iff {code : ByteArray} {pcs : List Nat} {target : Nat}
    (hpath : ScanPath code 0 pcs code.size) :
    Decode.isValidJumpDest code target = true ↔ target ∈ targets code pcs := by
  have hl := path_length hpath
  exact validFrom_iff hpath (by omega)

theorem equal_all_targets {left right : ByteArray} {lpcs rpcs : List Nat}
    (hl : ScanPath left 0 lpcs left.size)
    (hr : ScanPath right 0 rpcs right.size)
    (hhits : targets left lpcs = targets right rpcs) (target : Nat) :
    Decode.isValidJumpDest left target = Decode.isValidJumpDest right target := by
  have he : (Decode.isValidJumpDest left target = true) ↔
      (Decode.isValidJumpDest right target = true) := by
    rw [valid_iff hl, valid_iff hr, hhits]
  cases ha : Decode.isValidJumpDest left target <;>
    cases hb : Decode.isValidJumpDest right target <;> simp_all


/-- A valid target necessarily has the JUMPDEST byte. Proving a five-byte
interior contains no JUMPDEST needs no full scanner reduction per target. -/
theorem validFrom_boundary {code : ByteArray} {target : Nat} :
    ∀ fuel pc, Decode.validJumpDestFrom code target pc fuel = true →
      JumpDestLayout.boundaryIsJumpDest code target = true := by
  intro fuel
  induction fuel with
  | zero => intro pc h; simp [Decode.validJumpDestFrom] at h
  | succ fuel ih =>
    intro pc h
    by_cases he : pc = target
    · subst pc
      simpa [Decode.validJumpDestFrom, JumpDestLayout.boundaryIsJumpDest] using h
    · rw [Decode.validJumpDestFrom, if_neg he] at h
      by_cases hstop : pc > target ∨ pc ≥ code.size
      · simp [hstop] at h
      · rw [if_neg hstop] at h
        exact ih _ h

theorem valid_boundary {code : ByteArray} {target : Nat}
    (h : Decode.isValidJumpDest code target = true) :
    JumpDestLayout.boundaryIsJumpDest code target = true :=
  validFrom_boundary _ _ h

end Challenge.Modexp.Submission.LocalPatch.ScannerTargets

