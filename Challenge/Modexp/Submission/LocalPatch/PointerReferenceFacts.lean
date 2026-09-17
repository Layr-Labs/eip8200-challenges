import Challenge.Modexp.Submission.LocalPatch.ScannerTargets
import Challenge.Modexp.Submission.LocalPatch.StaticDomainFrontier64
import Challenge.Modexp.Submission.LocalPatch.PointerReferenceArtifactFacts

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.LocalPatch.PointerSub32
open EvmSemantics EvmSemantics.EVM
open StaticDomain

abbrev reference : ByteArray := ReferenceArtifactFacts.code

section boundedReferenceFacts
set_option maxRecDepth 40000

/-- Frozen frontier64 patch-site facts, isolated from the full byte provider. -/
def oldCode : OldCode reference := ReferenceArtifactFacts.oldCode

private theorem scanNext_le_of_mem_before
    {code : ByteArray} {start stop pc barrier : Nat} {pcs : List Nat}
    (hpath : ScanPath code start pcs stop)
    (hpc : pc ∈ pcs) (hbarrier : barrier ∈ pcs)
    (hlt : pc < barrier) :
    scanNext code pc ≤ barrier := by
  induction pcs generalizing start with
  | nil => simp at hpc
  | cons head tail ih =>
      simp only [ScanPath] at hpath
      rcases hpath with ⟨rfl, _, htail⟩
      simp only [List.mem_cons] at hpc hbarrier
      rcases hpc with rfl | hpc
      · rcases hbarrier with rfl | hbarrier
        · omega
        · exact ScannerTargets.path_lower htail barrier hbarrier
      · have hstart_lt_pc : start < pc := by
          have hl := ScannerTargets.path_lower htail pc hpc
          dsimp [scanNext] at hl
          omega
        rcases hbarrier with rfl | hbarrier
        · omega
        · exact ih htail hpc hbarrier

private theorem patch_pc_mem {pc : Nat}
    (hpc : pc ∈ StaticDomainFrontier64.pcs32) :
    pc ∈ StaticDomainFrontier64.pcs := by
  simp [StaticDomainFrontier64.pcs, hpc]

private theorem entry_mem : entryPC ∈ StaticDomainFrontier64.pcs := by
  change 2539 ∈ StaticDomainFrontier64.pcs
  exact patch_pc_mem (by decide)

private theorem next_facts_of_site {pc : Nat} {op : Operation}
    {imm : Option (UInt256 × Nat)}
    (hdecode : Decode.decodeAt reference pc = some (op, imm))
    (hflow : flowKind op = .next ∨ flowKind op = .jumpi)
    (hsite : siteCheck reference pc = true) :
    execNext reference pc = scanNext reference pc ∧
      execNext reference pc < reference.size := by
  rw [siteCheck, hdecode] at hsite
  simp only [Bool.and_eq_true] at hsite
  have hrest := hsite.2
  rcases hflow with hflow | hflow <;> simp only [hflow] at hrest
  all_goals
    simp only [Bool.and_eq_true] at hrest
    exact ⟨beq_iff_eq.mp hrest.1, of_decide_eq_true hrest.2⟩

private theorem decodeAt_jumpdest_of_boundary {code : ByteArray} {pc : Nat}
    (h : JumpDestLayout.boundaryIsJumpDest code pc = true) :
    Decode.decodeAt code pc = some (.JUMPDEST, none) := by
  unfold JumpDestLayout.boundaryIsJumpDest at h
  by_cases hpc : pc < code.size
  · have hbyte : code[pc] = (0x5b : UInt8) := by
      simpa [Decode.validJumpDestFrom, hpc] using h
    simp [Decode.decodeAt, hpc, hbyte, Decode.opcodeOf]
  · simp [Decode.validJumpDestFrom, hpc] at h

private theorem old_payload_not_valid :
    Decode.isValidJumpDest reference 2541 ≠ true := by
  intro hv
  have hmem := StaticDomainFrontier64.valid_jump_target_mem hv
  have h2540 : 2540 ∈ StaticDomainFrontier64.pcs :=
    patch_pc_mem (by decide)
  have hbound := scanNext_le_of_mem_before
    StaticDomainFrontier64.completePath h2540 hmem (by omega)
  have hcode : StaticDomainFrontier64.code = reference := rfl
  rw [hcode] at hbound
  obtain ⟨heq, _⟩ := next_facts_of_site oldCode.d1
    (Or.inl (by rfl)) (StaticDomainFrontier64.safe h2540)
  have hexec : execNext reference 2540 = 2542 := by
    simp [execNext, oldCode.d1, execWidth]
  omega

/-- Independent of candidate bytes. Four positions are real non-JUMPDEST
instructions certified by `oldCode`; 2541 is the old PUSH1 payload and is
excluded by the already-certified scanner path. -/
theorem no_jump_interior {dest : Nat} (hd : Interior dest) :
    Decode.isValidJumpDest reference dest ≠ true := by
  intro hv
  rcases hd with ⟨hl, hh⟩
  change 2539 < dest at hl
  change dest < 2545 at hh
  have hdest :
      dest = 2540 ∨ dest = 2541 ∨ dest = 2542 ∨
        dest = 2543 ∨ dest = 2544 := by
    omega
  rcases hdest with rfl | rfl | rfl | rfl | rfl
  · have hjump :=
      decodeAt_jumpdest_of_boundary (ScannerTargets.valid_boundary hv)
    rw [oldCode.d1] at hjump
    cases hjump
  · exact old_payload_not_valid hv
  · have hjump :=
      decodeAt_jumpdest_of_boundary (ScannerTargets.valid_boundary hv)
    rw [oldCode.d2] at hjump
    cases hjump
  · have hjump :=
      decodeAt_jumpdest_of_boundary (ScannerTargets.valid_boundary hv)
    rw [oldCode.d3] at hjump
    cases hjump
  · have hjump :=
      decodeAt_jumpdest_of_boundary (ScannerTargets.valid_boundary hv)
    rw [oldCode.d4] at hjump
    cases hjump

/-- Check only exterior fallthroughs. Jumps are handled by no_jump_interior,
not by a no-PUSH-literal audit. -/
def exteriorNextCheck (pc : Nat) : Bool :=
  if Exterior pc then
    match Decode.decodeAt reference pc with
    | some (op, _) =>
        match flowKind op with
        | .next | .jumpi => decide (¬ Interior (execNext reference pc))
        | _ => true
    | none => true
  else true

private theorem pc_lt_execNext {pc : Nat} {op : Operation}
    {imm : Option (UInt256 × Nat)}
    (hdecode : Decode.decodeAt reference pc = some (op, imm)) :
    pc < execNext reference pc := by
  have hwidth : 0 < execWidth op := by
    cases op <;> simp [execWidth]
  simp only [execNext, hdecode]
  omega

private theorem fallthrough_not_interior {pc : Nat} {op : Operation}
    {imm : Option (UInt256 × Nat)}
    (hm : pc ∈ StaticDomainFrontier64.pcs) (he : Exterior pc)
    (hdecode : Decode.decodeAt reference pc = some (op, imm))
    (hflow : flowKind op = .next ∨ flowKind op = .jumpi)
    (hsite : siteCheck reference pc = true) :
    ¬ Interior (execNext reference pc) := by
  obtain ⟨heq, _⟩ := next_facts_of_site hdecode hflow hsite
  rcases he with hbefore | hafter
  · have hbound := scanNext_le_of_mem_before
      StaticDomainFrontier64.completePath hm entry_mem hbefore
    have hcode : StaticDomainFrontier64.code = reference := rfl
    rw [hcode] at hbound
    intro hi
    dsimp [entryPC] at hbound hbefore
    dsimp [Interior, entryPC, exitPC] at hi
    omega
  · have hlt := pc_lt_execNext hdecode
    intro hi
    dsimp [exitPC] at hafter
    dsimp [Interior, entryPC, exitPC] at hi
    omega

private theorem exteriorNextCheck_of_mem {pc : Nat}
    (hm : pc ∈ StaticDomainFrontier64.pcs) :
    exteriorNextCheck pc = true := by
  by_cases he : Exterior pc
  · obtain ⟨op, imm, hdecode, _⟩ :=
      StaticDomainFrontier64.decoded_safe hm
    rw [exteriorNextCheck, if_pos he, hdecode]
    cases hflow : flowKind op with
    | halt => simp only [hflow]
    | jump => simp only [hflow]
    | jumpi =>
        simp only [hflow]
        exact decide_eq_true
          (fallthrough_not_interior hm he hdecode (Or.inr hflow)
            (StaticDomainFrontier64.safe hm))
    | next =>
        simp only [hflow]
        exact decide_eq_true
          (fallthrough_not_interior hm he hdecode (Or.inl hflow)
            (StaticDomainFrontier64.safe hm))
  · simp [exteriorNextCheck, he]

theorem outside_all :
    StaticDomainFrontier64.pcs.all exteriorNextCheck = true := by
  apply List.all_eq_true.mpr
  intro pc hpc
  exact exteriorNextCheck_of_mem hpc

/-- Compatibility projections retained for existing imports.  They are
structural consequences of `outside_all`; none re-evaluates the bytecode. -/
private theorem outside_parts :

    StaticDomainFrontier64.pcs00.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs01.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs02.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs03.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs04.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs05.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs06.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs07.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs08.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs09.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs10.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs11.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs12.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs13.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs14.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs15.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs16.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs17.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs18.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs19.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs20.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs21.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs22.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs23.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs24.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs25.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs26.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs27.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs28.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs29.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs30.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs31.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs32.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs33.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs34.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs35.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs36.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs37.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs38.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs39.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs40.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs41.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs42.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs43.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs44.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs45.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs46.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs47.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs48.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs49.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs50.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs51.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs52.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs53.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs54.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs55.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs56.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs57.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs58.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs59.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs60.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs61.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs62.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs63.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs64.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs65.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs66.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs67.all exteriorNextCheck = true ∧
    StaticDomainFrontier64.pcs68.all exteriorNextCheck = true := by
  have h := outside_all
  unfold StaticDomainFrontier64.pcs at h
  simpa only [List.all_append, Bool.and_eq_true, and_assoc] using h

theorem outside00 :
    StaticDomainFrontier64.pcs00.all exteriorNextCheck = true :=
  outside_parts.1

theorem outside01 :
    StaticDomainFrontier64.pcs01.all exteriorNextCheck = true :=
  outside_parts.2.1

theorem outside02 :
    StaticDomainFrontier64.pcs02.all exteriorNextCheck = true :=
  outside_parts.2.2.1

theorem outside03 :
    StaticDomainFrontier64.pcs03.all exteriorNextCheck = true :=
  outside_parts.2.2.2.1

theorem outside04 :
    StaticDomainFrontier64.pcs04.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.1

theorem outside05 :
    StaticDomainFrontier64.pcs05.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.1

theorem outside06 :
    StaticDomainFrontier64.pcs06.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.1

theorem outside07 :
    StaticDomainFrontier64.pcs07.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.1

theorem outside08 :
    StaticDomainFrontier64.pcs08.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.1

theorem outside09 :
    StaticDomainFrontier64.pcs09.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.1

theorem outside10 :
    StaticDomainFrontier64.pcs10.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.1

theorem outside11 :
    StaticDomainFrontier64.pcs11.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside12 :
    StaticDomainFrontier64.pcs12.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside13 :
    StaticDomainFrontier64.pcs13.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside14 :
    StaticDomainFrontier64.pcs14.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside15 :
    StaticDomainFrontier64.pcs15.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside16 :
    StaticDomainFrontier64.pcs16.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside17 :
    StaticDomainFrontier64.pcs17.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside18 :
    StaticDomainFrontier64.pcs18.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside19 :
    StaticDomainFrontier64.pcs19.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside20 :
    StaticDomainFrontier64.pcs20.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside21 :
    StaticDomainFrontier64.pcs21.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside22 :
    StaticDomainFrontier64.pcs22.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside23 :
    StaticDomainFrontier64.pcs23.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside24 :
    StaticDomainFrontier64.pcs24.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside25 :
    StaticDomainFrontier64.pcs25.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside26 :
    StaticDomainFrontier64.pcs26.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside27 :
    StaticDomainFrontier64.pcs27.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside28 :
    StaticDomainFrontier64.pcs28.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside29 :
    StaticDomainFrontier64.pcs29.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside30 :
    StaticDomainFrontier64.pcs30.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside31 :
    StaticDomainFrontier64.pcs31.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside32 :
    StaticDomainFrontier64.pcs32.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside33 :
    StaticDomainFrontier64.pcs33.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside34 :
    StaticDomainFrontier64.pcs34.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside35 :
    StaticDomainFrontier64.pcs35.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside36 :
    StaticDomainFrontier64.pcs36.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside37 :
    StaticDomainFrontier64.pcs37.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside38 :
    StaticDomainFrontier64.pcs38.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside39 :
    StaticDomainFrontier64.pcs39.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside40 :
    StaticDomainFrontier64.pcs40.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside41 :
    StaticDomainFrontier64.pcs41.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside42 :
    StaticDomainFrontier64.pcs42.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside43 :
    StaticDomainFrontier64.pcs43.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside44 :
    StaticDomainFrontier64.pcs44.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside45 :
    StaticDomainFrontier64.pcs45.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside46 :
    StaticDomainFrontier64.pcs46.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside47 :
    StaticDomainFrontier64.pcs47.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside48 :
    StaticDomainFrontier64.pcs48.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside49 :
    StaticDomainFrontier64.pcs49.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside50 :
    StaticDomainFrontier64.pcs50.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside51 :
    StaticDomainFrontier64.pcs51.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside52 :
    StaticDomainFrontier64.pcs52.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside53 :
    StaticDomainFrontier64.pcs53.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside54 :
    StaticDomainFrontier64.pcs54.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside55 :
    StaticDomainFrontier64.pcs55.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside56 :
    StaticDomainFrontier64.pcs56.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside57 :
    StaticDomainFrontier64.pcs57.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside58 :
    StaticDomainFrontier64.pcs58.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside59 :
    StaticDomainFrontier64.pcs59.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside60 :
    StaticDomainFrontier64.pcs60.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside61 :
    StaticDomainFrontier64.pcs61.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside62 :
    StaticDomainFrontier64.pcs62.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside63 :
    StaticDomainFrontier64.pcs63.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside64 :
    StaticDomainFrontier64.pcs64.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside65 :
    StaticDomainFrontier64.pcs65.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside66 :
    StaticDomainFrontier64.pcs66.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside67 :
    StaticDomainFrontier64.pcs67.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem outside68 :
    StaticDomainFrontier64.pcs68.all exteriorNextCheck = true :=
  outside_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- An actual static successor from outside the macro cannot jump or fall
into a proper source prefix. The excluded entry is handled by the dispatcher. -/
theorem exterior_no_entry {pc next : Nat}
    (hm : pc ∈ StaticDomainFrontier64.pcs) (he : Exterior pc)
    (hs : StaticSuccessor reference pc next) : ¬ Interior next := by
  obtain ⟨op, imm, hdecode, _⟩ :=
    StaticDomainFrontier64.decoded_safe hm
  rw [StaticSuccessor, hdecode] at hs
  cases hflow : flowKind op with
  | halt => simp [hflow] at hs
  | jump =>
      have hv : Decode.isValidJumpDest reference next = true := by
        simpa only [hflow] using hs
      exact fun hi => no_jump_interior hi hv
  | jumpi =>
      have hh : next = execNext reference pc ∨
          Decode.isValidJumpDest reference next = true := by
        simpa only [hflow] using hs
      rcases hh with rfl | hv
      · exact fallthrough_not_interior hm he hdecode (Or.inr hflow)
          (StaticDomainFrontier64.safe hm)
      · exact fun hi => no_jump_interior hi hv
  | next =>
      have hh : next = execNext reference pc := by
        simpa only [hflow] using hs
      subst next
      exact fallthrough_not_interior hm he hdecode (Or.inl hflow)
        (StaticDomainFrontier64.safe hm)

end boundedReferenceFacts

end Challenge.Modexp.Submission.LocalPatch.PointerSub32
