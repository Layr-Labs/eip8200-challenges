import Challenge
set_option warningAsError true
/-!
# Checks

CI meta-checks for this repository's guarantees. **Not** part of the
`Challenge` library; CI type-checks this file separately
(`lake env lean Checks.lean`).

Each `#guard_msgs in #print axioms …` pins the *exact* axiom set of a theorem.
If a `sorry` (which appears as `sorryAx`), a `native_decide`
(`Lean.ofReduceBool`), or any new axiom ever slips in — directly or through a
dependency edit — the printed message changes and elaboration fails. The
expected set is Lean's three standard classical axioms and nothing else, which
is also the footprint the pinned compiler and semantics are checked against
upstream.

The same discipline applies to a submission: a Tier-2 proof is only a proof if
`#print axioms` of it prints this line.
-/

/-- info: 'Challenge.EvmProof.Bytecode.assemble_disassemble' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.Bytecode.assemble_disassemble

/-- info: 'Challenge.EvmProof.Bytecode.JumpDestCertificate.valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.Bytecode.JumpDestCertificate.valid

/-- info: 'Challenge.EvmProof.eval_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.eval_of_steps

/-- info: 'Challenge.EvmProof.Reaches.toEval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.EvmProof.Reaches.toEval

/--
info: 'Challenge.Sha256.ProofSupport.Bytecode.correct_of_directProof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Sha256.ProofSupport.Bytecode.correct_of_directProof

/--
info: 'Challenge.Sha256.Reference.Proofs.Bytecode.Reference.reaches_firstTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Sha256.Reference.Proofs.Bytecode.Reference.reaches_firstTarget

/--
info: 'Challenge.Sha256.Reference.Proofs.Bytecode.ReferenceCorrect.referenceDirectProof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Sha256.Reference.Proofs.Bytecode.ReferenceCorrect.referenceDirectProof

/--
info: 'Challenge.Sha256.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Sha256.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correct

/-- info: 'Challenge.Sha256.correct_of_computesDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Sha256.correct_of_computesDigest

/-- info: 'Challenge.Sha256.reference_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Sha256.reference_correct

/-- info: 'Challenge.Sha256.correct_of_schedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Sha256.correct_of_schedule

/-- info: 'Challenge.Sha256.frame_frameOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Sha256.frame_frameOK
