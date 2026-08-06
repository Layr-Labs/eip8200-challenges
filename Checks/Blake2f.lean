import Challenge.Blake2f
set_option warningAsError true
/-! BLAKE2f axiom-footprint checks. -/

/--
info: 'Challenge.Blake2f.ProofSupport.Bytecode.correct_of_directProof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.ProofSupport.Bytecode.correct_of_directProof

/-- info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.MixG.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.MixG.run

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.MixG.gasSteps_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.MixG.gasSteps_cost

/-- info: 'Challenge.Blake2f.ProofSupport.Algorithm.mixLanesEVM_embed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Blake2f.ProofSupport.Algorithm.mixLanesEVM_embed

/-- info: 'Challenge.Blake2f.ProofSupport.Algorithm.lanesAt_crypto_mixG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Challenge.Blake2f.ProofSupport.Algorithm.lanesAt_crypto_mixG

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.Initialization.hLoopGasSteps_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.Initialization.hLoopGasSteps_cost

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.Initialization.mLoopGasSteps_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.Initialization.mLoopGasSteps_cost

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.Initialization.vLoopGasSteps_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.Initialization.vLoopGasSteps_cost

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.Initialization.constantsGasSteps_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.Initialization.constantsGasSteps_cost

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.ScalarInitialization.gasSteps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.ScalarInitialization.gasSteps

/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.ScalarInitialization.gasSteps_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.ScalarInitialization.gasSteps_cost

/-
The entire valid-input prefix, through calldata decoding and work-vector setup,
is certified without any project axioms beyond Lean's standard quotient and
extensionality foundations.
-/
/--
info: 'Challenge.Blake2f.Reference.Proofs.Bytecode.ScalarInitialization.fullGasSteps_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Challenge.Blake2f.Reference.Proofs.Bytecode.ScalarInitialization.fullGasSteps_cost
