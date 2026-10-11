import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolCertificatesV2

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

/-!
The 594 store consumes word 11 for the last time. Masking only that store,
not every load of word 11, can replace the later byte-610 MSTORE8.
These certificates describe the fused store's final byte provenance. They
are independent of calldata, but are not yet a whole-bytecode certificate.
-/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FusedTerminalCertificates
open PoolShape PoolShapeV2

/-- Apply the two-lane mask at the terminal store, after all earlier stores. -/
def fusedStoreSource (f : Nat → Source) (g : Nat → Nat → Source)
    (a i p : Nat) : Source :=
  if a ≤ p ∧ p < a + 32 then
    if a = 594 then maskSource (p-a) (g i (p-a)) else g i (p-a)
  else f p

def fusedStoreSources (g : Nat → Nat → Source) :
    (Nat → Source) → List (Nat × Nat) → (Nat → Source)
  | f, [] => f
  | f, (a,i)::rest => fusedStoreSources g (fusedStoreSource f g a i) rest

def resultSource : Nat → Source :=
  fusedStoreSources poolSourceV2 fanSourceV2 writes

/-- Every live lane byte is unchanged, including the adjacent overlapping slots. -/
theorem lane_sources : ∀ j : Fin 61, ∀ k : Fin 4,
    resultSource (18*j.val+10+k.val) = resultSourceV2 (18*j.val+10+k.val) ∧
    resultSource (18*j.val+28+k.val) = resultSourceV2 (18*j.val+28+k.val) := by decide

/-- The next block's complete zero-byte invariant is preserved. -/
theorem clear_sources : ∀ a ∈ zeroAddressesV2, resultSource a = .zero := by decide

/-- The old slack witnesses remain valid; reducing junk does not create a carry. -/
theorem slack_sources : ∀ j : Fin 61,
    resultSource (18*j.val+PoolCertificatesV2.zeroByte[j.val]!) = .zero := by decide

/-- All three bytes required by the exceptional terminal addition are zero. -/
theorem terminal_gap_sources : ∀ k : Fin 3,
    resultSource (608+k.val) = .zero := by decide

/-- No later store overlaps the fused store's 32-byte window. -/
theorem tail_disjoint : ∀ x ∈ PoolRawWriter.writes4 (fun _ => EvmSemantics.UInt256.ofNat 0) |>.drop 1,
    x.1 + 32 ≤ 594 ∨ 626 ≤ x.1 := by decide

#print axioms lane_sources
#print axioms clear_sources
#print axioms slack_sources
#print axioms terminal_gap_sources
#print axioms tail_disjoint
end Challenge.Ripemd160.Submission.Proofs.Bytecode.FusedTerminalCertificates
