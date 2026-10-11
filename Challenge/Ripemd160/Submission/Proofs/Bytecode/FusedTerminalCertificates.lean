import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolCertificatesV2

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

/-!
The 594 store consumes word 11 for the last time. Masking only that store,
not every load of word 11, can replace the later byte-610 MSTORE8.
In addition, all four 16-byte schedule fan copies are replaced by full 32-byte
`MLOAD`/`MSTORE` snapshots (`146 → 128`, `178 → 196`, `236 → 218`, `268 → 286`),
whose source intervals are pairwise disjoint from all earlier snapshot destinations.
-/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FusedTerminalCertificates
open PoolShape PoolShapeV2

/-- All four 32-byte snapshot sources (`[146,178)`, `[178,210)`, `[236,268)`, `[268,300)`)
lie outside every earlier snapshot's 32-byte destination (`[128,160)`, `[196,228)`, `[218,250)`),
so the four snapshots compose to a single flat address map. -/
def copiedAddress4 (a : Nat) : Nat :=
  if 286 ≤ a ∧ a < 318 then a - 18
  else if 218 ≤ a ∧ a < 250 then a + 18
  else if 196 ≤ a ∧ a < 218 then a - 18
  else if 128 ≤ a ∧ a < 160 then a + 18 else a

def fanSource4 (a : Nat) : Source := scratchSourceV2 (copiedAddress4 a)

def loadSource4 (i j : Nat) : Source := fanSource4 (Pair13PoolRaw.poolAddrV2 i + j)

def poolSource4 (i j : Nat) : Source := loadSource4 i j

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
  fusedStoreSources poolSource4 fanSource4 writes

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
