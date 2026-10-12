import Challenge.Modexp.Submission.Proofs.Bytecode.WindowSixteenBlock

set_option warningAsError true

/-!
Precopy route (lane precopy256): every modulus copy is pushed before the
accumulator exists, so a window is four squarings and an immediate-mask digit
multiply over a pool `replicate remaining modulus`, with no refill and with any
frame `below` the pool.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowPrecopy

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- One window: `DUP1 MULMOD` four times, then `PUSH2 laddr MLOAD PUSH2 01e0 AND MLOAD MULMOD`. -/
def windowProgram (laddr : Nat) : List Instr :=
  WindowSixteenBlock.Block.squares 4 ++ WindowSixteenBlock.Lookup.lookupImmediateProgram laddr

theorem run_window (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator : UInt256) (below : List UInt256) (remaining : Nat)
    (hremaining : 5 ≤ remaining)
    (laddr : Nat) (hladdr : laddr + 32 ≤ 576)
    (index : Nat) (hindex : index < 16)
    (hread : MachineState.readWord mem (32 * index) =
      WindowMath.tableWord base modulus index)
    (haddress :
      (UInt256.land (UInt256.ofNat 480) (MachineState.readWord mem laddr)).toNat =
        32 * index)
    (hcap : remaining + below.length + 4 < 1024) :
    runInstructions (windowProgram laddr)
      (WindowTwentyOneLookup.framed template pc mem 18
        (accumulator :: List.replicate remaining modulus ++ below)) =
    some (WindowTwentyOneLookup.framed template (advancePC 18 pc) mem 18
      (WindowMath.nibbleWordStep modulus base accumulator index ::
        List.replicate (remaining - 5) modulus ++ below)) := by
  have hsplit := WindowSixteenBlock.Block.replicate_split modulus remaining 4 (by omega)
  let tail := List.replicate (remaining - 4) modulus ++ below
  have hs := WindowSixteenBlock.Block.run_squares template pc mem 18 modulus accumulator
    tail 4 (by decide) (by
      simp only [tail, List.length_append, List.length_replicate]
      omega)
  let tail' := List.replicate (remaining - 5) modulus ++ below
  have hl := WindowSixteenBlock.Lookup.run_lookupImmediate template (advancePC 8 pc) mem
    base modulus (WindowMath.squareWordAfter modulus 4 accumulator) tail' laddr hladdr
    index hindex hread haddress (by
      simp only [tail', List.length_append, List.length_replicate]
      omega)
  have hrep : tail = modulus :: tail' := by
    have h : remaining - 4 = (remaining - 5) + 1 := by omega
    simp only [tail, tail', h, List.replicate_succ, List.cons_append]
  rw [← hrep, mulMod_comm (WindowMath.tableWord base modulus index)
      (WindowMath.squareWordAfter modulus 4 accumulator) modulus] at hl
  have hall := runInstructions_append_some _ _ _ _ _ hs hl
  have hpc : advancePC 10 (advancePC 8 pc) = advancePC 18 pc := by
    rw [← advancePC_add]
  simpa only [windowProgram, tail, tail', hsplit, hpc, WindowMath.nibbleWordStep, List.cons_append,
    List.append_assoc] using hall

/-- One window per load address, in execution order. -/
def windows : List Nat → List Instr
  | [] => []
  | laddr :: rest => windowProgram laddr ++ windows rest

/-- The accumulator after one window step per digit index. -/
def foldSteps (modulus base : UInt256) : UInt256 → List Nat → UInt256
  | acc, [] => acc
  | acc, index :: rest => foldSteps modulus base (WindowMath.nibbleWordStep modulus base acc index) rest

/-- A run of windows over `(laddr, index)` pairs consumes five pool copies each. -/
theorem run_windows (template : State) (mem : ByteArray) (base modulus : UInt256)
    (below : List UInt256)
    (hread : ∀ index, index < 16 →
      MachineState.readWord mem (32 * index) = WindowMath.tableWord base modulus index) :
    ∀ (ws : List (Nat × Nat)),
    (∀ w ∈ ws, w.1 + 32 ≤ 576 ∧ w.2 < 16 ∧
      (UInt256.land (UInt256.ofNat 480) (MachineState.readWord mem w.1)).toNat = 32 * w.2) →
    ∀ (pc accumulator : UInt256) (extra : Nat),
    5 * ws.length + extra + below.length + 4 < 1024 →
    runInstructions (windows (ws.map Prod.fst))
      (WindowTwentyOneLookup.framed template pc mem 18
        (accumulator :: List.replicate (5 * ws.length + extra) modulus ++ below)) =
    some (WindowTwentyOneLookup.framed template (advancePC (18 * ws.length) pc) mem 18
      (foldSteps modulus base accumulator (ws.map Prod.snd) ::
        List.replicate extra modulus ++ below))
  | [], _, pc, accumulator, extra, _ => by
      simp [windows, foldSteps, runInstructions, advancePC]
  | w :: ws, hws, pc, accumulator, extra, hcap => by
      have hw := hws w (by simp)
      have hs := run_window template pc mem base modulus accumulator below
        (5 * (ws.length + 1) + extra) (by omega) w.1 hw.1 w.2 hw.2.1 (hread w.2 hw.2.1) hw.2.2
        (by simp only [List.length_cons] at hcap; omega)
      have hsub : 5 * (ws.length + 1) + extra - 5 = 5 * ws.length + extra := by omega
      rw [hsub] at hs
      have hi := run_windows template mem base modulus below hread ws
        (fun v hv => hws v (by simp [hv])) (advancePC 18 pc)
        (WindowMath.nibbleWordStep modulus base accumulator w.2) extra
        (by simp only [List.length_cons] at hcap; omega)
      have hall := runInstructions_append_some _ _ _ _ _ hs hi
      have hpc : advancePC (18 * ws.length) (advancePC 18 pc) =
          advancePC (18 * (ws.length + 1)) pc := by
        rw [← advancePC_add]
        congr 1
        omega
      simpa only [windows, foldSteps, List.map_cons, List.length_cons, hpc] using hall

/-- `count` copies of `DUP1`: the modulus pool push after the leading `DUP2`. -/
def dupOnes : Nat → List Instr
  | 0 => []
  | count + 1 => .op (.Dup ⟨0, by decide⟩) :: dupOnes count

private theorem run_dupOne (template : State) (pc : UInt256) (mem : ByteArray)
    (active : Nat) (modulus : UInt256) (tail : List UInt256)
    (hcap : tail.length + 2 < 1024) :
    runInstructions [.op (.Dup ⟨0, by decide⟩)]
      (WindowTwentyOneLookup.framed template pc mem active (modulus :: tail)) =
    some (WindowTwentyOneLookup.framed template (advancePC 1 pc) mem active
      (modulus :: modulus :: tail)) := by
  have hcap1 : tail.length + 1 < 1024 := by omega
  simp (disch := omega)
    [runInstructions, WindowTwentyOneLookup.framed,
      Challenge.EvmProof.Stepper.runInstr, hcap1,
      List.getElem?_cons_zero, advancePC]

theorem run_dupOnes (template : State) (mem : ByteArray) (active : Nat)
    (modulus : UInt256) :
    ∀ (count : Nat) (pc : UInt256) (tail : List UInt256),
    count + tail.length + 1 < 1024 →
    runInstructions (dupOnes count)
      (WindowTwentyOneLookup.framed template pc mem active (modulus :: tail)) =
    some (WindowTwentyOneLookup.framed template (advancePC count pc) mem active
      (List.replicate (count + 1) modulus ++ tail))
  | 0, pc, tail, _ => by
      simp [dupOnes, runInstructions, advancePC]
  | count + 1, pc, tail, hcap => by
      have hs := run_dupOne template pc mem active modulus tail (by omega)
      have hi := run_dupOnes template mem active modulus count (advancePC 1 pc)
        (modulus :: tail) (by simp only [List.length_cons]; omega)
      have hall := runInstructions_append_some _ _ _ _ _ hs hi
      have hpc : advancePC count (advancePC 1 pc) = advancePC (count + 1) pc := by
        rw [← advancePC_add, Nat.add_comm]
      have hrep : List.replicate (count + 1) modulus ++ modulus :: tail =
          List.replicate (count + 1 + 1) modulus ++ tail := by
        rw [List.replicate_succ' (n := count + 1), List.append_assoc, List.singleton_append]
      simpa only [dupOnes, List.singleton_append, hpc, hrep] using hall

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowPrecopy
