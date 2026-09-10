import Challenge.Modexp.Submission.Proofs.Fast.CsubAffineStep

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CsubPairsCore

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast.Csub
open Challenge.Modexp.Submission.Proofs.Fast.CsubAffineStep

def runRaw : List Instr → State → Option State
  | [], s => some s
  | i :: rest, s =>
      match Challenge.EvmProof.Stepper.runInstr i s with
      | none => none
      | some next =>
          match rest with
          | [] => some next
          | _ :: _ =>
              match next.halt with
              | .Running => runRaw rest next
              | _ => none

/-- Composition for `runRaw`, mirroring `runLocatedBlock_append`: the only
proofs the structural lane needs for reassembling segments. -/
theorem runRaw_append (left right : List Instr) (s t u : State)
    (hleft : runRaw left s = some t)
    (hrunning : t.halt = .Running)
    (hright : runRaw right t = some u) :
    runRaw (left ++ right) s = some u := by
  induction left generalizing s with
  | nil =>
      simp [runRaw] at hleft
      subst t
      exact hright
  | cons i rest ih =>
      cases rest with
      | nil =>
          cases hnext : Challenge.EvmProof.Stepper.runInstr i s with
          | none => simp [runRaw, hnext] at hleft
          | some next =>
              simp [runRaw, hnext] at hleft
              subst next
              cases right with
              | nil => simpa [runRaw, hnext] using hright
              | cons j tail =>
                  simpa [runRaw, hnext, hrunning] using hright
      | cons j tail =>
          cases hnext : Challenge.EvmProof.Stepper.runInstr i s with
          | none => simp [runRaw, hnext] at hleft
          | some next =>
              cases hhalt : next.halt with
              | Running =>
                  have hrest : runRaw (j :: tail) next = some t := by
                    simpa [runRaw, hnext, hhalt] using hleft
                  have happ := ih next hrest
                  simpa [runRaw, hnext, hhalt] using happ
              | Success => simp [runRaw, hnext, hhalt] at hleft
              | Returned => simp [runRaw, hnext, hhalt] at hleft
              | Reverted => simp [runRaw, hnext, hhalt] at hleft
              | Exception error => simp [runRaw, hnext, hhalt] at hleft


def affineLoadT : List Instr :=
  [Instr.op .JUMPDEST,
   Instr.op (.Dup ⟨0, by decide⟩),
   Instr.op .MLOAD]

/-- Load prefix, M half `[2314, 2350)`: `PUSH32 (W-8256); DUP3; ADD;
MLOAD`. -/
def affineLoadM : List Instr :=
  [Instr.push 32
     115792089237316195423570985008687907853269984665640564039457584007913129631680,
   Instr.op (.Dup ⟨2, by decide⟩),
   Instr.op .ADD,
   Instr.op .MLOAD]

/-- Full 7-instruction load prefix `[2311, 2350)`, by concatenation. -/
def affineLoad : List Instr := affineLoadT ++ affineLoadM


def limbRest : List Instr :=
  [Instr.op (.Dup ⟨1, by decide⟩),
   Instr.op (.Dup ⟨1, by decide⟩),
   Instr.op .GT,
   Instr.op (.Swap ⟨1, by decide⟩),
   Instr.op .SUB,
   Instr.op (.Dup ⟨3, by decide⟩),
   Instr.op (.Dup ⟨1, by decide⟩),
   Instr.op .SUB,
   Instr.op (.Swap ⟨0, by decide⟩),
   Instr.op (.Dup ⟨4, by decide⟩),
   Instr.op .GT,
   Instr.op (.Swap ⟨0, by decide⟩),
   Instr.op (.Swap ⟨1, by decide⟩),
   Instr.op .OR,
   Instr.op (.Swap ⟨2, by decide⟩),
   Instr.op .POP,
   Instr.push 32
     115792089237316195423570985008687907853269984665640564039457584007913129638848,
   Instr.op (.Dup ⟨2, by decide⟩),
   Instr.op .ADD,
   Instr.op .MSTORE,
   Instr.push 32
     115792089237316195423570985008687907853269984665640564039457584007913129639904,
   Instr.op .ADD]

def limbPC (first : Bool) : Nat := if first then 2241 else 2366

def walkState (pc : Nat) (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat pc
    stack := [UInt256.ofNat (affinePt n j), (csStep memory n j).flag, pdst, ret] ++ rest
    memory := (csStep memory n j).memory }

def loadedTState (pc : Nat) (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (pc + 3)
    stack := [MachineState.readWord (csStep memory n j).memory
        (8256 + 32 * (n - 1 - j)), UInt256.ofNat (affinePt n j),
        (csStep memory n j).flag, pdst, ret] ++ rest
    memory := (csStep memory n j).memory }

def loadedState (pc : Nat) (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat (pc + 39)
    stack := [MachineState.readWord (csStep memory n j).memory (32 * (n - 1 - j)),
        MachineState.readWord (csStep memory n j).memory (8256 + 32 * (n - 1 - j)),
        UInt256.ofNat (affinePt n j), (csStep memory n j).flag, pdst, ret] ++ rest
    memory := (csStep memory n j).memory }

def limbProgram : List Instr := affineLoad ++ limbRest

theorem limbProgram_length : limbProgram.length = 29 := by rfl

set_option linter.unusedSimpArgs false in
theorem run_loadT (first : Bool) (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j < n) (hn32 : n ≤ 32) :
    runRaw affineLoadT (walkState (limbPC first) s memory n j pdst ret rest) =
      some (loadedTState (limbPC first) s memory n j pdst ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have h256 : (2 ^ 256 : Nat) =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    decide
  have hta : affinePt n j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 1 - j) := by
    have hlt : affinePt n j <
        115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      rw [← h256]; exact affinePt_lt_word n j hn32 (by omega)
    rw [Nat.mod_eq_of_lt hlt, affinePt_eq_taddr n j hj]
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  cases first <;> simp (config := { maxSteps := 400000 })
    [limbPC, limbRest, walkState, loadedTState, loadedState, runRaw, affineLoadT, Challenge.EvmProof.Stepper.runInstr,

      hc4, hc5, hrun, hta, hactT,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_loadM (first : Bool) (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j < n) (hn32 : n ≤ 32) :
    runRaw affineLoadM (loadedTState (limbPC first) s memory n j pdst ret rest) =
      some (loadedState (limbPC first) s memory n j pdst ret rest) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hmodM : (affinePt n j + UInt256.toNat
      115792089237316195423570985008687907853269984665640564039457584007913129631680) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * (n - 1 - j) := by
    have hC : UInt256.toNat
        115792089237316195423570985008687907853269984665640564039457584007913129631680 =
        115792089237316195423570985008687907853269984665640564039457584007913129631680 := by
      decide
    have h1 := affinePt_eq_taddr n j hj
    have hR : 8256 +
        115792089237316195423570985008687907853269984665640564039457584007913129631680 =
        115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      decide
    rw [hC]; omega
  have hactM : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  cases first <;> simp (config := { maxSteps := 400000 })
    [limbPC, limbRest, walkState, loadedTState, loadedState, runRaw, affineLoadM, Challenge.EvmProof.Stepper.runInstr,

      hc5, hc6, hc7, hrun, hmodM, hactM,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_limbRest (first : Bool) (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hj : j < n) (hn32 : n ≤ 32) :
    runRaw limbRest (loadedState (limbPC first) s memory n j pdst ret rest) =
      some (walkState (limbPC first + 125) s memory n (j + 1) pdst ret rest) := by
  have hjn : j < n := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hmodD : (affinePt n j + UInt256.toNat
      115792089237316195423570985008687907853269984665640564039457584007913129638848) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      7168 + 32 * (n - 1 - j) := by
    have hC : UInt256.toNat
        115792089237316195423570985008687907853269984665640564039457584007913129638848 =
        115792089237316195423570985008687907853269984665640564039457584007913129638848 := by
      decide
    have h1 := affinePt_eq_taddr n j hjn
    have hR : 8256 +
        115792089237316195423570985008687907853269984665640564039457584007913129638848 =
        115792089237316195423570985008687907853269984665640564039457584007913129639936 +
          7168 := by
      decide
    rw [hC]; omega
  have hmodN : (UInt256.toNat
      115792089237316195423570985008687907853269984665640564039457584007913129639904 +
      affinePt n j) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      affinePt n (j + 1) := by
    have hC : UInt256.toNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 =
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
      decide
    have h1 := affinePt_eq_taddr n j hjn
    have hS := affinePt_succ n j (by omega)
    have hR :
        115792089237316195423570985008687907853269984665640564039457584007913129639904 +
          8256 =
        115792089237316195423570985008687907853269984665640564039457584007913129639936 +
          8224 := by
      decide
    rw [hC]; omega
  have hnext : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
        UInt256) + UInt256.ofNat (affinePt n j) =
      UInt256.ofNat (affinePt n (j + 1)) :=
    affine_add_next_word_left n j (by omega) hn32
  have hactD : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (7168 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  cases first <;> simp (config := { maxSteps := 400000 })
    [limbPC, limbRest, walkState, loadedTState, loadedState, runRaw, Challenge.EvmProof.Stepper.runInstr,
      csStep, hnext,
      hc4, hc5, hc6, hc7, hc8, hrun,
      hmodD, hmodN, hactD,
      State.activeWordsAfterUInt256,
      UInt256.gt, UInt256.lt, UInt256.isTrue,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

theorem run_limb (first : Bool) (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) (hj : j < n) (hn32 : n ≤ 32) :
    runRaw limbProgram (walkState (limbPC first) s memory n j pdst ret rest) =
      some (walkState (limbPC first + 125) s memory n (j + 1) pdst ret rest) := by
  have h1 := run_loadT first s memory n j pdst ret rest hcap hrun hact hj hn32
  have h2 := run_loadM first s memory n j pdst ret rest hcap hrun hact hj hn32
  have h3 := run_limbRest first s memory n j pdst ret rest hcap hrun hact hj hn32
  have h12 := runRaw_append affineLoadT affineLoadM _ _ _ h1 hrun h2
  exact runRaw_append affineLoad limbRest _ _ _ h12 hrun h3



end Challenge.Modexp.Submission.Proofs.Fast.CsubPairsCore
