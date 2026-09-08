import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskHoistInline

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CallsConstantCache

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundState QuadRoundTemplate

/-- The cached constant is an extra stack value. Every arithmetic operation
    keeps its original operands. Order is kept too, except at the last cached
    use: there the constant is already directly under the accumulator, so the
    exchange that would restore the original order is dropped entirely and
    the closing `ADD` sees its two operands the other way round. `ADD` is
    commutative, so the value is unchanged (see `uint256_add_comm`). -/
def rewrite (constant : UInt256) (remaining depth : Nat) : List Instr → List Instr
  | [] => []
  | .push width value :: rest =>
    if width.val = 4 ∧ value = constant then
      if remaining = 1 then rest
      else .op (.Dup ⟨depth % 16, Nat.mod_lt _ (by decide)⟩) ::
        rewrite constant (remaining - 1) (depth + 1) rest
    else .push width value :: rewrite constant remaining (depth + 1) rest
  | .op (.Dup d) :: rest =>
    .op (.Dup ⟨(d.idx.val + if depth ≤ d.idx.val then 1 else 0) % 16,
      Nat.mod_lt _ (by decide)⟩) :: rewrite constant remaining (depth + 1) rest
  | .op (.Swap d) :: rest =>
    .op (.Swap ⟨(d.idx.val + if depth ≤ d.idx.val + 1 then 1 else 0) % 16,
      Nat.mod_lt _ (by decide)⟩) :: rewrite constant remaining depth rest
  | .op .ADD :: rest => .op .ADD :: rewrite constant remaining (depth - 1) rest
  | .op .MUL :: rest => .op .MUL :: rewrite constant remaining (depth - 1) rest
  | .op .AND :: rest => .op .AND :: rewrite constant remaining (depth - 1) rest
  | .op .OR :: rest => .op .OR :: rewrite constant remaining (depth - 1) rest
  | .op .XOR :: rest => .op .XOR :: rewrite constant remaining (depth - 1) rest
  | .op .SHR :: rest => .op .SHR :: rewrite constant remaining (depth - 1) rest
  | instruction :: rest => instruction :: rewrite constant remaining depth rest

def keepTemplate (shift : Fin 6) (j : Nat) (p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256) : List Instr :=
  rewrite constant 5 1
    (CachedMaskHoistInline.template shift j p0 p1 p2 p3 r0 r1 r2 r3 constant)

def finishTemplate (shift : Fin 6) (j : Nat) (p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256) : List Instr :=
  rewrite constant 4 1
    (CachedMaskHoistInline.template shift j p0 p1 p2 p3 r0 r1 r2 r3 constant)

def insertConstant (constant : UInt256) (s : State) : State :=
  { s with stack := match s.stack with
    | [] => [constant]
    | value :: rest => value :: constant :: rest }

def frame (right : Bool) (a b c d e : UInt256) (rho : List UInt256) : List UInt256 :=
  if right then a :: b :: c :: d :: e :: mask :: rho else mask :: rho

private theorem uint256_add_method (u v : UInt256) : u.add v = u + v := rfl

private theorem uint256_add_assoc (u v w : UInt256) : (u + v) + w = u + (v + w) := by
  apply Word.word_ext
  change ((u.val + v.val) + w.val).val = (u.val + (v.val + w.val)).val
  simp [Fin.add_def, Nat.add_assoc]

/-- The dropped `SWAP1` of the last cached use leaves the final `ADD`'s two
operands in the opposite order; addition on words is commutative. -/
private theorem uint256_add_comm (u v : UInt256) : u + v = v + u :=
  Word.word_add_comm u v

private theorem left_keep (j : Fin 3)
    (s : State) (startPC p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running) :
    runInstrSeq (keepTemplate 0 (j.val + 2) p0 p1 p2 p3 r0 r1 r2 r3 constant)
      (insertConstant constant (roundEntry s startPC working.a working.b working.c working.d
        working.e (factor :: mask :: rho))) =
      Option.map
        (fun out => insertConstant constant {out with
          pc := pcAfter startPC (keepTemplate 0 (j.val + 2) p0 p1 p2 p3 r0 r1 r2 r3 constant)})
        (runInstrSeq (CachedMaskHoistInline.template 0 (j.val + 2)
          p0 p1 p2 p3 r0 r1 r2 r3 constant)
          (roundEntry s startPC working.a working.b working.c working.d working.e
            (factor :: mask :: rho))) := by
  have hcap (m : Nat) (hm : m ≤ 18) : rho.length + m < 1024 := by omega
  fin_cases j <;>
    simp (config := { maxSteps := 5000000 }) (discharger := omega)
      [insertConstant, keepTemplate, rewrite, CachedMaskHoistInline.template,
       roundEntry, runInstrSeq, Stepper.runInstr, pcAfter, hrun, hcap,
       Instr.size, UInt256.succ, List.exchange, List.getElem?_cons_zero,
       Option.bind_some, Nat.add_assoc, State.activeWordsAfterUInt256,
       uint256_add_method, uint256_add_assoc]

private theorem left_finish (j : Fin 3)
    (s : State) (startPC p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running) :
    runInstrSeq (finishTemplate 0 (j.val + 2) p0 p1 p2 p3 r0 r1 r2 r3 constant)
      (insertConstant constant (roundEntry s startPC working.a working.b working.c working.d
        working.e (factor :: mask :: rho))) =
      Option.map
        (fun out => {out with
          pc := pcAfter startPC (finishTemplate 0 (j.val + 2) p0 p1 p2 p3 r0 r1 r2 r3 constant)})
        (runInstrSeq (CachedMaskHoistInline.template 0 (j.val + 2)
          p0 p1 p2 p3 r0 r1 r2 r3 constant)
          (roundEntry s startPC working.a working.b working.c working.d working.e
            (factor :: mask :: rho))) := by
  have hcap (m : Nat) (hm : m ≤ 18) : rho.length + m < 1024 := by omega
  fin_cases j <;>
    simp (config := { maxSteps := 5000000 }) (discharger := omega)
      [insertConstant, finishTemplate, rewrite, CachedMaskHoistInline.template,
       roundEntry, runInstrSeq, Stepper.runInstr, pcAfter, hrun, hcap,
       Instr.size, UInt256.succ, List.exchange, List.getElem?_cons_zero,
       Option.bind_some, Nat.add_assoc, State.activeWordsAfterUInt256,
       uint256_add_method, uint256_add_assoc, uint256_add_comm]

private theorem right_keep (j : Fin 3)
    (s : State) (startPC p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256)
    (working : Compression.EvmWorking) (a b c d e : UInt256) (rho : List UInt256)
    (hstack : rho.length < 1001) (hrun : s.halt = .Running) :
    runInstrSeq (keepTemplate 5 (j.val + 2) p0 p1 p2 p3 r0 r1 r2 r3 constant)
      (insertConstant constant (roundEntry s startPC working.a working.b working.c working.d
        working.e (factor :: a :: b :: c :: d :: e :: mask :: rho))) =
      Option.map
        (fun out => insertConstant constant {out with
          pc := pcAfter startPC (keepTemplate 5 (j.val + 2) p0 p1 p2 p3 r0 r1 r2 r3 constant)})
        (runInstrSeq (CachedMaskHoistInline.template 5 (j.val + 2)
          p0 p1 p2 p3 r0 r1 r2 r3 constant)
          (roundEntry s startPC working.a working.b working.c working.d working.e
            (factor :: a :: b :: c :: d :: e :: mask :: rho))) := by
  have hcap (m : Nat) (hm : m ≤ 23) : rho.length + m < 1024 := by omega
  fin_cases j <;>
    simp (config := { maxSteps := 5000000 }) (discharger := omega)
      [insertConstant, keepTemplate, rewrite, CachedMaskHoistInline.template,
       roundEntry, runInstrSeq, Stepper.runInstr, pcAfter, hrun, hcap,
       Instr.size, UInt256.succ, List.exchange, List.getElem?_cons_zero,
       Option.bind_some, Nat.add_assoc, State.activeWordsAfterUInt256,
       uint256_add_method, uint256_add_assoc]

private theorem right_finish (j : Fin 3)
    (s : State) (startPC p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256)
    (working : Compression.EvmWorking) (a b c d e : UInt256) (rho : List UInt256)
    (hstack : rho.length < 1001) (hrun : s.halt = .Running) :
    runInstrSeq (finishTemplate 5 (j.val + 2) p0 p1 p2 p3 r0 r1 r2 r3 constant)
      (insertConstant constant (roundEntry s startPC working.a working.b working.c working.d
        working.e (factor :: a :: b :: c :: d :: e :: mask :: rho))) =
      Option.map
        (fun out => {out with
          pc := pcAfter startPC (finishTemplate 5 (j.val + 2) p0 p1 p2 p3 r0 r1 r2 r3 constant)})
        (runInstrSeq (CachedMaskHoistInline.template 5 (j.val + 2)
          p0 p1 p2 p3 r0 r1 r2 r3 constant)
          (roundEntry s startPC working.a working.b working.c working.d working.e
            (factor :: a :: b :: c :: d :: e :: mask :: rho))) := by
  have hcap (m : Nat) (hm : m ≤ 23) : rho.length + m < 1024 := by omega
  fin_cases j <;>
    simp (config := { maxSteps := 5000000 }) (discharger := omega)
      [insertConstant, finishTemplate, rewrite, CachedMaskHoistInline.template,
       roundEntry, runInstrSeq, Stepper.runInstr, pcAfter, hrun, hcap,
       Instr.size, UInt256.succ, List.exchange, List.getElem?_cons_zero,
       Option.bind_some, Nat.add_assoc, State.activeWordsAfterUInt256,
       uint256_add_method, uint256_add_assoc, uint256_add_comm]

/-- Both cache modes preserve the existing left and right suffix bounds. -/
theorem cache_equiv (right finish : Bool) (j : Fin 3)
    (s : State) (startPC p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256)
    (working : Compression.EvmWorking) (a b c d e : UInt256) (rho : List UInt256)
    (hstack : rho.length < if right then 1001 else 1006)
    (hrun : s.halt = .Running) :
    let shift : Fin 6 := if right then 5 else 0
    let original := CachedMaskHoistInline.template shift (j.val + 2)
      p0 p1 p2 p3 r0 r1 r2 r3 constant
    let cached := if finish then finishTemplate shift (j.val + 2)
      p0 p1 p2 p3 r0 r1 r2 r3 constant else keepTemplate shift (j.val + 2)
      p0 p1 p2 p3 r0 r1 r2 r3 constant
    let entry := roundEntry s startPC working.a working.b working.c working.d
      working.e (factor :: frame right a b c d e rho)
    runInstrSeq cached (insertConstant constant entry) =
      Option.map (fun out =>
        if finish then { out with pc := pcAfter startPC cached }
        else insertConstant constant { out with pc := pcAfter startPC cached })
        (runInstrSeq original entry) := by
  cases right <;> cases finish
  · simpa [frame] using
      (left_keep j s startPC p0 p1 p2 p3 r0 r1 r2 r3 constant working rho
        (by simpa using hstack) hrun)
  · simpa [frame] using
      (left_finish j s startPC p0 p1 p2 p3 r0 r1 r2 r3 constant working rho
        (by simpa using hstack) hrun)
  · simpa [frame] using
      (right_keep j s startPC p0 p1 p2 p3 r0 r1 r2 r3 constant working a b c d e rho
        (by simpa using hstack) hrun)
  · simpa [frame] using
      (right_finish j s startPC p0 p1 p2 p3 r0 r1 r2 r3 constant working a b c d e rho
        (by simpa using hstack) hrun)

#print axioms cache_equiv

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CallsConstantCache
