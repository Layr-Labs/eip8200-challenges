import Challenge.Ripemd160.Submission.Proofs.Bytecode.CallsConstantParams

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.WordCacheTemplates

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundState QuadRoundTemplate
open CavityQuadGroup

/-- The three values are loaded once after the message schedule is populated. -/
def words (s : State) : List UInt256 :=
  [MachineState.readWord s.memory 192, MachineState.readWord s.memory 196,
   MachineState.readWord s.memory 200]

/-- `depth` is the zero-based stack position of the first cached word.
Only an adjacent PUSH1/MLOAD pair naming one of the three schedule offsets is
replaced. All other instructions, operands, and their order are preserved. -/
def rewrite (depth : Nat) : List Instr → List Instr
  | .push width address :: .op .MLOAD :: rest =>
    if width.val = 1 ∧ address = UInt256.ofNat 192 then
      .op (.Dup ⟨depth % 16, Nat.mod_lt _ (by decide)⟩) :: rewrite (depth + 1) rest
    else if width.val = 1 ∧ address = UInt256.ofNat 196 then
      .op (.Dup ⟨(depth + 1) % 16, Nat.mod_lt _ (by decide)⟩) :: rewrite (depth + 1) rest
    else if width.val = 1 ∧ address = UInt256.ofNat 200 then
      .op (.Dup ⟨(depth + 2) % 16, Nat.mod_lt _ (by decide)⟩) :: rewrite (depth + 1) rest
    else .push width address :: .op .MLOAD :: rewrite (depth + 1) rest
  | .push width value :: rest => .push width value :: rewrite (depth + 1) rest
  | .op (.Dup d) :: rest => .op (.Dup d) :: rewrite (depth + 1) rest
  | .op .ADD :: rest => .op .ADD :: rewrite (depth - 1) rest
  | .op .MUL :: rest => .op .MUL :: rewrite (depth - 1) rest
  | .op .AND :: rest => .op .AND :: rewrite (depth - 1) rest
  | .op .OR :: rest => .op .OR :: rewrite (depth - 1) rest
  | .op .XOR :: rest => .op .XOR :: rewrite (depth - 1) rest
  | .op .SHR :: rest => .op .SHR :: rewrite (depth - 1) rest
  | instruction :: rest => instruction :: rewrite depth rest
  | [] => []

/-- Group order: L0, L2, L4, R0, R1, R2, R4. -/
def params (g : Fin 7) : Fin 4 → Params :=
  match g.val with
  | 0 => CachedMaskParams.left 0
  | 1 => CallsConstantParams.left2
  | 2 => CallsConstantParams.left4
  | 3 => CallsConstantParams.right0
  | 4 => CallsConstantParams.right1
  | 5 => CallsConstantParams.right2
  | _ => CachedMaskParams.right

def isRight (g : Fin 7) : Bool := decide (3 ≤ g.val)
def hasConstant (g : Fin 7) : Bool := decide (g.val ≠ 0 ∧ g.val ≠ 6)
def shift (g : Fin 7) : Fin 6 := if isRight g then 5 else 0
def functionIndex (g : Fin 7) : Fin 3 :=
  match g.val with
  | 2 | 3 => 2
  | 4 => 1
  | _ => 0
def constant (g : Fin 7) : UInt256 := (params g 0).constant

def sourceQuad (g : Fin 7) (k : Fin 4) : List Instr :=
  if hasConstant g then
    if k.val = 3 then
      CallsConstantGroup.finishCode (shift g) (functionIndex g) (params g k) (constant g)
    else
      CallsConstantGroup.keepCode (shift g) (functionIndex g) (params g k) (constant g)
  else CachedMaskQuadGroup.code (params g k) (shift g)

def depth (g : Fin 7) : Nat := 7 + (shift g).val + if hasConstant g then 1 else 0
def quadCode (g : Fin 7) (k : Fin 4) : List Instr := rewrite (depth g) (sourceQuad g k)

def frame (g : Fin 7) (s : State) (a b c d e : UInt256) (rho : List UInt256) :
    List UInt256 :=
  if isRight g then a :: b :: c :: d :: e :: mask :: (words s ++ rho)
  else mask :: (words s ++ rho)

def entry (g : Fin 7) (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256) : State :=
  if hasConstant g then
    CallsConstantCache.insertConstant (constant g) (stateAt s pc w (frame g s a b c d e rho))
  else stateAt s pc w (frame g s a b c d e rho)

def afterQuad (g : Fin 7) (k : Fin 4) (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (a b c d e : UInt256) (rho : List UInt256) : State :=
  if hasConstant g then
    if k.val = 3 then stateAt s pc w (frame g s a b c d e rho)
    else entry g s pc w a b c d e rho
  else stateAt s pc w (frame g s a b c d e rho)

private theorem activeWordsAfter_of_le (curr offset : Nat)
    (hcurr : 11 ≤ curr) (hoffset : offset ≤ 320) :
    MachineState.activeWordsAfter curr offset 32 = curr := by
  unfold MachineState.activeWordsAfter
  simp only [show (32 : Nat) ≠ 0 by decide, if_false]
  apply Nat.max_eq_left
  have hq : (offset + 32 - 1) / 32 < curr :=
    (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
  omega

private theorem ofNat_toNat (w : UInt256) : UInt256.ofNat w.toNat = w := by
  cases w with
  | mk val => simp [UInt256.ofNat, UInt256.toNat, UInt256.size]

set_option linter.unusedSimpArgs false in
private theorem quad_equiv0 (k : Fin 4)
    (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1003) (hrun : s.halt = .Running) :
    runInstrSeq (quadCode 0 k) (entry 0 s pc w a b c d e rho) =
      Option.map (fun out => {out with pc := pcAfter pc (quadCode 0 k)})
        (runInstrSeq (sourceQuad 0 k) (entry 0 s pc w a b c d e rho)) := by
  have hcap (m : Nat) (hm : m ≤ 21) : rho.length + m < 1024 := by omega
  fin_cases k <;>
    simp (config := { maxSteps := 5000000 }) (discharger := omega)
      [quadCode, sourceQuad, depth, shift, hasConstant, isRight, functionIndex,
       params, constant, CallsConstantParams.left2, CallsConstantParams.left4,
       CallsConstantParams.right0, CallsConstantParams.right1, CallsConstantParams.right2,
       CallsConstantParams.left, CallsConstantParams.right,
       CachedMaskParams.left, CachedMaskParams.right, CavityParams.right,
       SingleCachedMaskInlineParams.rightParams,
       CachedMaskQuadGroup.code, CallsConstantGroup.keepCode, CallsConstantGroup.finishCode,
       CallsConstantCache.keepTemplate, CallsConstantCache.finishTemplate,
       CallsConstantCache.rewrite, CachedMaskHoistInline.template,
       StackRoundData.leftAddress, StackRoundData.rightAddress,
       StackRoundData.leftRotation, StackRoundData.rightRotation,
       StackRoundData.leftConstant, StackRoundData.rightConstant,
       Crypto.Ripemd160.r, Crypto.Ripemd160.rP, Crypto.Ripemd160.s, Crypto.Ripemd160.sP,
       Crypto.Ripemd160.K, Crypto.Ripemd160.KP,
       rewrite, entry, frame, words, CallsConstantCache.insertConstant,
       stateAt, roundEntry, runInstrSeq, Stepper.runInstr, pcAfter,
       hrun, hcap, Instr.size, UInt256.succ, List.exchange,
       List.getElem?_cons_zero, Option.bind_some, Nat.add_assoc,
       State.activeWordsAfterUInt256, activeWordsAfter_of_le, hactive,
       ofNat_toNat, Word.word_toNat_ofNat]


set_option linter.unusedSimpArgs false in
private theorem quad_equiv1 (k : Fin 4)
    (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1003) (hrun : s.halt = .Running) :
    runInstrSeq (quadCode 1 k) (entry 1 s pc w a b c d e rho) =
      Option.map (fun out => {out with pc := pcAfter pc (quadCode 1 k)})
        (runInstrSeq (sourceQuad 1 k) (entry 1 s pc w a b c d e rho)) := by
  have hcap (m : Nat) (hm : m ≤ 21) : rho.length + m < 1024 := by omega
  fin_cases k <;>
    simp (config := { maxSteps := 5000000 }) (discharger := omega)
      [quadCode, sourceQuad, depth, shift, hasConstant, isRight, functionIndex,
       params, constant, CallsConstantParams.left2, CallsConstantParams.left4,
       CallsConstantParams.right0, CallsConstantParams.right1, CallsConstantParams.right2,
       CallsConstantParams.left, CallsConstantParams.right,
       CachedMaskParams.left, CachedMaskParams.right, CavityParams.right,
       SingleCachedMaskInlineParams.rightParams,
       CachedMaskQuadGroup.code, CallsConstantGroup.keepCode, CallsConstantGroup.finishCode,
       CallsConstantCache.keepTemplate, CallsConstantCache.finishTemplate,
       CallsConstantCache.rewrite, CachedMaskHoistInline.template,
       StackRoundData.leftAddress, StackRoundData.rightAddress,
       StackRoundData.leftRotation, StackRoundData.rightRotation,
       StackRoundData.leftConstant, StackRoundData.rightConstant,
       Crypto.Ripemd160.r, Crypto.Ripemd160.rP, Crypto.Ripemd160.s, Crypto.Ripemd160.sP,
       Crypto.Ripemd160.K, Crypto.Ripemd160.KP,
       rewrite, entry, frame, words, CallsConstantCache.insertConstant,
       stateAt, roundEntry, runInstrSeq, Stepper.runInstr, pcAfter,
       hrun, hcap, Instr.size, UInt256.succ, List.exchange,
       List.getElem?_cons_zero, Option.bind_some, Nat.add_assoc,
       State.activeWordsAfterUInt256, activeWordsAfter_of_le, hactive,
       ofNat_toNat, Word.word_toNat_ofNat]


set_option linter.unusedSimpArgs false in
private theorem quad_equiv2 (k : Fin 4)
    (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1003) (hrun : s.halt = .Running) :
    runInstrSeq (quadCode 2 k) (entry 2 s pc w a b c d e rho) =
      Option.map (fun out => {out with pc := pcAfter pc (quadCode 2 k)})
        (runInstrSeq (sourceQuad 2 k) (entry 2 s pc w a b c d e rho)) := by
  have hcap (m : Nat) (hm : m ≤ 21) : rho.length + m < 1024 := by omega
  fin_cases k <;>
    simp (config := { maxSteps := 5000000 }) (discharger := omega)
      [quadCode, sourceQuad, depth, shift, hasConstant, isRight, functionIndex,
       params, constant, CallsConstantParams.left2, CallsConstantParams.left4,
       CallsConstantParams.right0, CallsConstantParams.right1, CallsConstantParams.right2,
       CallsConstantParams.left, CallsConstantParams.right,
       CachedMaskParams.left, CachedMaskParams.right, CavityParams.right,
       SingleCachedMaskInlineParams.rightParams,
       CachedMaskQuadGroup.code, CallsConstantGroup.keepCode, CallsConstantGroup.finishCode,
       CallsConstantCache.keepTemplate, CallsConstantCache.finishTemplate,
       CallsConstantCache.rewrite, CachedMaskHoistInline.template,
       StackRoundData.leftAddress, StackRoundData.rightAddress,
       StackRoundData.leftRotation, StackRoundData.rightRotation,
       StackRoundData.leftConstant, StackRoundData.rightConstant,
       Crypto.Ripemd160.r, Crypto.Ripemd160.rP, Crypto.Ripemd160.s, Crypto.Ripemd160.sP,
       Crypto.Ripemd160.K, Crypto.Ripemd160.KP,
       rewrite, entry, frame, words, CallsConstantCache.insertConstant,
       stateAt, roundEntry, runInstrSeq, Stepper.runInstr, pcAfter,
       hrun, hcap, Instr.size, UInt256.succ, List.exchange,
       List.getElem?_cons_zero, Option.bind_some, Nat.add_assoc,
       State.activeWordsAfterUInt256, activeWordsAfter_of_le, hactive,
       ofNat_toNat, Word.word_toNat_ofNat]


set_option linter.unusedSimpArgs false in
private theorem quad_equiv3 (k : Fin 4)
    (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < 998) (hrun : s.halt = .Running) :
    runInstrSeq (quadCode 3 k) (entry 3 s pc w a b c d e rho) =
      Option.map (fun out => {out with pc := pcAfter pc (quadCode 3 k)})
        (runInstrSeq (sourceQuad 3 k) (entry 3 s pc w a b c d e rho)) := by
  have hcap (m : Nat) (hm : m ≤ 26) : rho.length + m < 1024 := by omega
  fin_cases k <;>
    simp (config := { maxSteps := 5000000 }) (discharger := omega)
      [quadCode, sourceQuad, depth, shift, hasConstant, isRight, functionIndex,
       params, constant, CallsConstantParams.left2, CallsConstantParams.left4,
       CallsConstantParams.right0, CallsConstantParams.right1, CallsConstantParams.right2,
       CallsConstantParams.left, CallsConstantParams.right,
       CachedMaskParams.left, CachedMaskParams.right, CavityParams.right,
       SingleCachedMaskInlineParams.rightParams,
       CachedMaskQuadGroup.code, CallsConstantGroup.keepCode, CallsConstantGroup.finishCode,
       CallsConstantCache.keepTemplate, CallsConstantCache.finishTemplate,
       CallsConstantCache.rewrite, CachedMaskHoistInline.template,
       StackRoundData.leftAddress, StackRoundData.rightAddress,
       StackRoundData.leftRotation, StackRoundData.rightRotation,
       StackRoundData.leftConstant, StackRoundData.rightConstant,
       Crypto.Ripemd160.r, Crypto.Ripemd160.rP, Crypto.Ripemd160.s, Crypto.Ripemd160.sP,
       Crypto.Ripemd160.K, Crypto.Ripemd160.KP,
       rewrite, entry, frame, words, CallsConstantCache.insertConstant,
       stateAt, roundEntry, runInstrSeq, Stepper.runInstr, pcAfter,
       hrun, hcap, Instr.size, UInt256.succ, List.exchange,
       List.getElem?_cons_zero, Option.bind_some, Nat.add_assoc,
       State.activeWordsAfterUInt256, activeWordsAfter_of_le, hactive,
       ofNat_toNat, Word.word_toNat_ofNat]


set_option linter.unusedSimpArgs false in
private theorem quad_equiv4 (k : Fin 4)
    (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < 998) (hrun : s.halt = .Running) :
    runInstrSeq (quadCode 4 k) (entry 4 s pc w a b c d e rho) =
      Option.map (fun out => {out with pc := pcAfter pc (quadCode 4 k)})
        (runInstrSeq (sourceQuad 4 k) (entry 4 s pc w a b c d e rho)) := by
  have hcap (m : Nat) (hm : m ≤ 26) : rho.length + m < 1024 := by omega
  fin_cases k <;>
    simp (config := { maxSteps := 5000000 }) (discharger := omega)
      [quadCode, sourceQuad, depth, shift, hasConstant, isRight, functionIndex,
       params, constant, CallsConstantParams.left2, CallsConstantParams.left4,
       CallsConstantParams.right0, CallsConstantParams.right1, CallsConstantParams.right2,
       CallsConstantParams.left, CallsConstantParams.right,
       CachedMaskParams.left, CachedMaskParams.right, CavityParams.right,
       SingleCachedMaskInlineParams.rightParams,
       CachedMaskQuadGroup.code, CallsConstantGroup.keepCode, CallsConstantGroup.finishCode,
       CallsConstantCache.keepTemplate, CallsConstantCache.finishTemplate,
       CallsConstantCache.rewrite, CachedMaskHoistInline.template,
       StackRoundData.leftAddress, StackRoundData.rightAddress,
       StackRoundData.leftRotation, StackRoundData.rightRotation,
       StackRoundData.leftConstant, StackRoundData.rightConstant,
       Crypto.Ripemd160.r, Crypto.Ripemd160.rP, Crypto.Ripemd160.s, Crypto.Ripemd160.sP,
       Crypto.Ripemd160.K, Crypto.Ripemd160.KP,
       rewrite, entry, frame, words, CallsConstantCache.insertConstant,
       stateAt, roundEntry, runInstrSeq, Stepper.runInstr, pcAfter,
       hrun, hcap, Instr.size, UInt256.succ, List.exchange,
       List.getElem?_cons_zero, Option.bind_some, Nat.add_assoc,
       State.activeWordsAfterUInt256, activeWordsAfter_of_le, hactive,
       ofNat_toNat, Word.word_toNat_ofNat]


set_option linter.unusedSimpArgs false in
private theorem quad_equiv5 (k : Fin 4)
    (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < 998) (hrun : s.halt = .Running) :
    runInstrSeq (quadCode 5 k) (entry 5 s pc w a b c d e rho) =
      Option.map (fun out => {out with pc := pcAfter pc (quadCode 5 k)})
        (runInstrSeq (sourceQuad 5 k) (entry 5 s pc w a b c d e rho)) := by
  have hcap (m : Nat) (hm : m ≤ 26) : rho.length + m < 1024 := by omega
  fin_cases k <;>
    simp (config := { maxSteps := 5000000 }) (discharger := omega)
      [quadCode, sourceQuad, depth, shift, hasConstant, isRight, functionIndex,
       params, constant, CallsConstantParams.left2, CallsConstantParams.left4,
       CallsConstantParams.right0, CallsConstantParams.right1, CallsConstantParams.right2,
       CallsConstantParams.left, CallsConstantParams.right,
       CachedMaskParams.left, CachedMaskParams.right, CavityParams.right,
       SingleCachedMaskInlineParams.rightParams,
       CachedMaskQuadGroup.code, CallsConstantGroup.keepCode, CallsConstantGroup.finishCode,
       CallsConstantCache.keepTemplate, CallsConstantCache.finishTemplate,
       CallsConstantCache.rewrite, CachedMaskHoistInline.template,
       StackRoundData.leftAddress, StackRoundData.rightAddress,
       StackRoundData.leftRotation, StackRoundData.rightRotation,
       StackRoundData.leftConstant, StackRoundData.rightConstant,
       Crypto.Ripemd160.r, Crypto.Ripemd160.rP, Crypto.Ripemd160.s, Crypto.Ripemd160.sP,
       Crypto.Ripemd160.K, Crypto.Ripemd160.KP,
       rewrite, entry, frame, words, CallsConstantCache.insertConstant,
       stateAt, roundEntry, runInstrSeq, Stepper.runInstr, pcAfter,
       hrun, hcap, Instr.size, UInt256.succ, List.exchange,
       List.getElem?_cons_zero, Option.bind_some, Nat.add_assoc,
       State.activeWordsAfterUInt256, activeWordsAfter_of_le, hactive,
       ofNat_toNat, Word.word_toNat_ofNat]


set_option linter.unusedSimpArgs false in
private theorem quad_equiv6 (k : Fin 4)
    (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < 998) (hrun : s.halt = .Running) :
    runInstrSeq (quadCode 6 k) (entry 6 s pc w a b c d e rho) =
      Option.map (fun out => {out with pc := pcAfter pc (quadCode 6 k)})
        (runInstrSeq (sourceQuad 6 k) (entry 6 s pc w a b c d e rho)) := by
  have hcap (m : Nat) (hm : m ≤ 26) : rho.length + m < 1024 := by omega
  fin_cases k <;>
    simp (config := { maxSteps := 5000000 }) (discharger := omega)
      [quadCode, sourceQuad, depth, shift, hasConstant, isRight, functionIndex,
       params, constant, CallsConstantParams.left2, CallsConstantParams.left4,
       CallsConstantParams.right0, CallsConstantParams.right1, CallsConstantParams.right2,
       CallsConstantParams.left, CallsConstantParams.right,
       CachedMaskParams.left, CachedMaskParams.right, CavityParams.right,
       SingleCachedMaskInlineParams.rightParams,
       CachedMaskQuadGroup.code, CallsConstantGroup.keepCode, CallsConstantGroup.finishCode,
       CallsConstantCache.keepTemplate, CallsConstantCache.finishTemplate,
       CallsConstantCache.rewrite, CachedMaskHoistInline.template,
       StackRoundData.leftAddress, StackRoundData.rightAddress,
       StackRoundData.leftRotation, StackRoundData.rightRotation,
       StackRoundData.leftConstant, StackRoundData.rightConstant,
       Crypto.Ripemd160.r, Crypto.Ripemd160.rP, Crypto.Ripemd160.s, Crypto.Ripemd160.sP,
       Crypto.Ripemd160.K, Crypto.Ripemd160.KP,
       rewrite, entry, frame, words, CallsConstantCache.insertConstant,
       stateAt, roundEntry, runInstrSeq, Stepper.runInstr, pcAfter,
       hrun, hcap, Instr.size, UInt256.succ, List.exchange,
       List.getElem?_cons_zero, Option.bind_some, Nat.add_assoc,
       State.activeWordsAfterUInt256, activeWordsAfter_of_le, hactive,
       ofNat_toNat, Word.word_toNat_ofNat]


/-- Each finite group has its own symbolic proof, keeping the four-round
expression expansion local to one group. No arithmetic identity is changed. -/
theorem quad_equiv (g : Fin 7) (k : Fin 4)
    (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < if isRight g then 998 else 1003)
    (hrun : s.halt = .Running) :
    runInstrSeq (quadCode g k) (entry g s pc w a b c d e rho) =
      Option.map (fun out => {out with pc := pcAfter pc (quadCode g k)})
        (runInstrSeq (sourceQuad g k) (entry g s pc w a b c d e rho)) := by
  fin_cases g
  · exact quad_equiv0 k s pc w a b c d e rho hactive hstack hrun
  · exact quad_equiv1 k s pc w a b c d e rho hactive hstack hrun
  · exact quad_equiv2 k s pc w a b c d e rho hactive hstack hrun
  · exact quad_equiv3 k s pc w a b c d e rho hactive hstack hrun
  · exact quad_equiv4 k s pc w a b c d e rho hactive hstack hrun
  · exact quad_equiv5 k s pc w a b c d e rho hactive hstack hrun
  · exact quad_equiv6 k s pc w a b c d e rho hactive hstack hrun

theorem source_run_quad (g : Fin 7) (k : Fin 4)
    (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < if isRight g then 998 else 1003)
    (hrun : s.halt = .Running) :
    runInstrSeq (sourceQuad g k) (entry g s pc w a b c d e rho) =
      some (afterQuad g k s (pcAfter pc (sourceQuad g k))
        ((params g k).apply s w) a b c d e rho) := by
  have hs : (words s ++ rho).length < if isRight g then 1001 else 1006 := by
    simp only [words, List.length_append, List.length_cons, List.length_nil]
    split_ifs at hstack ⊢ <;> omega
  fin_cases g
  · simpa [sourceQuad, entry, afterQuad, frame, params, shift, isRight, hasConstant] using
      CachedMaskQuadGroup.run_left (CachedMaskParams.left 0 k) s pc w (words s ++ rho)
        (CachedMaskParams.left_fits s 0 hactive k) hs hrun
  · by_cases hk : k.val = 3
    · simpa [sourceQuad, entry, afterQuad, frame, params, shift, isRight, hasConstant,
        functionIndex, constant, hk] using
        CallsConstantGroup.run_cached_finish_left 0 (CallsConstantParams.left2 k)
          ((CallsConstantParams.left2 0).constant) s pc w (words s ++ rho)
          (CallsConstantParams.left2_function k) (CallsConstantParams.left2_constant k)
          (CallsConstantParams.left2_fits s hactive k) hs hrun
    · simpa [sourceQuad, entry, afterQuad, frame, params, shift, isRight, hasConstant,
        functionIndex, constant, hk] using
        CallsConstantGroup.run_cached_keep_left 0 (CallsConstantParams.left2 k)
          ((CallsConstantParams.left2 0).constant) s pc w (words s ++ rho)
          (CallsConstantParams.left2_function k) (CallsConstantParams.left2_constant k)
          (CallsConstantParams.left2_fits s hactive k) hs hrun
  · by_cases hk : k.val = 3
    · simpa [sourceQuad, entry, afterQuad, frame, params, shift, isRight, hasConstant,
        functionIndex, constant, hk] using
        CallsConstantGroup.run_cached_finish_left 2 (CallsConstantParams.left4 k)
          ((CallsConstantParams.left4 0).constant) s pc w (words s ++ rho)
          (CallsConstantParams.left4_function k) (CallsConstantParams.left4_constant k)
          (CallsConstantParams.left4_fits s hactive k) hs hrun
    · simpa [sourceQuad, entry, afterQuad, frame, params, shift, isRight, hasConstant,
        functionIndex, constant, hk] using
        CallsConstantGroup.run_cached_keep_left 2 (CallsConstantParams.left4 k)
          ((CallsConstantParams.left4 0).constant) s pc w (words s ++ rho)
          (CallsConstantParams.left4_function k) (CallsConstantParams.left4_constant k)
          (CallsConstantParams.left4_fits s hactive k) hs hrun
  · by_cases hk : k.val = 3
    · simpa [sourceQuad, entry, afterQuad, frame, params, shift, isRight, hasConstant,
        functionIndex, constant, hk] using
        CallsConstantGroup.run_cached_finish_right 2 (CallsConstantParams.right0 k)
          ((CallsConstantParams.right0 0).constant) s pc w a b c d e (words s ++ rho)
          (CallsConstantParams.right0_function k) (CallsConstantParams.right0_constant k)
          (CallsConstantParams.right0_fits s hactive k) hs hrun
    · simpa [sourceQuad, entry, afterQuad, frame, params, shift, isRight, hasConstant,
        functionIndex, constant, hk] using
        CallsConstantGroup.run_cached_keep_right 2 (CallsConstantParams.right0 k)
          ((CallsConstantParams.right0 0).constant) s pc w a b c d e (words s ++ rho)
          (CallsConstantParams.right0_function k) (CallsConstantParams.right0_constant k)
          (CallsConstantParams.right0_fits s hactive k) hs hrun
  · by_cases hk : k.val = 3
    · simpa [sourceQuad, entry, afterQuad, frame, params, shift, isRight, hasConstant,
        functionIndex, constant, hk] using
        CallsConstantGroup.run_cached_finish_right 1 (CallsConstantParams.right1 k)
          ((CallsConstantParams.right1 0).constant) s pc w a b c d e (words s ++ rho)
          (CallsConstantParams.right1_function k) (CallsConstantParams.right1_constant k)
          (CallsConstantParams.right1_fits s hactive k) hs hrun
    · simpa [sourceQuad, entry, afterQuad, frame, params, shift, isRight, hasConstant,
        functionIndex, constant, hk] using
        CallsConstantGroup.run_cached_keep_right 1 (CallsConstantParams.right1 k)
          ((CallsConstantParams.right1 0).constant) s pc w a b c d e (words s ++ rho)
          (CallsConstantParams.right1_function k) (CallsConstantParams.right1_constant k)
          (CallsConstantParams.right1_fits s hactive k) hs hrun
  · by_cases hk : k.val = 3
    · simpa [sourceQuad, entry, afterQuad, frame, params, shift, isRight, hasConstant,
        functionIndex, constant, hk] using
        CallsConstantGroup.run_cached_finish_right 0 (CallsConstantParams.right2 k)
          ((CallsConstantParams.right2 0).constant) s pc w a b c d e (words s ++ rho)
          (CallsConstantParams.right2_function k) (CallsConstantParams.right2_constant k)
          (CallsConstantParams.right2_fits s hactive k) hs hrun
    · simpa [sourceQuad, entry, afterQuad, frame, params, shift, isRight, hasConstant,
        functionIndex, constant, hk] using
        CallsConstantGroup.run_cached_keep_right 0 (CallsConstantParams.right2 k)
          ((CallsConstantParams.right2 0).constant) s pc w a b c d e (words s ++ rho)
          (CallsConstantParams.right2_function k) (CallsConstantParams.right2_constant k)
          (CallsConstantParams.right2_fits s hactive k) hs hrun
  · simpa [sourceQuad, entry, afterQuad, frame, params, shift, isRight, hasConstant] using
      CachedMaskQuadGroup.run_right (CachedMaskParams.right k) s pc w a b c d e (words s ++ rho)
        (CavityResultSemantic.right_fits s hactive k) hs hrun

theorem run_quad (g : Fin 7) (k : Fin 4)
    (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < if isRight g then 998 else 1003)
    (hrun : s.halt = .Running) :
    runInstrSeq (quadCode g k) (entry g s pc w a b c d e rho) =
      some (afterQuad g k s (pcAfter pc (quadCode g k))
        ((params g k).apply s w) a b c d e rho) := by
  rw [quad_equiv g k s pc w a b c d e rho hactive hstack hrun,
    source_run_quad g k s pc w a b c d e rho hactive hstack hrun]
  simp [afterQuad, entry, stateAt, roundEntry, CallsConstantCache.insertConstant]

#print axioms quad_equiv
#print axioms source_run_quad
#print axioms run_quad

end Challenge.Ripemd160.Submission.Proofs.Bytecode.WordCacheTemplates
