import Challenge.Modexp.Submission.Dsl
import YulEvmCompiler.Optimizer.Implementation.MemorySpillStateSound
set_option warningAsError true
set_option maxHeartbeats 1000000

/-!
# Asm-level proof library for the MODEXP submission

Reusable small-step facts about the labeled-assembly machine
(`YulEvmCompiler.AsmSem`), targeting the expression DSL of `Submission/Dsl.lean`:

* **activeWords pinning** — once the program's preamble has touched `TOP`,
  every later memory access lies inside the active window, so `touchMemory`
  is the identity and `mload`/`mstore`/`mstore8` have pure word semantics
  (`touchMemory_noop`, `astep_mstore_pinned`, …);
* **per-op step lemmas** — one `AStep`/`AHalt` fact per op the program uses,
  valid for *every* external model (local ops never consult the model), with
  the memory effects stated exactly (`astep_add`, `astep_mload`,
  `ahalt_ret`, …);
* **expression evaluation** — a denotational semantics `evalExpr` for the DSL
  and `compileExpr_steps`/`compileExpr_steps'`: under the side condition
  `exprOK e yst` (all loads pinned, all op nodes pure), `compileExpr e`
  pushes `evalExpr e yst` onto the stack and leaves the state unchanged;
* **statement fragments** — `store`/`storeAt`/`storeAt8`/`jumpIf*`/`jump`/
  `label`/`pushLabel`/`dynJump`/`ret` executed against an arbitrary
  continuation, with jump-target premises (`findLabel …`, `l ∈ labelDefs …`)
  left as hypotheses for callers to discharge by `decide` on the concrete
  program;
* **a counted-loop combinator** (`loop_counted`) packaging the Nat-induction
  discipline shared by the program's loops, and the procedure-call pattern
  (`call_entry_steps`/`dynJump_steps`);
* **Yul-side memory algebra** — load/store disjointness and roundtrip lemmas
  on `Nat → UInt8` function memories, reusing the compiler's
  spill-soundness layer where it already proved them.

Nothing here is specific to the MODEXP algorithm; the library only makes the
Asm machine tractable for a functional correctness proof built on the DSL.
-/

namespace Challenge.Modexp.Submission

open YulEvmCompiler
open YulSemantics.EVM (U256 Op EvmState stepOp builtinWithExternal touchMemory
  activeWordsAfter loadWord storeWord storeByte readBytes wordFrom byteFrom byteAt b2w
  bin ter un)

/-! ## activeWords pinning -/

/-- Re-wrapping a word's `toNat` is the identity (used by `touchMemory`
bookkeeping). -/
theorem ofNat_toNat (v : U256) : BitVec.ofNat 256 v.toNat = v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt v.isLt]

/-- The high-water mark already covers a full word starting at `p`. -/
theorem activeWordsAfter_word {curr p : Nat}
    (h : (p + 31) / 32 + 1 ≤ curr) : activeWordsAfter curr p 32 = curr := by
  show (if (32 : Nat) = 0 then curr else Nat.max curr ((p + 32 - 1) / 32 + 1)) = curr
  rw [if_neg (by norm_num)]
  exact Nat.max_eq_left (by omega)

/-- Touching an already-active 32-byte word is a no-op: `touchMemory` writes
only the `activeWords` high-water mark. -/
theorem touchMemory_noop {yst : EvmState} {p : Nat}
    (h : (p + 31) / 32 + 1 ≤ yst.activeWords.toNat) : touchMemory yst p 32 = yst := by
  show { yst with activeWords :=
      BitVec.ofNat 256 (activeWordsAfter yst.activeWords.toNat p 32) } = yst
  rw [activeWordsAfter_word h, ofNat_toNat]

/-- General pinning: touching any nonempty range that ends inside the active
window is a no-op. -/
theorem touchMemoryRange_noop {yst : EvmState} {p n : Nat} (hn : 0 < n)
    (h : p + n ≤ 32 * yst.activeWords.toNat) : touchMemory yst p n = yst := by
  show { yst with activeWords :=
      BitVec.ofNat 256 (activeWordsAfter yst.activeWords.toNat p n) } = yst
  have haw : activeWordsAfter yst.activeWords.toNat p n = yst.activeWords.toNat := by
    show (if n = 0 then yst.activeWords.toNat else
        Nat.max yst.activeWords.toNat ((p + n - 1) / 32 + 1)) = yst.activeWords.toNat
    rw [if_neg (by omega)]
    exact Nat.max_eq_left (by omega)
  rw [haw, ofNat_toNat]

/-- Word-touch no-op, in the additive form `p + 32 ≤ 32 · activeWords`
(equivalent to `touchMemory_noop`'s divided form, and the shape that combines
with address-bound arithmetic). -/
theorem touchMemory_word_noop {yst : EvmState} {p : Nat}
    (h : p + 32 ≤ 32 * yst.activeWords.toNat) : touchMemory yst p 32 = yst :=
  touchMemory_noop (by omega)

/-- Byte-touch (`mstore8`) no-op: the byte lies inside the active window. -/
theorem touchMemory_byte_noop {yst : EvmState} {p : Nat}
    (h : p < 32 * yst.activeWords.toNat) : touchMemory yst p 1 = yst :=
  touchMemoryRange_noop (p := p) (by norm_num) (by omega)

/-- A pinned `mstore`'s full machine effect is just the memory write. -/
theorem mstore_word_state {yst : EvmState} {p : Nat} {v : U256}
    (h : p + 32 ≤ 32 * yst.activeWords.toNat) :
    { touchMemory yst p 32 with memory := storeWord yst.memory p v } =
      { yst with memory := storeWord yst.memory p v } := by
  rw [touchMemory_word_noop h]

/-- A pinned `mstore8`'s full machine effect is just the byte write. -/
theorem mstore_byte_state {yst : EvmState} {p : Nat} {v : U256}
    (h : p < 32 * yst.activeWords.toNat) :
    { touchMemory yst p 1 with memory := storeByte yst.memory p v } =
      { yst with memory := storeByte yst.memory p v } := by
  rw [touchMemory_byte_noop h]

/-! ## Per-op step lemmas

Every lemma in this section holds for an arbitrary external model: the ops
involved are *local* (they unfold to a `stepOp` computation), so the
`builtinWithExternal` premise never consults the model's relations. -/

/-- `AStep.op` for a two-argument op with a one-word result and unchanged
state; the premise is the raw relational judgment, which for a concrete pure
op is `rfl`. -/
theorem astep_bin_of [model : ExternalModel] {prog : List Asm} {o : Op}
    {a b r : U256} {k : List Asm} {σ : List AVal} {yst : EvmState}
    (h : builtinWithExternal model.calls model.creates o [a, b] yst (.ok [r] yst)) :
    AStep prog ⟨.op o :: k, words [a, b] ++ σ, yst⟩ ⟨k, .word r :: σ, yst⟩ :=
  AStep.op h

/-- `AStep.op` for a three-argument op with a one-word result and unchanged
state (premise: the raw relational judgment; `rfl` for concrete pure ops). -/
theorem astep_ter_of [model : ExternalModel] {prog : List Asm} {o : Op}
    {a b c r : U256} {k : List Asm} {σ : List AVal} {yst : EvmState}
    (h : builtinWithExternal model.calls model.creates o [a, b, c] yst (.ok [r] yst)) :
    AStep prog ⟨.op o :: k, words [a, b, c] ++ σ, yst⟩ ⟨k, .word r :: σ, yst⟩ :=
  AStep.op h

/-- `AStep.op` for a one-argument op with a one-word result and unchanged
state (premise: the raw relational judgment; `rfl` for concrete pure ops). -/
theorem astep_un_of [model : ExternalModel] {prog : List Asm} {o : Op}
    {a r : U256} {k : List Asm} {σ : List AVal} {yst : EvmState}
    (h : builtinWithExternal model.calls model.creates o [a] yst (.ok [r] yst)) :
    AStep prog ⟨.op o :: k, words [a] ++ σ, yst⟩ ⟨k, .word r :: σ, yst⟩ :=
  AStep.op h

/-- `AStep.op` for a nullary op yielding one word (premise: the raw
relational judgment; `rfl` for concrete pure reads). -/
theorem astep_nullary_of [model : ExternalModel] {prog : List Asm} {o : Op}
    {r : U256} {k : List Asm} {σ : List AVal} {yst : EvmState}
    (h : builtinWithExternal model.calls model.creates o [] yst (.ok [r] yst)) :
    AStep prog ⟨.op o :: k, σ, yst⟩ ⟨k, .word r :: σ, yst⟩ :=
  AStep.op h

/-- The binary ops whose `stepOp` on two arguments is a pure one-word value
function (the domain where `evalBin` mirrors the machine). -/
def binOK : Op → Bool
  | .add | .sub | .mul | .div | .sdiv | .mod | .smod | .exp
  | .lt | .gt | .slt | .sgt | .eq
  | .and | .or | .xor | .byte | .shl | .shr | .sar => true
  | _ => false

/-- The ternary ops with a pure one-word `stepOp` result. -/
def terOK : Op → Bool
  | .addmod | .mulmod => true
  | _ => false

/-- The unary ops with a pure one-word `stepOp` result. -/
def unOK : Op → Bool
  | .iszero | .not => true
  | _ => false

/-- The value of a pure binary op, mirroring `stepOp`'s per-op function
exactly (`evalBin o a b` is `o(a, b)` in Yul argument order). Ops outside
`binOK` evaluate to `0` and cannot occur in a well-formed DSL term. -/
def evalBin : Op → U256 → U256 → U256
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => if b = 0 then 0 else a / b
  | .sdiv, a, b => if b = 0 then 0 else BitVec.sdiv a b
  | .mod, a, b => if b = 0 then 0 else a % b
  | .smod, a, b => if b = 0 then 0 else BitVec.srem a b
  | .exp, a, b => BitVec.ofNat 256 (a.toNat ^ b.toNat)
  | .lt, a, b => b2w (a.ult b)
  | .gt, a, b => b2w (b.ult a)
  | .slt, a, b => b2w (a.slt b)
  | .sgt, a, b => b2w (b.slt a)
  | .eq, a, b => b2w (a = b)
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .byte, i, x => if 32 ≤ i.toNat then 0 else (x >>> (248 - 8 * i.toNat)) &&& 0xff
  | .shl, s, v => v <<< s.toNat
  | .shr, s, v => v >>> s.toNat
  | .sar, s, v => BitVec.sshiftRight v s.toNat
  | _, _, _ => 0

/-- The value of a pure ternary op (Yul argument order: `evalTer o a b c` is
`o(a, b, c)`); ops outside `terOK` evaluate to `0`. -/
def evalTer : Op → U256 → U256 → U256 → U256
  | .addmod, a, b, n => if n = 0 then 0 else BitVec.ofNat 256 ((a.toNat + b.toNat) % n.toNat)
  | .mulmod, a, b, n => if n = 0 then 0 else BitVec.ofNat 256 ((a.toNat * b.toNat) % n.toNat)
  | _, _, _, _ => 0

/-- The value of a pure unary op; ops outside `unOK` evaluate to `0`. -/
def evalUn : Op → U256 → U256
  | .iszero, a => b2w (a = 0)
  | .not, a => ~~~a
  | _, _ => 0

/-- `ADD`: wrapped sum. -/
theorem astep_add [model : ExternalModel] {prog : List Asm} {a b : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .add :: k, words [a, b] ++ σ, yst⟩
      ⟨k, .word (a + b) :: σ, yst⟩ :=
  astep_bin_of rfl

/-- `SUB`: wrapped difference. -/
theorem astep_sub [model : ExternalModel] {prog : List Asm} {a b : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .sub :: k, words [a, b] ++ σ, yst⟩
      ⟨k, .word (a - b) :: σ, yst⟩ :=
  astep_bin_of rfl

/-- `MUL`: wrapped product. -/
theorem astep_mul [model : ExternalModel] {prog : List Asm} {a b : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .mul :: k, words [a, b] ++ σ, yst⟩
      ⟨k, .word (a * b) :: σ, yst⟩ :=
  astep_bin_of rfl

/-- `DIV`: EVM division (0 on zero divisor). -/
theorem astep_div [model : ExternalModel] {prog : List Asm} {a b : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .div :: k, words [a, b] ++ σ, yst⟩
      ⟨k, .word (if b = 0 then 0 else a / b) :: σ, yst⟩ :=
  astep_bin_of rfl

/-- `MOD`: EVM remainder (0 on zero divisor). -/
theorem astep_mod [model : ExternalModel] {prog : List Asm} {a b : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .mod :: k, words [a, b] ++ σ, yst⟩
      ⟨k, .word (if b = 0 then 0 else a % b) :: σ, yst⟩ :=
  astep_bin_of rfl

/-- `LT`: unsigned less-than as a word. -/
theorem astep_lt [model : ExternalModel] {prog : List Asm} {a b : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .lt :: k, words [a, b] ++ σ, yst⟩
      ⟨k, .word (b2w (a.ult b)) :: σ, yst⟩ :=
  astep_bin_of rfl

/-- `GT`: unsigned greater-than as a word. -/
theorem astep_gt [model : ExternalModel] {prog : List Asm} {a b : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .gt :: k, words [a, b] ++ σ, yst⟩
      ⟨k, .word (b2w (b.ult a)) :: σ, yst⟩ :=
  astep_bin_of rfl

/-- `EQ`: equality as a word. -/
theorem astep_eq [model : ExternalModel] {prog : List Asm} {a b : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .eq :: k, words [a, b] ++ σ, yst⟩
      ⟨k, .word (b2w (a = b)) :: σ, yst⟩ :=
  astep_bin_of rfl

/-- `AND`. -/
theorem astep_and [model : ExternalModel] {prog : List Asm} {a b : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .and :: k, words [a, b] ++ σ, yst⟩
      ⟨k, .word (a &&& b) :: σ, yst⟩ :=
  astep_bin_of rfl

/-- `OR`. -/
theorem astep_or [model : ExternalModel] {prog : List Asm} {a b : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .or :: k, words [a, b] ++ σ, yst⟩
      ⟨k, .word (a ||| b) :: σ, yst⟩ :=
  astep_bin_of rfl

/-- `XOR`. -/
theorem astep_xor [model : ExternalModel] {prog : List Asm} {a b : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .xor :: k, words [a, b] ++ σ, yst⟩
      ⟨k, .word (a ^^^ b) :: σ, yst⟩ :=
  astep_bin_of rfl

/-- `SHL`: args `[shift, val]`, result `val <<< shift.toNat`. -/
theorem astep_shl [model : ExternalModel] {prog : List Asm} {s v : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .shl :: k, words [s, v] ++ σ, yst⟩
      ⟨k, .word (v <<< s.toNat) :: σ, yst⟩ :=
  astep_bin_of rfl

/-- `SHR`: args `[shift, val]`, result `val >>> shift.toNat`. -/
theorem astep_shr [model : ExternalModel] {prog : List Asm} {s v : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .shr :: k, words [s, v] ++ σ, yst⟩
      ⟨k, .word (v >>> s.toNat) :: σ, yst⟩ :=
  astep_bin_of rfl

/-- `BYTE`: args `[i, x]`, the `i`-th big-endian byte of `x`. -/
theorem astep_byte [model : ExternalModel] {prog : List Asm} {i x : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .byte :: k, words [i, x] ++ σ, yst⟩
      ⟨k, .word (if 32 ≤ i.toNat then 0 else (x >>> (248 - 8 * i.toNat)) &&& 0xff) :: σ, yst⟩ :=
  astep_bin_of rfl

/-- `NOT`. -/
theorem astep_not [model : ExternalModel] {prog : List Asm} {a : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .not :: k, words [a] ++ σ, yst⟩
      ⟨k, .word (~~~a) :: σ, yst⟩ :=
  astep_un_of rfl

/-- `ISZERO`: 1 exactly on zero. -/
theorem astep_iszero [model : ExternalModel] {prog : List Asm} {a : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .iszero :: k, words [a] ++ σ, yst⟩
      ⟨k, .word (b2w (a = 0)) :: σ, yst⟩ :=
  astep_un_of rfl

/-- `ADDMOD`: args `[a, b, n]`, `(a + b) % n` on naturals (0 on `n = 0`). -/
theorem astep_addmod [model : ExternalModel] {prog : List Asm} {a b n : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .addmod :: k, words [a, b, n] ++ σ, yst⟩
      ⟨k, .word (if n = 0 then 0 else BitVec.ofNat 256 ((a.toNat + b.toNat) % n.toNat)) :: σ, yst⟩ :=
  astep_ter_of rfl

/-- `MULMOD`: args `[a, b, n]`, `(a * b) % n` on naturals (0 on `n = 0`). -/
theorem astep_mulmod [model : ExternalModel] {prog : List Asm} {a b n : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .mulmod :: k, words [a, b, n] ++ σ, yst⟩
      ⟨k, .word (if n = 0 then 0 else BitVec.ofNat 256 ((a.toNat * b.toNat) % n.toNat)) :: σ, yst⟩ :=
  astep_ter_of rfl

/-- `CALLDATALOAD [p]`: the zero-padded big-endian word of the calldata at
`p`; no memory effect. -/
theorem astep_calldataload [model : ExternalModel] {prog : List Asm} {p : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .calldataload :: k, words [p] ++ σ, yst⟩
      ⟨k, .word (wordFrom yst.env.calldata p.toNat) :: σ, yst⟩ :=
  astep_un_of rfl

/-- `CALLDATASIZE`. -/
theorem astep_calldatasize [model : ExternalModel] {prog : List Asm}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .calldatasize :: k, σ, yst⟩
      ⟨k, .word (BitVec.ofNat 256 yst.env.calldata.length) :: σ, yst⟩ :=
  astep_nullary_of rfl

/-- `MLOAD [p]`: the word at `p.toNat`, with the exact `touchMemory`
high-water-mark effect. -/
theorem astep_mload [model : ExternalModel] {prog : List Asm} {p : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .mload :: k, words [p] ++ σ, yst⟩
      ⟨k, .word (loadWord yst.memory p.toNat) :: σ, touchMemory yst p.toNat 32⟩ := by
  have h := AStep.op (model := model) (prog := prog) (yop := .mload)
    (args := [p]) (rets := [loadWord yst.memory p.toNat]) (c := k) (σ := σ)
    (yst := yst) (yst' := touchMemory yst p.toNat 32) rfl
  simpa [words] using h

/-- `MSTORE [p, v]`: writes `v` at `p.toNat`, with the exact effect on
`activeWords` and memory. -/
theorem astep_mstore [model : ExternalModel] {prog : List Asm} {p v : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .mstore :: k, words [p, v] ++ σ, yst⟩
      ⟨k, σ, { touchMemory yst p.toNat 32 with
          memory := storeWord yst.memory p.toNat v }⟩ := by
  have h := AStep.op (model := model) (prog := prog) (yop := .mstore)
    (args := [p, v]) (rets := []) (c := k) (σ := σ) (yst := yst)
    (yst' := { touchMemory yst p.toNat 32 with
      memory := storeWord yst.memory p.toNat v }) rfl
  simpa [words] using h

/-- `MSTORE8 [p, v]`: writes `v`'s low byte at `p.toNat`, with the exact
effect on `activeWords` and memory. -/
theorem astep_mstore8 [model : ExternalModel] {prog : List Asm} {p v : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.op .mstore8 :: k, words [p, v] ++ σ, yst⟩
      ⟨k, σ, { touchMemory yst p.toNat 1 with
          memory := storeByte yst.memory p.toNat v }⟩ := by
  have h := AStep.op (model := model) (prog := prog) (yop := .mstore8)
    (args := [p, v]) (rets := []) (c := k) (σ := σ) (yst := yst)
    (yst' := { touchMemory yst p.toNat 1 with
      memory := storeByte yst.memory p.toNat v }) rfl
  simpa [words] using h

/-- `MLOAD` at an address inside the active window: pure read, state
unchanged. -/
theorem astep_mload_pinned [model : ExternalModel] {prog : List Asm} {p : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState}
    (h : p.toNat + 32 ≤ 32 * yst.activeWords.toNat) :
    AStep prog ⟨.op .mload :: k, words [p] ++ σ, yst⟩
      ⟨k, .word (loadWord yst.memory p.toNat) :: σ, yst⟩ := by
  have hst := astep_mload (model := model) (prog := prog) (p := p) (k := k) (σ := σ)
    (yst := yst)
  rwa [touchMemory_word_noop h] at hst

/-- `MSTORE` at an address inside the active window: the state change is
exactly the word write. -/
theorem astep_mstore_pinned [model : ExternalModel] {prog : List Asm} {p v : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState}
    (h : p.toNat + 32 ≤ 32 * yst.activeWords.toNat) :
    AStep prog ⟨.op .mstore :: k, words [p, v] ++ σ, yst⟩
      ⟨k, σ, { yst with memory := storeWord yst.memory p.toNat v }⟩ := by
  have hst := astep_mstore (model := model) (prog := prog) (p := p) (v := v) (k := k)
    (σ := σ) (yst := yst)
  rwa [mstore_word_state h] at hst

/-- `MSTORE8` at a byte inside the active window: the state change is
exactly the byte write. -/
theorem astep_mstore8_pinned [model : ExternalModel] {prog : List Asm} {p v : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState}
    (h : p.toNat < 32 * yst.activeWords.toNat) :
    AStep prog ⟨.op .mstore8 :: k, words [p, v] ++ σ, yst⟩
      ⟨k, σ, { yst with memory := storeByte yst.memory p.toNat v }⟩ := by
  have hst := astep_mstore8 (model := model) (prog := prog) (p := p) (v := v) (k := k)
    (σ := σ) (yst := yst)
  rwa [mstore_byte_state h] at hst

/-- Any pure binary op (predicate `binOK`) steps by its `evalBin` value. -/
theorem astep_bin [model : ExternalModel] {prog : List Asm} {o : Op} {a b : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} (h : binOK o = true) :
    AStep prog ⟨.op o :: k, words [a, b] ++ σ, yst⟩
      ⟨k, .word (evalBin o a b) :: σ, yst⟩ := by
  refine astep_bin_of (r := evalBin o a b) ?_
  cases o <;> simp_all [binOK, evalBin, stepOp, bin, builtinWithExternal]

/-- Any pure ternary op (predicate `terOK`) steps by its `evalTer` value. -/
theorem astep_ter [model : ExternalModel] {prog : List Asm} {o : Op} {a b c : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} (h : terOK o = true) :
    AStep prog ⟨.op o :: k, words [a, b, c] ++ σ, yst⟩
      ⟨k, .word (evalTer o a b c) :: σ, yst⟩ := by
  refine astep_ter_of (r := evalTer o a b c) ?_
  cases o <;> simp_all [terOK, evalTer, stepOp, ter, builtinWithExternal]

/-- Any pure unary op (predicate `unOK`) steps by its `evalUn` value. -/
theorem astep_un [model : ExternalModel] {prog : List Asm} {o : Op} {a : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} (h : unOK o = true) :
    AStep prog ⟨.op o :: k, words [a] ++ σ, yst⟩
      ⟨k, .word (evalUn o a) :: σ, yst⟩ := by
  refine astep_un_of (r := evalUn o a) ?_
  cases o <;> simp_all [unOK, evalUn, stepOp, un, builtinWithExternal]

/-! ### Control steps (repackaged constructors) -/

/-- Push a word. -/
theorem astep_push [model : ExternalModel] {prog : List Asm} {v : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.push v :: k, σ, yst⟩ ⟨k, .word v :: σ, yst⟩ :=
  AStep.push

/-- Discard the stack top. -/
theorem astep_pop [model : ExternalModel] {prog : List Asm}
    {k : List Asm} {σ : List AVal} {yst : EvmState} {v : AVal} :
    AStep prog ⟨.pop :: k, v :: σ, yst⟩ ⟨k, σ, yst⟩ :=
  AStep.pop

/-- A label definition is a no-op step. -/
theorem astep_label [model : ExternalModel] {prog : List Asm} {l : Label}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AStep prog ⟨.label l :: k, σ, yst⟩ ⟨k, σ, yst⟩ :=
  AStep.label

/-- Unconditional jump, landing right after `.label l`. -/
theorem astep_jump [model : ExternalModel] {prog : List Asm} {l : Label}
    {c' : List Asm} {k : List Asm} {σ : List AVal} {yst : EvmState}
    (hfind : findLabel l prog = some c') :
    AStep prog ⟨.jump l :: k, σ, yst⟩ ⟨c', σ, yst⟩ :=
  AStep.jump hfind

/-- Conditional jump, taken branch (condition word nonzero). -/
theorem astep_jumpi_taken [model : ExternalModel] {prog : List Asm} {l : Label}
    {v : U256} {c' : List Asm} {k : List Asm} {σ : List AVal} {yst : EvmState}
    (hv : v ≠ 0) (hfind : findLabel l prog = some c') :
    AStep prog ⟨.jumpi l :: k, .word v :: σ, yst⟩ ⟨c', σ, yst⟩ :=
  AStep.jumpiTaken hv hfind

/-- Conditional jump, fall-through branch (condition word zero). -/
theorem astep_jumpi_fall [model : ExternalModel] {prog : List Asm} {l : Label}
    {v : U256} {k : List Asm} {σ : List AVal} {yst : EvmState}
    (hv : v = 0) :
    AStep prog ⟨.jumpi l :: k, .word v :: σ, yst⟩ ⟨k, σ, yst⟩ :=
  AStep.jumpiFall hv

/-- Push a defined label's code address. -/
theorem astep_pushLabel [model : ExternalModel] {prog : List Asm} {l : Label}
    {k : List Asm} {σ : List AVal} {yst : EvmState}
    (hmem : l ∈ labelDefs prog) :
    AStep prog ⟨.pushLabel l :: k, σ, yst⟩ ⟨k, .code l :: σ, yst⟩ :=
  AStep.pushLabel hmem

/-- `DUP(n+1)`. -/
theorem astep_dup [model : ExternalModel] {prog : List Asm} {n : Fin 16}
    {v : AVal} {τ ρ : List AVal} {k : List Asm} {yst : EvmState}
    (hlen : τ.length = n.val) :
    AStep prog ⟨.dup n :: k, τ ++ v :: ρ, yst⟩ ⟨k, v :: (τ ++ v :: ρ), yst⟩ :=
  AStep.dup hlen

/-- `SWAP(n+1)`. -/
theorem astep_swap [model : ExternalModel] {prog : List Asm} {n : Fin 16}
    {a b : AVal} {τ ρ : List AVal} {k : List Asm} {yst : EvmState}
    (hlen : τ.length = n.val) :
    AStep prog ⟨.swap n :: k, a :: (τ ++ b :: ρ), yst⟩
      ⟨k, b :: (τ ++ a :: ρ), yst⟩ :=
  AStep.swap hlen

/-- Dynamic jump to a code address on the stack (procedure return). -/
theorem astep_dynJump [model : ExternalModel] {prog : List Asm} {l : Label}
    {c' : List Asm} {k : List Asm} {σ : List AVal} {yst : EvmState}
    (hfind : findLabel l prog = some c') :
    AStep prog ⟨.dynJump :: k, .code l :: σ, yst⟩ ⟨c', σ, yst⟩ :=
  AStep.dynJump hfind

/-- `RET [p, s]` halts, exposing `readBytes` of the return window (the
state's final `touchMemory` is recorded but unobservable). -/
theorem ahalt_ret [model : ExternalModel] {prog : List Asm} {p s : U256}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AHalt prog ⟨.op .ret :: k, words [p, s] ++ σ, yst⟩
      { touchMemory yst p.toNat s.toNat with
          halted := some (.ret, readBytes yst.memory p.toNat s.toNat) } :=
  AHalt.op (model := model) (prog := prog) (yop := .ret) (args := [p, s])
    (c := k) (σ := σ) (yst := yst)
    (yst' := { touchMemory yst p.toNat s.toNat with
      halted := some (.ret, readBytes yst.memory p.toNat s.toNat) }) rfl

/-- `INVALID` halts with no data. -/
theorem ahalt_invalid [model : ExternalModel] {prog : List Asm}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    AHalt prog ⟨.op .invalid :: k, σ, yst⟩ { yst with halted := some (.invalid, []) } :=
  AHalt.op (model := model) (prog := prog) (yop := .invalid) (args := [])
    (c := k) (σ := σ) (yst := yst)
    (yst' := { yst with halted := some (.invalid, []) }) rfl

/-! ## Expression evaluation -/

/-- Denotational semantics of the DSL: the word `compileExpr e` leaves on the
stack when run in `yst`. Constant loads read `yst.memory` at the cell;
computed `mload` reads at the evaluated address; `cdload`/`cdb` read the
calldata; the op nodes use the pure `evalBin`/`evalTer`/`evalUn` functions. -/
def evalExpr : Expr → EvmState → U256
  | .imm k, _ => BitVec.ofNat 256 k
  | .load c, yst => loadWord yst.memory c
  | .mload e, yst => loadWord yst.memory (evalExpr e yst).toNat
  | .cdload e, yst => wordFrom yst.env.calldata (evalExpr e yst).toNat
  | .cdb e, yst => evalBin .byte 0 (wordFrom yst.env.calldata (evalExpr e yst).toNat)
  | .bin o a b, yst => evalBin o (evalExpr a yst) (evalExpr b yst)
  | .ter o a b c, yst => evalTer o (evalExpr a yst) (evalExpr b yst) (evalExpr c yst)
  | .un o a, yst => evalUn o (evalExpr a yst)

/-- Side condition for running an expression unchanged. `exprOK e yst`
holds when:

* every constant cell `c` loaded by `e` satisfies `c < 2 ^ 256` (so the
  pushed address really is `c`) and lies inside the active window;
* every computed `mload` address lies inside the active window;
* every op node is pure (`binOK`/`terOK`/`unOK`) — the DSL never evaluates
  a state-writing op as a value.

Under `exprOK e yst`, running `compileExpr e` leaves the machine state
byte-for-byte unchanged. Calldata reads need no pinning (`calldataload`
never touches memory). -/
def exprOK : Expr → EvmState → Prop
  | .imm _, _ => True
  | .load c, yst => c < 2 ^ 256 ∧ c + 32 ≤ 32 * yst.activeWords.toNat
  | .mload e, yst => (evalExpr e yst).toNat + 32 ≤ 32 * yst.activeWords.toNat ∧ exprOK e yst
  | .cdload e, yst => exprOK e yst
  | .cdb e, yst => exprOK e yst
  | .bin o a b, yst => binOK o = true ∧ exprOK a yst ∧ exprOK b yst
  | .ter o a b c, yst =>
      terOK o = true ∧ exprOK a yst ∧ exprOK b yst ∧ exprOK c yst
  | .un o a, yst => unOK o = true ∧ exprOK a yst

/-- The fundamental expression lemma: under `exprOK e yst`, `compileExpr e`
pushes exactly `evalExpr e yst` and leaves code-continuation `k`, stack `σ`,
and state `yst` otherwise untouched.

Composition discipline: a fragment `compileExpr e ++ rest` running against
continuation `k` is applied via `compileExpr_steps e (rest ++ k) …` after a
single associativity rewrite `((e ++ rest) ++ k) = (e ++ (rest ++ k))` (the
`rw [show … from by simp [compileExpr, List.append_assoc]]` idiom used
throughout the fragment lemmas below). -/
theorem compileExpr_steps [model : ExternalModel] {prog : List Asm} :
    ∀ (e : Expr) (k : List Asm) (σ : List AVal) (yst : EvmState),
      exprOK e yst →
      ASteps prog ⟨compileExpr e ++ k, σ, yst⟩ ⟨k, .word (evalExpr e yst) :: σ, yst⟩ := by
  intro e
  induction e with
  | imm v =>
    intro k σ _yst _
    exact ASteps.single AStep.push
  | load c =>
    intro k σ yst h
    obtain ⟨hlt, hpin⟩ := h
    have hc : (BitVec.ofNat 256 c).toNat = c := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    refine (ASteps.single AStep.push).trans (ASteps.single ?_)
    have h2 := astep_mload (model := model) (prog := prog)
      (p := BitVec.ofNat 256 c) (k := k) (σ := σ) (yst := yst)
    rw [hc, touchMemory_word_noop hpin] at h2
    exact h2
  | mload e ih =>
    intro k σ yst h
    obtain ⟨haddr, he⟩ := h
    rw [show compileExpr (Expr.mload e) ++ k
        = compileExpr e ++ ([.op .mload] ++ k) from by
      simp [compileExpr, List.append_assoc]]
    exact (ih _ σ yst he).trans (ASteps.single (astep_mload_pinned haddr))
  | cdload e ih =>
    intro k σ yst h
    rw [show compileExpr (Expr.cdload e) ++ k
        = compileExpr e ++ ([.op .calldataload] ++ k) from by
      simp [compileExpr, List.append_assoc]]
    exact (ih _ σ yst h).trans (ASteps.single astep_calldataload)
  | cdb e ih =>
    intro k σ yst h
    rw [show compileExpr (Expr.cdb e) ++ k
        = compileExpr e ++ ([.op .calldataload, .push (BitVec.ofNat 256 0), .op .byte] ++ k) from by
      simp [compileExpr, List.append_assoc]]
    exact (ih _ σ yst h).trans
      ((ASteps.single astep_calldataload).trans
        ((ASteps.single AStep.push).trans (ASteps.single astep_byte)))
  | bin o a b iha ihb =>
    intro k σ yst h
    obtain ⟨ho, ha, hb⟩ := h
    rw [show compileExpr (Expr.bin o a b) ++ k
        = compileExpr b ++ ((compileExpr a ++ [.op o]) ++ k) from by
      simp [compileExpr, List.append_assoc]]
    refine (ihb _ σ yst hb).trans ?_
    rw [List.append_assoc]
    exact (iha _ _ yst ha).trans (ASteps.single (astep_bin ho))
  | ter o a b c iha ihb ihc =>
    intro k σ yst h
    obtain ⟨ho, ha, hb, hc⟩ := h
    rw [show compileExpr (Expr.ter o a b c) ++ k
        = compileExpr c ++ ((compileExpr b ++ (compileExpr a ++ [.op o])) ++ k) from by
      simp [compileExpr, List.append_assoc]]
    refine (ihc _ σ yst hc).trans ?_
    rw [show (compileExpr b ++ (compileExpr a ++ [.op o])) ++ k
        = compileExpr b ++ ((compileExpr a ++ [.op o]) ++ k) from by
      simp [List.append_assoc]]
    refine (ihb _ _ yst hb).trans ?_
    rw [List.append_assoc]
    exact (iha _ _ yst ha).trans (ASteps.single (astep_ter ho))
  | un o a ih =>
    intro k σ yst h
    obtain ⟨ho, ha⟩ := h
    rw [show compileExpr (Expr.un o a) ++ k
        = compileExpr a ++ ([.op o] ++ k) from by
      simp [compileExpr, List.append_assoc]]
    exact (ih _ σ yst ha).trans (ASteps.single (astep_un ho))

/-! ## Statement fragments -/

/-- `store c e` in continuation `k`: evaluate `e`, push the cell address,
`MSTORE`. The exact effect — no pinning assumed: `activeWords` grows by
`touchMemory` at `c % 2 ^ 256` and the word is written there. (`e` itself
must still be `exprOK`; the generated program evaluates load-free
expressions before the window is established.) -/
theorem store_steps_exact [model : ExternalModel] {prog : List Asm} {c : Nat} {e : Expr}
    {k : List Asm} {σ : List AVal} {yst : EvmState} (he : exprOK e yst) :
    ASteps prog ⟨store c e ++ k, σ, yst⟩ ⟨k, σ,
      { touchMemory yst (c % 2 ^ 256) 32 with
          memory := storeWord yst.memory (c % 2 ^ 256) (evalExpr e yst) }⟩ := by
  rw [show store c e ++ k
      = compileExpr e ++ ([.push (BitVec.ofNat 256 c), .op .mstore] ++ k) from by
    simp [store, List.append_assoc]]
  refine (compileExpr_steps e _ σ yst he).trans ?_
  refine (ASteps.single AStep.push).trans (ASteps.single ?_)
  have h2 := astep_mstore (model := model) (prog := prog)
    (p := BitVec.ofNat 256 c) (v := evalExpr e yst) (k := k) (σ := σ) (yst := yst)
  rwa [BitVec.toNat_ofNat] at h2

/-- `store c e` with the cell pinned inside the active window (and below
`2 ^ 256`): the state change is exactly the word write. -/
theorem store_steps [model : ExternalModel] {prog : List Asm} {c : Nat} {e : Expr}
    {k : List Asm} {σ : List AVal} {yst : EvmState}
    (he : exprOK e yst) (hc : c < 2 ^ 256 ∧ c + 32 ≤ 32 * yst.activeWords.toNat) :
    ASteps prog ⟨store c e ++ k, σ, yst⟩
      ⟨k, σ, { yst with memory := storeWord yst.memory c (evalExpr e yst) }⟩ := by
  have h := store_steps_exact (c := c) (k := k) (σ := σ) (model := model) (prog := prog) he
  rwa [Nat.mod_eq_of_lt hc.1, touchMemory_word_noop hc.2] at h

/-- `storeAt addrE valE` in continuation `k`: the exact effect — `activeWords`
grows by `touchMemory` at the evaluated address, and the word is written
there. Address and value are both evaluated first (value ends up below the
address on the stack). -/
theorem storeAt_steps_exact [model : ExternalModel] {prog : List Asm}
    {addrE valE : Expr} {k : List Asm} {σ : List AVal} {yst : EvmState}
    (hv : exprOK valE yst) (ha : exprOK addrE yst) :
    ASteps prog ⟨storeAt addrE valE ++ k, σ, yst⟩ ⟨k, σ,
      { touchMemory yst (evalExpr addrE yst).toNat 32 with
          memory := storeWord yst.memory (evalExpr addrE yst).toNat
            (evalExpr valE yst) }⟩ := by
  rw [show storeAt addrE valE ++ k
      = compileExpr valE ++ ((compileExpr addrE ++ [.op .mstore]) ++ k) from by
    simp [storeAt, List.append_assoc]]
  refine (compileExpr_steps valE _ σ yst hv).trans ?_
  rw [List.append_assoc]
  refine (compileExpr_steps addrE _ _ yst ha).trans ?_
  exact ASteps.single astep_mstore

/-- `storeAt` at a pinned address: the state change is exactly the word
write at the evaluated address. -/
theorem storeAt_steps [model : ExternalModel] {prog : List Asm}
    {addrE valE : Expr} {k : List Asm} {σ : List AVal} {yst : EvmState}
    (hv : exprOK valE yst) (ha : exprOK addrE yst)
    (hp : (evalExpr addrE yst).toNat + 32 ≤ 32 * yst.activeWords.toNat) :
    ASteps prog ⟨storeAt addrE valE ++ k, σ, yst⟩
      ⟨k, σ, { yst with
          memory := storeWord yst.memory (evalExpr addrE yst).toNat (evalExpr valE yst) }⟩ := by
  have h := storeAt_steps_exact (k := k) (σ := σ) (model := model) (prog := prog) hv ha
  rwa [touchMemory_word_noop hp] at h

/-- `storeAt8 addrE valE` in continuation `k`: the exact byte-store effect. -/
theorem storeAt8_steps_exact [model : ExternalModel] {prog : List Asm}
    {addrE valE : Expr} {k : List Asm} {σ : List AVal} {yst : EvmState}
    (hv : exprOK valE yst) (ha : exprOK addrE yst) :
    ASteps prog ⟨storeAt8 addrE valE ++ k, σ, yst⟩ ⟨k, σ,
      { touchMemory yst (evalExpr addrE yst).toNat 1 with
          memory := storeByte yst.memory (evalExpr addrE yst).toNat
            (evalExpr valE yst) }⟩ := by
  rw [show storeAt8 addrE valE ++ k
      = compileExpr valE ++ ((compileExpr addrE ++ [.op .mstore8]) ++ k) from by
    simp [storeAt8, List.append_assoc]]
  refine (compileExpr_steps valE _ σ yst hv).trans ?_
  rw [List.append_assoc]
  refine (compileExpr_steps addrE _ _ yst ha).trans ?_
  exact ASteps.single astep_mstore8

/-- `storeAt8` at a pinned byte: the state change is exactly the byte write. -/
theorem storeAt8_steps [model : ExternalModel] {prog : List Asm}
    {addrE valE : Expr} {k : List Asm} {σ : List AVal} {yst : EvmState}
    (hv : exprOK valE yst) (ha : exprOK addrE yst)
    (hp : (evalExpr addrE yst).toNat < 32 * yst.activeWords.toNat) :
    ASteps prog ⟨storeAt8 addrE valE ++ k, σ, yst⟩
      ⟨k, σ, { yst with
          memory := storeByte yst.memory (evalExpr addrE yst).toNat (evalExpr valE yst) }⟩ := by
  have h := storeAt8_steps_exact (k := k) (σ := σ) (model := model) (prog := prog) hv ha
  rwa [touchMemory_byte_noop hp] at h

/-- `b2w b = 0` exactly when `b` is false. -/
theorem b2w_eq_zero {b : Bool} (h : ¬b) : b2w b = 0 := by
  simp [b2w, h]

/-- `b2w b ≠ 0` exactly when `b` holds. -/
theorem b2w_ne_zero {b : Bool} (h : b) : b2w b ≠ 0 := by
  simp [b2w, h]

/-- The `iszero` idiom: `b2w (x = 0) ≠ 0` when `x = 0`. -/
theorem b2w_iszero_ne {x : U256} (h : x = 0) : b2w (x = 0) ≠ 0 := by
  simp [b2w, h]

/-- The `iszero` idiom: `b2w (x = 0) = 0` when `x ≠ 0`. -/
theorem b2w_iszero_eq {x : U256} (h : x ≠ 0) : b2w (x = 0) = 0 := by
  unfold b2w
  split
  · next hx => exact absurd (of_decide_eq_true hx) h
  · rfl

/-- `jumpIfNz e l`, taken branch: `evalExpr e yst ≠ 0` jumps to the label's
suffix, stack and state unchanged. -/
theorem jumpIfNz_taken [model : ExternalModel] {prog : List Asm} {e : Expr} {l : Label}
    {c' : List Asm} {k : List Asm} {σ : List AVal} {yst : EvmState}
    (he : exprOK e yst) (hv : evalExpr e yst ≠ 0)
    (hfind : findLabel l prog = some c') :
    ASteps prog ⟨jumpIfNz e l ++ k, σ, yst⟩ ⟨c', σ, yst⟩ := by
  rw [show jumpIfNz e l ++ k = compileExpr e ++ ([.jumpi l] ++ k) from by
    simp [jumpIfNz, List.append_assoc]]
  exact (compileExpr_steps e _ σ yst he).trans (ASteps.single (astep_jumpi_taken hv hfind))

/-- `jumpIfNz e l`, fall-through branch: `evalExpr e yst = 0` continues at
`k`, stack and state unchanged. -/
theorem jumpIfNz_fall [model : ExternalModel] {prog : List Asm} {e : Expr} {l : Label}
    {k : List Asm} {σ : List AVal} {yst : EvmState}
    (he : exprOK e yst) (hv : evalExpr e yst = 0) :
    ASteps prog ⟨jumpIfNz e l ++ k, σ, yst⟩ ⟨k, σ, yst⟩ := by
  rw [show jumpIfNz e l ++ k = compileExpr e ++ ([.jumpi l] ++ k) from by
    simp [jumpIfNz, List.append_assoc]]
  exact (compileExpr_steps e _ σ yst he).trans (ASteps.single (astep_jumpi_fall hv))

/-- `jumpIfZ e l`, taken branch: `evalExpr e yst = 0` jumps to the label's
suffix, stack and state unchanged. -/
theorem jumpIfZ_taken [model : ExternalModel] {prog : List Asm} {e : Expr} {l : Label}
    {c' : List Asm} {k : List Asm} {σ : List AVal} {yst : EvmState}
    (he : exprOK e yst) (hv : evalExpr e yst = 0)
    (hfind : findLabel l prog = some c') :
    ASteps prog ⟨jumpIfZ e l ++ k, σ, yst⟩ ⟨c', σ, yst⟩ := by
  rw [show jumpIfZ e l ++ k
      = compileExpr e ++ ([.op .iszero, .jumpi l] ++ k) from by
    simp [jumpIfZ, List.append_assoc]]
  exact (compileExpr_steps e _ σ yst he).trans
    ((ASteps.single astep_iszero).trans
      (ASteps.single (astep_jumpi_taken (b2w_iszero_ne hv) hfind)))

/-- `jumpIfZ e l`, fall-through branch: `evalExpr e yst ≠ 0` continues at
`k`, stack and state unchanged. -/
theorem jumpIfZ_fall [model : ExternalModel] {prog : List Asm} {e : Expr} {l : Label}
    {k : List Asm} {σ : List AVal} {yst : EvmState}
    (he : exprOK e yst) (hv : evalExpr e yst ≠ 0) :
    ASteps prog ⟨jumpIfZ e l ++ k, σ, yst⟩ ⟨k, σ, yst⟩ := by
  rw [show jumpIfZ e l ++ k
      = compileExpr e ++ ([.op .iszero, .jumpi l] ++ k) from by
    simp [jumpIfZ, List.append_assoc]]
  exact (compileExpr_steps e _ σ yst he).trans
    ((ASteps.single astep_iszero).trans
      (ASteps.single (astep_jumpi_fall (b2w_iszero_eq hv))))

/-- `jumpUnlessLt e₁ e₂ l`, taken branch (the loop-exit test): when
`¬ (evalExpr e₁ yst).ult (evalExpr e₂ yst)`, jump to the label's suffix. -/
theorem jumpUnlessLt_taken [model : ExternalModel] {prog : List Asm}
    {e₁ e₂ : Expr} {l : Label} {c' : List Asm} {k : List Asm} {σ : List AVal}
    {yst : EvmState} (he₁ : exprOK e₁ yst) (he₂ : exprOK e₂ yst)
    (hlt : ¬ (evalExpr e₁ yst).ult (evalExpr e₂ yst))
    (hfind : findLabel l prog = some c') :
    ASteps prog ⟨jumpUnlessLt e₁ e₂ l ++ k, σ, yst⟩ ⟨c', σ, yst⟩ := by
  rw [show jumpUnlessLt e₁ e₂ l ++ k
      = compileExpr e₂ ++ ((compileExpr e₁ ++ [.op .lt, .op .iszero, .jumpi l]) ++ k) from by
    simp [jumpUnlessLt, List.append_assoc]]
  refine (compileExpr_steps e₂ _ σ yst he₂).trans ?_
  rw [List.append_assoc]
  refine (compileExpr_steps e₁ _ _ yst he₁).trans ?_
  exact (ASteps.single astep_lt).trans
    ((ASteps.single astep_iszero).trans
      (ASteps.single (astep_jumpi_taken (b2w_iszero_ne (b2w_eq_zero hlt)) hfind)))

/-- `jumpUnlessLt e₁ e₂ l`, fall-through branch: when
`(evalExpr e₁ yst).ult (evalExpr e₂ yst)`, continue at `k`. -/
theorem jumpUnlessLt_fall [model : ExternalModel] {prog : List Asm}
    {e₁ e₂ : Expr} {l : Label} {k : List Asm} {σ : List AVal} {yst : EvmState}
    (he₁ : exprOK e₁ yst) (he₂ : exprOK e₂ yst)
    (hlt : (evalExpr e₁ yst).ult (evalExpr e₂ yst)) :
    ASteps prog ⟨jumpUnlessLt e₁ e₂ l ++ k, σ, yst⟩ ⟨k, σ, yst⟩ := by
  rw [show jumpUnlessLt e₁ e₂ l ++ k
      = compileExpr e₂ ++ ((compileExpr e₁ ++ [.op .lt, .op .iszero, .jumpi l]) ++ k) from by
    simp [jumpUnlessLt, List.append_assoc]]
  refine (compileExpr_steps e₂ _ σ yst he₂).trans ?_
  rw [List.append_assoc]
  refine (compileExpr_steps e₁ _ _ yst he₁).trans ?_
  exact (ASteps.single astep_lt).trans
    ((ASteps.single astep_iszero).trans
      (ASteps.single (astep_jumpi_fall (b2w_iszero_eq (b2w_ne_zero hlt)))))

/-- A label definition executes as a no-op. -/
theorem label_steps [model : ExternalModel] {prog : List Asm} {l : Label}
    {k : List Asm} {σ : List AVal} {yst : EvmState} :
    ASteps prog ⟨[.label l] ++ k, σ, yst⟩ ⟨k, σ, yst⟩ :=
  ASteps.single astep_label

/-- An unconditional jump to a defined label. -/
theorem jump_steps [model : ExternalModel] {prog : List Asm} {l : Label}
    {c' : List Asm} {k : List Asm} {σ : List AVal} {yst : EvmState}
    (hfind : findLabel l prog = some c') :
    ASteps prog ⟨[.jump l] ++ k, σ, yst⟩ ⟨c', σ, yst⟩ :=
  ASteps.single (astep_jump hfind)

/-- Push a defined label's code address. -/
theorem pushLabel_steps [model : ExternalModel] {prog : List Asm} {l : Label}
    {k : List Asm} {σ : List AVal} {yst : EvmState}
    (hmem : l ∈ labelDefs prog) :
    ASteps prog ⟨[.pushLabel l] ++ k, σ, yst⟩ ⟨k, .code l :: σ, yst⟩ :=
  ASteps.single (astep_pushLabel hmem)

/-- A procedure's trailing dynamic jump returns to the code after
`.label l` (the caller's continuation). -/
theorem dynJump_steps [model : ExternalModel] {prog : List Asm} {l : Label}
    {k : List Asm} {σ : List AVal} {yst : EvmState}
    (hfind : findLabel l prog = some k) :
    ASteps prog ⟨[.dynJump] ++ k, .code l :: σ, yst⟩ ⟨k, σ, yst⟩ :=
  ASteps.single (astep_dynJump hfind)

/-- The call prefix `pushLabel lret; jump lproc` enters the procedure body
with the return address pushed; the `.label lret` definition (reached on
return) stays in the caller's `k`. -/
theorem call_entry_steps [model : ExternalModel] {prog : List Asm}
    {lret lproc : Label} {procBody : List Asm} {k : List Asm} {σ : List AVal}
    {yst : EvmState}
    (hmem : lret ∈ labelDefs prog)
    (hfind : findLabel lproc prog = some procBody) :
    ASteps prog ⟨[.pushLabel lret, .jump lproc, .label lret] ++ k, σ, yst⟩
      ⟨procBody, .code lret :: σ, yst⟩ :=
  (ASteps.single (astep_pushLabel hmem)).trans (ASteps.single (astep_jump hfind))

/-- Build the `RET` configuration: `compileExpr sizeE ++ compileExpr offE ++
[.op .ret]` pushes the two return arguments, offset on top (the machine
consumes `[offset, size]`). Pair with `ahalt_ret`. -/
theorem ret_args_steps [model : ExternalModel] {prog : List Asm}
    {sizeE offE : Expr} {k : List Asm} {σ : List AVal} {yst : EvmState}
    (hs : exprOK sizeE yst) (ho : exprOK offE yst) :
    ASteps prog ⟨(compileExpr sizeE ++ compileExpr offE ++ [.op .ret]) ++ k, σ, yst⟩
      ⟨.op .ret :: k,
        words [evalExpr offE yst, evalExpr sizeE yst] ++ σ, yst⟩ := by
  rw [show (compileExpr sizeE ++ compileExpr offE ++ [.op .ret]) ++ k
      = compileExpr sizeE ++ ((compileExpr offE ++ [.op .ret]) ++ k) from by
    simp [List.append_assoc]]
  refine (compileExpr_steps sizeE _ σ yst hs).trans ?_
  rw [List.append_assoc]
  exact compileExpr_steps offE _ _ yst ho

/-! ## The counted-loop combinator -/

/-- Generic counted-loop termination. `top` is the code suffix the loop's
top label resolves to; the stack `σ` is a loop invariant (the DSL's
discipline). Each round from a state satisfying `Inv yst n` with `0 < n`
either

* exits (right disjunct): the exit branch runs, landing in `c'` with the
  caller-chosen postcondition `P` already holding at `yst`, or
* iterates (left disjunct): control returns to `top` with `Inv yst' (n-1)`.

From `Inv yst 0` the exit branch runs (`hexit`). Induction on `n` then
reaches the exit in a state satisfying `P`. The back-jump and exit-target
resolutions live inside the caller's round/exit derivations, so this lemma
never mentions labels. -/
theorem loop_counted [model : ExternalModel] {prog : List Asm} {top : List Asm}
    {σ : List AVal} {c' : List Asm} {Inv : EvmState → Nat → Prop}
    {P : EvmState → Prop}
    (hround : ∀ {n : Nat} {yst : EvmState}, 0 < n → Inv yst n →
      (∃ yst', Inv yst' (n - 1) ∧ ASteps prog ⟨top, σ, yst⟩ ⟨top, σ, yst'⟩) ∨
      (P yst ∧ ASteps prog ⟨top, σ, yst⟩ ⟨c', σ, yst⟩))
    (hexit : ∀ yst, Inv yst 0 → P yst ∧ ASteps prog ⟨top, σ, yst⟩ ⟨c', σ, yst⟩) :
    ∀ {n : Nat} {yst : EvmState}, Inv yst n →
      ∃ yst', P yst' ∧ ASteps prog ⟨top, σ, yst⟩ ⟨c', σ, yst'⟩ := by
  intro n
  induction n with
  | zero =>
    intro yst h
    obtain ⟨hP, hsteps⟩ := hexit yst h
    exact ⟨yst, hP, hsteps⟩
  | succ m ih =>
    intro yst h
    rcases hround (by omega) h with ⟨yst', hInv, hroundSteps⟩ | ⟨hP, hexitSteps⟩
    · obtain ⟨yst'', hP', hsteps'⟩ := ih hInv
      exact ⟨yst'', hP', hroundSteps.trans hsteps'⟩
    · exact ⟨yst, hP, hexitSteps⟩

/-! ## Yul-side memory algebra

Load/store facts on the `Nat → UInt8` function memories of
`YulSemantics.EVM.EvmState`, for limb arithmetic: roundtrips, disjointness,
and byte-level views. `loadWord_storeWord` and the disjoint-word version are
imported from the compiler's spill-soundness layer, which proved them for the
same memories. -/

/-- Reading back a stored word yields it. -/
theorem loadWord_storeWord (m : Nat → UInt8) (p : Nat) (v : U256) :
    loadWord (storeWord m p v) p = v :=
  YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord m p v

/-- A word store leaves a disjoint word load unchanged. -/
theorem loadWord_storeWord_disj {m : Nat → UInt8} {p q : Nat} {v : U256}
    (h : p + 32 ≤ q ∨ q + 32 ≤ p) :
    loadWord (storeWord m p v) q = loadWord m q :=
  YulEvmCompiler.Optimizer.MemorySpillStateSound.loadWord_storeWord_other m p q v h

/-- The stored window's bytes are `v`'s big-endian digits. -/
theorem storeWord_apply {m : Nat → UInt8} {p : Nat} {v : U256} {i : Nat}
    (hi : i < 32) : storeWord m p v (p + i) = byteAt v (31 - i) := by
  simp only [storeWord]
  rw [if_pos (by omega : p ≤ p + i ∧ p + i < p + 32)]
  congr 1
  omega

/-- Outside its window, a word store keeps the old byte. -/
theorem storeWord_other {m : Nat → UInt8} {p a : Nat} {v : U256}
    (h : a < p ∨ p + 32 ≤ a) : storeWord m p v a = m a := by
  simp only [storeWord]
  rw [if_neg (by omega)]

/-- Overwriting the same cell keeps only the last word. -/
theorem storeWord_storeWord_self (m : Nat → UInt8) (p : Nat) (v w : U256) :
    storeWord (storeWord m p v) p w = storeWord m p w := by
  funext a
  simp only [storeWord]
  by_cases h : p ≤ a ∧ a < p + 32
  · simp only [if_pos h]
  · simp only [if_neg h]

/-- Word stores on disjoint windows commute. -/
theorem storeWord_storeWord_disj {m : Nat → UInt8} {p q : Nat} {v w : U256}
    (h : p + 32 ≤ q ∨ q + 32 ≤ p) :
    storeWord (storeWord m p v) q w = storeWord (storeWord m q w) p v := by
  funext a
  simp only [storeWord]
  by_cases hq : q ≤ a ∧ a < q + 32
  · have hp : ¬(p ≤ a ∧ a < p + 32) := by omega
    simp only [if_pos hq, if_neg hp]
  · by_cases hp : p ≤ a ∧ a < p + 32
    · simp only [if_neg hq, if_pos hp]
    · simp only [if_neg hq, if_neg hp]

/-- The stored byte. -/
theorem storeByte_apply {m : Nat → UInt8} {p : Nat} {v : U256} :
    storeByte m p v p = byteAt v 0 := by
  simp [storeByte]

/-- Outside its byte, a byte store keeps the old byte. -/
theorem storeByte_other {m : Nat → UInt8} {p a : Nat} {v : U256}
    (h : a ≠ p) : storeByte m p v a = m a := by
  simp only [storeByte]
  rw [if_neg h]

/-- Overwriting the same byte keeps only the last value. -/
theorem storeByte_storeByte_self (m : Nat → UInt8) (p : Nat) (v w : U256) :
    storeByte (storeByte m p v) p w = storeByte m p w := by
  funext a
  simp only [storeByte]
  by_cases h : a = p <;> simp [h]

/-- Byte stores on distinct addresses commute. -/
theorem storeByte_storeByte_disj {m : Nat → UInt8} {p q : Nat} {v w : U256}
    (h : p ≠ q) :
    storeByte (storeByte m p v) q w = storeByte (storeByte m q w) p v := by
  funext a
  simp only [storeByte]
  by_cases h1 : a = p
  · by_cases h2 : a = q
    · exact absurd (h1.symm.trans h2) h
    · subst h1
      rw [if_neg h, if_pos rfl, if_pos rfl]
  · by_cases h2 : a = q
    · subst h2
      rw [if_pos rfl, if_neg (Ne.symm h), if_pos rfl]
    · simp [h1, h2]

/-- A byte store and a disjoint word store commute. -/
theorem storeByte_storeWord_disj {m : Nat → UInt8} {p q : Nat} {v w : U256}
    (h : q + 32 ≤ p ∨ p < q) :
    storeByte (storeWord m q w) p v = storeWord (storeByte m p v) q w := by
  funext a
  simp only [storeByte, storeWord]
  by_cases hb : a = p
  · have hw : ¬(q ≤ a ∧ a < q + 32) := by omega
    subst hb
    rw [if_pos rfl, if_neg hw, if_pos rfl]
  · by_cases hw : q ≤ a ∧ a < q + 32
    · rw [if_neg hb, if_pos hw, if_pos hw]
    · rw [if_neg hb, if_neg hw, if_neg hw, if_neg hb]

/-- `readBytes` over a range disjoint from a word store is unchanged. -/
theorem readBytes_storeWord_disj {m : Nat → UInt8} {p q n : Nat} {v : U256}
    (h : q + n ≤ p ∨ p + 32 ≤ q) :
    readBytes (storeWord m p v) q n = readBytes m q n := by
  unfold readBytes
  apply List.map_congr_left
  intro i hi
  have hin : i < n := List.mem_range.mp hi
  have hw : ¬(p ≤ q + i ∧ q + i < p + 32) := by omega
  simp only [storeWord, if_neg hw]

/-- `readBytes` of the stored window (whole prefix, `n ≤ 32`): the big-endian
digits of `v`. -/
theorem readBytes_storeWord_self {m : Nat → UInt8} {p n : Nat} {v : U256}
    (hn : n ≤ 32) :
    readBytes (storeWord m p v) p n = (List.range n).map (fun i => byteAt v (31 - i)) := by
  unfold readBytes
  apply List.map_congr_left
  intro i hi
  have hi' : i < n := List.mem_range.mp hi
  simp only [storeWord]
  rw [if_pos (by omega : p ≤ p + i ∧ p + i < p + 32)]
  congr 1
  omega

/-- `readBytes` over a range disjoint from a byte store is unchanged. -/
theorem readBytes_storeByte_disj {m : Nat → UInt8} {p q n : Nat} {v : U256}
    (h : p < q ∨ q + n ≤ p) :
    readBytes (storeByte m p v) q n = readBytes m q n := by
  unfold readBytes
  apply List.map_congr_left
  intro i hi
  have hin : i < n := List.mem_range.mp hi
  by_cases hp : q + i = p
  · exfalso; omega
  · simp only [storeByte]
    rw [if_neg hp]

/-- `readBytes` of a stored byte. -/
theorem readBytes_storeByte_self {m : Nat → UInt8} {p : Nat} {v : U256} :
    readBytes (storeByte m p v) p 1 = [byteAt v 0] := by
  simp [readBytes, storeByte_apply]

private theorem readBytes_succ (m : Nat → UInt8) (p n : Nat) :
    readBytes m p (n + 1) = readBytes m p n ++ [m (p + n)] := by
  unfold readBytes
  rw [List.range_succ, List.map_append]
  rfl

/-- `readBytes` splits at an inner boundary (used to decompose a return
window). -/
theorem readBytes_append (m : Nat → UInt8) (p n₁ n₂ : Nat) :
    readBytes m p (n₁ + n₂) = readBytes m p n₁ ++ readBytes m (p + n₁) n₂ := by
  induction n₂ with
  | zero => simp [readBytes]
  | succ k ih =>
    rw [show n₁ + (k + 1) = n₁ + k + 1 from rfl, readBytes_succ, ih,
      readBytes_succ, show p + (n₁ + k) = p + n₁ + k from by omega]
    rw [List.append_assoc]

/-- A `byteFrom` index inside the slice reads the corresponding memory
byte (the bridge from calldata-style reads to memory words). -/
theorem byteFrom_readBytes {m : Nat → UInt8} {p i : Nat} (hi : i < 32) :
    byteFrom (readBytes m p 32) i = m (p + i) := by
  simp only [byteFrom, readBytes]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  have hlen : i < (List.range 32).length := by simp; omega
  rw [List.getElem?_eq_getElem hlen, List.getElem_range hlen]
  simp

/-- The word view of a memory slice: `loadWord` is `wordFrom` of the read
bytes (connecting memory words with calldata-style word reads). -/
private theorem foldl_congr' {β α : Type} {f g : β → α → β} :
    ∀ (init : β) (l : List α), (∀ a, a ∈ l → ∀ b, f b a = g b a) →
    List.foldl f init l = List.foldl g init l := by
  intro init l
  induction l generalizing init with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    rw [List.foldl_cons, List.foldl_cons,
      ih (f init x) (fun a ha => h a (by simp [ha])), h x (by simp)]

theorem loadWord_eq_wordFrom_readBytes (m : Nat → UInt8) (p : Nat) :
    loadWord m p = wordFrom (readBytes m p 32) 0 := by
  unfold loadWord wordFrom
  refine foldl_congr' 0 (List.range 32) ?_
  intro a ha b
  have ha' : a < 32 := List.mem_range.mp ha
  have hi : 0 + a < 32 := by omega
  rw [byteFrom_readBytes hi, Nat.zero_add]

/-- `loadWord` depends only on the memory through its window. -/
theorem loadWord_congr {m m' : Nat → UInt8} {p : Nat}
    (h : ∀ i, p ≤ i → i < p + 32 → m i = m' i) :
    loadWord m p = loadWord m' p := by
  rw [loadWord_eq_wordFrom_readBytes, loadWord_eq_wordFrom_readBytes]
  congr 1
  unfold readBytes
  apply List.map_congr_left
  intro i hi
  have hi' : i < 32 := List.mem_range.mp hi
  exact h (p + i) (by omega) (by omega)

/-- A byte store outside a word's window leaves the load unchanged. -/
theorem loadWord_storeByte_disj {m : Nat → UInt8} {p q : Nat} {v : U256}
    (h : q + 32 ≤ p ∨ p < q) :
    loadWord (storeByte m p v) q = loadWord m q := by
  apply loadWord_congr
  intro i _ _
  exact storeByte_other (by omega)

end Challenge.Modexp.Submission
