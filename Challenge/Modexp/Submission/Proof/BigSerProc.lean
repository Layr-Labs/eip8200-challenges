import Challenge.Modexp.Submission.Proof.BigLoadProc
import Mathlib.Tactic

set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

/-!
# The MODEXP big path: serialize and return

The `lbSerLoop` loop of `secBigPath`: given the ACC region holding `a` with
`a < 256 ^ msize` (as `RepresentsY` limbs) and the scalar cells set as by the
header/preamble (`MS = W msize`, `activeWords = 250`), the loop writes the
big-endian `msize`-byte encoding of `a` into RET byte-by-byte — byte `i` of
RET is byte `(msize-1-i) % 32` of ACC limb `(msize-1-i) / 32` — and then
`lbReturn` halts with `.ret` exposing exactly `Precompile.natToBytes a
msize`.

Entry contract: control at `.label lbSer` (the caller supplies it via
`findLbSer`; the m = 0 dispatch lands here with ACC still zero, which
`RepresentsY`s `a = 0`).

Exit contract (`big_ser_ret`): from
`⟨bpSer programLabels ++ progTail, [], yst⟩` with
`RepresentsY yst.memory ACC (limbCount msize) a`, `a < 256 ^ msize`,
`loadWord yst.memory MS = W msize`, `yst.activeWords.toNat = 250`, the run
halts with `halted = some (.ret, (Precompile.natToBytes a msize).toList)`.
-/

namespace Challenge.Modexp.Submission.Proof.BigSer

open YulEvmCompiler
open YulSemantics.EVM (U256 EvmState byteFrom byteAt loadWord storeWord
  storeByte readBytes activeWordsAfter touchMemory)
open Challenge.Modexp.Submission (Expr store storeAt8 jumpUnlessLt cdbCell
  compileExpr loadAt evalExpr exprOK
  BS ES MS BO EO MO Ncell Icell Jcell Wcell T0 T1 T2 RET TOP ACC
  programAsm localModel)
open Challenge.Modexp.Submission.Proof.Header
open Challenge.Modexp.Submission.Proof.BigLoad
open Challenge.Modexp.Submission.Proof.YulMem
open Challenge.Modexp.Submission.Proof.YulLimbs
open Challenge.Modexp.Submission.Proofs.Limbs (radix limbCount limbDigits
  length_limbDigits limbDigits_lt value_limbDigits radix_pos pow_radix
  limbCount_le_32 limbCount_pos)
open Challenge.Modexp (ValidInput modulusSize)
open EvmSemantics.EVM.Precompile (natToBytes)

/-- Shorthand for the 256-bit word carrying the natural `n`. -/
local notation:max "W " n:max => BitVec.ofNat 256 n

/-! ## Fixed-width big-endian encodings -/

/-- `bytesNat` (the `readBytes` fold) of the fixed-width big-endian encoding
of any `a < 256 ^ w` is `a`. -/
private theorem bytesNat_be (a w : Nat) (hlt : a < 256 ^ w) :
    Challenge.EvmProof.Bytes.bytesNat ((List.range w).map
      (fun i => UInt8.ofNat (a / 256 ^ (w - 1 - i) % 256))) = a := by
  induction w generalizing a with
  | zero =>
      have h0 : (List.range 0).map
          (fun i => UInt8.ofNat (a / 256 ^ (0 - 1 - i) % 256)) = [] := rfl
      rw [h0]
      show (0 : Nat) = a
      have : 256 ^ 0 = 1 := by norm_num
      omega
  | succ w ih =>
      have hlt256 : a < 256 * 256 ^ w := by
        calc a < 256 ^ (w + 1) := hlt
          _ = 256 * 256 ^ w := by rw [Nat.pow_succ]; ring
      have hdiv : a / 256 < 256 ^ w := Nat.div_lt_of_lt_mul hlt256
      have hmap : (List.range w).map (fun i => UInt8.ofNat (a / 256 ^ (w + 1 - 1 - i) % 256))
          = (List.range w).map (fun i => UInt8.ofNat (a / 256 / 256 ^ (w - 1 - i) % 256)) := by
        apply List.map_congr_left
        intro i hi
        have hiw : i < w := List.mem_range.mp hi
        have hd : a / 256 ^ (w + 1 - 1 - i) = a / 256 / 256 ^ (w - 1 - i) := by
          rw [Nat.div_div_eq_div_mul,
            show 256 * 256 ^ (w - 1 - i) = 256 ^ ((w - 1 - i) + 1) from by
              rw [Nat.pow_succ]; ring,
            show (w - 1 - i) + 1 = w + 1 - 1 - i from by omega]
        rw [hd]
      have hrest := ih (a / 256) hdiv
      rw [List.range_succ, List.map_append,
        Challenge.EvmProof.Bytes.bytesNat_append, hmap, hrest]
      show a / 256 * 256 + Challenge.EvmProof.Bytes.bytesNat
          [UInt8.ofNat (a / 256 ^ (w + 1 - 1 - w) % 256)] = a
      rw [show w + 1 - 1 - w = 0 from by omega, Nat.pow_zero,
        Nat.div_one, Challenge.EvmProof.Bytes.bytesNat_cons,
        List.length_nil, Nat.pow_zero]
      have h0 : Challenge.EvmProof.Bytes.bytesNat ([] : List UInt8) = 0 := rfl
      have h1 : (UInt8.ofNat (a % 256)).toNat = a % 256 :=
        Nat.mod_eq_of_lt (Nat.mod_lt a (by norm_num : (0 : Nat) < 256))
      rw [h0, h1, Nat.add_zero]
      have hsplit : 256 * (a / 256) + a % 256 = a := Nat.div_add_mod a 256
      omega

/-- The fixed-width big-endian encoding is unique among byte lists. -/
private theorem bytesNat_inj : ∀ (l₁ l₂ : List UInt8), l₁.length = l₂.length →
    Challenge.EvmProof.Bytes.bytesNat l₁ = Challenge.EvmProof.Bytes.bytesNat l₂ →
    l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ hlen hval
      cases l₂ with
      | nil => rfl
      | cons b bs => simp at hlen
  | cons a as ih =>
      intro l₂ hlen hval
      cases l₂ with
      | nil => simp at hlen
      | cons b bs =>
          have hlen' : as.length = bs.length := by simpa using hlen
          rw [Challenge.EvmProof.Bytes.bytesNat_cons,
            Challenge.EvmProof.Bytes.bytesNat_cons] at hval
          have hltA : Challenge.EvmProof.Bytes.bytesNat as < 256 ^ as.length :=
            Challenge.EvmProof.Bytes.bytesNat_lt_pow _
          have hltB : Challenge.EvmProof.Bytes.bytesNat bs < 256 ^ as.length := by
            have := Challenge.EvmProof.Bytes.bytesNat_lt_pow bs
            rw [show bs.length = as.length from hlen'.symm] at this
            exact this
          have hpos : (0 : Nat) < 256 ^ as.length := Nat.pow_pos (by norm_num)
          rw [show 256 ^ bs.length = 256 ^ as.length from by rw [hlen']] at hval
          have ha : a.toNat < 256 := a.toNat_lt
          have hb : b.toNat < 256 := b.toNat_lt
          rcases Nat.lt_trichotomy a.toNat b.toNat with hlt | heq | hgt
          · have hstep : b.toNat * 256 ^ as.length
              ≥ a.toNat * 256 ^ as.length + 256 ^ as.length := by
              have hle : a.toNat + 1 ≤ b.toNat := by omega
              calc b.toNat * 256 ^ as.length ≥ (a.toNat + 1) * 256 ^ as.length :=
                  Nat.mul_le_mul_right _ hle
                _ = a.toNat * 256 ^ as.length + 256 ^ as.length := by ring
            omega
          · have hbb : a = b := UInt8.toNat_inj.mp heq
            rw [heq] at hval
            have hrest : Challenge.EvmProof.Bytes.bytesNat as
                = Challenge.EvmProof.Bytes.bytesNat bs := by omega
            rw [hbb, ih bs hlen' hrest]
          · have hstep : a.toNat * 256 ^ as.length
              ≥ b.toNat * 256 ^ as.length + 256 ^ as.length := by
              have hle : b.toNat + 1 ≤ a.toNat := by omega
              calc a.toNat * 256 ^ as.length ≥ (b.toNat + 1) * 256 ^ as.length :=
                  Nat.mul_le_mul_right _ hle
                _ = b.toNat * 256 ^ as.length + 256 ^ as.length := by ring
            omega

/-- `natToBytes a w` as a list is the fixed-width big-endian encoding of
`a`: its fold is `a` and its length is `w`. -/
private theorem natToBytes_toList_bytesNat (a w : Nat) (hlt : a < 256 ^ w) :
    Challenge.EvmProof.Bytes.bytesNat (natToBytes a w).toList = a ∧
      (natToBytes a w).toList.length = w := by
  have hrt : EvmSemantics.Data.Bytes.bytesToBigEndianNat (EvmSemantics.Data.Bytes.natToBytesPadded a w) = a :=
    Challenge.EvmProof.Memory.bytesToBigEndianNat_natToBytesPadded a w hlt
  have h1 : Challenge.EvmProof.Bytes.bytesNat (EvmSemantics.Data.Bytes.natToBytesPadded a w).toList = a := by
    rw [Challenge.EvmProof.Bytes.bytesNat_toList]
    exact hrt
  constructor
  · show Challenge.EvmProof.Bytes.bytesNat
        (EvmSemantics.Data.Bytes.natToBytesPadded a w).toList = a
    exact h1
  · show (EvmSemantics.Data.Bytes.natToBytesPadded a w).toList.length = w
    rw [Challenge.EvmProof.Bytecode.toList_eq_data, Array.length_toList]
    unfold EvmSemantics.Data.Bytes.natToBytesPadded
    simp

/-- The list produced by the loop equals `natToBytes`'s list, by encoding
uniqueness. -/
private theorem loop_out_eq (a w : Nat) (hlt : a < 256 ^ w) :
    (List.range w).map (fun i => UInt8.ofNat (a / 256 ^ (w - 1 - i) % 256))
      = (natToBytes a w).toList := by
  apply bytesNat_inj
  · simp [natToBytes_toList_bytesNat a w hlt]
  · rw [bytesNat_be a w hlt]
    exact ((natToBytes_toList_bytesNat a w hlt).1).symm

/-! ## The serialize loop -/

/-- A pinned `storeAt8` at a byte below 8000 with `activeWords = 250`. -/
private theorem storeAt8_pin {addrE valE : Expr} {p v : U256} {yst : EvmState}
    {k : List Asm} (haw : yst.activeWords.toNat = 250)
    (hv : exprOK valE yst) (ha : exprOK addrE yst)
    (haddr : (evalExpr addrE yst).toNat = p.toNat) (hval : evalExpr valE yst = v)
    (hpin : p.toNat < 8000) :
    ASteps programAsm ⟨storeAt8 addrE valE ++ k, [], yst⟩
      ⟨k, [], { yst with memory := storeByte yst.memory p.toNat v }⟩ := by
  have h := storeAt8_steps_exact (model := localModel) (prog := programAsm)
    (addrE := addrE) (valE := valE) (k := k) (σ := []) hv ha
  rw [haddr, hval, mstore_byte_state (by rw [haw]; omega)] at h
  exact h
/-! ## Byte extraction from limbs -/

/-- Byte `k` of a number and of its truncation to `32` bytes agree. -/
private theorem byte_mod2 (q k : Nat) (hk : k < 32) :
    (q % 256 ^ 32) / 256 ^ k % 256 = q / 256 ^ k % 256 := by
  have hp : (0 : Nat) < 256 ^ k := Nat.pow_pos (by norm_num)
  have hdvd1 : 256 ^ (k + 1) ∣ 256 ^ 32 := Nat.pow_dvd_pow 256 (by omega)
  have hdvd2 : 256 ^ k ∣ 256 ^ 32 := Nat.pow_dvd_pow 256 (by omega)
  have e1 : q % 256 ^ 32 % 256 ^ (k + 1) = q % 256 ^ (k + 1) :=
    Nat.mod_mod_of_dvd _ hdvd1
  have e2 : q % 256 ^ 32 % 256 ^ k = q % 256 ^ k :=
    Nat.mod_mod_of_dvd _ hdvd2
  have p1 : q % 256 ^ (k + 1)
      = q % 256 ^ k + 256 ^ k * (q / 256 ^ k % 256) := Nat.mod_pow_succ
  have p2 : q % 256 ^ 32 % 256 ^ (k + 1)
      = q % 256 ^ 32 % 256 ^ k + 256 ^ k * (q % 256 ^ 32 / 256 ^ k % 256) :=
    Nat.mod_pow_succ
  rw [e1, e2] at p2
  have hprod : 256 ^ k * (q % 256 ^ 32 / 256 ^ k % 256)
      = 256 ^ k * (q / 256 ^ k % 256) := by omega
  rw [Nat.mul_comm (256 ^ k) (q % 256 ^ 32 / 256 ^ k % 256),
    Nat.mul_comm (256 ^ k) (q / 256 ^ k % 256)] at hprod
  exact Nat.mul_right_cancel hp hprod

/-- Byte `t = 32 * L + k` of a value equals byte `k` of limb `L`. -/
private theorem byte_of_limb {a t L k : Nat} (ht : t = 32 * L + k) (hk : k < 32) :
    (a / radix ^ L % radix) / 256 ^ k % 256 = a / 256 ^ t % 256 := by
  have hrad : (radix : Nat) ^ L = 256 ^ (32 * L) := pow_radix L
  have hdivt : a / 256 ^ t = (a / 256 ^ (32 * L)) / 256 ^ k := by
    rw [ht, Nat.pow_add]
    exact (Nat.div_div_eq_div_mul a (256 ^ (32 * L)) (256 ^ k)).symm
  rw [hrad, hdivt]
  exact byte_mod2 (a / 256 ^ (32 * L)) k hk

/-- The byte stored by one serialize round, as the output-list byte. -/
private theorem ser_byte {digit t : Nat} (hd : digit < 2 ^ 256)
    (hb : digit / 256 ^ (t % 32) % 256 = a / 256 ^ t % 256) :
    (byteAt (W digit >>> (8 * (t % 32))) 0).toNat = a / 256 ^ t % 256 := by
  have hp : (2 : Nat) ^ (8 * (t % 32)) = 256 ^ (t % 32) := by
    rw [Nat.pow_mul]
  have h1 : W digit >>> (8 * (t % 32)) = W (digit / 2 ^ (8 * (t % 32))) :=
    W_shr hd (8 * (t % 32))
  have hlt : digit / 2 ^ (8 * (t % 32)) < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hd
  have hz : (W digit >>> (8 * (t % 32))) >>> 0 = W digit >>> (8 * (t % 32)) := by simp
  show (UInt8.ofNat ((W digit >>> (8 * (t % 32))) >>> (8 * 0)).toNat).toNat = _
  rw [show (8 * 0) = 0 from by norm_num, hz, h1, toNat_W hlt, hp]
  have he : (UInt8.ofNat (digit / 256 ^ (t % 32))).toNat
      = digit / 256 ^ (t % 32) % 256 := by simp
  rw [he, hb]

/-- Byte equality via values. -/
private theorem u8_eq_of_toNat {x y : UInt8} (h : x.toNat = y.toNat) : x = y := by
  simp only [UInt8.toNat] at h
  cases x with | ofBitVec xb =>
  cases y with | ofBitVec yb =>
  simp only [UInt8.ofBitVec.injEq]
  exact BitVec.eq_of_toNat_eq h

/-! ## The serialize loop -/

/-- The loop body from `.label lbSerLoop` on, minus the label. -/
def serBody (l : ProgLabels) : List Asm :=
  jumpUnlessLt (.load Icell) (.load MS) l.lbReturn ++
  (store T0 (.bin .sub (.bin .sub (.load MS) (.imm 1)) (.load Icell)) ++
  (storeAt8 (.bin .add (.imm RET) (.load Icell))
    (.bin .shr (.bin .mul (.imm 8) (.bin .mod (.load T0) (.imm 32)))
      (loadAt (.bin .add (.imm ACC)
        (.bin .mul (.imm 32) (.bin .div (.load T0) (.imm 32)))))) ++
  (store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump l.lbSerLoop])))

/-- The return code from `.label lbReturn` on. -/
def serTail (l : ProgLabels) : List Asm :=
  [.label l.lbReturn] ++ (compileExpr (.load MS) ++
    (compileExpr (.imm RET) ++ [.op .ret]))

/-- `bpSer` splits into the `Icell` preamble, the loop body, and the tail. -/
theorem bpSer_eq (l : ProgLabels) :
    bpSer l = store Icell (.imm 0) ++
      ([.label l.lbSerLoop] ++ (serBody l ++ serTail l)) := by
  simp only [bpSer, serBody, serTail, List.append_assoc]

/-- The loop-top label resolves to the body plus the tail. -/
theorem findLbSerLoop : findLabel programLabels.lbSerLoop programAsm =
    some (serBody programLabels ++ (serTail programLabels ++ progTail)) :=
  resolve_big
    (pre := [.label programLabels.lbig] ++ bpEntry programLabels ++
      [.label programLabels.lbLoad] ++ bpLoad programLabels ++
      [.label programLabels.lbLoadDone] ++ bpScanInit programLabels ++
      [.label programLabels.lbMScan] ++ bpMScan programLabels ++
      bpMScanDone programLabels ++ [Asm.label programLabels.lbSer] ++
      store Icell (.imm 0))
    (by decide) (by decide) (by decide)
    (show secBigPath programLabels =
        [.label programLabels.lbig] ++ bpEntry programLabels ++
        [.label programLabels.lbLoad] ++ bpLoad programLabels ++
        [.label programLabels.lbLoadDone] ++ bpScanInit programLabels ++
        [.label programLabels.lbMScan] ++ bpMScan programLabels ++
        bpMScanDone programLabels ++ [Asm.label programLabels.lbSer] ++
        store Icell (.imm 0) ++ [Asm.label programLabels.lbSerLoop] ++
        (serBody programLabels ++ serTail programLabels) from by
      rw [secBigPath_splitSer, secTailSer, bpSer_eq, serTail]
      simp only [List.append_assoc])

/-- The return label resolves to the pushing sequence. -/
theorem findLbReturn : findLabel programLabels.lbReturn programAsm =
    some (compileExpr (.load MS) ++
      (compileExpr (.imm RET) ++ ([.op .ret] ++ progTail))) :=
  resolve_big
    (pre := [.label programLabels.lbig] ++ bpEntry programLabels ++
      [.label programLabels.lbLoad] ++ bpLoad programLabels ++
      [.label programLabels.lbLoadDone] ++ bpScanInit programLabels ++
      [.label programLabels.lbMScan] ++ bpMScan programLabels ++
      bpMScanDone programLabels ++ [Asm.label programLabels.lbSer] ++
      store Icell (.imm 0) ++ [Asm.label programLabels.lbSerLoop] ++
      serBody programLabels)
    (by decide) (by decide) (by decide)
    (show secBigPath programLabels =
        [.label programLabels.lbig] ++ bpEntry programLabels ++
        [.label programLabels.lbLoad] ++ bpLoad programLabels ++
        [.label programLabels.lbLoadDone] ++ bpScanInit programLabels ++
        [.label programLabels.lbMScan] ++ bpMScan programLabels ++
        bpMScanDone programLabels ++ [Asm.label programLabels.lbSer] ++
        store Icell (.imm 0) ++ [Asm.label programLabels.lbSerLoop] ++
        serBody programLabels ++ [Asm.label programLabels.lbReturn] ++
        (compileExpr (.load MS) ++
          (compileExpr (.imm RET) ++ [.op .ret])) from by
      rw [secBigPath_splitSer, secTailSer, bpSer_eq, serTail]
      simp only [List.append_assoc])

/-- A single byte stored outside a region leaves it unchanged. -/
theorem yLimbs_storeByte_disjoint {mem : Nat → UInt8} {base n q : Nat} {v : U256}
    (h : base + 32 * n ≤ q) :
    yLimbs (storeByte mem q v) base n = yLimbs mem base n := by
  rw [yLimbs_congr]
  intro a ha1 ha2
  exact storeByte_other (by omega)

/-- The serialize state at output index `i`: `i` bytes of the result are
already at `RET`, `Icell = i`, `MS` and the limb region untouched. -/
structure BSer (yst : EvmState) (cd : ByteArray) (a i : Nat) : Prop where
  aw : yst.activeWords.toNat = 250
  icell : loadWord yst.memory Icell = W i
  mscell : loadWord yst.memory MS = W (modulusSize cd)
  rep : RepresentsY yst.memory ACC (nlimbs cd) a
  out : ∀ j, j < i →
    yst.memory (RET + j) = UInt8.ofNat (a / 256 ^ (modulusSize cd - 1 - j) % 256)

def bs1st (yst : EvmState) (t : Nat) : EvmState :=
  { yst with memory := storeWord yst.memory T0 (W t) }

def bs2st (yst : EvmState) (t i : Nat) (vb : U256) : EvmState :=
  { bs1st yst t with
      memory := storeByte (bs1st yst t).memory (W (RET + i)).toNat vb }

def bs3st (yst : EvmState) (t i : Nat) (vb : U256) : EvmState :=
  { bs2st yst t i vb with
      memory := storeWord (bs2st yst t i vb).memory Icell (W (i + 1)) }

/-- The serialize round's expressions, as named defs. -/
def serT0E : Expr :=
  .bin .sub (.bin .sub (.load MS) (.imm 1)) (.load Icell)

def serRetE : Expr :=
  .bin .add (.imm RET) (.load Icell)

def serValE : Expr :=
  .bin .shr (.bin .mul (.imm 8) (.bin .mod (.load T0) (.imm 32)))
    (loadAt (.bin .add (.imm ACC)
      (.bin .mul (.imm 32) (.bin .div (.load T0) (.imm 32)))))

def serIncE : Expr :=
  .bin .add (.load Icell) (.imm 1)

/-- One serialize round: store output byte `i`, bump `Icell`, jump back. -/
theorem ser_round {cd : ByteArray} {a : Nat} {yst : EvmState} (hv : ValidInput cd)
    {i : Nat} (hi : i < modulusSize cd) (hinv : BSer yst cd a i) :
    ∃ yst', BSer yst' cd a (i + 1) ∧
      ASteps programAsm ⟨serBody programLabels ++
          (serTail programLabels ++ progTail), [], yst⟩
        ⟨serBody programLabels ++ (serTail programLabels ++ progTail),
          [], yst'⟩ := by
  obtain ⟨hBS, hES, hMS, hBO, hEO, hMO, hNc, hIc, hJc, hT0p, hT1p, hWc, hI2c⟩ := cells_num
  have hRETv : RET = 6144 := rfl
  have hACCv : ACC = 2048 := rfl
  have haw : yst.activeWords.toNat = 250 := hinv.aw
  have hms1024 : modulusSize cd ≤ 1024 := by obtain ⟨-, -, hm⟩ := hv; omega
  have hmsw : modulusSize cd < 2 ^ 256 := size_lt _ hms1024
  have hitw : modulusSize cd - 1 - i < 2 ^ 256 := by omega
  -- T0 value
  have hvT0 : evalExpr serT0E yst = W (modulusSize cd - 1 - i) := by
    show (loadWord yst.memory MS - W 1) - loadWord yst.memory Icell = _
    rw [hinv.mscell, hinv.icell, W_sub (by omega) hmsw,
      W_sub (by omega) (by omega)]
  have hltb : (evalExpr (.load Icell) yst).ult (evalExpr (.load MS) yst) := by
    show (loadWord yst.memory Icell).ult (loadWord yst.memory MS) = true
    rw [hinv.icell, hinv.mscell]
    exact W_ult (by omega) hmsw (by omega)
  have hfall := jumpUnlessLt_fall (model := localModel) (prog := programAsm)
    (l := programLabels.lbReturn)
    (e₁ := .load Icell) (e₂ := .load MS)
    (k := store T0 serT0E ++ (storeAt8 serRetE serValE ++
      (store Icell serIncE ++ ([.jump programLabels.lbSerLoop] ++
        (serTail programLabels ++ progTail)))))
    (σ := ([] : List AVal))
    (pin250 haw (by omega)) (pin250 haw (by omega)) hltb
  have he1 : exprOK serT0E yst := by
    show binOK .sub = true ∧
      exprOK (.bin .sub (.load MS) (.imm 1)) yst ∧
      exprOK (.load Icell) yst
    exact ⟨by trivial, ⟨by trivial, pin250 haw (by omega), by trivial⟩,
      pin250 haw (by omega)⟩
  have hs1 := store_pin (c := T0) (e := serT0E)
    (k := storeAt8 serRetE serValE ++
      (store Icell serIncE ++ ([.jump programLabels.lbSerLoop] ++
        (serTail programLabels ++ progTail))))
    (v := W (modulusSize cd - 1 - i)) (yst := yst)
    he1
    (by decide) (by rw [haw]; show T0 + 32 ≤ 32 * 250; omega) hvT0
  have haw1 : (bs1st yst (modulusSize cd - 1 - i)).activeWords.toNat = 250 := haw
  have hT01 : loadWord (bs1st yst (modulusSize cd - 1 - i)).memory T0
      = W (modulusSize cd - 1 - i) := loadWord_storeWord_self _ _ _
  have hIc1 : loadWord (bs1st yst (modulusSize cd - 1 - i)).memory Icell = W i := by
    rw [show (bs1st yst (modulusSize cd - 1 - i)).memory =
        storeWord yst.memory T0 (W (modulusSize cd - 1 - i)) from rfl]
    exact (load_disj' yst.memory T0 Icell (W (modulusSize cd - 1 - i))
      (Or.inr (by omega))).trans hinv.icell
  -- the digit
  have hn32 : nlimbs cd ≤ 32 := limbCount_le_32 _ hms1024
  have hLn : (modulusSize cd - 1 - i) / 32 < nlimbs cd := by
    show (modulusSize cd - 1 - i) / 32 < (modulusSize cd + 31) / 32
    omega
  have h1 : (yLimbs yst.memory ACC (nlimbs cd))[(modulusSize cd - 1 - i) / 32]!
      = (limbDigits (nlimbs cd) a)[(modulusSize cd - 1 - i) / 32]! := by
    rw [hinv.rep.2]
  have h2 := limbDigit (n := nlimbs cd) (v := a)
    (L := (modulusSize cd - 1 - i) / 32) hLn hinv.rep.1
  have hdigit : (loadWord yst.memory
        (ACC + 32 * ((modulusSize cd - 1 - i) / 32))).toNat
      = a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix :=
    (yLimb_get hLn).symm.trans (h1.trans h2)
  have hdlt : a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix < 2 ^ 256 := by
    have h := Nat.mod_lt (a / radix ^ ((modulusSize cd - 1 - i) / 32)) radix_pos
    exact h
  have hlimbW : loadWord (bs1st yst (modulusSize cd - 1 - i)).memory
      (ACC + 32 * ((modulusSize cd - 1 - i) / 32))
      = W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix) := by
    apply BitVec.eq_of_toNat_eq
    show (loadWord (storeWord yst.memory T0 (W (modulusSize cd - 1 - i)))
        (ACC + 32 * ((modulusSize cd - 1 - i) / 32))).toNat = _
    rw [load_disj' yst.memory T0
        (ACC + 32 * ((modulusSize cd - 1 - i) / 32)) (W (modulusSize cd - 1 - i))
        (Or.inr (by rw [hACCv]; omega)), hdigit]
    exact (toNat_W hdlt).symm
  -- the storeAt8 value
  have hshift : evalExpr (.bin .mul (.imm 8) (.bin .mod (.load T0) (.imm 32)))
      (bs1st yst (modulusSize cd - 1 - i))
      = W (8 * ((modulusSize cd - 1 - i) % 32)) := by
    show W 8 * (loadWord (bs1st yst (modulusSize cd - 1 - i)).memory T0 % W 32) = _
    rw [hT01, W_mod hitw (by norm_num)]
    exact W_mul 8 _
  have haddr2 : evalExpr (.bin .add (.imm ACC)
      (.bin .mul (.imm 32) (.bin .div (.load T0) (.imm 32))))
      (bs1st yst (modulusSize cd - 1 - i))
      = W (ACC + 32 * ((modulusSize cd - 1 - i) / 32)) := by
    show W ACC + W 32 * (loadWord (bs1st yst (modulusSize cd - 1 - i)).memory T0 / W 32) = _
    rw [hT01, W_div hitw (by norm_num)]
    rw [W_mul 32 _, W_add (by rw [hACCv]; omega)]
  have hval : evalExpr serValE (bs1st yst (modulusSize cd - 1 - i))
      = W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
        >>> (8 * ((modulusSize cd - 1 - i) % 32)) := by
    show (loadWord (bs1st yst (modulusSize cd - 1 - i)).memory
        (evalExpr (.bin .add (.imm ACC)
          (.bin .mul (.imm 32) (.bin .div (.load T0) (.imm 32))))
          (bs1st yst (modulusSize cd - 1 - i))).toNat)
      >>> (evalExpr (.bin .mul (.imm 8) (.bin .mod (.load T0) (.imm 32)))
        (bs1st yst (modulusSize cd - 1 - i))).toNat = _
    rw [hshift, toNat_W (by omega), haddr2, toNat_W (by rw [hACCv]; omega), hlimbW]
  have haddr : (evalExpr serRetE (bs1st yst (modulusSize cd - 1 - i))).toNat
      = (W (RET + i)).toNat := by
    show (W RET + loadWord (bs1st yst (modulusSize cd - 1 - i)).memory Icell).toNat = _
    rw [hIc1, W_add (by omega)]
  have he2a : exprOK serValE (bs1st yst (modulusSize cd - 1 - i)) := by
    show binOK .shr = true ∧
      exprOK (.bin .mul (.imm 8) (.bin .mod (.load T0) (.imm 32)))
        (bs1st yst (modulusSize cd - 1 - i)) ∧
      exprOK (loadAt (.bin .add (.imm ACC)
        (.bin .mul (.imm 32) (.bin .div (.load T0) (.imm 32)))))
        (bs1st yst (modulusSize cd - 1 - i))
    refine ⟨by trivial, ⟨?_, ?_⟩⟩
    · show binOK .mul = true ∧
        exprOK (.imm 8) (bs1st yst (modulusSize cd - 1 - i)) ∧
        exprOK (.bin .mod (.load T0) (.imm 32)) (bs1st yst (modulusSize cd - 1 - i))
      exact ⟨by trivial, ⟨by trivial, ⟨by trivial,
        pin250 haw1 (by omega), by trivial⟩⟩⟩
    · show (evalExpr (.bin .add (.imm ACC)
          (.bin .mul (.imm 32) (.bin .div (.load T0) (.imm 32))))
          (bs1st yst (modulusSize cd - 1 - i))).toNat + 32
          ≤ 32 * (bs1st yst (modulusSize cd - 1 - i)).activeWords.toNat ∧
        exprOK (.bin .add (.imm ACC)
          (.bin .mul (.imm 32) (.bin .div (.load T0) (.imm 32))))
          (bs1st yst (modulusSize cd - 1 - i))
      rw [haw1, haddr2, toNat_W (by rw [hACCv]; omega)]
      refine ⟨by omega, ?_⟩
      show binOK .add = true ∧
        exprOK (.imm ACC) (bs1st yst (modulusSize cd - 1 - i)) ∧
        exprOK (.bin .mul (.imm 32) (.bin .div (.load T0) (.imm 32)))
          (bs1st yst (modulusSize cd - 1 - i))
      exact ⟨by trivial, ⟨by trivial, ⟨by trivial, by trivial,
        ⟨by trivial, pin250 haw1 (by omega), by trivial⟩⟩⟩⟩
  have he2b : exprOK serRetE (bs1st yst (modulusSize cd - 1 - i)) := by
    show binOK .add = true ∧
      exprOK (.imm RET) (bs1st yst (modulusSize cd - 1 - i)) ∧
      exprOK (.load Icell) (bs1st yst (modulusSize cd - 1 - i))
    exact ⟨by trivial, by trivial, pin250 haw1 (by omega)⟩
  have hpin2 : (W (RET + i)).toNat < 8000 := by
    show (W (RET + i)).toNat < 8000
    rw [toNat_W (by omega)]
    omega
  have hs2 := storeAt8_pin (addrE := serRetE) (valE := serValE)
    (p := W (RET + i))
    (v := W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
      >>> (8 * ((modulusSize cd - 1 - i) % 32)))
    (k := store Icell serIncE ++ ([.jump programLabels.lbSerLoop] ++
        (serTail programLabels ++ progTail)))
    (yst := bs1st yst (modulusSize cd - 1 - i))
    haw1 he2a he2b haddr hval hpin2
  have haw2 : (bs2st yst (modulusSize cd - 1 - i) i
      (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
        >>> (8 * ((modulusSize cd - 1 - i) % 32)))).activeWords.toNat = 250 := haw
  have hIc2 : loadWord (bs2st yst (modulusSize cd - 1 - i) i
      (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
        >>> (8 * ((modulusSize cd - 1 - i) % 32)))).memory Icell = W i := by
    show loadWord (storeByte (bs1st yst (modulusSize cd - 1 - i)).memory
      (W (RET + i)).toNat
      (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
        >>> (8 * ((modulusSize cd - 1 - i) % 32)))) Icell = _
    rw [loadWord_storeByte_disjoint (Or.inr (by
      show (W (RET + i)).toNat < Icell
      rw [toNat_W (by omega)]
      omega))]
    exact hIc1
  -- the Icell bump
  have hvalI : evalExpr serIncE (bs2st yst (modulusSize cd - 1 - i) i
      (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
        >>> (8 * ((modulusSize cd - 1 - i) % 32)))) = W (i + 1) := by
    show loadWord (bs2st yst (modulusSize cd - 1 - i) i
      (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
        >>> (8 * ((modulusSize cd - 1 - i) % 32)))).memory Icell + W 1 = _
    rw [hIc2, W_add (by omega)]
  have he3 : exprOK serIncE (bs2st yst (modulusSize cd - 1 - i) i
      (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
        >>> (8 * ((modulusSize cd - 1 - i) % 32)))) := by
    show binOK .add = true ∧
      exprOK (.load Icell) (bs2st yst (modulusSize cd - 1 - i) i
        (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
          >>> (8 * ((modulusSize cd - 1 - i) % 32)))) ∧
      exprOK (.imm 1) (bs2st yst (modulusSize cd - 1 - i) i
        (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
          >>> (8 * ((modulusSize cd - 1 - i) % 32))))
    exact ⟨by trivial, pin250 haw2 (by omega), by trivial⟩
  have hs3 := store_pin (c := Icell) (e := serIncE)
    (k := [.jump programLabels.lbSerLoop] ++
      (serTail programLabels ++ progTail))
    (v := W (i + 1)) (yst := bs2st yst (modulusSize cd - 1 - i) i
      (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
        >>> (8 * ((modulusSize cd - 1 - i) % 32))))
    he3
    (by decide) (by rw [haw2]; show Icell + 32 ≤ 32 * 250; omega) hvalI
  -- the back-jump
  have hjmp : ASteps programAsm ⟨[.jump programLabels.lbSerLoop] ++
      (serTail programLabels ++ progTail), ([] : List AVal),
      bs3st yst (modulusSize cd - 1 - i) i
      (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
        >>> (8 * ((modulusSize cd - 1 - i) % 32)))⟩
      ⟨serBody programLabels ++ (serTail programLabels ++ progTail), [],
        bs3st yst (modulusSize cd - 1 - i) i
        (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
          >>> (8 * ((modulusSize cd - 1 - i) % 32)))⟩ :=
    jump_steps (model := localModel) (σ := ([] : List AVal)) findLbSerLoop
  refine ⟨bs3st yst (modulusSize cd - 1 - i) i
    (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
      >>> (8 * ((modulusSize cd - 1 - i) % 32))), ?_, ?_⟩
  · refine ⟨haw2, loadWord_storeWord_self _ _ _, ?_, ?_, ?_⟩
    · show loadWord (bs3st yst (modulusSize cd - 1 - i) i
          (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
            >>> (8 * ((modulusSize cd - 1 - i) % 32)))).memory MS = _
      rw [show (bs3st yst (modulusSize cd - 1 - i) i
          (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
            >>> (8 * ((modulusSize cd - 1 - i) % 32)))).memory =
          storeWord (bs2st yst (modulusSize cd - 1 - i) i
            (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
              >>> (8 * ((modulusSize cd - 1 - i) % 32)))).memory Icell (W (i + 1)) from rfl]
      rw [load_disj' _ Icell MS (W (i + 1)) (Or.inr (by omega))]
      show loadWord (bs2st yst (modulusSize cd - 1 - i) i
        (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
          >>> (8 * ((modulusSize cd - 1 - i) % 32)))).memory MS = _
      show loadWord (storeByte (bs1st yst (modulusSize cd - 1 - i)).memory
        (W (RET + i)).toNat
        (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
          >>> (8 * ((modulusSize cd - 1 - i) % 32)))) MS = _
      rw [loadWord_storeByte_disjoint (Or.inr (by
        show (W (RET + i)).toNat < MS
        rw [toNat_W (by omega)]
        omega))]
      exact (load_disj' yst.memory T0 MS
        (W (modulusSize cd - 1 - i)) (Or.inr (by omega))).trans hinv.mscell
    · show RepresentsY (bs3st yst (modulusSize cd - 1 - i) i
          (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
            >>> (8 * ((modulusSize cd - 1 - i) % 32)))).memory ACC (nlimbs cd) a
      rw [show (bs3st yst (modulusSize cd - 1 - i) i
          (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
            >>> (8 * ((modulusSize cd - 1 - i) % 32)))).memory =
          storeWord (bs2st yst (modulusSize cd - 1 - i) i
            (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
              >>> (8 * ((modulusSize cd - 1 - i) % 32)))).memory Icell (W (i + 1)) from rfl]
      refine RepresentsY_storeWord_disjoint ?_ (by rw [hACCv]; omega)
      show RepresentsY (storeByte (bs1st yst (modulusSize cd - 1 - i)).memory
        (W (RET + i)).toNat
        (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
          >>> (8 * ((modulusSize cd - 1 - i) % 32)))) ACC (nlimbs cd) a
      refine ⟨hinv.rep.1, ?_⟩
      show yLimbs (storeByte (bs1st yst (modulusSize cd - 1 - i)).memory
        (W (RET + i)).toNat
        (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
          >>> (8 * ((modulusSize cd - 1 - i) % 32)))) ACC (nlimbs cd)
        = limbDigits (nlimbs cd) a
      rw [yLimbs_storeByte_disjoint (by
        show ACC + 32 * nlimbs cd ≤ (W (RET + i)).toNat
        rw [toNat_W (by omega)]
        omega),
        show yLimbs (bs1st yst (modulusSize cd - 1 - i)).memory ACC (nlimbs cd)
          = yLimbs yst.memory ACC (nlimbs cd) from by
          rw [show (bs1st yst (modulusSize cd - 1 - i)).memory =
            storeWord yst.memory T0 (W (modulusSize cd - 1 - i)) from rfl]
          exact yLimbs_storeWord_disjoint (Or.inr (by rw [hACCv]; omega)),
        hinv.rep.2]
    · intro j hj
      by_cases hje : j = i
      · rw [hje]
        rw [show RET + i = (W (RET + i)).toNat from (toNat_W (by omega)).symm]
        show (bs3st yst (modulusSize cd - 1 - i) i
          (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
            >>> (8 * ((modulusSize cd - 1 - i) % 32)))).memory (W (RET + i)).toNat = _
        rw [show (bs3st yst (modulusSize cd - 1 - i) i
            (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
              >>> (8 * ((modulusSize cd - 1 - i) % 32)))).memory =
            storeWord (bs2st yst (modulusSize cd - 1 - i) i
              (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
                >>> (8 * ((modulusSize cd - 1 - i) % 32)))).memory Icell (W (i + 1)) from rfl,
          storeWord_out _ _ _ _ (by
            show ¬(Icell ≤ (W (RET + i)).toNat ∧ (W (RET + i)).toNat < Icell + 32)
            rw [toNat_W (by omega)]
            omega),
          show (bs2st yst (modulusSize cd - 1 - i) i
            (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
              >>> (8 * ((modulusSize cd - 1 - i) % 32)))).memory =
            storeByte (bs1st yst (modulusSize cd - 1 - i)).memory (W (RET + i)).toNat
              (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
                >>> (8 * ((modulusSize cd - 1 - i) % 32))) from rfl,
          storeByte_apply]
        refine u8_eq_of_toNat ?_
        show (byteAt (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
            >>> (8 * ((modulusSize cd - 1 - i) % 32))) 0).toNat =
          (UInt8.ofNat (a / 256 ^ (modulusSize cd - 1 - i) % 256)).toNat
        rw [ser_byte hdlt (byte_of_limb (by omega) (by omega))]
        simp
      · have hbyte := hinv.out j (by omega)
        show (bs3st yst (modulusSize cd - 1 - i) i
          (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
            >>> (8 * ((modulusSize cd - 1 - i) % 32)))).memory (RET + j) = _
        rw [show (bs3st yst (modulusSize cd - 1 - i) i
            (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
              >>> (8 * ((modulusSize cd - 1 - i) % 32)))).memory =
            storeWord (bs2st yst (modulusSize cd - 1 - i) i
              (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
                >>> (8 * ((modulusSize cd - 1 - i) % 32)))).memory Icell (W (i + 1)) from rfl,
          storeWord_out _ _ _ _ (by omega : ¬(Icell ≤ RET + j ∧ RET + j < Icell + 32)),
          show (bs2st yst (modulusSize cd - 1 - i) i
            (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
              >>> (8 * ((modulusSize cd - 1 - i) % 32)))).memory =
            storeByte (bs1st yst (modulusSize cd - 1 - i)).memory (W (RET + i)).toNat
              (W (a / radix ^ ((modulusSize cd - 1 - i) / 32) % radix)
                >>> (8 * ((modulusSize cd - 1 - i) % 32))) from rfl,
          storeByte_other (by
            show RET + j ≠ (W (RET + i)).toNat
            rw [toNat_W (by omega)]
            omega),
          show (bs1st yst (modulusSize cd - 1 - i)).memory (RET + j) = _
            from storeWord_out _ _ _ _
              (by omega : ¬(T0 ≤ RET + j ∧ RET + j < T0 + 32))]
        exact hbyte
  · rw [show serBody programLabels ++ (serTail programLabels ++ progTail) =
      jumpUnlessLt (.load Icell) (.load MS) programLabels.lbReturn ++
        (store T0 serT0E ++ (storeAt8 serRetE serValE ++
          (store Icell serIncE ++ ([.jump programLabels.lbSerLoop] ++
            (serTail programLabels ++ progTail))))) from by
        rw [serBody]; simp only [List.append_assoc]; rfl]
    exact ((hfall.trans hs1).trans hs2).trans (hs3.trans hjmp)

/-- The serialize loop: from `Icell = i`, the remaining rounds leave all
`msize` result bytes at `RET` and land at the return-pushing code. -/
theorem big_ser_loop {cd : ByteArray} {a : Nat} {yst : EvmState} (hv : ValidInput cd)
    (hmspos : 0 < modulusSize cd) (hle : i ≤ modulusSize cd)
    (hinv : BSer yst cd a i) :
    ∃ yst', BSer yst' cd a (modulusSize cd) ∧
      ASteps programAsm ⟨serBody programLabels ++
          (serTail programLabels ++ progTail), [], yst⟩
        ⟨compileExpr (.load MS) ++ (compileExpr (.imm RET) ++
            ([.op .ret] ++ progTail)), [], yst'⟩ := by
  have hMSv : MS = 7232 := rfl
  have hIcv : Icell = 7392 := rfl
  have hms1024 : modulusSize cd ≤ 1024 := by obtain ⟨-, -, hm⟩ := hv; omega
  have hmsw : modulusSize cd < 2 ^ 256 := size_lt _ hms1024
  refine loop_counted (model := localModel)
    (prog := programAsm)
    (top := serBody programLabels ++ (serTail programLabels ++ progTail))
    (σ := ([] : List AVal))
    (c' := compileExpr (.load MS) ++ (compileExpr (.imm RET) ++
      ([.op .ret] ++ progTail)))
    (Inv := fun yst r => r ≤ modulusSize cd - i ∧ BSer yst cd a (modulusSize cd - r))
    (P := fun yst => BSer yst cd a (modulusSize cd))
    ?_ ?_ (n := modulusSize cd - i)
    (by refine ⟨le_refl _, ?_⟩; rw [Nat.sub_sub_self hle]; exact hinv)
  · intro r yst hr ⟨hrle, hinv⟩
    obtain ⟨yst2, hinv2, hst⟩ := ser_round hv (by omega) hinv
    refine Or.inl ⟨yst2, ⟨by omega, ?_⟩, hst⟩
    rw [show modulusSize cd - (r - 1) = modulusSize cd - r + 1 from by omega]
    exact hinv2
  · intro yst ⟨hr0, hinv⟩
    simp only [Nat.sub_zero] at hinv
    have hexit : ¬ (loadWord yst.memory Icell).ult (loadWord yst.memory MS) := by
      rw [hinv.icell, hinv.mscell]
      exact W_nult hmsw hmsw (le_refl _)
    refine ⟨hinv, ?_⟩
    rw [show serBody programLabels ++ (serTail programLabels ++ progTail) =
        jumpUnlessLt (.load Icell) (.load MS) programLabels.lbReturn ++
          (store T0 serT0E ++ (storeAt8 serRetE serValE ++ (store Icell serIncE ++
            ([.jump programLabels.lbSerLoop] ++
              (serTail programLabels ++ progTail))))) from by
        rw [serBody]; simp only [List.append_assoc]; rfl]
    exact jumpUnlessLt_taken (model := localModel) (prog := programAsm)
      (e₁ := .load Icell) (e₂ := .load MS)
      (pin250 hinv.aw (by omega)) (pin250 hinv.aw (by omega)) hexit findLbReturn

/-- The serializer's top theorem: from the entry contract, the program halts
returning exactly the `msize` big-endian bytes of `a`. -/
theorem big_ser_ret (cd : ByteArray) (hv : ValidInput cd)
    (hmspos : 0 < modulusSize cd) {a : Nat} {yst : EvmState}
    (hrep : RepresentsY yst.memory ACC (nlimbs cd) a)
    (halt : a < 256 ^ modulusSize cd)
    (hms : loadWord yst.memory MS = W (modulusSize cd))
    (haw : yst.activeWords.toNat = 250) :
    ∃ (b : AConf) (yst' : EvmState),
      ASteps programAsm ⟨bpSer programLabels ++ progTail, [], yst⟩ b ∧
      AHalt programAsm b yst' ∧
      yst'.halted = some (.ret, (natToBytes a (modulusSize cd)).toList) := by
  obtain ⟨hBS, hES, hMS, hBO, hEO, hMO, hNc, hIc, hJc, hT0p, hT1p, hWc, hI2c⟩ := cells_num
  have hRETv : RET = 6144 := rfl
  have hACCv : ACC = 2048 := rfl
  have hn32 : nlimbs cd ≤ 32 := limbCount_le_32 _ (by obtain ⟨-, -, hm⟩ := hv; omega)
  have hms1024 : modulusSize cd ≤ 1024 := by obtain ⟨-, -, hm⟩ := hv; omega
  -- the preamble store and label
  have hs0 := store_pin (c := Icell) (e := .imm 0)
    (k := [.label programLabels.lbSerLoop] ++
      (serBody programLabels ++ (serTail programLabels ++ progTail)))
    (v := W 0) (yst := yst) (by trivial) (by decide)
    (by rw [haw]; show Icell + 32 ≤ 32 * 250; omega) (by rfl)
  have hlab : ASteps programAsm ⟨[.label programLabels.lbSerLoop] ++
      (serBody programLabels ++ (serTail programLabels ++ progTail)),
      ([] : List AVal), { yst with memory := storeWord yst.memory Icell (W 0) }⟩
      ⟨serBody programLabels ++ (serTail programLabels ++ progTail), [],
        { yst with memory := storeWord yst.memory Icell (W 0) }⟩ :=
    label_steps (model := localModel)
  have hinv0 : BSer ({ yst with memory := storeWord yst.memory Icell (W 0) } :
      EvmState) cd a 0 := by
    refine ⟨haw, loadWord_storeWord_self _ _ _, ?_, ?_, ?_⟩
    · show loadWord (storeWord yst.memory Icell (W 0)) MS = _
      exact (load_disj' yst.memory Icell MS (W 0) (Or.inr (by omega))).trans hms
    · exact RepresentsY_storeWord_disjoint hrep (by omega)
    · intro j hj
      exact absurd hj (by omega)
  obtain ⟨ystF, hinvF, hloop⟩ := big_ser_loop (i := 0) hv hmspos (by omega) hinv0
  -- the pushes and the ret
  have hret0 : ASteps programAsm ⟨compileExpr (.load MS) ++ (compileExpr (.imm RET) ++
      ([.op .ret] ++ progTail)), ([] : List AVal), ystF⟩
      ⟨.op .ret :: progTail,
        words [W RET, W (modulusSize cd)] ++ ([] : List AVal), ystF⟩ := by
    rw [show compileExpr (.load MS) ++ (compileExpr (.imm RET) ++
        ([.op .ret] ++ progTail)) =
        (compileExpr (.load MS) ++ compileExpr (.imm RET) ++ [.op .ret]) ++
          progTail from by
        simp only [List.append_assoc]]
    have hr := ret_args_steps (model := localModel) (prog := programAsm)
      (sizeE := .load MS) (offE := .imm RET)
      (k := progTail) (σ := ([] : List AVal))
      (pin250 hinvF.aw (by omega)) (by trivial)
    rw [show evalExpr (.load MS) ystF = loadWord ystF.memory MS from rfl,
      hinvF.mscell] at hr
    exact hr
  have hret0' : ASteps programAsm ⟨compileExpr (.load MS) ++ (compileExpr (.imm RET) ++
      ([.op .ret] ++ progTail)), ([] : List AVal), ystF⟩
      ⟨.op .ret :: progTail,
        words [W RET, W (modulusSize cd)], ystF⟩ := hret0
  -- the halt
  have hhalt : AHalt programAsm ⟨.op .ret :: progTail,
      words [W RET, W (modulusSize cd)], ystF⟩
      { touchMemory ystF (W RET).toNat (W (modulusSize cd)).toNat with
          halted := some (.ret,
            readBytes ystF.memory (W RET).toNat (W (modulusSize cd)).toNat) } :=
    ahalt_ret (model := localModel) (prog := programAsm)
      (p := W RET) (s := W (modulusSize cd))
      (k := progTail) (σ := ([] : List AVal)) (yst := ystF)
  -- the return window equals natToBytes
  have hread : readBytes ystF.memory (W RET).toNat (W (modulusSize cd)).toNat
      = (natToBytes a (modulusSize cd)).toList := by
    rw [show (W RET).toNat = RET from toNat_W (by omega),
      show (W (modulusSize cd)).toNat = modulusSize cd from toNat_W (by omega)]
    show (List.range (modulusSize cd)).map (fun i => ystF.memory (RET + i)) = _
    rw [List.map_congr_left ?_]
    · exact loop_out_eq a (modulusSize cd) halt
    · intro i hi
      exact hinvF.out i (List.mem_range.mp hi)
  -- the touch is a no-op
  have hRETv : RET = 6144 := rfl
  have htouch : touchMemory ystF (W RET).toNat (W (modulusSize cd)).toNat = ystF := by
    rw [show (W RET).toNat = RET from toNat_W (by omega),
      show (W (modulusSize cd)).toNat = modulusSize cd from toNat_W (by omega)]
    refine touchMemoryRange_noop (n := modulusSize cd) hmspos ?_
    rw [hinvF.aw]
    show RET + modulusSize cd ≤ 32 * 250
    omega
  rw [htouch, hread] at hhalt
  refine ⟨⟨.op .ret :: progTail, words [W RET, W (modulusSize cd)], ystF⟩,
    { ystF with halted := some (.ret, (natToBytes a (modulusSize cd)).toList) },
    ?_, hhalt, rfl⟩
  rw [show bpSer programLabels ++ progTail =
      store Icell (.imm 0) ++ ([.label programLabels.lbSerLoop] ++
        (serBody programLabels ++ (serTail programLabels ++ progTail))) from by
      rw [bpSer_eq]; simp only [List.append_assoc]]
  exact ((hs0.trans hlab).trans hloop).trans hret0'



end Challenge.Modexp.Submission.Proof.BigSer
