import Challenge.Modexp.Submission.Proofs.Fast.R4Value
import Challenge.Modexp.Submission.Proofs.Fast.SquareResult

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# R4：内存模型与 CSUB 结果

`r4Mem mem W` 是例程写回 `t` 窗口五个字后的内存；`rows4 mem` 是同一内存，其中
`W` 由内存本身决定（`k = maxWord`，模数字取自字 0..96，`np` 取自 2720）。

`rows4_represents`：在 `a < m`、`m` 奇、`n0·np ≡ −1` 下，`rows4` 之后的 CSUB 把
`montMul m R⁴ a a` 写到目标——与旧 `sqRowsCarry_represents` 同一结论，不经过旧行模型。
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R4Bridge

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro R4Math R4Value

/-- 例程写回的内存：`t0..t4` 依次存到 2208, 2176, 2144, 2112, 2080。 -/
def r4Mem (mem : ByteArray) (W : W5) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes
    (MachineState.writeBytes (MachineState.writeBytes mem
      (Data.Bytes.natToBytesPadded W.t0.toNat 32) 2208)
      (Data.Bytes.natToBytesPadded W.t1.toNat 32) 2176)
      (Data.Bytes.natToBytesPadded W.t2.toNat 32) 2144)
      (Data.Bytes.natToBytesPadded W.t3.toNat 32) 2112)
      (Data.Bytes.natToBytesPadded W.t4.toNat 32) 2080

/-- R4 的五个输出字：`a` 取自 A 窗口，`n3` 取自字 0，其余模数字、`np`、`k` 取自帧。 -/
def r4Final (mem : ByteArray) (k n0 n1 n2 np : UInt256) : W5 :=
  final (MachineState.readWord mem 2464) (MachineState.readWord mem 2432)
    (MachineState.readWord mem 2400) (MachineState.readWord mem 2368) n0 n1 n2
    (MachineState.readWord mem 0) np k

/-- 只由内存决定的 R4 输出内存。 -/
def rows4 (mem : ByteArray) : ByteArray :=
  r4Mem mem (r4Final mem maxWord (MachineState.readWord mem 96) (MachineState.readWord mem 64)
    (MachineState.readWord mem 32) (MachineState.readWord mem 2720))

theorem radix_eq : Limbs.radix = 2 ^ 256 := by
  rw [← SquareModel.two_half_radix]; norm_num

/-! ## 读回 -/

theorem readWord_r4Mem_outside (mem : ByteArray) (W : W5) (addr : Nat)
    (h : addr + 32 ≤ 2080 ∨ 2240 ≤ addr) :
    MachineState.readWord (r4Mem mem W) addr = MachineState.readWord mem addr := by
  unfold r4Mem
  rw [readWord_storeWord_outside _ _ 2080 addr (by omega),
    readWord_storeWord_outside _ _ 2112 addr (by omega),
    readWord_storeWord_outside _ _ 2144 addr (by omega),
    readWord_storeWord_outside _ _ 2176 addr (by omega),
    readWord_storeWord_outside _ _ 2208 addr (by omega)]

theorem readWord_r4Mem_t4 (mem : ByteArray) (W : W5) :
    MachineState.readWord (r4Mem mem W) 2080 = W.t4 := by
  unfold r4Mem
  exact Challenge.EvmProof.Memory.readWord_writeWord _ 2080 W.t4

theorem readWord_r4Mem_t3 (mem : ByteArray) (W : W5) :
    MachineState.readWord (r4Mem mem W) 2112 = W.t3 := by
  unfold r4Mem
  rw [readWord_storeWord_outside _ _ 2080 2112 (by omega)]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ 2112 W.t3

theorem readWord_r4Mem_t2 (mem : ByteArray) (W : W5) :
    MachineState.readWord (r4Mem mem W) 2144 = W.t2 := by
  unfold r4Mem
  rw [readWord_storeWord_outside _ _ 2080 2144 (by omega),
    readWord_storeWord_outside _ _ 2112 2144 (by omega)]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ 2144 W.t2

theorem readWord_r4Mem_t1 (mem : ByteArray) (W : W5) :
    MachineState.readWord (r4Mem mem W) 2176 = W.t1 := by
  unfold r4Mem
  rw [readWord_storeWord_outside _ _ 2080 2176 (by omega),
    readWord_storeWord_outside _ _ 2112 2176 (by omega),
    readWord_storeWord_outside _ _ 2144 2176 (by omega)]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ 2176 W.t1

theorem readWord_r4Mem_t0 (mem : ByteArray) (W : W5) :
    MachineState.readWord (r4Mem mem W) 2208 = W.t0 := by
  unfold r4Mem
  rw [readWord_storeWord_outside _ _ 2080 2208 (by omega),
    readWord_storeWord_outside _ _ 2112 2208 (by omega),
    readWord_storeWord_outside _ _ 2144 2208 (by omega),
    readWord_storeWord_outside _ _ 2176 2208 (by omega)]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ 2208 W.t0

/-- 写回后的 CIOS 累加器数值就是 `val5 W`。 -/
theorem tValue_r4Mem (mem : ByteArray) (W : W5) : tValue (r4Mem mem W) 4 = val5 W := by
  have e3 : Csub.lowValue (r4Mem mem W) 2112 4 4 = Csub.lowValue (r4Mem mem W) 2112 4 3 +
      (MachineState.readWord (r4Mem mem W) 2112).toNat * Limbs.radix ^ 3 :=
    Csub.lowValue_succ (r4Mem mem W) 2112 4 3
  have e2 : Csub.lowValue (r4Mem mem W) 2112 4 3 = Csub.lowValue (r4Mem mem W) 2112 4 2 +
      (MachineState.readWord (r4Mem mem W) 2144).toNat * Limbs.radix ^ 2 :=
    Csub.lowValue_succ (r4Mem mem W) 2112 4 2
  have e1 : Csub.lowValue (r4Mem mem W) 2112 4 2 = Csub.lowValue (r4Mem mem W) 2112 4 1 +
      (MachineState.readWord (r4Mem mem W) 2176).toNat * Limbs.radix ^ 1 :=
    Csub.lowValue_succ (r4Mem mem W) 2112 4 1
  have e0 : Csub.lowValue (r4Mem mem W) 2112 4 1 = Csub.lowValue (r4Mem mem W) 2112 4 0 +
      (MachineState.readWord (r4Mem mem W) 2208).toNat * Limbs.radix ^ 0 :=
    Csub.lowValue_succ (r4Mem mem W) 2112 4 0
  unfold tValue
  rw [e3, e2, e1, e0, Csub.lowValue_zero, readWord_r4Mem_t4, readWord_r4Mem_t3,
    readWord_r4Mem_t2, readWord_r4Mem_t1, readWord_r4Mem_t0, radix_eq]
  unfold val5
  ring

/-! ## 数值 -/

/-- 四肢数的肢和展开。 -/
theorem limbSum_four (f : Nat → Nat) :
    limbSum f 4 = f 0 + f 1 * 2 ^ 256 + f 2 * (2 ^ 256) ^ 2 + f 3 * (2 ^ 256) ^ 3 := by
  have h : limbSum f 4 = 0 + f 0 * Limbs.radix ^ 0 + f 1 * Limbs.radix ^ 1 +
      f 2 * Limbs.radix ^ 2 + f 3 * Limbs.radix ^ 3 := rfl
  rw [h, radix_eq]
  ring

theorem lsum_four (f : Nat → Nat) :
    SquareMath.lsum (2 * 2 ^ 255) f 4 =
      f 0 + f 1 * 2 ^ 256 + f 2 * (2 ^ 256) ^ 2 + f 3 * (2 ^ 256) ^ 3 := by
  have h : SquareMath.lsum (2 * 2 ^ 255) f 4 = 0 + f 0 * (2 * 2 ^ 255) ^ 0 +
      f 1 * (2 * 2 ^ 255) ^ 1 + f 2 * (2 * 2 ^ 255) ^ 2 + f 3 * (2 * 2 ^ 255) ^ 3 := rfl
  rw [h, show (2 : Nat) * 2 ^ 255 = 2 ^ 256 by norm_num]
  ring

/-- `rows4` 的累加器满足 `T · R⁴ = a² + Q · m`，`Q < R⁴`。 -/
theorem rows4_eq (mem : ByteArray) (a mm : Nat)
    (ha : Model.FastRepresents mem 2368 4 a) (hm : Model.FastRepresents mem 0 4 mm)
    (hminv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    ∃ Q, Q < Limbs.radix ^ 4 ∧ tValue (rows4 mem) 4 * Limbs.radix ^ 4 = a * a + Q * mm := by
  obtain ⟨Q, hQ, hf⟩ := final_eq (MachineState.readWord mem 2464) (MachineState.readWord mem 2432)
    (MachineState.readWord mem 2400) (MachineState.readWord mem 2368)
    (MachineState.readWord mem 96) (MachineState.readWord mem 64) (MachineState.readWord mem 32)
    (MachineState.readWord mem 0) (MachineState.readWord mem 2720) hminv
  have hA : SquareMath.lsum (2 * 2 ^ 255) (limbs4 (MachineState.readWord mem 2464)
      (MachineState.readWord mem 2432) (MachineState.readWord mem 2400)
      (MachineState.readWord mem 2368)) 4 = a := by
    rw [← limbSum_fastRepresents ha, lsum_four, limbSum_four]
    rfl
  have hM : (MachineState.readWord mem 96).toNat + (MachineState.readWord mem 64).toNat * 2 ^ 256 +
      (MachineState.readWord mem 32).toNat * (2 ^ 256) ^ 2 +
      (MachineState.readWord mem 0).toNat * (2 ^ 256) ^ 3 = mm := by
    rw [← limbSum_fastRepresents hm, limbSum_four]
  refine ⟨Q, by rw [radix_eq]; exact hQ, ?_⟩
  rw [rows4, tValue_r4Mem, radix_eq]
  unfold r4Final
  rw [hf, hA, hM]
  ring

theorem rows4_readWord_outside (mem : ByteArray) (addr : Nat)
    (h : addr + 32 ≤ 2080 ∨ 2240 ≤ addr) :
    MachineState.readWord (rows4 mem) addr = MachineState.readWord mem addr :=
  readWord_r4Mem_outside mem _ addr h

theorem rows4_fastRepresents_outside (mem : ByteArray) (ptr cnt v : Nat)
    (h : ptr + 32 * cnt ≤ 2080 ∨ 2240 ≤ ptr) (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (rows4 mem) ptr cnt v := by
  refine (Model.fastRepresents_congr (a := mem) ?_ v).1 hrep
  intro j hj
  rw [rows4_readWord_outside mem (ptr + 32 * j) (by omega)]

/-- 累加器 `< 2m`。 -/
theorem rows4_lt (mem : ByteArray) (a mm : Nat)
    (ha : Model.FastRepresents mem 2368 4 a) (hm : Model.FastRepresents mem 0 4 mm)
    (hminv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) (ham : a < mm) :
    tValue (rows4 mem) 4 < 2 * mm := by
  obtain ⟨Q, hQ, hinv⟩ := rows4_eq mem a mm ha hm hminv
  have hmlt : mm < Limbs.radix ^ 4 := hm.1
  have hmpos : 0 < mm := by omega
  have h1 : a * a < mm * mm := Nat.mul_self_lt_mul_self ham
  have h2 : mm * mm ≤ mm * Limbs.radix ^ 4 := Nat.mul_le_mul_left _ (le_of_lt hmlt)
  have h3 : Q * mm < Limbs.radix ^ 4 * mm := Nat.mul_lt_mul_of_pos_right hQ hmpos
  by_contra hcon
  have hge : 2 * mm * Limbs.radix ^ 4 ≤ tValue (rows4 mem) 4 * Limbs.radix ^ 4 :=
    Nat.mul_le_mul_right _ (Nat.le_of_not_lt hcon)
  have h4 : Limbs.radix ^ 4 * mm = mm * Limbs.radix ^ 4 := Nat.mul_comm _ _
  have h5 : 2 * mm * Limbs.radix ^ 4 = mm * Limbs.radix ^ 4 + mm * Limbs.radix ^ 4 := by ring
  omega

/-- 顶字 `≤ 1`。 -/
theorem rows4_tn_le_one (mem : ByteArray) (a mm : Nat)
    (ha : Model.FastRepresents mem 2368 4 a) (hm : Model.FastRepresents mem 0 4 mm)
    (hminv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) (ham : a < mm) :
    (MachineState.readWord (rows4 mem) 2080).toNat ≤ 1 := by
  have hlt := rows4_lt mem a mm ha hm hminv ham
  simp only [tValue] at hlt
  have hmlt : mm < Limbs.radix ^ 4 := hm.1
  by_contra hcon
  have hge : 2 ≤ (MachineState.readWord (rows4 mem) 2080).toNat := by omega
  have hmul : 2 * Limbs.radix ^ 4 ≤
      (MachineState.readWord (rows4 mem) 2080).toNat * Limbs.radix ^ 4 :=
    Nat.mul_le_mul_right _ hge
  omega

/-- **R4 之后的 CSUB 给出 Montgomery 平方。** -/
theorem rows4_represents (mem : ByteArray) (a mm pdst : Nat)
    (ha : Model.FastRepresents mem 2368 4 a) (hm : Model.FastRepresents mem 0 4 mm)
    (hodd : mm % 2 = 1) (ham : a < mm)
    (hminv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    Model.FastRepresents (Csub.csResultMemory (rows4 mem) 4 pdst) pdst 4
      (Model.montMul mm (Limbs.radix ^ 4) a a) := by
  have hmpos : 0 < mm := by omega
  obtain ⟨Q, -, hinv⟩ := rows4_eq mem a mm ha hm hminv
  have hlt := rows4_lt mem a mm ha hm hminv ham
  have htn1 := rows4_tn_le_one mem a mm ha hm hminv ham
  have hcop : Nat.Coprime (Limbs.radix ^ 4) mm := Model.coprime_radix_pow_of_odd hodd 4
  have hval : Model.montMul mm (Limbs.radix ^ 4) a a = tValue (rows4 mem) 4 % mm :=
    Model.montMul_eq_mod_of_mul_eq hmpos hcop hinv
  have hmR := rows4_fastRepresents_outside mem 0 4 mm (Or.inl (by omega)) hm
  rw [hval]
  simp only [tValue] at hlt ⊢
  exact Csub.csub_correct (rows4 mem) 4 (Csub.lowValue (rows4 mem) 2112 4 4) mm
    (MachineState.readWord (rows4 mem) 2080).toNat pdst (by omega) (by omega)
    (Csub.fastRepresents_lowValue (rows4 mem) 2112 4) hmR rfl htn1 hmpos hlt

end Challenge.Modexp.Submission.Proofs.Fast.R4Bridge
