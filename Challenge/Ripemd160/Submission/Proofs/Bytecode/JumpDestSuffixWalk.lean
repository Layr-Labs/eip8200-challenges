import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.JumpDestSuffixWalk

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

theorem byte_at_shift (pre data rest : List UInt8) (q : Nat)
    (hq : q < data.length) :
    (mkCode (pre ++ data ++ rest))[pre.length + q]'(by
      simp only [size_mkCode, List.length_append]
      omega) =
      (mkCode (data ++ rest))[q]'(by
        simp only [size_mkCode, List.length_append]
        omega) := by
  have hfull : pre.length + q < (mkCode (pre ++ data ++ rest)).size := by
    simp only [size_mkCode, List.length_append]
    omega
  have hsuf : q < (mkCode (data ++ rest)).size := by
    simp only [size_mkCode, List.length_append]
    omega
  rw [getElem_mkCode (pre ++ data ++ rest) (pre.length + q) hfull,
    getElem_mkCode (data ++ rest) q hsuf]
  have h? : (pre ++ data ++ rest)[pre.length + q]? =
      (data ++ rest)[q]? := by
    rw [List.append_assoc, List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
  have hL : (pre ++ data ++ rest)[pre.length + q]'(by
      simp only [List.length_append]
      omega) = (data ++ rest)[q]'(by
      simp only [List.length_append]
      omega) := by
    have h1 : (pre ++ data ++ rest)[pre.length + q]? = some
        ((pre ++ data ++ rest)[pre.length + q]'(by
          simp only [List.length_append]
          omega)) := List.getElem?_eq_getElem (by
            simp only [List.length_append]
            omega)
    have h2 : (data ++ rest)[q]? = some
        ((data ++ rest)[q]'(by
          simp only [List.length_append]
          omega)) := List.getElem?_eq_getElem (by
            simp only [List.length_append]
            omega)
    exact Option.some.inj (h1.symm.trans (h?.trans h2))
  exact hL

theorem byte_at_shift_end (pre data rest : List UInt8)
    (hr : rest ≠ []) :
    (mkCode (pre ++ data ++ rest))[pre.length + data.length]'(by
      simp only [size_mkCode, List.length_append]
      cases rest with
      | nil => contradiction
      | cons b tail => simp
      ) =
      (mkCode (data ++ rest))[data.length]'(by
        simp only [size_mkCode, List.length_append]
        cases rest with
        | nil => contradiction
        | cons b tail => simp
        ) := by
  obtain ⟨b, tail, hrest⟩ := List.exists_cons_of_ne_nil hr
  subst rest
  have hfull : pre.length + data.length
      < (mkCode (pre ++ data ++ b :: tail)).size := by
    simp [size_mkCode]
  have hsuf : data.length < (mkCode (data ++ b :: tail)).size := by
    simp [size_mkCode]
  rw [getElem_mkCode (pre ++ data ++ b :: tail)
        (pre.length + data.length) hfull,
      getElem_mkCode (data ++ b :: tail) data.length hsuf]
  have h? : (pre ++ data ++ b :: tail)[pre.length + data.length]? =
      (data ++ b :: tail)[data.length]? := by
    rw [show pre ++ data ++ b :: tail = pre ++ (data ++ b :: tail) by simp,
      List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
  have hpre : pre.length + data.length
      < (pre ++ data ++ b :: tail).length := by
    simp only [List.length_append, List.length_cons]
    omega
  have hdata : data.length < (data ++ b :: tail).length := by
    simp only [List.length_append, List.length_cons]
    omega
  have hL : (pre ++ data ++ b :: tail)[pre.length + data.length]'hpre =
      (data ++ b :: tail)[data.length]'hdata := by
    have h1 : (pre ++ data ++ b :: tail)[pre.length + data.length]? = some
        ((pre ++ data ++ b :: tail)[pre.length + data.length]'hpre) :=
      List.getElem?_eq_getElem hpre
    have h2 : (data ++ b :: tail)[data.length]? = some
        ((data ++ b :: tail)[data.length]'hdata) :=
      List.getElem?_eq_getElem hdata
    exact Option.some.inj (h1.symm.trans (h?.trans h2))
  exact hL

theorem pushDataSize_shift (pre data rest : List UInt8) (q : Nat)
    (hq : q < data.length) :
    Decode.pushDataSize (mkCode (pre ++ data ++ rest)) (pre.length + q) =
      Decode.pushDataSize (mkCode (data ++ rest)) q := by
  unfold Decode.pushDataSize
  rw [dif_pos (by
        simp only [size_mkCode, List.length_append]
        omega),
      dif_pos (by
        simp only [size_mkCode, List.length_append]
        omega),
      byte_at_shift pre data rest q hq]

private theorem bytes_pos (i : Instr) : 1 ≤ i.bytes.length := by
  cases i <;> simp

private theorem getElem_boundary (pre post : List UInt8) (b : UInt8) (rest : List UInt8)
    (h : pre.length < (mkCode (pre ++ (b :: rest) ++ post)).size) :
    (mkCode (pre ++ (b :: rest) ++ post))[pre.length] = b := by
  have hlen : pre.length < (pre ++ (b :: rest) ++ post).length := by simp
  have h? : (pre ++ (b :: rest) ++ post)[pre.length]? = some b := by
    rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
    simp
  have hL : (pre ++ (b :: rest) ++ post)[pre.length]'hlen = b := by
    have h1 : (pre ++ (b :: rest) ++ post)[pre.length]?
        = some ((pre ++ (b :: rest) ++ post)[pre.length]'hlen) :=
      List.getElem?_eq_getElem hlen
    exact Option.some.inj (h1.symm.trans h?)
  simp only [mkCode, ByteArray.getElem_eq_data_getElem, List.getElem_toArray]
  exact hL

private theorem opcodeOf_opByte_not_push (o : Operation) :
    (match Decode.opcodeOf (Instr.opByte o) with
     | some (.Push p) => p.width.val
     | _ => 0) = 0 := by
  cases o with
  | StopArith op => cases op <;> rfl
  | CompBit op => cases op <;> rfl
  | Keccak op => rfl
  | Env op => cases op <;> rfl
  | Block op => cases op <;> rfl
  | StackMemFlow op => cases op <;> rfl
  | Push p => rfl
  | Dup d =>
    obtain ⟨⟨n, hn⟩⟩ := d
    rw [(dup_roundtrip ⟨n, hn⟩).1]
  | Swap s =>
    obtain ⟨⟨n, hn⟩⟩ := s
    rw [(swap_roundtrip ⟨n, hn⟩).1]
  | DupN d => rfl
  | SwapN d => rfl
  | Exchange e => rfl
  | Log l =>
    obtain ⟨⟨n, hn⟩⟩ := l
    interval_cases n <;> rfl
  | System op => cases op <;> rfl

private theorem pushDataSize_at (i : Instr) (pre rest : List UInt8) :
    Decode.pushDataSize (mkCode (pre ++ i.bytes ++ rest)) pre.length
      = i.bytes.length - 1 := by
  have hsz : pre.length < (mkCode (pre ++ i.bytes ++ rest)).size := by
    have := bytes_pos i
    simp
    omega
  unfold Decode.pushDataSize
  rw [dif_pos hsz]
  cases i with
  | push w v =>
    have hb : (mkCode (pre ++ (Instr.push w v).bytes ++ rest))[pre.length]'hsz
        = UInt8.ofNat (0x5f + w.val) :=
      getElem_boundary pre rest (UInt8.ofNat (0x5f + w.val))
        (natToBE v.toNat w.val) hsz
    rw [hb, opcodeOf_push w]
    simp
  | op o =>
    have hb : (mkCode (pre ++ (Instr.op o).bytes ++ rest))[pre.length]'hsz
        = Instr.opByte o :=
      getElem_boundary pre rest (Instr.opByte o) [] hsz
    rw [hb]
    exact opcodeOf_opByte_not_push o

theorem typed_prefix_shift (is : List Instr) (pre rest : List UInt8)
    (target fuel : Nat)
    (htarget : pre.length + (assembleBytes is).length ≤ target)
    (hfuel : is.length ≤ fuel) :
    Decode.validJumpDestFrom (mkCode (pre ++ assembleBytes is ++ rest))
        target pre.length fuel =
      Decode.validJumpDestFrom (mkCode (pre ++ assembleBytes is ++ rest))
        target (pre ++ assembleBytes is).length (fuel - is.length) := by
  induction is generalizing pre target fuel with
  | nil =>
    simp
  | cons i is ih =>
    cases fuel with
    | zero =>
      simp only [List.length_cons] at hfuel
      omega
    | succ fuel =>
      simp only [assembleBytes_cons, List.append_assoc] at htarget ⊢
      have hpos := bytes_pos i
      have htarget' : (pre ++ i.bytes).length +
          (assembleBytes is).length ≤ target := by
        simp only [List.length_append] at htarget ⊢
        omega
      have hpc : pre.length <
          (mkCode (pre ++ (i.bytes ++ (assembleBytes is ++ rest)))).size := by
        simp [size_mkCode]
        omega
      have hnot_target : pre.length ≠ target := by
        simp only [List.length_append] at htarget
        omega
      have hnot_past : ¬ (pre.length > target) := by
        simp only [List.length_append] at htarget
        omega
      conv_lhs =>
        unfold Decode.validJumpDestFrom
      rw [if_neg hnot_target, if_neg (not_or.mpr ⟨hnot_past, by omega⟩)]
      have hstep : Decode.pushDataSize
          (mkCode (pre ++ (i.bytes ++ (assembleBytes is ++ rest)))) pre.length
          = i.bytes.length - 1 := by
        simpa [List.append_assoc] using
          (pushDataSize_at i pre (assembleBytes is ++ rest))
      rw [hstep]
      rw [show pre.length + 1 + (i.bytes.length - 1) = (pre ++ i.bytes).length by
        simp
        omega]
      have hfuel' : is.length ≤ fuel := by
        simp only [List.length_cons] at hfuel
        omega
      have hi := ih (pre ++ i.bytes) target fuel htarget' hfuel'
      have hsub : fuel + 1 - (i :: is).length = fuel - is.length := by
        simp only [List.length_cons]
        omega
      rw [hsub]
      simpa [List.append_assoc, Nat.add_assoc] using hi

theorem valid_shift (pre data rest : List UInt8) (target : Nat)
    (hr : rest ≠ []) :
    ∀ (fuel q : Nat),
      target = pre.length + data.length →
      q ≤ data.length →
      Decode.validJumpDestFrom (mkCode (pre ++ data ++ rest))
          target (pre.length + q) fuel =
        Decode.validJumpDestFrom (mkCode (data ++ rest))
          data.length q fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro q ht hq
    rfl
  | succ fuel ih =>
    intro q ht hq
    by_cases hqend : q = data.length
    · subst q
      have hfull : pre.length + data.length
          < (mkCode (pre ++ data ++ rest)).size := by
        cases rest with
        | nil => contradiction
        | cons b tail => simp [size_mkCode]
      have hsuf : data.length < (mkCode (data ++ rest)).size := by
        cases rest with
        | nil => contradiction
        | cons b tail => simp [size_mkCode]
      unfold Decode.validJumpDestFrom
      rw [if_pos ht.symm, dif_pos hfull, if_pos rfl, dif_pos hsuf]
      simpa using congrArg (fun b : UInt8 => decide (b = 0x5b))
        (byte_at_shift_end pre data rest hr)
    · have hq_lt : q < data.length := by omega
      have hfull : pre.length + q
          < (mkCode (pre ++ data ++ rest)).size := by
        simp only [size_mkCode, List.length_append]
        omega
      have hsuf : q < (mkCode (data ++ rest)).size := by
        simp only [size_mkCode, List.length_append]
        omega
      have hfull_not_target : pre.length + q ≠ target := by omega
      have hsuf_not_target : q ≠ data.length := by omega
      have hfull_not_past : ¬ (pre.length + q > target) := by omega
      have hsuf_not_past : ¬ (q > data.length) := by omega
      have hfull_not_or : ¬ (pre.length + q > target ∨
          pre.length + q ≥ (mkCode (pre ++ data ++ rest)).size) := by
        exact not_or.mpr ⟨hfull_not_past, by omega⟩
      have hsuf_not_or : ¬ (q > data.length ∨
          q ≥ (mkCode (data ++ rest)).size) := by
        exact not_or.mpr ⟨hsuf_not_past, by omega⟩
      unfold Decode.validJumpDestFrom
      rw [if_neg hfull_not_target, if_neg hfull_not_or,
        if_neg hsuf_not_target, if_neg hsuf_not_or]
      rw [pushDataSize_shift pre data rest q hq_lt]
      by_cases hnext : q + 1 +
          Decode.pushDataSize (mkCode (data ++ rest)) q ≤ data.length
      · simpa [Nat.add_assoc] using
          (ih (q + 1 + Decode.pushDataSize (mkCode (data ++ rest)) q)
            ht hnext)
      · have hpast_full :
            Decode.validJumpDestFrom (mkCode (pre ++ data ++ rest)) target
                (pre.length + q + 1 +
                  Decode.pushDataSize (mkCode (data ++ rest)) q) fuel = false := by
          induction fuel with
          | zero => rfl
          | succ fuel ihpast =>
            simp only [Decode.validJumpDestFrom]
            rw [if_neg (by omega), if_pos (by omega)]
        have hpast_suffix :
            Decode.validJumpDestFrom (mkCode (data ++ rest)) data.length
                (q + 1 + Decode.pushDataSize (mkCode (data ++ rest)) q) fuel = false := by
          induction fuel with
          | zero => rfl
          | succ fuel ihpast =>
            simp only [Decode.validJumpDestFrom]
            rw [if_neg (by omega), if_pos (by omega)]
        rw [hpast_full, hpast_suffix]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.JumpDestSuffixWalk
