import Challenge.Modexp.Submission.Proofs.Bytecode.BigDouble
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigDouble

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

theorem doubleCarry_eq_correct (x carry : UInt256)
    (hcarry : carry.toNat ≤ 1) :
    UInt256.shiftRight x (UInt256.ofNat 255) =
      UInt256.lor (UInt256.lt (x + x) x)
        (UInt256.lt ((x + x) + carry) (x + x)) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.shiftRight_toNat x (by omega)]
  rw [(BigHelpers.addLimbStep_toNat x x carry hcarry).2]
  rw [Nat.shiftRight_eq_div_pow]
  change x.toNat / 2 ^ 255 =
    (x.toNat + x.toNat + carry.toNat) / 2 ^ 256
  have hxlt : x.toNat < 2 ^ 256 := x.val.isLt
  have hpow : 2 ^ 256 = 2 * 2 ^ 255 := by norm_num [pow_succ]
  by_cases hx : x.toNat < 2 ^ 255
  · have htotal : x.toNat + x.toNat + carry.toNat < 2 ^ 256 := by omega
    rw [Nat.div_eq_of_lt hx, Nat.div_eq_of_lt htotal]
  · have hxle : 2 ^ 255 ≤ x.toNat := by omega
    have htotalLe : 2 ^ 256 ≤ x.toNat + x.toNat + carry.toNat := by omega
    have htotalLt : x.toNat + x.toNat + carry.toNat < 2 * 2 ^ 256 := by omega
    have hxdiv : x.toNat / 2 ^ 255 = 1 := by
      apply Nat.div_eq_of_lt_le
      · exact hxle
      · omega
    have htotaldiv : (x.toNat + x.toNat + carry.toNat) / 2 ^ 256 = 1 := by
      apply Nat.div_eq_of_lt_le
      · exact htotalLe
      · exact htotalLt
    rw [hxdiv, htotaldiv]

theorem readWord_fusedProgress_disjoint_region (memory : ByteArray)
    (activeWords modulus : UInt256) (dst ptr count iter j : Nat)
    (hiter : iter ≤ count) (hj : j < count)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (hptrDst : dst + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ dst)
    (hptrCandidate : ptr + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ ptr) :
    MachineState.readWord
        (fusedProgress memory activeWords (UInt256.ofNat dst) modulus iter).memory
        (ptr + 32 * j) =
      MachineState.readWord memory (ptr + 32 * j) := by
  induction iter with
  | zero => rfl
  | succ iter ih =>
      simp only [fusedProgress]
      rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
        · exact ih (by omega)
        · have hsize (value : Nat) :
              (Data.Bytes.natToBytesPadded value 32).size = 32 := by
            simp [Data.Bytes.natToBytesPadded, ByteArray.size]
          rw [hsize, BigHelpers.addOffset_toNat dst iter (by omega)]
          rcases hptrDst with hbefore | hafter
          · right; omega
          · left; omega
      · have hsize (value : Nat) :
            (Data.Bytes.natToBytesPadded value 32).size = 32 := by
          simp [Data.Bytes.natToBytesPadded, ByteArray.size]
        rw [hsize, BigHelpers.addOffset_toNat 5120 iter (by omega)]
        rcases hptrCandidate with hbefore | hafter
        · left; omega
        · right; omega

theorem represents_fusedProgress_disjoint_region (memory : ByteArray)
    (activeWords modulus : UInt256) (dst ptr count iter value : Nat)
    (hiter : iter ≤ count)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (hptrDst : dst + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ dst)
    (hptrCandidate : ptr + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ ptr)
    (hrep : Limbs.Represents memory ptr count value) :
    Limbs.Represents
      (fusedProgress memory activeWords (UInt256.ofNat dst) modulus iter).memory
      ptr count value := by
  refine ⟨hrep.1, ?_⟩
  unfold Limbs.memoryLimbs
  rw [← hrep.2]
  apply List.map_congr_left
  intro j hj
  rw [readWord_fusedProgress_disjoint_region memory activeWords modulus dst ptr
    count iter j hiter (by simpa using hj) hdstFit hcandidateFit hptrDst
    hptrCandidate]

theorem readWord_fusedProgress_future_dst (memory : ByteArray)
    (activeWords modulus : UInt256) (dst count iter j : Nat)
    (hiter : iter ≤ j) (hj : j < count)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (hdstCandidate : dst + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ dst) :
    MachineState.readWord
        (fusedProgress memory activeWords (UInt256.ofNat dst) modulus iter).memory
        (dst + 32 * j) = MachineState.readWord memory (dst + 32 * j) := by
  induction iter with
  | zero => rfl
  | succ iter ih =>
      simp only [fusedProgress]
      rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
        · exact ih (by omega)
        · have hsize (value : Nat) :
              (Data.Bytes.natToBytesPadded value 32).size = 32 := by
            simp [Data.Bytes.natToBytesPadded, ByteArray.size]
          rw [hsize, BigHelpers.addOffset_toNat dst iter (by omega)]
          right; omega
      · have hsize (value : Nat) :
            (Data.Bytes.natToBytesPadded value 32).size = 32 := by
          simp [Data.Bytes.natToBytesPadded, ByteArray.size]
        rw [hsize, BigHelpers.addOffset_toNat 5120 iter (by omega)]
        rcases hdstCandidate with hbefore | hafter
        · left; omega
        · right; omega

private theorem memoryLimbs_writeWord_disjoint (memory : ByteArray)
    (writeAt ptr count : Nat) (value : UInt256)
    (hdisjoint : writeAt + 32 ≤ ptr ∨ ptr + 32 * count ≤ writeAt) :
    Limbs.memoryLimbs
      (MachineState.writeBytes memory (Data.Bytes.natToBytesPadded value.toNat 32)
        writeAt) ptr count = Limbs.memoryLimbs memory ptr count := by
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro j hj
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  have hjlt : j < count := by simpa using hj
  have hsize : (Data.Bytes.natToBytesPadded value.toNat 32).size = 32 := by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  rw [hsize]
  rcases hdisjoint with hbefore | hafter
  · right; omega
  · left; omega

structure FusedNatProgress where
  digits : List Nat
  candidates : List Nat
  carry : Nat
  borrow : Nat

def fusedNatProgress (memory : ByteArray) (dst modulus : Nat) :
    Nat → FusedNatProgress
  | 0 => ⟨[], [], 0, 0⟩
  | i + 1 =>
      let before := fusedNatProgress memory dst modulus i
      let x := (MachineState.readWord memory (dst + 32 * i)).toNat
      let y := (MachineState.readWord memory (modulus + 32 * i)).toNat
      let total := x + x + before.carry
      let z := total % Limbs.radix
      let carry := total / Limbs.radix
      let nextBorrow := if z < y + before.borrow then 1 else 0
      let candidate := z + Limbs.radix * nextBorrow - y - before.borrow
      ⟨before.digits ++ [z], before.candidates ++ [candidate], carry,
        nextBorrow⟩

theorem fusedNatProgress_canonical (memory : ByteArray)
    (dst modulus count : Nat) :
    let natural := fusedNatProgress memory dst modulus count
    let added := Limbs.addDigitLists
      (Limbs.memoryLimbs memory dst count)
      (Limbs.memoryLimbs memory dst count) 0
    let subtracted := Limbs.subDigitLists natural.digits
      (Limbs.memoryLimbs memory modulus count) 0
    natural.digits = added.1 ∧ natural.carry = added.2 ∧
      natural.candidates = subtracted.1 ∧ natural.borrow = subtracted.2 := by
  induction count with
  | zero =>
      simp [fusedNatProgress, Limbs.memoryLimbs, Limbs.addDigitLists,
        Limbs.subDigitLists]
  | succ count ih =>
      rw [fusedNatProgress, BigHelpers.memoryLimbs_succ,
        BigHelpers.memoryLimbs_succ,
        Limbs.addDigitLists_append_single (by simp [Limbs.memoryLimbs])]
      rcases ih with ⟨hdigits, hcarry, hcandidates, hborrow⟩
      simp only
      rw [hdigits, hcarry]
      rw [hdigits] at hcandidates hborrow
      rw [Limbs.subDigitLists_append_single (by
        rw [Limbs.length_addDigitLists_left]
        simp only [Limbs.memoryLimbs, List.length_map, List.length_range]
        rfl),
        hcandidates, hborrow]
      exact ⟨rfl, rfl, rfl, rfl⟩

theorem fusedProgress_matches_nat (memory : ByteArray) (activeWords : UInt256)
    (dst modulus count iter : Nat) (hiter : iter ≤ count)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hmodulusFit : modulus + 32 * count < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (hdstModulus : dst + 32 * count ≤ modulus ∨
      modulus + 32 * count ≤ dst)
    (hdstCandidate : dst + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ dst)
    (hmodulusCandidate : modulus + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ modulus) :
    let progress := fusedProgress memory activeWords (UInt256.ofNat dst)
      (UInt256.ofNat modulus) iter
    let natural := fusedNatProgress memory dst modulus iter
    Limbs.memoryLimbs progress.memory dst iter = natural.digits ∧
      Limbs.memoryLimbs progress.memory 5120 iter = natural.candidates ∧
      progress.carry.toNat = natural.carry ∧
      progress.borrow.toNat = natural.borrow ∧
      natural.carry ≤ 1 ∧ natural.borrow ≤ 1 := by
  induction iter with
  | zero =>
      have hzero : (0 : UInt256).toNat = 0 := by decide
      simp [fusedProgress, fusedNatProgress, Limbs.memoryLimbs, hzero]
  | succ iter ih =>
      have hi : iter < count := by omega
      have hprefix := ih (by omega)
      let before := fusedProgress memory activeWords (UInt256.ofNat dst)
        (UInt256.ofNat modulus) iter
      let naturalBefore := fusedNatProgress memory dst modulus iter
      have hbeforeDst :
          Limbs.memoryLimbs before.memory dst iter = naturalBefore.digits :=
        hprefix.1
      have hbeforeCandidate :
          Limbs.memoryLimbs before.memory 5120 iter = naturalBefore.candidates :=
        hprefix.2.1
      have hbeforeCarry : before.carry.toNat = naturalBefore.carry :=
        hprefix.2.2.1
      have hbeforeBorrow : before.borrow.toNat = naturalBefore.borrow :=
        hprefix.2.2.2.1
      have hcarryLe : naturalBefore.carry ≤ 1 := hprefix.2.2.2.2.1
      have hborrowLe : naturalBefore.borrow ≤ 1 := hprefix.2.2.2.2.2
      let off := UInt256.shiftLeft (UInt256.ofNat iter) (UInt256.ofNat 5)
      let dstAt := UInt256.ofNat dst + off
      let modulusAt := UInt256.ofNat modulus + off
      let candidateAt := UInt256.ofNat 5120 + off
      let x := MachineState.readWord before.memory dstAt.toNat
      let z := (x + x) + before.carry
      let storedDst := MachineState.writeBytes before.memory
        (Data.Bytes.natToBytesPadded z.toNat 32) dstAt.toNat
      let y := MachineState.readWord storedDst modulusAt.toNat
      let difference := z - y
      let candidate := difference - before.borrow
      have hoffDst : dstAt.toNat = dst + 32 * iter := by
        exact BigHelpers.addOffset_toNat dst iter (by omega)
      have hoffModulus : modulusAt.toNat = modulus + 32 * iter := by
        exact BigHelpers.addOffset_toNat modulus iter (by omega)
      have hoffCandidate : candidateAt.toNat = 5120 + 32 * iter := by
        exact BigHelpers.addOffset_toNat 5120 iter (by omega)
      have hx : x = MachineState.readWord memory (dst + 32 * iter) := by
        simpa [x, dstAt, hoffDst, before] using
          readWord_fusedProgress_future_dst memory activeWords
            (UInt256.ofNat modulus) dst count iter iter (by omega) hi
            hdstFit hcandidateFit hdstCandidate
      have hyBefore : MachineState.readWord before.memory (modulus + 32 * iter) =
          MachineState.readWord memory (modulus + 32 * iter) := by
        exact readWord_fusedProgress_disjoint_region memory activeWords
          (UInt256.ofNat modulus) dst modulus count iter iter (by omega) hi
          hdstFit hcandidateFit hdstModulus hmodulusCandidate
      have hy : y = MachineState.readWord memory (modulus + 32 * iter) := by
        dsimp only [y]
        rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
        · simpa [modulusAt, hoffModulus, before] using hyBefore
        · have hsize : (Data.Bytes.natToBytesPadded z.toNat 32).size = 32 := by
            simp [Data.Bytes.natToBytesPadded, ByteArray.size]
          rw [hsize, hoffDst, hoffModulus]
          rcases hdstModulus with hbefore | hafter
          · right; omega
          · left; omega
      have hadd := BigHelpers.addLimbStep_toNat x x before.carry
        (by simpa [hbeforeCarry] using hcarryLe)
      have hcarryEq := doubleCarry_eq_correct x before.carry
        (by simpa [hbeforeCarry] using hcarryLe)
      have hsub := BigHelpers.subLimbStep_toNat z y before.borrow
        (by simpa [hbeforeBorrow] using hborrowLe)
      have hxBefore : MachineState.readWord before.memory (dst + 32 * iter) = x := by
        rw [← hoffDst]
      have hzBefore :
          (MachineState.readWord before.memory (dst + 32 * iter) +
            MachineState.readWord before.memory (dst + 32 * iter) +
            before.carry).toNat = z.toNat := by
        rw [hxBefore]
      have hdstMemory :
          Limbs.memoryLimbs
            (fusedProgress memory activeWords (UInt256.ofNat dst)
              (UInt256.ofNat modulus) (iter + 1)).memory dst (iter + 1) =
            naturalBefore.digits ++ [z.toNat] := by
        simp only [fusedProgress]
        rw [memoryLimbs_writeWord_disjoint]
        · rw [hoffDst, BigHelpers.memoryLimbs_write_next, hbeforeDst]
          rw [hzBefore]
        · rw [hoffCandidate]
          rcases hdstCandidate with hbefore | hafter
          · right; omega
          · left; omega
      have hcandidateMemory :
          Limbs.memoryLimbs
            (fusedProgress memory activeWords (UInt256.ofNat dst)
              (UInt256.ofNat modulus) (iter + 1)).memory 5120 (iter + 1) =
            naturalBefore.candidates ++ [candidate.toNat] := by
        simp only [fusedProgress]
        rw [hoffCandidate, BigHelpers.memoryLimbs_write_next]
        rw [memoryLimbs_writeWord_disjoint, hbeforeCandidate]
        rw [hoffDst]
        rcases hdstCandidate with hbefore | hafter
        · left; omega
        · right; omega
      have hzNatural : z.toNat =
          ((MachineState.readWord memory (dst + 32 * iter)).toNat +
            (MachineState.readWord memory (dst + 32 * iter)).toNat +
            naturalBefore.carry) % Limbs.radix := by
        calc
          z.toNat = (x.toNat + x.toNat + before.carry.toNat) %
              Limbs.radix := hadd.1
          _ = _ := by rw [hx, hbeforeCarry]
      have hcandidateNatural : candidate.toNat =
          z.toNat + Limbs.radix *
              (if z.toNat <
                (MachineState.readWord memory (modulus + 32 * iter)).toNat +
                  naturalBefore.borrow then 1 else 0) -
            (MachineState.readWord memory (modulus + 32 * iter)).toNat -
            naturalBefore.borrow := by
        calc
          candidate.toNat = z.toNat + Limbs.radix *
                (if z.toNat < y.toNat + before.borrow.toNat then 1 else 0) -
              y.toNat - before.borrow.toNat := hsub.1
          _ = _ := by rw [hy, hbeforeBorrow]
      have hcarryStep :
          (fusedProgress memory activeWords (UInt256.ofNat dst)
            (UInt256.ofNat modulus) (iter + 1)).carry =
          UInt256.shiftRight x (UInt256.ofNat 255) := by
        rfl
      have hcarryNatural :
          (fusedProgress memory activeWords (UInt256.ofNat dst)
            (UInt256.ofNat modulus) (iter + 1)).carry.toNat =
          ((MachineState.readWord memory (dst + 32 * iter)).toNat +
            (MachineState.readWord memory (dst + 32 * iter)).toNat +
            naturalBefore.carry) / Limbs.radix := by
        rw [hcarryStep, hcarryEq]
        calc
          (UInt256.lor (UInt256.lt (x + x) x)
            (UInt256.lt ((x + x) + before.carry) (x + x))).toNat =
              (x.toNat + x.toNat + before.carry.toNat) /
                Limbs.radix := hadd.2
          _ = _ := by rw [hx, hbeforeCarry]
      have hborrowStep :
          (fusedProgress memory activeWords (UInt256.ofNat dst)
            (UInt256.ofNat modulus) (iter + 1)).borrow =
          UInt256.lor (UInt256.lt z y)
            (UInt256.lt (z - y) before.borrow) := by
        rfl
      have hborrowNatural :
          (fusedProgress memory activeWords (UInt256.ofNat dst)
            (UInt256.ofNat modulus) (iter + 1)).borrow.toNat =
          if z.toNat <
              (MachineState.readWord memory (modulus + 32 * iter)).toNat +
                naturalBefore.borrow then 1 else 0 := by
        rw [hborrowStep]
        calc
          (UInt256.lor (UInt256.lt z y)
            (UInt256.lt (z - y) before.borrow)).toNat =
              (if z.toNat < y.toNat + before.borrow.toNat then 1 else 0) :=
                hsub.2
          _ = _ := by rw [hy, hbeforeBorrow]
      have hcarryBound :
          ((MachineState.readWord memory (dst + 32 * iter)).toNat +
            (MachineState.readWord memory (dst + 32 * iter)).toNat +
            naturalBefore.carry) / Limbs.radix ≤ 1 := by
        have hxLt :
            (MachineState.readWord memory (dst + 32 * iter)).toNat <
              Limbs.radix := by
          exact (MachineState.readWord memory (dst + 32 * iter)).val.isLt
        have htotal :
            (MachineState.readWord memory (dst + 32 * iter)).toNat +
                (MachineState.readWord memory (dst + 32 * iter)).toNat +
                naturalBefore.carry < 2 * Limbs.radix := by
          have hdouble := Nat.add_lt_add hxLt hxLt
          omega
        exact Nat.le_of_lt_succ
          (Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using htotal))
      have hborrowBound :
          (if z.toNat <
              (MachineState.readWord memory (modulus + 32 * iter)).toNat +
                naturalBefore.borrow then 1 else 0) ≤ 1 := by
        split <;> omega
      simp only [naturalBefore] at hzNatural hcandidateNatural hcarryNatural hborrowNatural hcarryBound hborrowBound
      rw [hzNatural] at hborrowNatural hborrowBound
      dsimp only [fusedNatProgress]
      rw [hdstMemory, hcandidateMemory]
      refine ⟨congrArg (fun n => naturalBefore.digits ++ [n]) hzNatural,
        ?_, hcarryNatural, hborrowNatural, hcarryBound, hborrowBound⟩
      rw [hcandidateNatural, hzNatural]

theorem fusedReturned_represents_mod (s : State)
    (dst modulus count x modulusValue : Nat) (returnDest : UInt256)
    (rest : List UInt256)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hmodulusFit : modulus + 32 * count < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (hdstModulus : dst + 32 * count ≤ modulus ∨
      modulus + 32 * count ≤ dst)
    (hdstCandidate : dst + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ dst)
    (hmodulusCandidate : modulus + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ modulus)
    (hdst : Limbs.Represents s.memory dst count x)
    (hmodulus : Limbs.Represents s.memory modulus count modulusValue)
    (hx : x < modulusValue)
    (hmodulusBound : modulusValue < Limbs.radix ^ count) :
    Limbs.Represents
      (fusedReturned s (UInt256.ofNat dst) (UInt256.ofNat modulus)
        count returnDest rest).memory dst count ((x + x) % modulusValue) := by
  let total := x + x
  let bound := Limbs.radix ^ count
  let progress := fusedProgress s.memory s.activeWords (UInt256.ofNat dst)
    (UInt256.ofNat modulus) count
  let natural := fusedNatProgress s.memory dst modulus count
  let wrapped := total % bound
  let candidate := Nat.ofDigits Limbs.radix
    (Limbs.memoryLimbs progress.memory 5120 count)
  have htotalLt : total < 2 * modulusValue := by omega
  have hmatch := fusedProgress_matches_nat s.memory s.activeWords dst modulus
    count count (by omega) hdstFit hmodulusFit hcandidateFit hdstModulus
    hdstCandidate hmodulusCandidate
  have hcanonical := fusedNatProgress_canonical s.memory dst modulus count
  dsimp only [progress, natural] at hmatch hcanonical
  have hlength :
      (Limbs.memoryLimbs s.memory dst count).length =
        (Limbs.memoryLimbs s.memory dst count).length := rfl
  have haddRaw := Limbs.addDigitLists_value (carry := 0) hlength
  rw [Nat.add_zero, Limbs.value_of_represents hdst] at haddRaw
  have haddValue :
      Nat.ofDigits Limbs.radix (Limbs.memoryLimbs progress.memory dst count) +
          bound * progress.carry.toNat = total := by
    dsimp only [progress, bound, total]
    rw [hmatch.1, hcanonical.1, hmatch.2.2.1, hcanonical.2.1]
    simpa [Nat.add_assoc, Limbs.length_memoryLimbs] using haddRaw
  have hcarryLe : progress.carry.toNat ≤ 1 := by
    rw [show progress.carry.toNat = natural.carry by
      simpa [progress, natural] using hmatch.2.2.1]
    exact hmatch.2.2.2.2.1
  have hvalueLt :
      Nat.ofDigits Limbs.radix (Limbs.memoryLimbs progress.memory dst count) <
        bound := by
    dsimp only [bound]
    exact BigHelpers.memoryLimbs_value_lt progress.memory dst count
  have hwrappedEq :
      Nat.ofDigits Limbs.radix (Limbs.memoryLimbs progress.memory dst count) =
        wrapped := by
    calc
      Nat.ofDigits Limbs.radix (Limbs.memoryLimbs progress.memory dst count) =
          Nat.ofDigits Limbs.radix (Limbs.memoryLimbs progress.memory dst count) %
            bound := (Nat.mod_eq_of_lt hvalueLt).symm
      _ = (Nat.ofDigits Limbs.radix
              (Limbs.memoryLimbs progress.memory dst count) +
            bound * progress.carry.toNat) % bound := by
              simp
      _ = total % bound := congrArg (· % bound) haddValue
      _ = wrapped := rfl
  have hwrapped : Limbs.Represents progress.memory dst count wrapped := by
    rw [Limbs.represents_iff_value (by
      exact Nat.mod_lt _ (pow_pos Limbs.radix_pos _))]
    exact hwrappedEq
  have hprogressModulus :
      Limbs.Represents progress.memory modulus count modulusValue := by
    exact represents_fusedProgress_disjoint_region s.memory s.activeWords
      (UInt256.ofNat modulus) dst modulus count count modulusValue (by omega)
      hdstFit hcandidateFit hdstModulus hmodulusCandidate hmodulus
  have hnaturalDigits : ∀ digit ∈ natural.digits, digit < Limbs.radix := by
    intro digit hdigit
    rw [hcanonical.1] at hdigit
    exact Limbs.addDigitLists_digits_lt hdigit
  have hnaturalLength : natural.digits.length =
      (Limbs.memoryLimbs s.memory modulus count).length := by
    rw [hcanonical.1, Limbs.length_addDigitLists_left]
    simp only [Limbs.memoryLimbs, List.length_map, List.length_range]
    rfl
  have hsubRaw := Limbs.subDigitLists_value (borrow := 0)
    hnaturalLength hnaturalDigits
    (fun _ hdigit => Limbs.memoryLimb_lt s.memory modulus count hdigit)
    (by omega)
  have hcandidateEq : candidate =
      Nat.ofDigits Limbs.radix natural.candidates := by
    dsimp only [candidate]
    rw [show Limbs.memoryLimbs progress.memory 5120 count =
      natural.candidates by simpa [progress, natural] using hmatch.2.1]
  have hborrowEq : progress.borrow.toNat = natural.borrow := by
    simpa [progress, natural] using hmatch.2.2.2.1
  have hnaturalValue : Nat.ofDigits Limbs.radix natural.digits = wrapped := by
    rw [← show Limbs.memoryLimbs progress.memory dst count = natural.digits by
      simpa [progress, natural] using hmatch.1]
    exact hwrappedEq
  have hsubNatural : Nat.ofDigits Limbs.radix natural.candidates + modulusValue =
      Nat.ofDigits Limbs.radix natural.digits + bound * natural.borrow := by
    rw [hcanonical.2.2.1, hcanonical.2.2.2]
    simpa [Limbs.value_of_represents hmodulus, hnaturalLength, bound] using hsubRaw
  have hsubValue : candidate + modulusValue =
      wrapped + bound * progress.borrow.toNat := by
    rw [hcandidateEq, hsubNatural, hnaturalValue, hborrowEq]
  have hborrowLe : progress.borrow.toNat ≤ 1 := by
    rw [hborrowEq]
    exact hmatch.2.2.2.2.2
  have hcandidateLt : candidate < bound := by
    exact BigHelpers.memoryLimbs_value_lt progress.memory 5120 count
  have hcandidate : Limbs.Represents progress.memory 5120 count candidate := by
    exact BigHelpers.represents_memoryLimbs_value progress.memory 5120 count
  have hcarryIff : progress.carry.toNat = 1 ↔ bound ≤ total := by
    apply BigHelpers.carry_eq_one_iff hvalueLt hcarryLe
    simpa [hwrappedEq] using haddValue
  have hborrowIff : progress.borrow.toNat = 0 ↔ modulusValue ≤ wrapped :=
    BigHelpers.borrow_eq_zero_iff hcandidateLt hmodulusBound hborrowLe hsubValue
  let useSub := UInt256.lor progress.carry (UInt256.isZero progress.borrow)
  have huseSubLe : useSub.toNat ≤ 1 :=
    BigHelpers.useSub_toNat_le_one progress.carry progress.borrow hcarryLe hborrowLe
  have huseSubIff : useSub.toNat = 1 ↔ modulusValue ≤ total :=
    BigHelpers.useSub_eq_one_iff progress.carry progress.borrow hmodulusBound rfl
      hcarryLe hborrowLe hcarryIff hborrowIff
  have hchosen : (if useSub.toNat = 1 then candidate else wrapped) =
      total % modulusValue := by
    rw [Limbs.mod_eq_cond_sub htotalLt]
    by_cases hlt : total < modulusValue
    · rw [if_pos hlt,
        if_neg (fun h => (Nat.not_le_of_lt hlt) (huseSubIff.mp h))]
      exact Nat.mod_eq_of_lt (by
        simpa [wrapped, bound, total] using
          (show total < bound from hlt.trans hmodulusBound))
    · have hge : modulusValue ≤ total := Nat.le_of_not_gt hlt
      rw [if_neg hlt, if_pos (huseSubIff.mpr hge)]
      let carryNat := progress.carry.toNat
      let borrowNat := progress.borrow.toNat
      have haddEq : wrapped + bound * carryNat = total := by
        simpa [carryNat, hwrappedEq] using haddValue
      have hsubEq : candidate + modulusValue =
          wrapped + bound * borrowNat := by simpa [borrowNat] using hsubValue
      have hcarryIff' : carryNat = 1 ↔ bound ≤ total := by
        simpa [carryNat] using hcarryIff
      have hborrowIff' : borrowNat = 0 ↔ modulusValue ≤ wrapped := by
        simpa [borrowNat] using hborrowIff
      have hcarryNat : carryNat ≤ 1 := hcarryLe
      have hborrowNat : borrowNat ≤ 1 := hborrowLe
      interval_cases carryNat <;> interval_cases borrowNat <;> omega
  have hresultFit : total % modulusValue < bound :=
    (Nat.mod_lt total (by omega)).trans hmodulusBound
  by_cases hmask : (0 - useSub).toNat = 0
  · have huseSubZero : useSub.toNat = 0 := by
      rcases Nat.eq_zero_or_pos useSub.toNat with h | h
      · exact h
      · exact absurd hmask (BigHelpers.mask_toNat_of_one useSub (by omega))
    have hchosen' : wrapped = total % modulusValue := by
      simpa [huseSubZero] using hchosen
    have hgoal : Limbs.Represents
        (BigHelpers.maskChoice progress.memory progress.activeWords
          (UInt256.ofNat dst) (0 - useSub) count).memory dst count
          (total % modulusValue) := by
      rw [BigHelpers.maskChoice_of_zero _ _ _ _ _ hmask, ← hchosen']
      exact hwrapped
    simpa [fusedReturned, fusedUseSub, progress, useSub, total] using hgoal
  · have huseSubOne : useSub.toNat = 1 := by
      rcases Nat.eq_zero_or_pos useSub.toNat with h | h
      · exact absurd (BigHelpers.mask_toNat_of_zero useSub h) hmask
      · omega
    have hchosen' : candidate = total % modulusValue := by
      simpa [huseSubOne] using hchosen
    have hdstNat : (UInt256.ofNat dst).toNat = dst := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
    have hsize : (BigHelpers.mcopySize count).toNat = 32 * count :=
      BigHelpers.mcopySize_toNat count (by omega)
    have hcopy := Mcopy.represents_mcopy progress.memory dst 5120 count
      candidate hcandidate
    rw [hchosen'] at hcopy
    have hgoal : Limbs.Represents
        (BigHelpers.maskChoice progress.memory progress.activeWords
          (UInt256.ofNat dst) (0 - useSub) count).memory dst count
          (total % modulusValue) := by
      rw [BigHelpers.maskChoice_of_pos _ _ _ _ _ hmask]
      simpa [hsize, hdstNat] using hcopy
    simpa [fusedReturned, fusedUseSub, progress, useSub, total] using hgoal

theorem safeTop_total_lt (s : State) (dst modulus count x modulusValue : Nat)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hmodulusFit : modulus + 32 * count < 2 ^ 256)
    (hdst : Limbs.Represents s.memory dst count x)
    (hmodulus : Limbs.Represents s.memory modulus count modulusValue)
    (hx : x < modulusValue)
    (hcarry : (topCarry s (UInt256.ofNat dst) count).toNat = 0)
    (hsafe : (topSum s (UInt256.ofNat dst) count).toNat <
      (modulusTop s (UInt256.ofNat modulus) count).toNat) :
    x + x < modulusValue := by
  have hcountPos : 0 < count := by
    by_contra h
    have : count = 0 := by omega
    subst count
    simp [Limbs.Represents, Limbs.memoryLimbs] at hmodulus
    omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : count ≠ 0)
  let topX := (MachineState.readWord s.memory (dst + 32 * n)).toNat
  let topM := (MachineState.readWord s.memory (modulus + 32 * n)).toNat
  let lowX := Nat.ofDigits Limbs.radix (Limbs.memoryLimbs s.memory dst n)
  let lowM := Nat.ofDigits Limbs.radix (Limbs.memoryLimbs s.memory modulus n)
  let scale := Limbs.radix ^ n
  have hxValue := Limbs.value_of_represents hdst
  have hmValue := Limbs.value_of_represents hmodulus
  rw [BigHelpers.memoryLimbs_succ, Nat.ofDigits_append] at hxValue hmValue
  simp only [Limbs.length_memoryLimbs, Nat.ofDigits_singleton] at hxValue hmValue
  have hlowX : lowX < scale := by
    exact BigHelpers.memoryLimbs_value_lt s.memory dst n
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have htopAddr :
      (UInt256.ofNat dst + topOffset (n + 1)).toNat =
        dst + 32 * n := by
    simpa [topOffset, BigHelpers.topOffset, hone] using
      BigHelpers.topOffset_toNat dst (n + 1) (by omega) hdstFit
  have hmodulusTopAddr :
      (UInt256.ofNat modulus + topOffset (n + 1)).toNat =
        modulus + 32 * n := by
    simpa [topOffset, BigHelpers.topOffset, hone] using
      BigHelpers.topOffset_toNat modulus (n + 1) (by omega) hmodulusFit
  have htopCarry : topX / 2 ^ 255 = 0 := by
    simp only [topCarry, topWord] at hcarry
    rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by omega),
      Nat.shiftRight_eq_div_pow, htopAddr] at hcarry
    exact hcarry
  have htopX : topX < 2 ^ 255 :=
    Nat.lt_of_div_eq_zero (by positivity) htopCarry
  have htopSum :
      (topSum s (UInt256.ofNat dst) (n + 1)).toNat = topX + topX + 1 := by
    have htwice : topX + topX < 2 ^ 256 := by omega
    have hplus : topX + topX + 1 < 2 ^ 256 := by omega
    have honeNat : (1 : UInt256).toNat = 1 := by decide
    simp only [topSum, topWord]
    rw [Challenge.EvmProof.Word.word_toNat_add,
      Challenge.EvmProof.Word.word_toNat_add,
      htopAddr, honeNat, Nat.mod_eq_of_lt htwice,
      Nat.mod_eq_of_lt hplus]
  have htopModulus :
      (modulusTop s (UInt256.ofNat modulus) (n + 1)).toNat = topM := by
    simp only [modulusTop]
    rw [hmodulusTopAddr]
  have htop : topX + topX + 1 < topM := by
    rw [← htopSum, ← htopModulus]
    exact hsafe
  have htwiceLow : lowX + lowX < scale + scale := Nat.add_lt_add hlowX hlowX
  calc
    x + x = (lowX + scale * topX) + (lowX + scale * topX) := by
      rw [hxValue]
    _ = (lowX + lowX) + scale * (topX + topX) := by ring
    _ < (scale + scale) + scale * (topX + topX) :=
      Nat.add_lt_add_right htwiceLow _
    _ = scale * (topX + topX + 2) := by ring
    _ ≤ scale * topM := Nat.mul_le_mul_left scale (by omega)
    _ ≤ lowM + scale * topM := Nat.le_add_left _ _
    _ = modulusValue := hmValue

theorem returned_represents_mod (s : State)
    (dst modulus count x modulusValue : Nat) (returnDest : UInt256)
    (rest : List UInt256)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hmodulusFit : modulus + 32 * count < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (hdstModulus : dst + 32 * count ≤ modulus ∨
      modulus + 32 * count ≤ dst)
    (hdstCandidate : dst + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ dst)
    (hmodulusCandidate : modulus + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ modulus)
    (hdst : Limbs.Represents s.memory dst count x)
    (hmodulus : Limbs.Represents s.memory modulus count modulusValue)
    (hx : x < modulusValue)
    (hmodulusBound : modulusValue < Limbs.radix ^ count) :
    Limbs.Represents
      (returned s (UInt256.ofNat dst) (UInt256.ofNat modulus)
        count returnDest rest).memory dst count ((x + x) % modulusValue) := by
  by_cases hcarry : (topCarry s (UInt256.ofNat dst) count).toNat = 0
  · by_cases hsafe :
        (topSum s (UInt256.ofNat dst) count).toNat <
          (modulusTop s (UInt256.ofNat modulus) count).toNat
    · let compared := topCompared s (UInt256.ofNat dst)
        (UInt256.ofNat modulus) count returnDest rest 1625
      have hadded := BigHelpers.addProgress_represents_wrapped s.memory
        compared.activeWords dst dst count 1 x x (by omega) hdstFit hdstFit
        (Or.inl rfl) hdst hdst
      have hlt := safeTop_total_lt s dst modulus count x modulusValue hdstFit
        hmodulusFit hdst hmodulus hx hcarry hsafe
      have hbound : x + x < Limbs.radix ^ count := hlt.trans hmodulusBound
      have hboundMod : (x + x) % Limbs.radix ^ count = x + x :=
        Nat.mod_eq_of_lt hbound
      have hmod : (x + x) % modulusValue = x + x := Nat.mod_eq_of_lt hlt
      have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
      simpa [returned, hcarry, hsafe, addOnlyReturned, compared, topCompared,
        topLoaded, hone, hboundMod, hmod, Nat.one_mul] using hadded
    · have hfused := fusedReturned_represents_mod
        (topCompared s (UInt256.ofNat dst) (UInt256.ofNat modulus)
          count returnDest rest 1618)
        dst modulus count x modulusValue returnDest rest hdstFit hmodulusFit
        hcandidateFit hdstModulus hdstCandidate hmodulusCandidate
        (by simpa [topCompared, topLoaded] using hdst)
        (by simpa [topCompared, topLoaded] using hmodulus)
        hx hmodulusBound
      simpa [returned, hcarry, hsafe] using hfused
  · have hfused := fusedReturned_represents_mod
      (topLoaded s (UInt256.ofNat dst) (UInt256.ofNat modulus)
        count returnDest rest 1618)
      dst modulus count x modulusValue returnDest rest hdstFit hmodulusFit
      hcandidateFit hdstModulus hdstCandidate hmodulusCandidate
      (by simpa [topLoaded] using hdst)
      (by simpa [topLoaded] using hmodulus)
      hx hmodulusBound
    simpa [returned, hcarry] using hfused

theorem fusedReturned_preserves_region (s : State)
    (dst modulus ptr count value : Nat) (returnDest : UInt256)
    (rest : List UInt256)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (hptrDst : dst + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ dst)
    (hptrCandidate : ptr + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ ptr)
    (hrep : Limbs.Represents s.memory ptr count value) :
    Limbs.Represents
      (fusedReturned s (UInt256.ofNat dst) (UInt256.ofNat modulus)
        count returnDest rest).memory ptr count value := by
  let progress := fusedProgress s.memory s.activeWords (UInt256.ofNat dst)
    (UInt256.ofNat modulus) count
  have hprogress : Limbs.Represents progress.memory ptr count value := by
    exact represents_fusedProgress_disjoint_region s.memory s.activeWords
      (UInt256.ofNat modulus) dst ptr count count value (by omega) hdstFit
      hcandidateFit hptrDst hptrCandidate hrep
  let useSub := fusedUseSub s (UInt256.ofNat dst) (UInt256.ofNat modulus) count
  by_cases hmask : (0 - useSub).toNat = 0
  · have hgoal : Limbs.Represents
        (BigHelpers.maskChoice progress.memory progress.activeWords
          (UInt256.ofNat dst) (0 - useSub) count).memory ptr count value := by
      rw [BigHelpers.maskChoice_of_zero _ _ _ _ _ hmask]
      exact hprogress
    simpa [fusedReturned, fusedUseSub, progress, useSub] using hgoal

  · have hdstNat : (UInt256.ofNat dst).toNat = dst := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hsize : (BigHelpers.mcopySize count).toNat = 32 * count :=
      BigHelpers.mcopySize_toNat count (by omega)
    have hcopy := Mcopy.represents_mcopy_disjoint_region progress.memory
      dst 5120 count ptr count value
      (by rcases hptrDst with h | h
          · exact Or.inr h
          · exact Or.inl h)
      hprogress
    have hgoal : Limbs.Represents
        (BigHelpers.maskChoice progress.memory progress.activeWords
          (UInt256.ofNat dst) (0 - useSub) count).memory ptr count value := by
      rw [BigHelpers.maskChoice_of_pos _ _ _ _ _ hmask]
      simpa [hsize, hdstNat] using hcopy
    simpa [fusedReturned, fusedUseSub, progress, useSub] using hgoal

theorem returned_preserves_region (s : State)
    (dst modulus ptr count value : Nat) (returnDest : UInt256)
    (rest : List UInt256)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (hptrDst : dst + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ dst)
    (hptrCandidate : ptr + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ ptr)
    (hrep : Limbs.Represents s.memory ptr count value) :
    Limbs.Represents
      (returned s (UInt256.ofNat dst) (UInt256.ofNat modulus)
        count returnDest rest).memory ptr count value := by
  by_cases hcarry : (topCarry s (UInt256.ofNat dst) count).toNat = 0
  · by_cases hsafe :
        (topSum s (UInt256.ofNat dst) count).toNat <
          (modulusTop s (UInt256.ofNat modulus) count).toNat
    · have hadd := BigHelpers.represents_addProgress_disjoint_region
        s.memory
        (topCompared s (UInt256.ofNat dst) (UInt256.ofNat modulus)
          count returnDest rest 1625).activeWords
        (UInt256.ofNat dst) (0 - 1) dst ptr count count value
        (by omega) hdstFit hptrDst hrep
      simpa [returned, hcarry, hsafe, addOnlyReturned, topCompared, topLoaded]
        using hadd
    · have hfused := fusedReturned_preserves_region
        (topCompared s (UInt256.ofNat dst) (UInt256.ofNat modulus)
          count returnDest rest 1618)
        dst modulus ptr count value returnDest rest hdstFit hcandidateFit
        hptrDst hptrCandidate (by simpa [topCompared, topLoaded] using hrep)
      simpa [returned, hcarry, hsafe] using hfused
  · have hfused := fusedReturned_preserves_region
      (topLoaded s (UInt256.ofNat dst) (UInt256.ofNat modulus)
        count returnDest rest 1618)
      dst modulus ptr count value returnDest rest hdstFit hcandidateFit
      hptrDst hptrCandidate (by simpa [topLoaded] using hrep)
    simpa [returned, hcarry] using hfused

@[simp] theorem returned_halt (s : State) (dst modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (returned s dst modulus count returnDest rest).halt = s.halt := by
  by_cases hcarry : (topCarry s dst count).toNat = 0
  · by_cases hsafe :
      (topSum s dst count).toNat < (modulusTop s modulus count).toNat
    · simp [returned, hcarry, hsafe, addOnlyReturned, topCompared, topLoaded]
    · simp [returned, hcarry, hsafe, fusedReturned, topCompared, topLoaded]
  · simp [returned, hcarry, fusedReturned, topLoaded]

@[simp] theorem returned_executionEnv (s : State) (dst modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (returned s dst modulus count returnDest rest).executionEnv =
      s.executionEnv := by
  by_cases hcarry : (topCarry s dst count).toNat = 0
  · by_cases hsafe :
      (topSum s dst count).toNat < (modulusTop s modulus count).toNat
    · simp [returned, hcarry, hsafe, addOnlyReturned, topCompared, topLoaded]
    · simp [returned, hcarry, hsafe, fusedReturned, topCompared, topLoaded]
  · simp [returned, hcarry, fusedReturned, topLoaded]

@[simp] theorem returned_pc (s : State) (dst modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (returned s dst modulus count returnDest rest).pc = returnDest := by
  by_cases hcarry : (topCarry s dst count).toNat = 0
  · by_cases hsafe :
      (topSum s dst count).toNat < (modulusTop s modulus count).toNat
    · simp [returned, hcarry, hsafe, addOnlyReturned]
    · simp [returned, hcarry, hsafe, fusedReturned]
  · simp [returned, hcarry, fusedReturned]

@[simp] theorem returned_stack (s : State) (dst modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (returned s dst modulus count returnDest rest).stack = rest := by
  by_cases hcarry : (topCarry s dst count).toNat = 0
  · by_cases hsafe :
      (topSum s dst count).toNat < (modulusTop s modulus count).toNat
    · simp [returned, hcarry, hsafe, addOnlyReturned]
    · simp [returned, hcarry, hsafe, fusedReturned]
  · simp [returned, hcarry, fusedReturned]

@[simp] theorem returned_gasAvailable (s : State) (dst modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (returned s dst modulus count returnDest rest).gasAvailable =
      s.gasAvailable := by
  simp only [returned]
  split
  next => split <;> rfl
  next => rfl

@[simp] theorem returned_returnData (s : State) (dst modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (returned s dst modulus count returnDest rest).returnData = s.returnData := by
  simp only [returned]
  split
  next => split <;> simp [addOnlyReturned, fusedReturned, topCompared, topLoaded]
  next => simp [fusedReturned, topLoaded]

@[simp] theorem returned_hReturn (s : State) (dst modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (returned s dst modulus count returnDest rest).hReturn = s.hReturn := by
  simp only [returned]
  split
  next => split <;> simp [addOnlyReturned, fusedReturned, topCompared, topLoaded]
  next => simp [fusedReturned, topLoaded]

@[simp] theorem returned_accountMap (s : State) (dst modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (returned s dst modulus count returnDest rest).accountMap = s.accountMap := by
  simp only [returned]
  split
  next => split <;> simp [addOnlyReturned, fusedReturned, topCompared, topLoaded]
  next => simp [fusedReturned, topLoaded]

@[simp] theorem returned_substate (s : State) (dst modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (returned s dst modulus count returnDest rest).substate = s.substate := by
  simp only [returned]
  split
  next => split <;> simp [addOnlyReturned, fusedReturned, topCompared, topLoaded]
  next => simp [fusedReturned, topLoaded]

@[simp] theorem returned_execLength (s : State) (dst modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (returned s dst modulus count returnDest rest).execLength = s.execLength := by
  simp only [returned]
  split
  next => split <;> simp [addOnlyReturned, fusedReturned, topCompared, topLoaded]
  next => simp [fusedReturned, topLoaded]

@[simp] theorem returned_callStack (s : State) (dst modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (returned s dst modulus count returnDest rest).callStack = s.callStack := by
  simp only [returned]
  split
  next => split <;> simp [addOnlyReturned, fusedReturned, topCompared, topLoaded]
  next => simp [fusedReturned, topLoaded]

theorem returned_memory_congr (s t : State) (dst modulus : UInt256)
    (count : Nat) (returnDestS returnDestT : UInt256)
    (restS restT : List UInt256)
    (hmemory : s.memory = t.memory) (hactive : s.activeWords = t.activeWords) :
    (returned s dst modulus count returnDestS restS).memory =
      (returned t dst modulus count returnDestT restT).memory := by
  have hcarry : topCarry s dst count = topCarry t dst count := by
    simp [topCarry, topWord, hmemory]
  have hsum : topSum s dst count = topSum t dst count := by
    simp [topSum, topWord, hmemory]
  have hmodulus : modulusTop s modulus count = modulusTop t modulus count := by
    simp [modulusTop, hmemory]
  by_cases hc : (topCarry s dst count).toNat = 0
  · have hct : (topCarry t dst count).toNat = 0 := by simpa [hcarry] using hc
    by_cases hs : (topSum s dst count).toNat < (modulusTop s modulus count).toNat
    · have hst : (topSum t dst count).toNat <
          (modulusTop t modulus count).toNat := by simpa [hsum, hmodulus] using hs
      simp [returned, hc, hct, hs, hst, addOnlyReturned, topCompared,
        topLoaded, hmemory, hactive]
    · have hst : ¬((topSum t dst count).toNat <
          (modulusTop t modulus count).toNat) := by simpa [hsum, hmodulus] using hs
      simp [returned, hc, hct, hs, hst, fusedReturned, fusedUseSub,
        topCompared, topLoaded, hmemory, hactive]
  · have hct : ¬((topCarry t dst count).toNat = 0) := by
      simpa [hcarry] using hc
    simp [returned, hc, hct, fusedReturned, fusedUseSub, topLoaded,
      hmemory, hactive]

theorem returned_activeWords_congr (s t : State) (dst modulus : UInt256)
    (count : Nat) (returnDestS returnDestT : UInt256)
    (restS restT : List UInt256)
    (hmemory : s.memory = t.memory) (hactive : s.activeWords = t.activeWords) :
    (returned s dst modulus count returnDestS restS).activeWords =
      (returned t dst modulus count returnDestT restT).activeWords := by
  have hcarry : topCarry s dst count = topCarry t dst count := by
    simp [topCarry, topWord, hmemory]
  have hsum : topSum s dst count = topSum t dst count := by
    simp [topSum, topWord, hmemory]
  have hmodulus : modulusTop s modulus count = modulusTop t modulus count := by
    simp [modulusTop, hmemory]
  by_cases hc : (topCarry s dst count).toNat = 0
  · have hct : (topCarry t dst count).toNat = 0 := by simpa [hcarry] using hc
    by_cases hs : (topSum s dst count).toNat < (modulusTop s modulus count).toNat
    · have hst : (topSum t dst count).toNat <
          (modulusTop t modulus count).toNat := by simpa [hsum, hmodulus] using hs
      simp [returned, hc, hct, hs, hst, addOnlyReturned, topCompared,
        topLoaded, hmemory, hactive]
    · have hst : ¬((topSum t dst count).toNat <
          (modulusTop t modulus count).toNat) := by simpa [hsum, hmodulus] using hs
      simp [returned, hc, hct, hs, hst, fusedReturned, fusedUseSub,
        topCompared, topLoaded, hmemory, hactive]
  · have hct : ¬((topCarry t dst count).toNat = 0) := by
      simpa [hcarry] using hc
    simp [returned, hc, hct, fusedReturned, fusedUseSub, topLoaded,
      hmemory, hactive]

end Challenge.Modexp.Submission.Proofs.Bytecode.BigDouble
