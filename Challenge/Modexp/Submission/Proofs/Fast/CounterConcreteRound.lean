import Challenge.Modexp.Submission.Proofs.Fast.CounterCommutation
import Challenge.Modexp.Submission.Proofs.Fast.CounterLoopBridge
import Challenge.Modexp.Submission.Proofs.Fast.CounterMemorySize
import Challenge.Modexp.Submission.Proofs.Fast.R4Loop

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace CounterConcreteRoundProof

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks
open Challenge.Modexp.Submission.Proofs.Fast.LazySquareMemory
open Monpro SquareModel SquareResult CarryRowModel
open CounterCommutationPrototype

def rawR4Round (mem : ByteArray) : ByteArray :=
  LazyCsub.resultMemory (R4Bridge.rows4 mem) 4 2368

def rawR8Round (s : State) (mem : ByteArray) : ByteArray :=
  LazyCsub.resultMemory
    (SquareResult.sqRowsCarry (Monpro.mpZeroed s mem 8) 8 8) 8 2368

theorem r4_csSrc_extent (mem : ByteArray) (a mm : Nat)
    (ha : Model.FastRepresents mem 2368 4 a)
    (hm : Model.FastRepresents mem 0 4 mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    (Csub.csSrc (R4Bridge.rows4 mem) 4 4).toNat + 32 * 4 ≤ 2624 := by
  have htn := r4_tn_le_one mem a mm ha hm hmpos hminv
  have hstep := Csub.csStep_readWord_disjoint (R4Bridge.rows4 mem) 4 2080
    (by norm_num) (Or.inr (by omega)) 4 le_rfl
  have htn' :
      (MachineState.readWord (Csub.csStep (R4Bridge.rows4 mem) 4 4).memory 2080).toNat ≤ 1 := by
    rw [hstep]
    exact htn
  exact csSrc_extent_of_top_le_one (R4Bridge.rows4 mem) 4 (by norm_num) htn'

theorem r8_csSrc_extent (s : State) (mem : ByteArray) (a mm : Nat)
    (ha : Model.FastRepresents mem 2368 8 a)
    (hm : Model.FastRepresents mem 0 8 mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem 224).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    (Csub.csSrc
      (SquareResult.sqRowsCarry (Monpro.mpZeroed s mem 8) 8 8) 8 8).toNat +
        32 * 8 ≤ 2624 := by
  have htn := SquareLoopMem.tn_le_one s mem 6 a mm (by norm_num) (Or.inr rfl)
    ha hm hmpos hminv
  have hstep := Csub.csStep_readWord_disjoint
    (SquareResult.sqRowsCarry (Monpro.mpZeroed s mem 8) 8 8) 8 2080
    (by norm_num) (Or.inr (by omega)) 8 le_rfl
  have htn' :
      (MachineState.readWord
        (Csub.csStep (SquareResult.sqRowsCarry (Monpro.mpZeroed s mem 8) 8 8) 8 8).memory
        2080).toNat ≤ 1 := by
    rw [hstep]
    exact htn
  exact csSrc_extent_of_top_le_one
    (SquareResult.sqRowsCarry (Monpro.mpZeroed s mem 8) 8 8) 8 (by norm_num) htn'

theorem rawR4Round_countMem_comm (mem : ByteArray) (c a mm : Nat)
    (ha : Model.FastRepresents mem 2368 4 a)
    (hm : Model.FastRepresents mem 0 4 mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    Challenge.Modexp.Submission.Proofs.Fast.R4Loop.r4Round c mem =
      SquareLoopBlocks.countMem (rawR4Round mem) c := by
  have hsrc := r4_csSrc_extent mem a mm ha hm hmpos hminv
  have hcomm := lazyResultMemory_countMem_comm (R4Bridge.rows4 mem) c 4 2368
    (by norm_num) (by norm_num) hsrc (by norm_num)
  unfold Challenge.Modexp.Submission.Proofs.Fast.R4Loop.r4Round rawR4Round
  exact hcomm

theorem rawR8Round_countMem_comm (s : State) (mem : ByteArray) (c a mm : Nat)
    (ha : Model.FastRepresents mem 2368 8 a)
    (hm : Model.FastRepresents mem 0 8 mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem 224).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    SquareLoopMem.sqRound s 8 c mem =
      SquareLoopBlocks.countMem (rawR8Round s mem) c := by
  let rows := SquareResult.sqRowsCarry (Monpro.mpZeroed s mem 8) 8 8
  have hsrc := r8_csSrc_extent s mem a mm ha hm hmpos hminv
  have hcomm := lazyResultMemory_countMem_comm rows c 8 2368
    (by norm_num) (by norm_num) hsrc (by norm_num)
  unfold SquareLoopMem.sqRound rawR8Round
  exact hcomm

theorem mpZeroed_countMem_comm_n (s : State) (mem : ByteArray) (c n : Nat)
    (hn : n ≤ 8) :
    Monpro.mpZeroed s (SquareLoopBlocks.countMem mem c) n =
      SquareLoopBlocks.countMem (Monpro.mpZeroed s mem n) c := by
  unfold Monpro.mpZeroed
  apply CounterCommutationPrototype.countMem_writeBytes_comm
  · rw [Challenge.EvmProof.Memory.readPadded_size]
    omega
  · rw [Challenge.EvmProof.Memory.readPadded_size]
    omega

theorem rawR4Round_countMem_input_comm (mem : ByteArray) (c a mm : Nat)
    (ha : Model.FastRepresents mem 2368 4 a)
    (hm : Model.FastRepresents mem 0 4 mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    rawR4Round (SquareLoopBlocks.countMem mem c) =
      SquareLoopBlocks.countMem (rawR4Round mem) c := by
  have hsrc := r4_csSrc_extent mem a mm ha hm hmpos hminv
  unfold rawR4Round
  rw [CounterCommutationPrototype.rows4_countMem_comm]
  exact lazyResultMemory_countMem_comm (R4Bridge.rows4 mem) c 4 2368
    (by norm_num) (by norm_num) hsrc (by norm_num)

theorem rawR8Round_countMem_input_comm (s : State) (mem : ByteArray) (c a mm : Nat)
    (ha : Model.FastRepresents mem 2368 8 a)
    (hm : Model.FastRepresents mem 0 8 mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem 224).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    rawR8Round s (SquareLoopBlocks.countMem mem c) =
      SquareLoopBlocks.countMem (rawR8Round s mem) c := by
  have hsrc := r8_csSrc_extent s mem a mm ha hm hmpos hminv
  unfold rawR8Round
  rw [mpZeroed_countMem_comm_n s mem c 8 (by norm_num),
    CounterCommutationPrototype.sqRowsCarry_countMem_comm _ c 8 8 (by norm_num)
      (by norm_num)]
  exact lazyResultMemory_countMem_comm
    (SquareResult.sqRowsCarry (Monpro.mpZeroed s mem 8) 8 8) c 8 2368
    (by norm_num) (by norm_num) hsrc (by norm_num)

theorem r4Round_countMem_input (mem : ByteArray) (c d : Nat) :
    R4Loop.r4Round d (SquareLoopBlocks.countMem mem c) =
      R4Loop.r4Round d mem := by
  unfold R4Loop.r4Round
  rw [CounterCommutationPrototype.rows4_countMem_comm,
    CounterLoopBridge.countMem_overwrite]

theorem sqRound_countMem_input (s : State) (mem : ByteArray) (c d : Nat) :
    SquareLoopMem.sqRound s 8 d (SquareLoopBlocks.countMem mem c) =
      SquareLoopMem.sqRound s 8 d mem := by
  unfold SquareLoopMem.sqRound
  rw [mpZeroed_countMem_comm_n s mem c 8 (by norm_num),
    CounterCommutationPrototype.sqRowsCarry_countMem_comm _ c 8 8 (by norm_num)
      (by norm_num), CounterLoopBridge.countMem_overwrite]

theorem r4RunMem_countMem (mem : ByteArray) (k c a mm : Nat)
    (hk : 1 ≤ k) (ha : Model.FastRepresents mem 2368 4 a)
    (hm : Model.FastRepresents mem 0 4 mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    R4Loop.r4RunMem k (SquareLoopBlocks.countMem mem c) =
      R4Loop.r4RunMem k mem := by
  have _hvalid := And.intro ha (And.intro hm (And.intro hmpos hminv))
  cases k with
  | zero => omega
  | succ j =>
      rw [R4Loop.r4RunMem_succ, R4Loop.r4RunMem_succ,
        r4Round_countMem_input]

theorem sqRunMem_countMem (s : State) (mem : ByteArray) (k c a mm : Nat)
    (hk : 1 ≤ k) (ha : Model.FastRepresents mem 2368 8 a)
    (hm : Model.FastRepresents mem 0 8 mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem 224).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    SquareLoopMem.sqRunMem s 8 k (SquareLoopBlocks.countMem mem c) =
      SquareLoopMem.sqRunMem s 8 k mem := by
  have _hvalid := And.intro ha (And.intro hm (And.intro hmpos hminv))
  cases k with
  | zero => omega
  | succ j =>
      rw [SquareLoopMem.sqRunMem_succ, SquareLoopMem.sqRunMem_succ,
        sqRound_countMem_input]

theorem rawR4Round_size_of_s32 (mem : ByteArray)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * 4)) :
    (rawR4Round mem).size = mem.size := by
  have hmem := CounterLoopBridge.physicalSize_of_s32 mem 4 (by norm_num) (by norm_num) hs32
  have hrows := rows4_size_of_mem_size mem hmem
  have hlazy := lazyResultMemory_size_of_mem_size (R4Bridge.rows4 mem) 4 2368
    (by norm_num) (by rw [hrows]; exact hmem) (by norm_num)
  exact hlazy.trans hrows

theorem rawR8Round_size_of_s32 (s : State) (mem : ByteArray)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * 8)) :
    (rawR8Round s mem).size = mem.size := by
  have hmem := CounterLoopBridge.physicalSize_of_s32 mem 8 (by norm_num) (by norm_num) hs32
  have hzero : (Monpro.mpZeroed s mem 8).size = mem.size := by
    unfold Monpro.mpZeroed
    exact writeBytes_readPadded_size_of_le _ _ _ _ _ (by omega)
  have hzero_mem : 2656 ≤ (Monpro.mpZeroed s mem 8).size := by
    rw [hzero]
    exact hmem
  have hrows := CounterMemoryPrototype.size_sqRowsCarry
    (Monpro.mpZeroed s mem 8) 8 (by norm_num) hzero_mem
  have hlazy := lazyResultMemory_size_of_mem_size
    (SquareResult.sqRowsCarry (Monpro.mpZeroed s mem 8) 8 8) 8 2368
    (by norm_num) (by rw [hrows]; exact hzero_mem) (by norm_num)
  exact hlazy.trans (hrows.trans hzero)

end CounterConcreteRoundProof
