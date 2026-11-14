import Challenge.Modexp.Submission.Proofs.CRT.CRTPacking
import Challenge.EvmProof.Memory
import YulEvmCompiler.BytesLemmas
set_option maxHeartbeats 2000000
set_option maxRecDepth 40000
namespace LowOverlapPackingArithmetic
open HistoricalSearch.MixedMontgomery HistoricalSearch.CRTPacking
theorem weighted_byte (n j r : Nat) (d : Nat → Nat)
 (hj : j < n) (hr : r < 30) (hd : ∀ k < n,d k < 256^30) :
 weighted (256^30) n d / 256^(30*j+r) % 256 = d j / 256^r % 256 := by
 have hp : (256:Nat)^(30*j+r) = (256^30)^j*256^r := by
  rw [Nat.pow_add,← Nat.pow_mul]
 rw [hp,← Nat.div_div_eq_div_mul,weighted_div _ n j d (by positivity) (by omega) hd]
 have hn : n-j = (n-j-1)+1 := by omega
 rw [hn,weightedHead]
 simp only [Nat.add_zero]
 have hb : (256:Nat)^30 = 256^r*(256*256^(29-r)) := by
  calc
   (256:Nat)^30 = 256^(r+(1+(29-r))) := by congr 1; omega
   _ = 256^r*(256*256^(29-r)) := by rw [Nat.pow_add,Nat.pow_add,Nat.pow_one]
 rw [hb]
 rw [Nat.mul_assoc]
 rw [Nat.add_mul_div_left _ _ (by positivity : 0 < (256:Nat)^r),Nat.add_mod]
 simp [Nat.mul_mod]
#print axioms weighted_byte
end LowOverlapPackingArithmetic
namespace LowOverlapPackingMemory
open EvmSemantics Challenge.EvmProof.Memory
open YulEvmCompiler.BytesLemmas
def store (mem : ByteArray) (ptr : Nat) (a : UInt256) : ByteArray :=
 MachineState.writeBytes mem (Data.Bytes.natToBytesPadded a.toNat 32) ptr
def memory9 (mem : ByteArray) (a : Nat → UInt256) : ByteArray :=
 (store (store (store (store (store (store (store (store (store mem 240 (a 0)) 210 (a 1)) 180 (a 2)) 150 (a 3)) 120 (a 4)) 90 (a 5)) 60 (a 6)) 30 (a 7)) 0 (a 8))
theorem byte9 (mem : ByteArray) (a : Nat → UInt256) (i : Nat) (hi : i < 256) :
 (memory9 mem a)[16+i]?.getD 0 =
 (Data.Bytes.natToBytesPadded (a ((255-i)/30)).toNat 32)[31-(255-i)%30]?.getD 0 := by
 have hj : (255-i)/30 < 9 := by omega
 generalize he : (255-i)/30 = j at *
 interval_cases j <;>
  simp (disch := omega) only [memory9,store,MachineState.writeBytes_getElem?_getD,natToBytesPadded_size,if_pos,if_neg]
 all_goals (congr 2; omega)
#print axioms byte9
def memory5 (mem : ByteArray) (a : Nat → UInt256) : ByteArray :=
 (store (store (store (store (store mem 120 (a 0)) 90 (a 1)) 60 (a 2)) 30 (a 3)) 0 (a 4))
theorem byte5 (mem : ByteArray) (a : Nat → UInt256) (i : Nat) (hi : i < 128) :
 (memory5 mem a)[24+i]?.getD 0 =
 (Data.Bytes.natToBytesPadded (a ((127-i)/30)).toNat 32)[31-(127-i)%30]?.getD 0 := by
 have hj : (127-i)/30 < 5 := by omega
 generalize he : (127-i)/30 = j at *
 interval_cases j <;>
  simp (disch := omega) only [memory5,store,MachineState.writeBytes_getElem?_getD,natToBytesPadded_size,if_pos,if_neg]
 all_goals (congr 2; omega)
#print axioms byte5
theorem returned9 (mem : ByteArray) (a : Nat → UInt256)
 (ha : ∀ k < 9,(a k).toNat < 256^30) :
 MachineState.readPadded (memory9 mem a) 16 256 =
 Data.Bytes.natToBytesPadded (HistoricalSearch.MixedMontgomery.weighted (256^30) 9 (fun k => (a k).toNat)) 256 := by
 apply ByteArray.ext_getElem
 · simp [natToBytesPadded_size]
 · intro i hia hib
   have hi : i < 256 := by simpa only [readPadded_size] using hia
   rw [← getD0_eq_getElem _ _ hia,← getD0_eq_getElem _ _ hib,
     readPadded_getElem?_getD,if_pos hi,byte9 mem a i hi]
   have hr : (255-i)%30 < 30 := Nat.mod_lt _ (by decide)
   have hk : 31-(255-i)%30 < 32 := by omega
   rw [natToBytesPadded_getElem?_getD _ 32 _ hk,
     natToBytesPadded_getElem?_getD _ 256 _ hi]
   have he : 32-1-(31-(255-i)%30) = (255-i)%30 := by omega
   rw [he]
   congr 1
   have hj : (255-i)/30 < 9 := by omega
   have hw := LowOverlapPackingArithmetic.weighted_byte 9 ((255-i)/30) ((255-i)%30)
     (fun k => (a k).toNat) hj hr ha
   have hexp : 30*((255-i)/30)+(255-i)%30 = 255-i := by omega
   simpa only [hexp] using hw.symm
#print axioms returned9
theorem returned5 (mem : ByteArray) (a : Nat → UInt256)
 (ha : ∀ k < 5,(a k).toNat < 256^30) :
 MachineState.readPadded (memory5 mem a) 24 128 =
 Data.Bytes.natToBytesPadded (HistoricalSearch.MixedMontgomery.weighted (256^30) 5 (fun k => (a k).toNat)) 128 := by
 apply ByteArray.ext_getElem
 · simp [natToBytesPadded_size]
 · intro i hia hib
   have hi : i < 128 := by simpa only [readPadded_size] using hia
   rw [← getD0_eq_getElem _ _ hia,← getD0_eq_getElem _ _ hib,
     readPadded_getElem?_getD,if_pos hi,byte5 mem a i hi]
   have hr : (127-i)%30 < 30 := Nat.mod_lt _ (by decide)
   have hk : 31-(127-i)%30 < 32 := by omega
   rw [natToBytesPadded_getElem?_getD _ 32 _ hk,
     natToBytesPadded_getElem?_getD _ 128 _ hi]
   have he : 32-1-(31-(127-i)%30) = (127-i)%30 := by omega
   rw [he]
   congr 1
   have hj : (127-i)/30 < 5 := by omega
   have hw := LowOverlapPackingArithmetic.weighted_byte 5 ((127-i)/30) ((127-i)%30)
     (fun k => (a k).toNat) hj hr ha
   have hexp : 30*((127-i)/30)+(127-i)%30 = 127-i := by omega
   simpa only [hexp] using hw.symm
#print axioms returned5
end LowOverlapPackingMemory
