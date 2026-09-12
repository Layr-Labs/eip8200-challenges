import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponents
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFused
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyExtra
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open CiosCachedMacCore CiosCached CiosCachedMidDefs WindowNibbleKernel Monpro

def extendedStack (carry mu bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [carry,mu,bi,pbi,pa,pb,flag,negative32,allOnes,target2,inv,m0,tl,m96,m64,m32,aEnd,dst,ret] ++ rest

def cacheAddress (slot : Fin 3) : Nat := 96-32*slot.val
def cacheWord (slot : Fin 3) (m96 m64 m32 : UInt256) : UInt256 :=
  if slot.val = 0 then m96 else if slot.val = 1 then m64 else m32

def extraLoad (slot : Fin 3) : List Instr :=
  [.op (.Dup ⟨13+slot.val, by omega⟩),
   .op (.Dup ⟨9, by decide⟩)]

theorem run_extraLoad (slot : Fin 3) (s : State)
    (pc carry mu bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions (extraLoad slot)
      (framed s pc (extendedStack carry mu bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s pc.succ.succ
      ([allOnes,cacheWord slot m96 m64 m32] ++
        extendedStack carry mu bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc19 : rest.length+19 < 1024 := by omega
  have hc20 : rest.length+20 < 1024 := by omega
  fin_cases slot <;>
    simp [extraLoad, cacheWord, extendedStack, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      framed, Nat.add_assoc, hc19, hc20]

structure ExtraCache (mem : ByteArray) (m96 m64 m32 : UInt256) : Prop where
  word96 : m96 = MachineState.readWord mem 96
  word64 : m64 = MachineState.readWord mem 64
  word32 : m32 = MachineState.readWord mem 32

theorem ExtraCache.of_preserved {mem mem' : ByteArray} {m96 m64 m32 : UInt256}
    (hc : ExtraCache mem m96 m64 m32)
    (h96 : MachineState.readWord mem' 96 = MachineState.readWord mem 96)
    (h64 : MachineState.readWord mem' 64 = MachineState.readWord mem 64)
    (h32 : MachineState.readWord mem' 32 = MachineState.readWord mem 32) :
    ExtraCache mem' m96 m64 m32 := ⟨hc.word96.trans h96.symm,hc.word64.trans h64.symm,hc.word32.trans h32.symm⟩

theorem ExtraCache.l1 {mem : ByteArray} {m96 m64 m32 : UInt256}
    (hc : ExtraCache mem m96 m64 m32) (bi : UInt256) (pa n j : Nat) (hn : n ≤ 32) :
    ExtraCache (l1Step mem bi pa n j).memory m96 m64 m32 :=
  hc.of_preserved (readWord_l1Step mem bi pa n 96 j hn (Or.inl (by decide)))
    (readWord_l1Step mem bi pa n 64 j hn (Or.inl (by decide)))
    (readWord_l1Step mem bi pa n 32 j hn (Or.inl (by decide)))

theorem ExtraCache.l2 {mem : ByteArray} {m96 m64 m32 : UInt256}
    (hc : ExtraCache mem m96 m64 m32) (mu c0 : UInt256) (n k : Nat) (hn : n ≤ 32) :
    ExtraCache (l2Step mem mu c0 n k).memory m96 m64 m32 :=
  hc.of_preserved (readWord_l2Step mem mu c0 n 96 k hn (Or.inl (by decide)))
    (readWord_l2Step mem mu c0 n 64 k hn (Or.inl (by decide)))
    (readWord_l2Step mem mu c0 n 32 k hn (Or.inl (by decide)))

theorem ExtraCache.rows {mem : ByteArray} {m96 m64 m32 : UInt256}
    (hc : ExtraCache mem m96 m64 m32) (pa pb n i : Nat) (hn : n ≤ 32) :
    ExtraCache (rowsMem mem pa pb n i) m96 m64 m32 :=
  hc.of_preserved (readWord_rowsMem mem pa pb n 96 hn (Or.inl (by decide)) i)
    (readWord_rowsMem mem pa pb n 64 hn (Or.inl (by decide)) i)
    (readWord_rowsMem mem pa pb n 32 hn (Or.inl (by decide)) i)

theorem ExtraCache.middle {mem : ByteArray} {m96 m64 m32 : UInt256}
    (hc : ExtraCache mem m96 m64 m32) (c : UInt256) :
    ExtraCache (Monpro.midMem mem c) m96 m64 m32 :=
  hc.of_preserved
    (CiosCachedMidMemory.read_mid mem c 96 (Or.inl (by decide)))
    (CiosCachedMidMemory.read_mid mem c 64 (Or.inl (by decide)))
    (CiosCachedMidMemory.read_mid mem c 32 (Or.inl (by decide)))

theorem ExtraCache.zeroed {mem : ByteArray} {m96 m64 m32 : UInt256}
    (hc : ExtraCache mem m96 m64 m32) (s : State) (n : Nat) (hn : n ≤ 32) :
    ExtraCache (mpZeroed s mem n) m96 m64 m32 :=
  hc.of_preserved
    (readWord_mpZeroed s mem n 96 hn (Or.inl (by decide)))
    (readWord_mpZeroed s mem n 64 hn (Or.inl (by decide)))
    (readWord_mpZeroed s mem n 32 hn (Or.inl (by decide)))

theorem ExtraCache.choose {mem : ByteArray} {m96 m64 m32 : UInt256}
    (hc : ExtraCache mem m96 m64 m32) (slot : Fin 3) :
    (cacheWord slot m96 m64 m32) = MachineState.readWord mem (cacheAddress slot) := by
  fin_cases slot
  · exact hc.word96
  · exact hc.word64
  · exact hc.word32

def extraProgram (slot : Fin 3) (tl ts : UInt256) : List Instr :=
  extraLoad slot ++ CiosCached.macFusedProgram tl ts

theorem run_extraStep (slot : Fin 3) (template : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 : UInt256) (n k : Nat) (x loadAddr storeAddr : UInt256)
    (hx : x.toNat = 32*(n-2-k))
    (hselect : x.toNat = cacheAddress slot)
    (hloadAddr : loadAddr.toNat = 2112+32*(n-2-k))
    (hstoreAddr : storeAddr.toNat = 2112+32*(n-1-k))
    (pbi paEnd pbEnd flag target2 cachedTL inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 998)
    (hactive : 93 ≤ template.activeWords.toNat) (hn : n ≤ 32) (hk : k+1 < n)
    (hc : ExtraCache mem m96 m64 m32) :
    runInstructions (extraProgram slot loadAddr storeAddr)
      (CiosCachedL2.state template pc mem bi mu c0 n k pbi paEnd pbEnd flag target2 inv
        (m0 :: cachedTL :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (CiosCachedL2.state template (pc+UInt256.ofNat 34) mem bi mu c0 n (k+1)
      pbi paEnd pbEnd flag target2 inv (m0 :: cachedTL :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (2112+32*(n-2-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hactW : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (2112+32*(n-1-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  let st : State := { template with memory := (l2Step mem mu c0 n k).memory }
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat loadAddr.toNat 32) =
      st.activeWords := by simpa only [st,hloadAddr] using hactT
  have hW : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat storeAddr.toNat 32) =
      st.activeWords := by simpa only [st,hstoreAddr] using hactW
  have hvalue : (cacheWord slot m96 m64 m32) = MachineState.readWord st.memory x.toNat := by
    rw [hselect]
    exact (hc.l2 mu c0 n k hn).choose slot
  have hl := run_extraLoad slot st pc (l2Step mem mu c0 n k).carry mu bi
    pbi paEnd pbEnd flag target2 cachedTL inv m0 aEnd m96 m64 m32 dst ret rest hrest
  rw [hvalue,allOnes_value] at hl
  have hpc2 : pc.succ.succ = pc+UInt256.ofNat 2 := by
    simp [succ_eq_add,word_add_assoc,Challenge.EvmProof.Word.ofNat_add_mod]
  rw [hpc2] at hl
  have hf := CiosCachedFused.run_fused st (pc+UInt256.ofNat 2)
    (MachineState.readWord st.memory x.toNat) mu (l2Step mem mu c0 n k).carry loadAddr storeAddr
    ([bi,pbi,paEnd,pbEnd,flag,negative32,allOnes,target2,inv,m0] ++
      (cachedTL :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))
    (by simp only [List.length_append,List.length_cons,List.length_nil]; omega) hT hW
  have hall := runInstructions_append_some _ _ _ _ _ hl hf
  have hpc : (pc+UInt256.ofNat 2)+UInt256.ofNat 32 = pc+UInt256.ofNat 34 := by
    simp [word_add_assoc,Challenge.EvmProof.Word.ofNat_add_mod]
  change runInstructions (extraLoad slot ++ CiosCached.macFusedProgram loadAddr storeAddr) _ = _
  simpa only [st,CiosCachedL2.state,framed,extendedStack,l2Step,hx,hloadAddr,hstoreAddr,hpc,
    List.cons_append,List.nil_append] using hall


end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyExtra
