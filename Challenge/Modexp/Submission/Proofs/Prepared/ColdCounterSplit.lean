import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
import Challenge.Modexp.Submission.Proofs.Fast.Monpro
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace CycleSubmission.ColdCounterSplit
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
local notation "N" => UInt256.ofNat
def state (s : State) (pc : Nat) (stack : List UInt256) : State :=
 {s with pc := N pc,stack := stack}
theorem max_add (k : UInt256) : Monpro.maxWord+k = k-N 1 := by
 apply Word.word_ext
 rw [Word.word_toNat_add,Word.word_toNat_sub]
 have hm : Monpro.maxWord.toNat = 2^256-1 := by decide
 have h1 : (N 1).toNat=1 := by decide
 rw [hm,h1]
 congr 1
 omega
theorem zero_add (k : UInt256) : N 0+k=k := by
 apply Word.word_ext
 change (0+k.toNat)%2^256=k.toNat
 rw [Nat.zero_add]
 exact Nat.mod_eq_of_lt k.val.isLt


def tail : List Instr := [.op .JUMPDEST,.op .ADD]
def repairPrefix : List Instr := [.op (.Dup ⟨0,by decide⟩),.op .ISZERO,
 .op (.Swap ⟨0,by decide⟩),.op .NOT,.op (.Swap ⟨0,by decide⟩),.push 2 10995,.op .JUMPI]


theorem run_tail (s : State) (k : UInt256) (rest : List UInt256) (hc : rest.length≤1000) :
 runInstructions tail (state s 10995 (Monpro.maxWord::k::rest)) =
 some (state s 10997 ((k-N 1)::rest)) := by
 have cap (j : Nat) (hj : j≤10) : rest.length+j<1024 := by omega
 have h0 : rest.length<1024 := by omega
 have h1 : rest.length+1<1024 := by omega
 simp (disch := omega) [tail,runInstructions,Stepper.runInstr,state,max_add,h0,h1,
  Word.succ_ofNat_mod,Word.ofNat_add_mod,Nat.add_assoc,cap]
theorem run_repair_done (s : State) (k : UInt256) (rest : List UInt256)
 (hc : rest.length≤1000) (hj : Decode.isValidJumpDest s.executionEnv.code 10995=true) :
 runInstructions repairPrefix (state s 3510 (N 0::k::rest)) =
 some (state s 10995 (Monpro.maxWord::k::rest)) := by
 have cap (j : Nat) (hj : j≤10) : rest.length+j<1024 := by omega
 have hm : UInt256.lnot (N 0)=Monpro.maxWord := by decide
 simp (config := {maxSteps := 2000000}) (disch := omega) [repairPrefix,runInstructions,Stepper.runInstr,state,hm,hj,cap,Nat.add_assoc,
  UInt256.isTrue,UInt256.isZero,Word.literal_eq_ofNat,Word.word_toNat_ofNat,
  Word.succ_ofNat_mod,Word.ofNat_add_mod,List.getElem?_cons_zero,List.exchange]
theorem not_not (v : UInt256) : UInt256.lnot (UInt256.lnot v)=v := by
 apply Word.word_ext
 simp only [UInt256.lnot,Word.word_toNat_ofNat,UInt256.size]
 have hv : v.toNat<2^256 := v.val.isLt
 have hbound : 2^256-1-v.toNat<2^256 := by omega
 rw [Nat.mod_eq_of_lt hbound]
 have hh : 2^256-1-(2^256-1-v.toNat)=v.toNat := by omega
 rw [hh,Nat.mod_eq_of_lt hv]
theorem run_repair_go (s : State) (v k : UInt256) (rest : List UInt256)
 (hc : rest.length≤1000) (hv : v.toNat≠0) :
 runInstructions (repairPrefix++[.op .NOT]) (state s 3510 (v::k::rest)) =
 some (state s 3520 (v::k::rest)) := by
 have cap (j : Nat) (hj : j≤10) : rest.length+j<1024 := by omega
 simp (config := {maxSteps := 2000000}) (disch := omega) [repairPrefix,runInstructions,Stepper.runInstr,state,cap,Nat.add_assoc,
  UInt256.isTrue,UInt256.isZero,hv,not_not,Word.literal_eq_ofNat,Word.word_toNat_ofNat,
  Word.succ_ofNat_mod,Word.ofNat_add_mod,List.getElem?_cons_zero,List.exchange]
def coldPrefix : List Instr := [.op .JUMPDEST,.op .ADD,.op (.Dup ⟨0,by decide⟩),.op (.Dup ⟨2,by decide⟩),.op .JUMPI]
theorem run_cold_more (s : State) (k head : UInt256) (rest : List UInt256)
 (hc : rest.length≤1000) (hk : (k-N 1).toNat≠0)
 (hj : Decode.isValidJumpDest s.executionEnv.code head.toNat=true) :
 runInstructions coldPrefix (state s 10995 (Monpro.maxWord::k::head::rest)) =
 some ({s with pc := head,stack := (k-N 1)::head::rest}) := by
 have cap (j : Nat) (hj : j≤10) : rest.length+j<1024 := by omega
 have hzero : (Monpro.maxWord+k).toNat≠0 := by rw [max_add]; exact hk
 have hcond : (2^256-1+k.toNat)%2^256≠0 := by simpa [Word.word_toNat_add,Monpro.maxWord] using hzero
 simp (disch := omega) [coldPrefix,runInstructions,Stepper.runInstr,state,max_add,hj,hk,hcond,
  UInt256.isTrue,cap,List.getElem?_cons_zero,List.getElem?_cons_succ,
  Word.succ_ofNat_mod,Word.ofNat_add_mod,Nat.add_assoc]
 all_goals intro hz; exact False.elim (hcond hz)
theorem run_cold_last (s : State) (head : UInt256) (rest : List UInt256)
 (hc : rest.length≤1000) :
 runInstructions coldPrefix (state s 10995 (Monpro.maxWord::N 1::head::rest)) =
 some (state s 11000 (N 0::head::rest)) := by
 have cap (j : Nat) (hj : j≤10) : rest.length+j<1024 := by omega
 have hm : Monpro.maxWord+N 1=N 0 := by decide
 simp (disch := omega) [coldPrefix,runInstructions,Stepper.runInstr,state,hm,
  UInt256.isTrue,cap,List.getElem?_cons_zero,List.getElem?_cons_succ,
  Word.literal_eq_ofNat,Word.word_toNat_ofNat,
  Word.succ_ofNat_mod,Word.ofNat_add_mod,Nat.add_assoc]
end CycleSubmission.ColdCounterSplit
