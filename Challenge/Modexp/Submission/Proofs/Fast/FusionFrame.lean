import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
import Challenge.EvmProof.Word
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
namespace Challenge.Modexp.Submission.Proofs.Fast.FusionFrame
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
-- Exact stack transformation of the selected runtime, split to keep simplification bounded.
def chunkA : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨9, by decide⟩),
   .push 2 256,
   .op .ADD,
   .op (.Swap ⟨13, by decide⟩),
   .op .POP]

def chunkB (head : UInt256) : List Instr :=
  [.op .POP,
   .push 3 1856,
   .op (.Dup ⟨9, by decide⟩),
   .op .SUB,
   .push 2 head,
   .op (.Swap ⟨1, by decide⟩),
   .op .POP,
   .push 1 224,
   .op (.Swap ⟨2, by decide⟩),
   .op .POP]

def chunkC (finish : UInt256) : List Instr :=
  [.push 2 288,
   .op (.Dup ⟨7, by decide⟩),
   .op .SUB,
   .op (.Swap ⟨3, by decide⟩),
   .op .POP,
   .push 2 256,
   .op (.Swap ⟨14, by decide⟩),
   .op .POP,
   .push 2 finish,
   .op (.Swap ⟨15, by decide⟩),
   .op .POP]

def frameProgram (head finish : UInt256) : List Instr :=
  (chunkA ++ chunkB head) ++ chunkC finish

variable (s : State) (p oldHead oldEnd ent neg mask ent2 inv m0 tl m96 m64 m32 aprev dst ret head finish : UInt256) (rest : List UInt256)

theorem run_a (hcap : rest.length ≤ 1005) :
    runInstructions (chunkA) { s with pc := 3469, stack := [p,oldHead,oldEnd,ent,neg,mask,ent2,inv,m0,tl,m96,m64,m32,aprev,dst,ret] ++ rest } =
      some { s with pc := 3477, stack := [p,oldHead,oldEnd,ent,neg,mask,ent2,inv,m0,tl,m96,m64,m32,tl+256,dst,ret] ++ rest } := by
  have h16 : rest.length + 16 < 1024 := by omega
  have h17 : rest.length + 17 < 1024 := by omega
  have h18 : rest.length + 18 < 1024 := by omega
  simp [chunkA, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, h16, h17, h18, Challenge.EvmProof.Word.word_add_comm]
  decide

theorem run_b (hcap : rest.length ≤ 1005) :
    runInstructions (chunkB head) { s with pc := 3477, stack := [p,oldHead,oldEnd,ent,neg,mask,ent2,inv,m0,tl,m96,m64,m32,tl+256,dst,ret] ++ rest } =
      some { s with pc := 3493, stack := [tl-1856,head,224,ent,neg,mask,ent2,inv,m0,tl,m96,m64,m32,tl+256,dst,ret] ++ rest } := by
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  have h17 : rest.length + 17 < 1024 := by omega
  have h18 : rest.length + 18 < 1024 := by omega
  simp [chunkB, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, h15, h16, h17, h18, Challenge.EvmProof.Word.word_add_comm]
  decide

theorem run_c (hcap : rest.length ≤ 1005) :
    runInstructions (chunkC finish) { s with pc := 3493, stack := [tl-1856,head,224,ent,neg,mask,ent2,inv,m0,tl,m96,m64,m32,tl+256,dst,ret] ++ rest } =
      some { s with pc := 3510, stack := [tl-1856,head,224,ent2-288,neg,mask,ent2,inv,m0,tl,m96,m64,m32,tl+256,256,finish] ++ rest } := by
  have h16 : rest.length + 16 < 1024 := by omega
  have h17 : rest.length + 17 < 1024 := by omega
  have h18 : rest.length + 18 < 1024 := by omega
  simp [chunkC, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, h16, h17, h18, Challenge.EvmProof.Word.word_add_comm]
  decide

theorem run_prefix (hcap : rest.length ≤ 1005) :
    runInstructions (frameProgram head finish) { s with pc := 3469, stack := [p,oldHead,oldEnd,ent,neg,mask,ent2,inv,m0,tl,m96,m64,m32,aprev,dst,ret] ++ rest } =
      some { s with pc := 3510, stack := [tl-1856,head,224,ent2-288,neg,mask,ent2,inv,m0,tl,m96,m64,m32,tl+256,256,finish] ++ rest } := by
  have ha := run_a (s := s) (p := p) (oldHead := oldHead) (oldEnd := oldEnd) (ent := ent) (neg := neg) (mask := mask) (ent2 := ent2) (inv := inv) (m0 := m0) (tl := tl) (m96 := m96) (m64 := m64) (m32 := m32) (aprev := aprev) (dst := dst) (ret := ret) (rest := rest) hcap
  have hb := run_b (s := s) (p := p) (oldHead := oldHead) (oldEnd := oldEnd) (ent := ent) (neg := neg) (mask := mask) (ent2 := ent2) (inv := inv) (m0 := m0) (tl := tl) (m96 := m96) (m64 := m64) (m32 := m32) (dst := dst) (ret := ret) (head := head) (rest := rest) hcap
  have hc := run_c (s := s) (ent := ent) (neg := neg) (mask := mask) (ent2 := ent2) (inv := inv) (m0 := m0) (tl := tl) (m96 := m96) (m64 := m64) (m32 := m32) (dst := dst) (ret := ret) (head := head) (finish := finish) (rest := rest) hcap
  exact runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _ ha hb) hc

end Challenge.Modexp.Submission.Proofs.Fast.FusionFrame
