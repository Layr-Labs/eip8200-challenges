import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheModel
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory
open Challenge.Modexp.Submission.Proofs.Fast.CiosCached

structure ReadOnlyCache where
  m0 : UInt256
  z0 : UInt256
  m32 : UInt256
  inv : UInt256
  tl : UInt256

def cacheTail (c : CachedMemory) (r : ReadOnlyCache) (dst ret : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [c.t0, c.t1, c.t2, r.m0, r.z0, r.m32, r.inv, r.tl, dst, ret] ++ rest

def rowFrame (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [pbi, paEnd, pbEnd, flag, negative32, allOnes] ++ cacheTail c r dst ret rest

def word (c : CachedMemory) (k : Fin 3) : UInt256 :=
  if k.val = 0 then c.t0 else if k.val = 1 then c.t1 else c.t2

def addr (k : Fin 3) : Nat := 8256+32*k.val

theorem word_eq_read (c : CachedMemory) (k : Fin 3) :
    word c k = MachineState.readWord c.virtual (addr k) := by
  fin_cases k <;> simp [word, addr]

def load1Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op .MLOAD, .op (.Dup ⟨9, by decide⟩)]

def cacheLoad1 (k : Fin 3) : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨11+k.val, by omega⟩)]

def cacheLoad2 (k : Fin 3) : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨11+k.val, by omega⟩)]

def cacheStore (k : Fin 3) : List Instr :=
  [.op (.Swap ⟨9+k.val, by omega⟩), .op .POP]

def sourceLoad2 (k : Fin 2) : List Instr :=
  [.op (.Dup ⟨13+k.val, by omega⟩), .op (.Dup ⟨9, by decide⟩)]

def sourceWord (r : ReadOnlyCache) (k : Fin 2) : UInt256 :=
  if k.val = 0 then r.z0 else r.m32

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache
