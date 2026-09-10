import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCachePrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheL1
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheL2

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCachePrograms

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache
open Challenge.Modexp.Submission.Proofs.Fast.CiosCached

theorem l1Mac0_eq : l1Mac0 = l1Program 8480 := rfl
theorem l1Mac1_eq : l1Mac1 = l1Program 8448 := rfl
theorem l1Mac2_eq : l1Mac2 = l1Program 8416 := rfl
theorem l1Mac3_eq : l1Mac3 = l1Program 8384 := rfl
theorem l1Mac4_eq : l1Mac4 = l1Program 8352 := rfl

theorem l1Mac5_eq : l1Mac5 = cachedL1Body ⟨2, by decide⟩ ++
    [.op (.Dup ⟨7, by decide⟩), .op .ADD] := rfl
theorem l1Mac6_eq : l1Mac6 = cachedL1Body ⟨1, by decide⟩ ++
    [.op (.Dup ⟨7, by decide⟩), .op .ADD] := rfl
theorem l1Mac7_eq : l1Mac7 = cachedL1Body ⟨0, by decide⟩ ++ [.op .POP] := rfl

theorem l2Mac0_eq : l2Mac0 = l2Program 192 8448 8480 := rfl
theorem l2Mac1_eq : l2Mac1 = l2Program 160 8416 8448 := rfl
theorem l2Mac2_eq : l2Mac2 = l2Program 128 8384 8416 := rfl
theorem l2Mac3_eq : l2Mac3 = l2Program 96 8352 8384 := rfl
theorem l2Mac4_eq : l2Mac4 = partialL2Body 64 8352 := rfl
theorem l2Mac5_eq : l2Mac5 = cachedL2Body ⟨1, by decide⟩ := rfl
theorem l2Mac6_eq : l2Mac6 = cachedL2Body ⟨0, by decide⟩ := rfl

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCachePrograms
