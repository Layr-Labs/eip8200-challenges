import Challenge.Ripemd160.Submission.Proofs.Bytecode.Trace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word
import YulEvmCompiler.LowerDefs
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
/-!
# Direct trace of the RIPEMD-160 Boolean helper

The compiler frame for `f(j,x,y,z)` is `[j,x,y,z,0,returnDest]`.  This
candidate replaces the reference's four sequential switch tests with a
constant-time jump table: the dispatch block computes `caseBase + (j <<< 5)`
and jumps straight to the arm for `j`.  Each arm carries its own inlined
return sequence, so no shared cleanup block is entered.

The arms use the reference's exact operand order, so every arm produces the
same `Word.evmF` term the reference produced.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.BooleanFunctionTrace

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

private def helperPCs : List Nat :=
  [1671, 1672, 1673, 1675, 1676, 1679, 1680, 1681, 1682, 1683, 1684, 1685,
   1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695, 1696, 1697,
   1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709,
   1710, 1711, 1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721,
   1722, 1723, 1724, 1725, 1726, 1727, 1728, 1729, 1730, 1731, 1732, 1733,
   1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743, 1744, 1745,
   1746, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759, 1760, 1761,
   1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773,
   1774, 1775, 1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785,
   1786, 1787, 1788, 1789, 1790, 1791, 1792, 1793, 1794, 1795, 1796, 1797,
   1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807, 1808, 1809,
   1810, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823, 1824, 1825,
   1826, 1827, 1828, 1829]

@[simp] private theorem helperPC (i : Nat) (hlo : 831 ≤ i) (hhi : i ≤ 978) :
    Artifact.instructionPC i = helperPCs[i - 831]! := by
  interval_cases i <;> rfl

@[simp] private theorem helperRefPC (i : Nat) (hlo : 831 ≤ i) (hhi : i ≤ 978) :
    Artifact.submissionArtifact.instructionPC i = helperPCs[i - 831]! := by
  interval_cases i <;> rfl

@[simp] private theorem helperAdd (a b : Nat) (ha : a ≤ 1830) (hb : b ≤ 5) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  exact Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)

@[simp] private theorem helperSucc (a : Nat) (ha : a ≤ 1830) :
    (UInt256.ofNat a).succ = UInt256.ofNat (a + 1) := by
  exact Challenge.EvmProof.Word.succ_ofNat (by omega)

@[simp] private theorem helperToNat (a : Nat) (ha : a ≤ 1830) :
    (UInt256.ofNat a).toNat = a := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

@[simp] private theorem numeralToNat (a : Nat) :
    UInt256.toNat (OfNat.ofNat a : UInt256) = a % 2 ^ 256 := by
  exact Challenge.EvmProof.Word.word_toNat_ofNat a

@[simp] private theorem numeralSucc (a : Nat) (ha : a ≤ 1829) :
    (OfNat.ofNat a : UInt256).succ = UInt256.ofNat (a + 1) := by
  exact helperSucc a (by omega)

@[simp] private theorem numeralAdd (a b : Nat) (ha : a ≤ 1830) (hb : b ≤ 5) :
    (OfNat.ofNat a : UInt256) + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  exact helperAdd a b ha hb

/-! ## The dispatch block and the five arms -/

def dispatchPath : List Located :=
  [⟨831, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨832, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨833, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨834, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨835, .push ⟨2, by decide⟩ (UInt256.ofNat 1681), by rfl, by decide⟩,
   ⟨836, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨837, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def arm0 : List Located :=
  [⟨838, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨839, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨840, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨841, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨842, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨843, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨844, .op (.Swap ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨845, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨846, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨847, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨848, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨849, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨850, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨851, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def arm1 : List Located :=
  [⟨870, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨871, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨872, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨873, .op .NOT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨874, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨875, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨876, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨877, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨878, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨879, .op (.Swap ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨880, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨881, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨882, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨883, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨884, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨885, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨886, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def arm2 : List Located :=
  [⟨902, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨903, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨904, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨905, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨906, .op .NOT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨907, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨908, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨909, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨910, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨911, .op (.Swap ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨912, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨913, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨914, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨915, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨916, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨917, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨918, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def arm3 : List Located :=
  [⟨930, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨931, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨932, .op .NOT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨933, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨934, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨935, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨936, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨937, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨938, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨939, .op (.Swap ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨940, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨941, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨942, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨943, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨944, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨945, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨946, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def arm4 : List Located :=
  [⟨962, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨963, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨964, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨965, .op .NOT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨966, .op (.Dup ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨967, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨968, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨969, .op .XOR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨970, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨971, .op (.Swap ⟨4, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨972, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨973, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨974, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨975, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨976, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨977, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨978, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def casePath : Nat → List Located
  | 0 => dispatchPath ++ arm0
  | 1 => dispatchPath ++ arm1
  | 2 => dispatchPath ++ arm2
  | 3 => dispatchPath ++ arm3
  | _ => dispatchPath ++ arm4

def fEntry (s : State) (j : Nat) (x y z returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 0x687
    stack := [UInt256.ofNat j, x, y, z, 0, returnDest] ++ rest }

def fReturned (s : State) (j : Nat) (x y z returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := returnDest
    stack := Word.evmF j x y z :: rest }

@[simp] private theorem validCase0 :
    Decode.isValidJumpDest submissionBytecode 0x691 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 838 = 0x691 := by rfl
  rw [← hpc]
  exact Artifact.submissionArtifact.isValidJumpDest_index 838 (by rfl)

@[simp] private theorem validCase1 :
    Decode.isValidJumpDest submissionBytecode 0x6b1 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 870 = 0x6b1 := by rfl
  rw [← hpc]
  exact Artifact.submissionArtifact.isValidJumpDest_index 870 (by rfl)

@[simp] private theorem validCase2 :
    Decode.isValidJumpDest submissionBytecode 0x6d1 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 902 = 0x6d1 := by rfl
  rw [← hpc]
  exact Artifact.submissionArtifact.isValidJumpDest_index 902 (by rfl)

@[simp] private theorem validCase3 :
    Decode.isValidJumpDest submissionBytecode 0x6f1 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 930 = 0x6f1 := by rfl
  rw [← hpc]
  exact Artifact.submissionArtifact.isValidJumpDest_index 930 (by rfl)

@[simp] private theorem validCase4 :
    Decode.isValidJumpDest submissionBytecode 0x711 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 962 = 0x711 := by rfl
  rw [← hpc]
  exact Artifact.submissionArtifact.isValidJumpDest_index 962 (by rfl)

@[simp] private theorem dispatchTarget0 :
    UInt256.ofNat 1681 + EvmSemantics.UInt256.shiftLeft (UInt256.ofNat 0)
        (UInt256.ofNat 5) = UInt256.ofNat 1681 := by
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by norm_num) (by norm_num)
        (by norm_num),
      Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)]
  norm_num

@[simp] private theorem dispatchTarget1 :
    UInt256.ofNat 1681 + EvmSemantics.UInt256.shiftLeft (UInt256.ofNat 1)
        (UInt256.ofNat 5) = UInt256.ofNat 1713 := by
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by norm_num) (by norm_num)
        (by norm_num),
      Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)]
  norm_num

@[simp] private theorem dispatchTarget2 :
    UInt256.ofNat 1681 + EvmSemantics.UInt256.shiftLeft (UInt256.ofNat 2)
        (UInt256.ofNat 5) = UInt256.ofNat 1745 := by
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by norm_num) (by norm_num)
        (by norm_num),
      Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)]
  norm_num

@[simp] private theorem dispatchTarget3 :
    UInt256.ofNat 1681 + EvmSemantics.UInt256.shiftLeft (UInt256.ofNat 3)
        (UInt256.ofNat 5) = UInt256.ofNat 1777 := by
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by norm_num) (by norm_num)
        (by norm_num),
      Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)]
  norm_num

@[simp] private theorem dispatchTarget4 :
    UInt256.ofNat 1681 + EvmSemantics.UInt256.shiftLeft (UInt256.ofNat 4)
        (UInt256.ofNat 5) = UInt256.ofNat 1809 := by
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by norm_num) (by norm_num)
        (by norm_num),
      Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)]
  norm_num

set_option linter.unusedSimpArgs false in
theorem run_fCase (s : State) (j : Nat) (hj : j < 5)
    (x y z returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1008) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock (casePath j)
      (fEntry s j x y z returnDest rest) =
        some (fReturned s j x y z returnDest rest) := by
  have hcap (n : Nat) (hn : n ≤ 15) : rest.length + n < 1024 := by omega
  have hswap6 (a b c d e f : UInt256) (rho : List UInt256) :
      (a :: b :: c :: d :: e :: f :: rho).exchange 0 5 =
        some (f :: b :: c :: d :: e :: a :: rho) := by
    simpa using YulEvmCompiler.exchange_swap a f [b, c, d, e] rho
  have hswap2 (a b : UInt256) (rho : List UInt256) :
      (a :: b :: rho).exchange 0 1 = some (b :: a :: rho) := by
    simpa using YulEvmCompiler.exchange_swap a b ([] : List UInt256) rho
  interval_cases j <;>
    simp (config := { maxSteps := 500000 })
      [casePath, dispatchPath, arm0, arm1, arm2, arm3, arm4,
        helperPCs, Challenge.EvmProof.Stepper.runLocatedBlock,
        Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
        fEntry, fReturned, Word.evmF, Challenge.EvmProof.Word.mask32,
        hrun, hcode, hvalid, hcap, hswap6, hswap2, Nat.add_assoc,
        UInt256.eq, UInt256.isZero, UInt256.isTrue,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.succ_ofNat] <;> rfl

def gasSteps_fCase (s : State) (j : Nat) (hj : j < 5)
    (x y z returnDest : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1008) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (fEntry s j x y z returnDest rest)
      (fReturned s j x y z returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka (casePath j)
  · exact hcode
  · exact hfork
  · exact run_fCase s j hj x y z returnDest rest hstack hcode hrun hvalid
  · exact hrun
  · exact hnp

theorem fReturned_ofUInt32 (s : State) (j : Nat) (hj : j < 5)
    (x y z : UInt32) (returnDest : UInt256) (rest : List UInt256) :
    (fReturned s j (Challenge.EvmProof.Word.ofUInt32 x)
      (Challenge.EvmProof.Word.ofUInt32 y) (Challenge.EvmProof.Word.ofUInt32 z)
      returnDest rest).stack =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.f j x y z) :: rest := by
  simp [fReturned, Word.evmF_ofUInt32 j x y z hj]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.BooleanFunctionTrace
