import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

def ccbCallBlock (i : Nat) :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  match i with
  | 0 => [opAt 1824 .JUMPDEST, pushAt 1825 2 3006,
          opAt 1826 (.Dup ⟨1, by decide⟩), opAt 1827 (.Dup ⟨0, by decide⟩),
          opAt 1828 (.Dup ⟨0, by decide⟩), pushAt 1829 2 1939, opAt 1830 .JUMP]
  | 1 => [opAt 1831 .JUMPDEST, pushAt 1832 2 3017,
          opAt 1833 (.Dup ⟨1, by decide⟩), opAt 1834 (.Dup ⟨0, by decide⟩),
          opAt 1835 (.Dup ⟨0, by decide⟩), pushAt 1836 2 1939, opAt 1837 .JUMP]
  | 2 => [opAt 1838 .JUMPDEST, pushAt 1839 2 3028,
          opAt 1840 (.Dup ⟨1, by decide⟩), opAt 1841 (.Dup ⟨0, by decide⟩),
          opAt 1842 (.Dup ⟨0, by decide⟩), pushAt 1843 2 1939, opAt 1844 .JUMP]
  | 3 => [opAt 1845 .JUMPDEST, pushAt 1846 2 3039,
          opAt 1847 (.Dup ⟨1, by decide⟩), opAt 1848 (.Dup ⟨0, by decide⟩),
          opAt 1849 (.Dup ⟨0, by decide⟩), pushAt 1850 2 1939, opAt 1851 .JUMP]
  | 4 => [opAt 1852 .JUMPDEST, pushAt 1853 2 3050,
          opAt 1854 (.Dup ⟨1, by decide⟩), opAt 1855 (.Dup ⟨0, by decide⟩),
          opAt 1856 (.Dup ⟨0, by decide⟩), pushAt 1857 2 1939, opAt 1858 .JUMP]
  | 5 => [opAt 1859 .JUMPDEST, pushAt 1860 2 3061,
          opAt 1861 (.Dup ⟨1, by decide⟩), opAt 1862 (.Dup ⟨0, by decide⟩),
          opAt 1863 (.Dup ⟨0, by decide⟩), pushAt 1864 2 1939, opAt 1865 .JUMP]
  | 6 => [opAt 1866 .JUMPDEST, pushAt 1867 2 3072,
          opAt 1868 (.Dup ⟨1, by decide⟩), opAt 1869 (.Dup ⟨0, by decide⟩),
          opAt 1870 (.Dup ⟨0, by decide⟩), pushAt 1871 2 1939, opAt 1872 .JUMP]
  | 7 => [opAt 1873 .JUMPDEST, pushAt 1874 2 3083,
          opAt 1875 (.Dup ⟨1, by decide⟩), opAt 1876 (.Dup ⟨0, by decide⟩),
          opAt 1877 (.Dup ⟨0, by decide⟩), pushAt 1878 2 1939, opAt 1879 .JUMP]
  | _ => []

def blkCcbExit :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1880 .JUMPDEST, opAt 1881 .POP, opAt 1882 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
