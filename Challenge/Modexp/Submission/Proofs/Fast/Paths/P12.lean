import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 12 (instructions 1627..1682). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1627..1661, pc 2500..2634. -/
def blk1627 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1875 .JUMPDEST,
   opAt 1876 (.Dup ⟨1, by decide⟩),
   opAt 1877 .MLOAD,
   opAt 1878 (.Dup ⟨3, by decide⟩),
   opAt 1879 .MLOAD,
   opAt 1880 (.Dup ⟨1, by decide⟩),
   opAt 1881 .ADD,
   opAt 1882 (.Swap ⟨0, by decide⟩),
   opAt 1883 (.Dup ⟨1, by decide⟩),
   opAt 1884 .LT,
   opAt 1885 (.Swap ⟨0, by decide⟩),
   opAt 1886 (.Dup ⟨5, by decide⟩),
   opAt 1887 .ADD,
   opAt 1888 (.Swap ⟨4, by decide⟩),
   opAt 1889 (.Dup ⟨5, by decide⟩),
   opAt 1890 .LT,
   opAt 1891 .OR,
   opAt 1892 (.Swap ⟨3, by decide⟩),
   opAt 1893 (.Dup ⟨1, by decide⟩),
   opAt 1894 .MSTORE,
   pushAt 1895 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1896 .ADD,
   opAt 1897 (.Swap ⟨0, by decide⟩),
   pushAt 1898 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1899 .ADD,
   opAt 1900 (.Swap ⟨0, by decide⟩),
   opAt 1901 (.Swap ⟨1, by decide⟩),
   pushAt 1902 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1903 .ADD,
   opAt 1904 (.Swap ⟨1, by decide⟩),
   pushAt 1905 2 8224,
   opAt 1906 (.Dup ⟨1, by decide⟩),
   opAt 1907 .GT,
   pushAt 1908 2 2513,
   opAt 1909 .JUMPI]

/-- Instructions 1662..1666, pc 2635..2641. -/
def blk1662 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1910 .POP,
   opAt 1911 .POP,
   opAt 1912 .POP,
   pushAt 1913 2 8224,
   opAt 1914 .MSTORE]

/-- Instructions 1667..1682, pc 2642..2665. -/
def blk1667 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1915 .JUMPDEST,
   pushAt 1916 2 9440,
   opAt 1917 .MLOAD,
   pushAt 1918 2 9408,
   opAt 1919 .MLOAD,
   opAt 1920 (.Dup ⟨0, by decide⟩),
   pushAt 1921 2 7168,
   opAt 1922 .ADD,
   pushAt 1923 2 8256,
   opAt 1924 .JUMPDEST,
   opAt 1925 .POP,
   pushAt 1926 0 0,
   opAt 1927 (.Swap ⟨2, by decide⟩),
   opAt 1928 (.Swap ⟨0, by decide⟩),
   opAt 1929 (.Swap ⟨1, by decide⟩),
   opAt 1930 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
