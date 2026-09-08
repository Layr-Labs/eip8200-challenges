import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 13 (instructions 1683..1741). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1683..1723, pc 2666..2806. -/
def blk1683 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1931 .JUMPDEST,
   opAt 1932 (.Dup ⟨0, by decide⟩),
   opAt 1933 .MLOAD,
   opAt 1934 (.Dup ⟨2, by decide⟩),
   opAt 1935 .MLOAD,
   opAt 1936 .JUMPDEST,
   opAt 1937 (.Dup ⟨1, by decide⟩),
   opAt 1938 (.Dup ⟨1, by decide⟩),
   opAt 1939 .GT,
   opAt 1940 (.Swap ⟨1, by decide⟩),
   opAt 1941 .JUMPDEST,
   opAt 1942 .SUB,
   opAt 1943 (.Dup ⟨5, by decide⟩),
   opAt 1944 (.Dup ⟨1, by decide⟩),
   opAt 1945 .SUB,
   opAt 1946 (.Swap ⟨0, by decide⟩),
   opAt 1947 (.Dup ⟨6, by decide⟩),
   opAt 1948 .JUMPDEST,
   opAt 1949 .GT,
   opAt 1950 (.Swap ⟨0, by decide⟩),
   opAt 1951 (.Swap ⟨1, by decide⟩),
   opAt 1952 .OR,
   opAt 1953 (.Swap ⟨4, by decide⟩),
   opAt 1954 .POP,
   opAt 1955 (.Dup ⟨3, by decide⟩),
   opAt 1956 .MSTORE,
   pushAt 1957 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1958 .ADD,
   opAt 1959 (.Swap ⟨0, by decide⟩),
   pushAt 1960 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1961 .ADD,
   opAt 1962 (.Swap ⟨0, by decide⟩),
   opAt 1963 (.Swap ⟨1, by decide⟩),
   pushAt 1964 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1965 .ADD,
   opAt 1966 (.Swap ⟨1, by decide⟩),
   pushAt 1967 2 8224,
   opAt 1968 (.Dup ⟨1, by decide⟩),
   opAt 1969 .GT,
   pushAt 1970 2 2679,
   opAt 1971 .JUMPI]

/-- Live instructions 1724..1739, pc 2807..2860; trailing padding is not executed. -/
def blk1724 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1972 .POP,
   opAt 1973 .POP,
   opAt 1974 .POP,
   opAt 1975 .ISZERO,
   pushAt 1976 2 8224,
   opAt 1977 .MLOAD,
   opAt 1978 .OR,
   pushAt 1979 32 115792089237316195423570985008687907853269984665640564039457584007913129638848,
   opAt 1980 .MUL,
   pushAt 1981 2 8256,
   opAt 1982 .ADD,
   pushAt 1983 2 9344,
   opAt 1984 .MLOAD,
   opAt 1985 (.Swap ⟨1, by decide⟩),
   opAt 1986 .MCOPY,
   opAt 1987 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
