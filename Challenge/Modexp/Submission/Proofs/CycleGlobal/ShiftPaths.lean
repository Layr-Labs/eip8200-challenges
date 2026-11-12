import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
open CycleSubmission.SharedStackArgs

noncomputable section
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the appended shift-reduce base conversion (generated). -/

namespace CycleSubmission.Global.Fast
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast


open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- The dispatcher guard (k2465): `bsize = 32 n` or jump straight to `modexpBig` (pc 219). -/
def blk2862 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1868 .JUMPDEST,
   opAt 1869 (.Dup ⟨0,by decide⟩),
   opAt 1870 (.Dup ⟨3,by decide⟩),
   opAt 1871 .XOR,
   pushAt 1872 1 207,
   opAt 1873 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1874 (.Dup ⟨0,by decide⟩),
   pushAt 1875 1 96,
   pushAt 1876 2 2112,
   opAt 1877 .CALLDATACOPY,
   pushAt 1878 2 2378,
   pushAt 1879 2 3484,
   opAt 1880 .JUMP]


/-- The negation width test (negun): `32 n = 128` jumps to the four-limb stub at pc 2336. -/
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1886 (.Dup ⟨0,by decide⟩),
   pushAt 1887 1 128,
   opAt 1888 .EQ,
   pushAt 1889 2 2284,
   opAt 1890 .JUMPI]

/-- Negation cell at pc 2429: `NEG[1504] := 0 - mem[224]`. -/
def negS8 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1891 1 224,
   opAt 1892 .MLOAD,
   pushAt 1893 0 0,
   opAt 1894 .SUB,
   pushAt 1895 2 1504,
   opAt 1896 .MSTORE]

/-- Negation cell at pc 2438: `NEG[1472] := NOT mem[192]`. -/
def negN8a :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1897 1 192,
   opAt 1898 .MLOAD,
   opAt 1899 .NOT,
   pushAt 1900 2 1472,
   opAt 1901 .MSTORE]

/-- Negation cell at pc 2446: `NEG[1440] := NOT mem[160]`. -/
def negN8b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1902 1 160,
   opAt 1903 .MLOAD,
   opAt 1904 .NOT,
   pushAt 1905 2 1440,
   opAt 1906 .MSTORE]

/-- Negation cell at pc 2454: `NEG[1408] := NOT mem[128]`. -/
def negN8c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1907 1 128,
   opAt 1908 .MLOAD,
   opAt 1909 .NOT,
   pushAt 1910 2 1408,
   opAt 1911 .MSTORE]

/-- Negation cell at pc 2462: `NEG[1376] := NOT mem[96]`. -/
def negN8d :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1912 1 96,
   opAt 1913 .MLOAD,
   opAt 1914 .NOT,
   pushAt 1915 2 1376,
   opAt 1916 .MSTORE]

/- Negation cell at pc 2471: `NEG[1344] := NOT mem[64]`. -/


/- Negation cell at pc 2479: `NEG[1312] := NOT mem[32]`. -/


/- Negation cell at pc 2487: `NEG[1280] := NOT mem[0]`. -/


/-- Negation cell at pc 2337: `NEG[1376] := 0 - mem[96]`. -/
def negS4 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1814 1 96,
   opAt 1815 .MLOAD,
   pushAt 1816 0 0,
   opAt 1817 .SUB,
   pushAt 1818 2 1376,
   opAt 1819 .MSTORE]

/-- The four-limb stub's `JUMPDEST` (pc 2336). -/
def negJ4 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1813 .JUMPDEST]

/-- The four-limb stub joins `NEG_TAIL` (pc 2470). -/
def negJ4b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1820 2 2436,
   opAt 1821 .JUMP]

/-- `NEG_TAIL`'s `JUMPDEST` (pc 2470). -/
def negJT :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1917 .JUMPDEST]

/-- Eight-limb negation cells 7..3 (limb 7: `0 - m_7`), falling into `NEG_TAIL`. -/
def blkNeg8 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  negS8 ++ negN8a ++ negN8b ++ negN8c ++ negN8d

/-- Four-limb negation stub (pc 2336): limb 3 as `0 - m_3`, then `NEG_TAIL` at pc 2470. -/
def blkNeg4 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  negJ4 ++ negS4 ++ negJ4b

/-- `NEG_TAIL` (pc 2470): negation cells 2..0. -/
def blkNegT :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1917 .JUMPDEST,
   pushAt 1918 1 64,
   opAt 1919 .MLOAD,
   opAt 1920 .NOT,
   pushAt 1921 2 1344,
   opAt 1922 .MSTORE,
   pushAt 1923 1 32,
   opAt 1924 .MLOAD,
   opAt 1925 .NOT,
   pushAt 1926 2 1312,
   opAt 1927 .MSTORE,
   pushAt 1928 0 0,
   opAt 1929 .MLOAD,
   opAt 1930 (.Dup ⟨0,by decide⟩),
   opAt 1931 .NOT,
   pushAt 1932 2 1280,
   opAt 1933 .MSTORE]


/-- `blk2919`, first part: `L = d &&& -d` twice on top of `d`, stopping before the `CLZ`. -/
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1934 (.Dup ⟨0,by decide⟩),
   pushAt 1935 0 0,
   opAt 1936 .SUB,
   opAt 1937 (.Dup ⟨1,by decide⟩),
   opAt 1938 .AND,
   opAt 1939 (.Dup ⟨0,by decide⟩)]


/-- `blk2919`, second part (pc 2673..2704), after the `CLZ`: `PRE_X := 0 - ~clz L`,
`PRE_L := 255 - clz L`, `PRE_DODD := d / L`, `PRE_BMOD := -dodd mod dodd`. -/
def blk2919b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1941 (.Dup ⟨0,by decide⟩),
   pushAt 1942 1 1,
   opAt 1943 .ADD,
   pushAt 1944 2 1600,
   opAt 1945 .MSTORE,
   pushAt 1946 1 255,
   opAt 1947 .SUB,
   pushAt 1948 2 1536,
   opAt 1949 .MSTORE,
   opAt 1950 (.Swap ⟨0,by decide⟩),
   opAt 1951 .DIV,
   opAt 1952 (.Dup ⟨0,by decide⟩),
   pushAt 1953 2 1568,
   opAt 1954 .MSTORE,
   opAt 1955 (.Dup ⟨0,by decide⟩),
   opAt 1956 (.Dup ⟨0,by decide⟩),
   pushAt 1957 0 0,
   opAt 1958 .SUB,
   opAt 1959 .MOD,
   pushAt 1960 2 1632,
   opAt 1961 .MSTORE]

/-- newton-batch head (pc 2535): load `n0 = mem[mem[0xac0]]` and form `dodd * n0` (inl693: the chain is inline). -/
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1962 2 2752,
   opAt 1963 .MLOAD,
   opAt 1964 .MLOAD,
   opAt 1965 (.Dup ⟨0,by decide⟩),
   opAt 1966 (.Dup ⟨2,by decide⟩),
   opAt 1967 .MUL]

/-- The inlined Newton chain (pc 2543): `[p] ++ rest` becomes `[newton8W p] ++ rest`. -/
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1968 (.Dup ⟨0,by decide⟩),
   pushAt 1969 1 3,
   opAt 1970 .MUL,
   pushAt 1971 1 2,
   opAt 1972 .XOR,
   opAt 1973 (.Dup ⟨0,by decide⟩),
   opAt 1974 (.Dup ⟨2,by decide⟩),
   opAt 1975 .MUL,
   pushAt 1976 1 2,
   opAt 1977 .SUB,
   opAt 1978 .MUL,
   opAt 1979 (.Dup ⟨0,by decide⟩),
   opAt 1980 (.Dup ⟨2,by decide⟩),
   opAt 1981 .MUL,
   pushAt 1982 1 2,
   opAt 1983 .SUB,
   opAt 1984 .MUL,
   opAt 1985 (.Dup ⟨0,by decide⟩),
   opAt 1986 (.Dup ⟨2,by decide⟩),
   opAt 1987 .MUL,
   pushAt 1988 1 2,
   opAt 1989 .SUB,
   opAt 1990 .MUL,
   opAt 1991 (.Dup ⟨0,by decide⟩),
   opAt 1992 (.Dup ⟨2,by decide⟩),
   opAt 1993 .MUL,
   pushAt 1994 1 2,
   opAt 1995 .SUB,
   opAt 1996 .MUL,
   opAt 1997 (.Dup ⟨0,by decide⟩),
   opAt 1998 (.Dup ⟨2,by decide⟩),
   opAt 1999 .MUL,
   pushAt 2000 1 2,
   opAt 2001 .SUB,
   opAt 2002 .MUL,
   opAt 2003 (.Dup ⟨0,by decide⟩),
   opAt 2004 (.Swap ⟨1,by decide⟩),
   opAt 2005 .MUL,
   pushAt 2006 1 2,
   opAt 2007 .SUB,
   opAt 2008 .MUL]

/-- newton-batch tail (pc 2741): `dinv := x * n0`, `V_MINV := -(dodd * x)`, drop the four
words, then the old `k := n` prologue. -/
def blkNbTailHead : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2009 (.Dup ⟨0,by decide⟩),
   opAt 2010 (.Swap ⟨1,by decide⟩),
   opAt 2011 .MUL,
   pushAt 2012 2 1664,
   opAt 2013 .MSTORE,
   opAt 2014 .MUL,
   pushAt 2015 0 0,
   opAt 2016 .SUB,
   pushAt 2017 2 2720,
   opAt 2018 .MSTORE,
   pushAt 2019 5 2310,
   opAt 2020 (.Dup ⟨4,by decide⟩),
   pushAt 2021 1 1,
   opAt 2022 .EQ,
   opAt 2023 .ISZERO,
   pushAt 2024 2 2600,
   opAt 2025 .JUMPI]
def blkNbTailByte : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2026 2 2656,
   opAt 2027 .MLOAD,
   opAt 2028 .CALLDATALOAD,
   pushAt 2029 0 0,
   opAt 2030 .BYTE,
   pushAt 2031 1 3,
   opAt 2032 .EQ,
   pushAt 2033 2 1605,
   opAt 2034 .MUL,
   opAt 2035 .ADD]
def blkNbTailJoin : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2036 .JUMPDEST,
   opAt 2037 (.Dup ⟨3,by decide⟩),
   opAt 2038 (.Dup ⟨3,by decide⟩),
   opAt 2039 (.Dup ⟨6,by decide⟩),
   pushAt 2040 2 1536,
   opAt 2041 .MLOAD,
   pushAt 2042 2 1568,
   opAt 2043 .MLOAD,
   pushAt 2044 2 1664,
   opAt 2045 .MLOAD,
   pushAt 2046 2 1632,
   opAt 2047 .MLOAD,
   pushAt 2048 2 1504,
   opAt 2049 .MLOAD,
   pushAt 2050 2 1472,
   opAt 2051 .MLOAD,
   pushAt 2052 2 1440,
   opAt 2053 .MLOAD,
   pushAt 2054 2 1408,
   opAt 2055 .MLOAD,
   pushAt 2056 2 1376,
   opAt 2057 .MLOAD,
   pushAt 2058 2 1344,
   opAt 2059 .MLOAD,
   pushAt 2060 2 1312,
   opAt 2061 .MLOAD,
   opAt 2062 (.Dup ⟨12,by decide⟩)]
def blkNbTail (esize : Nat) : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  blkNbTailHead ++ (if UInt256.ofNat esize = UInt256.ofNat 1 then blkNbTailByte else []) ++ blkNbTailJoin
theorem jumpDestNbJoin : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2600 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2036 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h

/-- Located block of the selected shift-reduce program. -/

def blkZero8 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [ opAt 2849 .JUMPDEST,
   opAt 2850 (.Dup ⟨15,by decide⟩),
   pushAt 2851 2 2112,
   pushAt 2852 2 2080,
   opAt 2853 .MCOPY,
   pushAt 2854 2 2080,
   opAt 2855 .MLOAD,
   pushAt 2856 2 2112,
   opAt 2857 .MLOAD,
   pushAt 2858 2 2721,
   opAt 2859 .JUMP]

def blkZero4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [ opAt 2975 .JUMPDEST,
   opAt 2976 (.Dup ⟨15,by decide⟩),
   pushAt 2977 2 2112,
   pushAt 2978 2 2080,
   opAt 2979 .MCOPY,
   pushAt 2980 2 2080,
   opAt 2981 .MLOAD,
   pushAt 2982 2 2112,
   opAt 2983 .MLOAD,
   pushAt 2984 2 10721,
   opAt 2985 .JUMP]

def blkEstimateSuffix8 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [ opAt 2113 .JUMPDEST,
   opAt 2114 (.Dup ⟨13,by decide⟩),
   opAt 2115 (.Dup ⟨0,by decide⟩),
   opAt 2116 (.Dup ⟨13,by decide⟩),
   opAt 2117 (.Dup ⟨4,by decide⟩),
   opAt 2118 .MULMOD,
   opAt 2119 (.Dup ⟨2,by decide⟩),
   opAt 2120 .ADDMOD,
   opAt 2121 (.Swap ⟨0,by decide⟩),
   opAt 2122 .SUB,
   opAt 2123 (.Dup ⟨12,by decide⟩),
   opAt 2124 .MUL,
   opAt 2125 (.Dup ⟨15,by decide⟩),
   opAt 2126 (.Dup ⟨1,by decide⟩),
   pushAt 2127 1 128,
   opAt 2128 .SHR,
   opAt 2129 .MUL,
   opAt 2130 (.Dup ⟨1,by decide⟩),
   pushAt 2131 0 0,
   opAt 2132 .MLOAD,
   opAt 2133 .MUL,
   pushAt 2134 2 2112,
   opAt 2135 .MLOAD,
   opAt 2136 .SUB,
   opAt 2137 .LT,
   opAt 2138 (.Swap ⟨0,by decide⟩),
   opAt 2139 .SUB,
   pushAt 2140 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2141 (.Swap ⟨1,by decide⟩),
   opAt 2142 (.Dup ⟨14,by decide⟩),
   opAt 2143 .GT,
   opAt 2144 (.Dup ⟨2,by decide⟩),
   opAt 2145 .ADD,
   opAt 2146 .OR]

def blkEstimateSuffix4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [ opAt 8243 .JUMPDEST,
   opAt 8244 (.Dup ⟨13,by decide⟩),
   opAt 8245 (.Dup ⟨0,by decide⟩),
   opAt 8246 (.Dup ⟨13,by decide⟩),
   opAt 8247 (.Dup ⟨4,by decide⟩),
   opAt 8248 .MULMOD,
   opAt 8249 (.Dup ⟨2,by decide⟩),
   opAt 8250 .ADDMOD,
   opAt 8251 (.Swap ⟨0,by decide⟩),
   opAt 8252 .SUB,
   opAt 8253 (.Dup ⟨12,by decide⟩),
   opAt 8254 .MUL,
   opAt 8255 (.Dup ⟨15,by decide⟩),
   opAt 8256 (.Dup ⟨1,by decide⟩),
   pushAt 8257 1 128,
   opAt 8258 .SHR,
   opAt 8259 .MUL,
   opAt 8260 (.Dup ⟨1,by decide⟩),
   pushAt 8261 0 0,
   opAt 8262 .MLOAD,
   opAt 8263 .MUL,
   pushAt 8264 2 2112,
   opAt 8265 .MLOAD,
   opAt 8266 .SUB,
   opAt 8267 .LT,
   opAt 8268 (.Swap ⟨0,by decide⟩),
   opAt 8269 .SUB,
   pushAt 8270 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8271 (.Swap ⟨1,by decide⟩),
   opAt 8272 (.Dup ⟨14,by decide⟩),
   opAt 8273 .GT,
   opAt 8274 (.Dup ⟨2,by decide⟩),
   opAt 8275 .ADD,
   opAt 8276 .OR]

def blk3013 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2094 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2095 (.Dup ⟨15,by decide⟩),
   pushAt 2096 2 2112,
   pushAt 2097 2 2080,
   opAt 2098 .MCOPY]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [ pushAt 2099 2 2080,
   opAt 2100 .MLOAD,
   opAt 2101 (.Dup ⟨0,by decide⟩),
   opAt 2102 (.Dup ⟨14,by decide⟩),
   opAt 2103 .SHR,
   opAt 2104 (.Swap ⟨0,by decide⟩),
   pushAt 2105 2 1600,
   opAt 2106 .MLOAD,
   opAt 2107 .SHL,
   pushAt 2108 2 2112,
   opAt 2109 .MLOAD,
   opAt 2110 (.Dup ⟨15,by decide⟩),
   opAt 2111 .SHR,
   opAt 2112 .ADD,
   opAt 2113 .JUMPDEST,
   opAt 2114 (.Dup ⟨13,by decide⟩),
   opAt 2115 (.Dup ⟨0,by decide⟩),
   opAt 2116 (.Dup ⟨13,by decide⟩),
   opAt 2117 (.Dup ⟨4,by decide⟩),
   opAt 2118 .MULMOD,
   opAt 2119 (.Dup ⟨2,by decide⟩),
   opAt 2120 .ADDMOD,
   opAt 2121 (.Swap ⟨0,by decide⟩),
   opAt 2122 .SUB,
   opAt 2123 (.Dup ⟨12,by decide⟩),
   opAt 2124 .MUL,
   opAt 2125 (.Dup ⟨15,by decide⟩),
   opAt 2126 (.Dup ⟨1,by decide⟩),
   pushAt 2127 1 128,
   opAt 2128 .SHR,
   opAt 2129 .MUL,
   opAt 2130 (.Dup ⟨1,by decide⟩),
   pushAt 2131 0 0,
   opAt 2132 .MLOAD,
   opAt 2133 .MUL,
   pushAt 2134 2 2112,
   opAt 2135 .MLOAD,
   opAt 2136 .SUB,
   opAt 2137 .LT,
   opAt 2138 (.Swap ⟨0,by decide⟩),
   opAt 2139 .SUB,
   pushAt 2140 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2141 (.Swap ⟨1,by decide⟩),
   opAt 2142 (.Dup ⟨14,by decide⟩),
   opAt 2143 .GT,
   opAt 2144 (.Dup ⟨2,by decide⟩),
   opAt 2145 .ADD,
   opAt 2146 .OR]



def blk3013h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8224 .JUMPDEST]

/-- The appended four-limb loop head (pc 10726): a byte copy of the eight-limb head. -/
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8225 (.Dup ⟨15,by decide⟩),
   pushAt 8226 2 2112,
   pushAt 8227 2 2080,
   opAt 8228 .MCOPY]

/-- The appended four-limb loop head (pc 10726): a byte copy of the eight-limb head. -/
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [ pushAt 8229 2 2080,
   opAt 8230 .MLOAD,
   opAt 8231 (.Dup ⟨0,by decide⟩),
   opAt 8232 (.Dup ⟨14,by decide⟩),
   opAt 8233 .SHR,
   opAt 8234 (.Swap ⟨0,by decide⟩),
   pushAt 8235 2 1600,
   opAt 8236 .MLOAD,
   opAt 8237 .SHL,
   pushAt 8238 2 2112,
   opAt 8239 .MLOAD,
   opAt 8240 (.Dup ⟨15,by decide⟩),
   opAt 8241 .SHR,
   opAt 8242 .ADD,
   opAt 8243 .JUMPDEST,
   opAt 8244 (.Dup ⟨13,by decide⟩),
   opAt 8245 (.Dup ⟨0,by decide⟩),
   opAt 8246 (.Dup ⟨13,by decide⟩),
   opAt 8247 (.Dup ⟨4,by decide⟩),
   opAt 8248 .MULMOD,
   opAt 8249 (.Dup ⟨2,by decide⟩),
   opAt 8250 .ADDMOD,
   opAt 8251 (.Swap ⟨0,by decide⟩),
   opAt 8252 .SUB,
   opAt 8253 (.Dup ⟨12,by decide⟩),
   opAt 8254 .MUL,
   opAt 8255 (.Dup ⟨15,by decide⟩),
   opAt 8256 (.Dup ⟨1,by decide⟩),
   pushAt 8257 1 128,
   opAt 8258 .SHR,
   opAt 8259 .MUL,
   opAt 8260 (.Dup ⟨1,by decide⟩),
   pushAt 8261 0 0,
   opAt 8262 .MLOAD,
   opAt 8263 .MUL,
   pushAt 8264 2 2112,
   opAt 8265 .MLOAD,
   opAt 8266 .SUB,
   opAt 8267 .LT,
   opAt 8268 (.Swap ⟨0,by decide⟩),
   opAt 8269 .SUB,
   pushAt 8270 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8271 (.Swap ⟨1,by decide⟩),
   opAt 8272 (.Dup ⟨14,by decide⟩),
   opAt 8273 .GT,
   opAt 8274 (.Dup ⟨2,by decide⟩),
   opAt 8275 .ADD,
   opAt 8276 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`.
Instructions 2578..2579 are `SWAP3 POP` (pc 3184..3185): they lift the `2^256-1` mask that the
three `JUMPDEST`s at pc 3168..3170 left in place and drop it, restoring the `[carry, q]` shape
before `SUB`. -/

def blk3125Unc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [ pushAt 2361 2 2080,
   opAt 2362 .MLOAD,
   opAt 2363 .ADD,
   opAt 2364 .SUB,
   opAt 2365 (.Dup ⟨0,by decide⟩),
   pushAt 2366 7 3067,
   opAt 2367 .JUMPI,
   opAt 2382 .JUMPDEST,
   pushAt 2383 2 2080,
   opAt 2384 .MSTORE]

def blk3125hUnc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [ pushAt 8379 2 2080,
   opAt 8380 .MLOAD,
   opAt 8381 .ADD,
   opAt 8382 .SUB,
   opAt 8383 (.Dup ⟨0,by decide⟩),
   pushAt 8384 29 3067,
   opAt 8385 .JUMPI,
   opAt 2382 .JUMPDEST,
   pushAt 2383 2 2080,
   opAt 2384 .MSTORE]

def blk3125 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [ pushAt 2361 2 2080,
   opAt 2362 .MLOAD,
   opAt 2363 .ADD,
   opAt 2364 .SUB,
   opAt 2365 (.Dup ⟨0,by decide⟩),
   pushAt 2366 7 3067,
   opAt 2367 .JUMPI,
   opAt 2368 (.Swap ⟨0,by decide⟩),
   opAt 2369 .POP]

/-- `UNC`: entered only with `neg ≠ 0`; drops it and falls into `ADD_LOOP`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2385 .POP]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2386 .JUMPDEST,
   pushAt 2387 0 0,
   pushAt 2388 2 2784,
   opAt 2389 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2390 .JUMPDEST,
   opAt 2391 (.Dup ⟨0,by decide⟩),
   opAt 2392 .MLOAD,
   pushAt 2393 2 2112,
   opAt 2394 (.Dup ⟨2,by decide⟩),
   opAt 2395 .SUB,
   opAt 2396 .MLOAD,
   opAt 2397 (.Dup ⟨1,by decide⟩),
   opAt 2398 .ADD,
   opAt 2399 (.Swap ⟨0,by decide⟩),
   opAt 2400 (.Dup ⟨1,by decide⟩),
   opAt 2401 .LT,
   opAt 2402 (.Swap ⟨0,by decide⟩),
   opAt 2403 (.Dup ⟨3,by decide⟩),
   opAt 2404 .ADD,
   opAt 2405 (.Swap ⟨2,by decide⟩),
   opAt 2406 (.Dup ⟨3,by decide⟩),
   opAt 2407 .LT,
   opAt 2408 .OR,
   opAt 2409 (.Swap ⟨1,by decide⟩),
   opAt 2410 (.Dup ⟨1,by decide⟩),
   opAt 2411 .MSTORE,
   pushAt 2412 1 31,
   opAt 2413 .NOT,
   opAt 2414 .ADD,
   pushAt 2415 2 2111,
   opAt 2416 (.Dup ⟨1,by decide⟩),
   opAt 2417 .GT,
   pushAt 2418 2 3079,
   opAt 2419 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2420 .POP,
   pushAt 2421 2 2080,
   opAt 2422 .MLOAD,
   opAt 2423 (.Dup ⟨1,by decide⟩),
   opAt 2424 .ADD,
   opAt 2425 (.Dup ⟨0,by decide⟩),
   pushAt 2426 2 2080,
   opAt 2427 .MSTORE,
   opAt 2428 .LT,
   opAt 2429 .ISZERO,
   pushAt 2430 2 3073,
   opAt 2431 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2432 2 2080,
   opAt 2433 .MLOAD,
   opAt 2434 (.Dup ⟨0,by decide⟩),
   opAt 2435 .ISZERO,
   pushAt 2436 2 3054,
   opAt 2437 .JUMPI]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), back to the loop head while `k ≠ 0` (the `CSUB` call is the identity on every reachable state). -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2370 .JUMPDEST,
   opAt 2371 .NOT,
   opAt 2372 .ADD,
   opAt 2373 (.Dup ⟨0,by decide⟩),
   opAt 2374 (.Dup ⟨2,by decide⟩),
   opAt 2375 .JUMPI]

def blk3253Last :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2370 .JUMPDEST,
   opAt 2371 .NOT,
   opAt 2372 .ADD,
   opAt 2373 (.Dup ⟨0,by decide⟩),
   opAt 2374 (.Dup ⟨2,by decide⟩),
   opAt 2375 .JUMPI,
   opAt 2376 .JUMPDEST]


/-- The loop exit after the last step: `SHIFT_DONE` is the `JUMPI` fall-through itself (the
exit block sits right behind the bottom test), so the exit path is empty. -/
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

/-- The four-limb private middle block (pc 10941). -/
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [ pushAt 8379 2 2080,
   opAt 8380 .MLOAD,
   opAt 8381 .ADD,
   opAt 8382 .SUB,
   opAt 8383 (.Dup ⟨0,by decide⟩),
   pushAt 8384 29 3067,
   opAt 8385 .JUMPI,
   opAt 8386 (.Swap ⟨0,by decide⟩),
   opAt 8387 .POP]

/-- The four-limb private counter (pc 10970; nothing jumps here, so no `JUMPDEST`). -/
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [ opAt 8388 .NOT,
   opAt 8389 .ADD,
   opAt 8390 (.Dup ⟨0,by decide⟩),
   opAt 8391 (.Dup ⟨2,by decide⟩),
   opAt 8392 .JUMPI]


theorem jumpDest4608 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2357 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1868 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 1868 = 2357 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestBigC : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 207 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 135 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 135 = 207 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest4657 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2378 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1881 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 1881 = 2378 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestNeg4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2284 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1813 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 1813 = 2284 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestNegT : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2436 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1917 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 1917 = 2436 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest4839 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2692 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2094 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2094 = 2692 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestHead4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10692 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8224 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 8224 = 10692 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5115 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3073 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2386 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2386 = 3073 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5121 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3079 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2390 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2390 = 3079 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestLazyStore : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3067 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2382 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2382 = 3067 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestUnc : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3067 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2382 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2382 = 3067 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5311 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3054 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2370 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2370 = 3054 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5366 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3061 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2377 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2377 = 3061 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest2471 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2298 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1822 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 1822 = 2298 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h



end CycleSubmission.Global.Fast

namespace CycleSubmission.Global.Fast
open EvmSemantics EvmSemantics.EVM
end CycleSubmission.Global.Fast
