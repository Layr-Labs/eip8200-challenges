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
   pushAt 1879 2 3492,
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
   pushAt 2019 6 2310,
   opAt 2020 (.Dup ⟨4,by decide⟩),
   pushAt 2021 1 1,
   opAt 2022 .EQ,
   opAt 2023 .ISZERO,
   pushAt 2024 2 2601,
   opAt 2025 .JUMPI]
def blkNbTailByte : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2026 2 2656,
   opAt 2027 .MLOAD,
   opAt 2028 .CALLDATALOAD,
   pushAt 2029 0 0,
   opAt 2030 .BYTE,
   pushAt 2031 1 3,
   opAt 2032 .EQ,
   pushAt 2033 2 1637,
   opAt 2034 .MUL,
   opAt 2035 .ADD]
def blkNbTailJoin : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2036 .JUMPDEST,
   pushAt 2037 3 2519,
   pushAt 2038 1 32,
   opAt 2039 .MLOAD,
   pushAt 2040 1 128,
   opAt 2041 .SHR,
   pushAt 2042 2 1536,
   opAt 2043 .MLOAD,
   pushAt 2044 2 1568,
   opAt 2045 .MLOAD,
   pushAt 2046 2 1664,
   opAt 2047 .MLOAD,
   pushAt 2048 2 1632,
   opAt 2049 .MLOAD,
   pushAt 2050 2 1504,
   opAt 2051 .MLOAD,
   pushAt 2052 2 1472,
   opAt 2053 .MLOAD,
   pushAt 2054 2 1440,
   opAt 2055 .MLOAD,
   pushAt 2056 2 1408,
   opAt 2057 .MLOAD,
   pushAt 2058 2 1376,
   opAt 2059 .MLOAD,
   pushAt 2060 2 1344,
   opAt 2061 .MLOAD,
   pushAt 2062 2 1312,
   opAt 2063 .MLOAD,
   opAt 2064 (.Dup ⟨15,by decide⟩)]
def blkNbTail (esize : Nat) : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  blkNbTailHead ++ (if UInt256.ofNat esize = UInt256.ofNat 1 then blkNbTailByte else []) ++ blkNbTailJoin
theorem jumpDestNbJoin : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2601 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2036 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h

/-- Located block of the selected shift-reduce program. -/

def blkZero8 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2854 .JUMPDEST,
   pushAt 2855 2 256,
   pushAt 2856 2 2112,
   pushAt 2857 2 2080,
   opAt 2858 .MCOPY,
   pushAt 2859 2 2080,
   opAt 2860 .MLOAD,
   pushAt 2861 2 2112,
   opAt 2862 .MLOAD,
   opAt 2863 (.Dup ⟨13,by decide⟩),
   opAt 2864 (.Dup ⟨0,by decide⟩),
   opAt 2865 (.Dup ⟨13,by decide⟩),
   opAt 2866 (.Dup ⟨4,by decide⟩),
   opAt 2867 .MULMOD,
   opAt 2868 (.Dup ⟨2,by decide⟩),
   opAt 2869 .ADDMOD,
   opAt 2870 (.Dup ⟨0,by decide⟩),
   opAt 2871 (.Swap ⟨1,by decide⟩),
   opAt 2872 .SUB,
   opAt 2873 (.Dup ⟨13,by decide⟩),
   opAt 2874 .MUL,
   opAt 2875 (.Dup ⟨15,by decide⟩),
   opAt 2876 (.Dup ⟨1,by decide⟩),
   pushAt 2877 1 128,
   opAt 2878 .SHR,
   opAt 2879 .MUL,
   opAt 2880 (.Swap ⟨0,by decide⟩),
   opAt 2881 (.Swap ⟨1,by decide⟩),
   opAt 2882 .LT,
   opAt 2883 (.Swap ⟨0,by decide⟩),
   opAt 2884 .SUB,
   pushAt 2885 2 2760,
   opAt 2886 .JUMP]

def blkZero4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 3002 .JUMPDEST,
   pushAt 3003 1 128,
   pushAt 3004 2 2112,
   pushAt 3005 2 2080,
   opAt 3006 .MCOPY,
   pushAt 3007 2 2080,
   opAt 3008 .MLOAD,
   pushAt 3009 2 2112,
   opAt 3010 .MLOAD,
   opAt 3011 (.Dup ⟨13,by decide⟩),
   opAt 3012 (.Dup ⟨0,by decide⟩),
   opAt 3013 (.Dup ⟨13,by decide⟩),
   opAt 3014 (.Dup ⟨4,by decide⟩),
   opAt 3015 .MULMOD,
   opAt 3016 (.Dup ⟨2,by decide⟩),
   opAt 3017 .ADDMOD,
   opAt 3018 (.Dup ⟨0,by decide⟩),
   opAt 3019 (.Swap ⟨1,by decide⟩),
   opAt 3020 .SUB,
   opAt 3021 (.Dup ⟨13,by decide⟩),
   opAt 3022 .MUL,
   opAt 3023 (.Dup ⟨15,by decide⟩),
   opAt 3024 (.Dup ⟨1,by decide⟩),
   pushAt 3025 1 128,
   opAt 3026 .SHR,
   opAt 3027 .MUL,
   opAt 3028 (.Swap ⟨0,by decide⟩),
   opAt 3029 (.Swap ⟨1,by decide⟩),
   opAt 3030 .LT,
   opAt 3031 (.Swap ⟨0,by decide⟩),
   opAt 3032 .SUB,
   pushAt 3033 2 10783,
   opAt 3034 .JUMP]

def blkEstimateSuffix8 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2142 .JUMPDEST,
   pushAt 2143 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2144 (.Swap ⟨1,by decide⟩),
   opAt 2145 (.Dup ⟨14,by decide⟩),
   opAt 2146 .GT,
   opAt 2147 (.Dup ⟨2,by decide⟩),
   opAt 2148 .ADD,
   opAt 2149 .OR]

def blkEstimateSuffix4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8318 .JUMPDEST,
   pushAt 8319 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8320 (.Swap ⟨1,by decide⟩),
   opAt 8321 (.Dup ⟨14,by decide⟩),
   opAt 8322 .GT,
   opAt 8323 (.Dup ⟨2,by decide⟩),
   opAt 8324 .ADD,
   opAt 8325 .OR]

def blk3013 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2097 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2098 2 256,
   pushAt 2099 2 2112,
   pushAt 2100 2 2080,
   opAt 2101 .MCOPY]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2102 2 2080,
   opAt 2103 .MLOAD,
   opAt 2104 (.Dup ⟨0,by decide⟩),
   opAt 2105 (.Dup ⟨14,by decide⟩),
   opAt 2106 .SHR,
   opAt 2107 (.Swap ⟨0,by decide⟩),
   pushAt 2108 2 1600,
   opAt 2109 .MLOAD,
   opAt 2110 .SHL,
   pushAt 2111 2 2112,
   opAt 2112 .MLOAD,
   opAt 2113 (.Dup ⟨15,by decide⟩),
   opAt 2114 .SHR,
   opAt 2115 .ADD,
   opAt 2116 (.Dup ⟨13,by decide⟩),
   opAt 2117 (.Dup ⟨0,by decide⟩),
   opAt 2118 (.Dup ⟨13,by decide⟩),
   opAt 2119 (.Dup ⟨4,by decide⟩),
   opAt 2120 .MULMOD,
   opAt 2121 (.Dup ⟨2,by decide⟩),
   opAt 2122 .ADDMOD,
   opAt 2123 (.Swap ⟨0,by decide⟩),
   opAt 2124 .SUB,
   opAt 2125 (.Dup ⟨12,by decide⟩),
   opAt 2126 .MUL,
   opAt 2127 (.Dup ⟨15,by decide⟩),
   opAt 2128 (.Dup ⟨1,by decide⟩),
   pushAt 2129 1 128,
   opAt 2130 .SHR,
   opAt 2131 .MUL,
   opAt 2132 (.Dup ⟨1,by decide⟩),
   pushAt 2133 0 0,
   opAt 2134 .MLOAD,
   opAt 2135 .MUL,
   pushAt 2136 2 2112,
   opAt 2137 .MLOAD,
   opAt 2138 .SUB,
   opAt 2139 .LT,
   opAt 2140 (.Swap ⟨0,by decide⟩),
   opAt 2141 .SUB,
   opAt 2142 .JUMPDEST,
   pushAt 2143 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2144 (.Swap ⟨1,by decide⟩),
   opAt 2145 (.Dup ⟨14,by decide⟩),
   opAt 2146 .GT,
   opAt 2147 (.Dup ⟨2,by decide⟩),
   opAt 2148 .ADD,
   opAt 2149 .OR]



def blk3013h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8273 .JUMPDEST]

/-- The appended four-limb loop head (pc 10726): a byte copy of the eight-limb head. -/
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8274 1 128,
   pushAt 8275 2 2112,
   pushAt 8276 2 2080,
   opAt 8277 .MCOPY]

/-- The appended four-limb loop head (pc 10726): a byte copy of the eight-limb head. -/
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8278 2 2080,
   opAt 8279 .MLOAD,
   opAt 8280 (.Dup ⟨0,by decide⟩),
   opAt 8281 (.Dup ⟨14,by decide⟩),
   opAt 8282 .SHR,
   opAt 8283 (.Swap ⟨0,by decide⟩),
   pushAt 8284 2 1600,
   opAt 8285 .MLOAD,
   opAt 8286 .SHL,
   pushAt 8287 2 2112,
   opAt 8288 .MLOAD,
   opAt 8289 (.Dup ⟨15,by decide⟩),
   opAt 8290 .SHR,
   opAt 8291 .ADD,
   opAt 8292 (.Dup ⟨13,by decide⟩),
   opAt 8293 (.Dup ⟨0,by decide⟩),
   opAt 8294 (.Dup ⟨13,by decide⟩),
   opAt 8295 (.Dup ⟨4,by decide⟩),
   opAt 8296 .MULMOD,
   opAt 8297 (.Dup ⟨2,by decide⟩),
   opAt 8298 .ADDMOD,
   opAt 8299 (.Swap ⟨0,by decide⟩),
   opAt 8300 .SUB,
   opAt 8301 (.Dup ⟨12,by decide⟩),
   opAt 8302 .MUL,
   opAt 8303 (.Dup ⟨15,by decide⟩),
   opAt 8304 (.Dup ⟨1,by decide⟩),
   pushAt 8305 1 128,
   opAt 8306 .SHR,
   opAt 8307 .MUL,
   opAt 8308 (.Dup ⟨1,by decide⟩),
   pushAt 8309 0 0,
   opAt 8310 .MLOAD,
   opAt 8311 .MUL,
   pushAt 8312 2 2112,
   opAt 8313 .MLOAD,
   opAt 8314 .SUB,
   opAt 8315 .LT,
   opAt 8316 (.Swap ⟨0,by decide⟩),
   opAt 8317 .SUB,
   opAt 8318 .JUMPDEST,
   pushAt 8319 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8320 (.Swap ⟨1,by decide⟩),
   opAt 8321 (.Dup ⟨14,by decide⟩),
   opAt 8322 .GT,
   opAt 8323 (.Dup ⟨2,by decide⟩),
   opAt 8324 .ADD,
   opAt 8325 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`.
Instructions 2578..2579 are `SWAP3 POP` (pc 3184..3185): they lift the `2^256-1` mask that the
three `JUMPDEST`s at pc 3168..3170 left in place and drop it, restoring the `[carry, q]` shape
before `SUB`. -/

def blk3125Unc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2364 2 2080,
   opAt 2365 .MLOAD,
   opAt 2366 .ADD,
   opAt 2367 .SUB,
   opAt 2368 (.Dup ⟨0,by decide⟩),
   opAt 2369 .JUMPDEST,
   opAt 2370 .JUMPDEST,
   pushAt 2371 3 3075,
   opAt 2372 .JUMPI,
   opAt 2387 .JUMPDEST,
   pushAt 2388 2 2080,
   opAt 2389 .MSTORE]

def blk3125hUnc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8428 2 2080,
   opAt 8429 .MLOAD,
   opAt 8430 .ADD,
   opAt 8431 .SUB,
   opAt 8432 (.Dup ⟨0,by decide⟩),
   opAt 8433 .JUMPDEST,
   opAt 8434 .JUMPDEST,
   pushAt 8435 26 3075,
   opAt 8436 .JUMPI,
   opAt 2387 .JUMPDEST,
   pushAt 2388 2 2080,
   opAt 2389 .MSTORE]

def blk3125 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2364 2 2080,
   opAt 2365 .MLOAD,
   opAt 2366 .ADD,
   opAt 2367 .SUB,
   opAt 2368 (.Dup ⟨0,by decide⟩),
   opAt 2369 .JUMPDEST,
   opAt 2370 .JUMPDEST,
   pushAt 2371 3 3075,
   opAt 2372 .JUMPI,
   opAt 2373 (.Swap ⟨0,by decide⟩),
   opAt 2374 .POP]

/-- `UNC`: entered only with `neg ≠ 0`; drops it and falls into `ADD_LOOP`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2390 .POP]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2391 .JUMPDEST,
   pushAt 2392 0 0,
   pushAt 2393 2 2784,
   opAt 2394 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2395 .JUMPDEST,
   opAt 2396 (.Dup ⟨0,by decide⟩),
   opAt 2397 .MLOAD,
   pushAt 2398 2 2112,
   opAt 2399 (.Dup ⟨2,by decide⟩),
   opAt 2400 .SUB,
   opAt 2401 .MLOAD,
   opAt 2402 (.Dup ⟨1,by decide⟩),
   opAt 2403 .ADD,
   opAt 2404 (.Swap ⟨0,by decide⟩),
   opAt 2405 (.Dup ⟨1,by decide⟩),
   opAt 2406 .LT,
   opAt 2407 (.Swap ⟨0,by decide⟩),
   opAt 2408 (.Dup ⟨3,by decide⟩),
   opAt 2409 .ADD,
   opAt 2410 (.Swap ⟨2,by decide⟩),
   opAt 2411 (.Dup ⟨3,by decide⟩),
   opAt 2412 .LT,
   opAt 2413 .OR,
   opAt 2414 (.Swap ⟨1,by decide⟩),
   opAt 2415 (.Dup ⟨1,by decide⟩),
   opAt 2416 .MSTORE,
   pushAt 2417 1 31,
   opAt 2418 .NOT,
   opAt 2419 .ADD,
   pushAt 2420 2 2111,
   opAt 2421 (.Dup ⟨1,by decide⟩),
   opAt 2422 .GT,
   pushAt 2423 2 3087,
   opAt 2424 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2425 .POP,
   pushAt 2426 2 2080,
   opAt 2427 .MLOAD,
   opAt 2428 (.Dup ⟨1,by decide⟩),
   opAt 2429 .ADD,
   opAt 2430 (.Dup ⟨0,by decide⟩),
   pushAt 2431 2 2080,
   opAt 2432 .MSTORE,
   opAt 2433 .LT,
   opAt 2434 .ISZERO,
   pushAt 2435 2 3081,
   opAt 2436 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2437 2 2080,
   opAt 2438 .MLOAD,
   opAt 2439 (.Dup ⟨0,by decide⟩),
   opAt 2440 .ISZERO,
   pushAt 2441 2 3062,
   opAt 2442 .JUMPI]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), back to the loop head while `k ≠ 0` (the `CSUB` call is the identity on every reachable state). -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2375 .JUMPDEST,
   opAt 2376 .NOT,
   opAt 2377 .ADD,
   opAt 2378 (.Dup ⟨0,by decide⟩),
   opAt 2379 (.Dup ⟨2,by decide⟩),
   opAt 2380 .JUMPI]

def blk3253Last :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2375 .JUMPDEST,
   opAt 2376 .NOT,
   opAt 2377 .ADD,
   opAt 2378 (.Dup ⟨0,by decide⟩),
   opAt 2379 (.Dup ⟨2,by decide⟩),
   opAt 2380 .JUMPI,
   opAt 2381 .JUMPDEST]


/-- The loop exit after the last step: `SHIFT_DONE` is the `JUMPI` fall-through itself (the
exit block sits right behind the bottom test), so the exit path is empty. -/
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

/-- The four-limb private middle block (pc 10941). -/
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8428 2 2080,
   opAt 8429 .MLOAD,
   opAt 8430 .ADD,
   opAt 8431 .SUB,
   opAt 8432 (.Dup ⟨0,by decide⟩),
   opAt 8433 .JUMPDEST,
   opAt 8434 .JUMPDEST,
   pushAt 8435 26 3075,
   opAt 8436 .JUMPI,
   opAt 8437 (.Swap ⟨0,by decide⟩),
   opAt 8438 .POP]

/-- The four-limb private counter (pc 10970; nothing jumps here, so no `JUMPDEST`). -/
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8439 .NOT,
   opAt 8440 .ADD,
   opAt 8441 (.Dup ⟨0,by decide⟩),
   opAt 8442 (.Dup ⟨2,by decide⟩),
   opAt 8443 .JUMPI]


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


theorem jumpDest4839 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2700 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2097 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2097 = 2700 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestHead4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10724 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8273 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 8273 = 10724 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5115 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3081 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2391 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2391 = 3081 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5121 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3087 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2395 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2395 = 3087 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestLazyStore : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3075 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2387 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2387 = 3075 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestUnc : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3075 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2387 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2387 = 3075 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5311 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3062 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2375 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2375 = 3062 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5366 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3069 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2382 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2382 = 3069 := by
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
