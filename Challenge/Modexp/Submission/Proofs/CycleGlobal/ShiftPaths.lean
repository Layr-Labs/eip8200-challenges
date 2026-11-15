import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
open CycleSubmission.SharedStackArgs
noncomputable section
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CycleSubmission.Global.Fast
private abbrev runtimeArtifact := CycleSubmission.Artifact.artifact
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
def blk2862 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 463 (.Dup ⟨0,by decide⟩),
   opAt 464 (.Dup ⟨3,by decide⟩),
   opAt 465 .XOR,
   pushAt 466 1 174,
   opAt 467 .JUMPI]
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 468 (.Dup ⟨0,by decide⟩),
   pushAt 469 1 96,
   pushAt 470 2 2112,
   opAt 471 .CALLDATACOPY]
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2002 (.Dup ⟨0,by decide⟩),
   pushAt 2003 1 128,
   opAt 2004 .EQ,
   pushAt 2005 2 2501,
   opAt 2006 .JUMPI]
def negS8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2007 1 224,
   opAt 2008 .MLOAD,
   pushAt 2009 0 0,
   opAt 2010 .SUB,
   pushAt 2011 2 1504,
   opAt 2012 .MSTORE]
def negN8a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2013 1 192,
   opAt 2014 .MLOAD,
   opAt 2015 .NOT,
   pushAt 2016 2 1472,
   opAt 2017 .MSTORE]
def negN8b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2018 1 160,
   opAt 2019 .MLOAD,
   opAt 2020 .NOT,
   pushAt 2021 2 1440,
   opAt 2022 .MSTORE]
def negN8c :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2023 1 128,
   opAt 2024 .MLOAD,
   opAt 2025 .NOT,
   pushAt 2026 2 1408,
   opAt 2027 .MSTORE]
def negN8d :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2028 1 96,
   opAt 2029 .MLOAD,
   opAt 2030 .NOT,
   pushAt 2031 2 1376,
   opAt 2032 .MSTORE]
def negS4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1964 1 96,
   opAt 1965 .MLOAD,
   pushAt 1966 0 0,
   opAt 1967 .SUB,
   pushAt 1968 2 1376,
   opAt 1969 .MSTORE]
def negJ4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1963 .JUMPDEST]
def negJ4b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1970 2 2612,
   opAt 1971 .JUMP]
def negJT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2033 .JUMPDEST]
def blkNeg8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negS8++negN8a++negN8b++negN8c++negN8d
def blkNeg4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negJ4++negS4++negJ4b
def blkNegT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2033 .JUMPDEST,
   pushAt 2034 1 64,
   opAt 2035 .MLOAD,
   opAt 2036 .NOT,
   pushAt 2037 2 1344,
   opAt 2038 .MSTORE,
   pushAt 2039 1 32,
   opAt 2040 .MLOAD,
   opAt 2041 .NOT,
   pushAt 2042 2 1312,
   opAt 2043 .MSTORE,
   pushAt 2044 0 0,
   opAt 2045 .MLOAD,
   opAt 2046 (.Dup ⟨0,by decide⟩),
   opAt 2047 .NOT,
   pushAt 2048 2 1280,
   opAt 2049 .MSTORE]
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2050 (.Dup ⟨0,by decide⟩),
   pushAt 2051 0 0,
   opAt 2052 .SUB,
   opAt 2053 (.Dup ⟨1,by decide⟩),
   opAt 2054 .AND]
def blk2919b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2056 (.Dup ⟨0,by decide⟩),
   pushAt 2057 1 1,
   opAt 2058 .ADD,
   pushAt 2059 2 1600,
   opAt 2060 .MSTORE,
   pushAt 2061 1 255,
   opAt 2062 .SUB,
   opAt 2063 (.Dup ⟨0,by decide⟩),
   pushAt 2064 2 1536,
   opAt 2065 .MSTORE,
   opAt 2066 .SHR,
   opAt 2067 (.Dup ⟨0,by decide⟩),
   pushAt 2068 2 1568,
   opAt 2069 .MSTORE,
   opAt 2070 (.Dup ⟨0,by decide⟩),
   opAt 2071 (.Dup ⟨0,by decide⟩),
   pushAt 2072 0 0,
   opAt 2073 .SUB,
   opAt 2074 .MOD,
   pushAt 2075 2 1632,
   opAt 2076 .MSTORE]
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2077 2 2752,
   opAt 2078 .MLOAD,
   opAt 2079 .MLOAD,
   opAt 2080 (.Dup ⟨0,by decide⟩),
   opAt 2081 (.Dup ⟨2,by decide⟩),
   opAt 2082 .MUL]
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2083 (.Dup ⟨0,by decide⟩),
   pushAt 2084 1 3,
   opAt 2085 .MUL,
   pushAt 2086 1 2,
   opAt 2087 .XOR,
   opAt 2088 (.Dup ⟨0,by decide⟩),
   opAt 2089 (.Dup ⟨2,by decide⟩),
   opAt 2090 .MUL,
   pushAt 2091 1 2,
   opAt 2092 .SUB,
   opAt 2093 .MUL,
   opAt 2094 (.Dup ⟨0,by decide⟩),
   opAt 2095 (.Dup ⟨2,by decide⟩),
   opAt 2096 .MUL,
   pushAt 2097 1 2,
   opAt 2098 .SUB,
   opAt 2099 .MUL,
   opAt 2100 (.Dup ⟨0,by decide⟩),
   opAt 2101 (.Dup ⟨2,by decide⟩),
   opAt 2102 .MUL,
   pushAt 2103 1 2,
   opAt 2104 .SUB,
   opAt 2105 .MUL,
   opAt 2106 (.Dup ⟨0,by decide⟩),
   opAt 2107 (.Dup ⟨2,by decide⟩),
   opAt 2108 .MUL,
   pushAt 2109 1 2,
   opAt 2110 .SUB,
   opAt 2111 .MUL,
   opAt 2112 (.Dup ⟨0,by decide⟩),
   opAt 2113 (.Dup ⟨2,by decide⟩),
   opAt 2114 .MUL,
   pushAt 2115 1 2,
   opAt 2116 .SUB,
   opAt 2117 .MUL,
   opAt 2118 (.Dup ⟨0,by decide⟩),
   opAt 2119 (.Swap ⟨1,by decide⟩),
   opAt 2120 .MUL,
   pushAt 2121 1 2,
   opAt 2122 .SUB,
   opAt 2123 .MUL]
def blkNbTailHead : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2124 (.Dup ⟨0,by decide⟩),
   opAt 2125 (.Swap ⟨1,by decide⟩),
   opAt 2126 .MUL,
   pushAt 2127 2 1664,
   opAt 2128 .MSTORE,
   opAt 2129 .MUL,
   pushAt 2130 0 0,
   opAt 2131 .SUB,
   pushAt 2132 2 2720,
   opAt 2133 .MSTORE,
   pushAt 2134 2 2522,
   opAt 2135 (.Dup ⟨4,by decide⟩),
   pushAt 2136 1 1,
   opAt 2137 .XOR,
   pushAt 2138 2 2771,
   opAt 2139 .JUMPI]
def blkNbTailByte : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2140 2 2656,
   opAt 2141 .MLOAD,
   opAt 2142 .CALLDATALOAD,
   pushAt 2143 0 0,
   opAt 2144 .BYTE,
   pushAt 2145 1 3,
   opAt 2146 .EQ,
   pushAt 2147 2 7895,
   opAt 2148 .MUL,
   opAt 2149 .ADD]
def blkNbTailJoin : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2150 .JUMPDEST,
   pushAt 2151 1 32,
   opAt 2152 .MLOAD,
   pushAt 2153 1 128,
   opAt 2154 .SHR,
   pushAt 2155 2 1536,
   opAt 2156 .MLOAD,
   pushAt 2157 2 1568,
   opAt 2158 .MLOAD,
   pushAt 2159 2 1664,
   opAt 2160 .MLOAD,
   pushAt 2161 2 1632,
   opAt 2162 .MLOAD,
   pushAt 2163 2 1504,
   opAt 2164 .MLOAD,
   pushAt 2165 2 1472,
   opAt 2166 .MLOAD,
   pushAt 2167 2 1440,
   opAt 2168 .MLOAD,
   pushAt 2169 2 1408,
   opAt 2170 .MLOAD,
   pushAt 2171 2 1376,
   opAt 2172 .MLOAD,
   pushAt 2173 2 1344,
   opAt 2174 .MLOAD,
   pushAt 2175 2 1312,
   opAt 2176 .MLOAD,
   opAt 2177 (.Dup ⟨14,by decide⟩)]
def blkNbTail (esize : Nat) : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  blkNbTailHead++(if UInt256.ofNat esize = UInt256.ofNat 1 then blkNbTailByte else [])++blkNbTailJoin
theorem jumpDestNbJoin : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2771 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2150 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
def blkZero8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 7812 .JUMPDEST,
   opAt 7813 (.Dup ⟨15,by decide⟩),
   pushAt 7814 2 2112,
   pushAt 7815 2 2080,
   opAt 7816 .MCOPY,
   pushAt 7817 2 2080,
   opAt 7818 .MLOAD,
   opAt 7819 (.Dup ⟨14,by decide⟩),
   pushAt 7820 2 2112,
   opAt 7821 .MLOAD,
   opAt 7822 (.Dup ⟨14,by decide⟩),
   opAt 7823 (.Dup ⟨0,by decide⟩),
   opAt 7824 (.Dup ⟨14,by decide⟩),
   opAt 7825 (.Dup ⟨5,by decide⟩),
   opAt 7826 .MULMOD,
   opAt 7827 (.Dup ⟨2,by decide⟩),
   opAt 7828 .ADDMOD,
   opAt 7829 (.Dup ⟨0,by decide⟩),
   opAt 7830 (.Swap ⟨1,by decide⟩),
   opAt 7831 .SUB,
   opAt 7832 (.Dup ⟨14,by decide⟩),
   opAt 7833 .MUL,
   opAt 7834 (.Swap ⟨1,by decide⟩),
   opAt 7835 (.Dup ⟨2,by decide⟩),
   pushAt 7836 1 128,
   opAt 7837 .SHR,
   opAt 7838 .MUL,
   opAt 7839 .GT,
   opAt 7840 (.Swap ⟨0,by decide⟩),
   opAt 7841 .SUB,
   pushAt 7842 2 2920,
   opAt 7843 .JUMP]
def blkZero4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 7845 .JUMPDEST,
   opAt 7846 (.Dup ⟨15,by decide⟩),
   pushAt 7847 2 2112,
   pushAt 7848 2 2080,
   opAt 7849 .MCOPY,
   pushAt 7850 2 2080,
   opAt 7851 .MLOAD,
   opAt 7852 (.Dup ⟨14,by decide⟩),
   pushAt 7853 2 2112,
   opAt 7854 .MLOAD,
   opAt 7855 (.Dup ⟨14,by decide⟩),
   opAt 7856 (.Dup ⟨0,by decide⟩),
   opAt 7857 (.Dup ⟨14,by decide⟩),
   opAt 7858 (.Dup ⟨5,by decide⟩),
   opAt 7859 .MULMOD,
   opAt 7860 (.Dup ⟨2,by decide⟩),
   opAt 7861 .ADDMOD,
   opAt 7862 (.Dup ⟨0,by decide⟩),
   opAt 7863 (.Swap ⟨1,by decide⟩),
   opAt 7864 .SUB,
   opAt 7865 (.Dup ⟨14,by decide⟩),
   opAt 7866 .MUL,
   opAt 7867 (.Swap ⟨1,by decide⟩),
   opAt 7868 (.Dup ⟨2,by decide⟩),
   pushAt 7869 1 128,
   opAt 7870 .SHR,
   opAt 7871 .MUL,
   opAt 7872 .GT,
   opAt 7873 (.Swap ⟨0,by decide⟩),
   opAt 7874 .SUB,
   pushAt 7875 2 10772,
   opAt 7876 .JUMP]
def blkEstimateSuffix8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2251 .JUMPDEST,
   pushAt 2252 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2253 (.Swap ⟨1,by decide⟩),
   opAt 2254 (.Dup ⟨14,by decide⟩),
   opAt 2255 .GT,
   opAt 2256 (.Dup ⟨2,by decide⟩),
   opAt 2257 .ADD,
   opAt 2258 .OR]
def blkEstimateSuffix4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8130 .JUMPDEST,
   pushAt 8131 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8132 (.Swap ⟨1,by decide⟩),
   opAt 8133 (.Dup ⟨14,by decide⟩),
   opAt 8134 .GT,
   opAt 8135 (.Dup ⟨2,by decide⟩),
   opAt 8136 .ADD,
   opAt 8137 .OR]
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2206 .JUMPDEST]
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2207 (.Dup ⟨15,by decide⟩),
   pushAt 2208 2 2112,
   pushAt 2209 2 2080,
   opAt 2210 .MCOPY]
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2211 2 2080,
   opAt 2212 .MLOAD,
   opAt 2213 (.Dup ⟨0,by decide⟩),
   opAt 2214 (.Dup ⟨14,by decide⟩),
   opAt 2215 .SHR,
   opAt 2216 (.Swap ⟨0,by decide⟩),
   pushAt 2217 2 1600,
   opAt 2218 .MLOAD,
   opAt 2219 .SHL,
   pushAt 2220 2 2112,
   opAt 2221 .MLOAD,
   opAt 2222 (.Dup ⟨15,by decide⟩),
   opAt 2223 .SHR,
   opAt 2224 .ADD,
   opAt 2225 (.Dup ⟨13,by decide⟩),
   opAt 2226 (.Dup ⟨0,by decide⟩),
   opAt 2227 (.Dup ⟨13,by decide⟩),
   opAt 2228 (.Dup ⟨4,by decide⟩),
   opAt 2229 .MULMOD,
   opAt 2230 (.Dup ⟨2,by decide⟩),
   opAt 2231 .ADDMOD,
   opAt 2232 (.Swap ⟨0,by decide⟩),
   opAt 2233 .SUB,
   opAt 2234 (.Dup ⟨12,by decide⟩),
   opAt 2235 .MUL,
   opAt 2236 (.Dup ⟨15,by decide⟩),
   opAt 2237 (.Dup ⟨1,by decide⟩),
   pushAt 2238 1 128,
   opAt 2239 .SHR,
   opAt 2240 .MUL,
   opAt 2241 (.Dup ⟨1,by decide⟩),
   pushAt 2242 0 0,
   opAt 2243 .MLOAD,
   opAt 2244 .MUL,
   pushAt 2245 2 2112,
   opAt 2246 .MLOAD,
   opAt 2247 .SUB,
   opAt 2248 .LT,
   opAt 2249 (.Swap ⟨0,by decide⟩),
   opAt 2250 .SUB,
   opAt 2251 .JUMPDEST,
   pushAt 2252 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2253 (.Swap ⟨1,by decide⟩),
   opAt 2254 (.Dup ⟨14,by decide⟩),
   opAt 2255 .GT,
   opAt 2256 (.Dup ⟨2,by decide⟩),
   opAt 2257 .ADD,
   opAt 2258 .OR]
def blk3013h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8085 .JUMPDEST]
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8086 (.Dup ⟨15,by decide⟩),
   pushAt 8087 2 2112,
   pushAt 8088 2 2080,
   opAt 8089 .MCOPY]
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8090 2 2080,
   opAt 8091 .MLOAD,
   opAt 8092 (.Dup ⟨0,by decide⟩),
   opAt 8093 (.Dup ⟨14,by decide⟩),
   opAt 8094 .SHR,
   opAt 8095 (.Swap ⟨0,by decide⟩),
   pushAt 8096 2 1600,
   opAt 8097 .MLOAD,
   opAt 8098 .SHL,
   pushAt 8099 2 2112,
   opAt 8100 .MLOAD,
   opAt 8101 (.Dup ⟨15,by decide⟩),
   opAt 8102 .SHR,
   opAt 8103 .ADD,
   opAt 8104 (.Dup ⟨13,by decide⟩),
   opAt 8105 (.Dup ⟨0,by decide⟩),
   opAt 8106 (.Dup ⟨13,by decide⟩),
   opAt 8107 (.Dup ⟨4,by decide⟩),
   opAt 8108 .MULMOD,
   opAt 8109 (.Dup ⟨2,by decide⟩),
   opAt 8110 .ADDMOD,
   opAt 8111 (.Swap ⟨0,by decide⟩),
   opAt 8112 .SUB,
   opAt 8113 (.Dup ⟨12,by decide⟩),
   opAt 8114 .MUL,
   opAt 8115 (.Dup ⟨15,by decide⟩),
   opAt 8116 (.Dup ⟨1,by decide⟩),
   pushAt 8117 1 128,
   opAt 8118 .SHR,
   opAt 8119 .MUL,
   opAt 8120 (.Dup ⟨1,by decide⟩),
   pushAt 8121 0 0,
   opAt 8122 .MLOAD,
   opAt 8123 .MUL,
   pushAt 8124 2 2112,
   opAt 8125 .MLOAD,
   opAt 8126 .SUB,
   opAt 8127 .LT,
   opAt 8128 (.Swap ⟨0,by decide⟩),
   opAt 8129 .SUB,
   opAt 8130 .JUMPDEST,
   pushAt 8131 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8132 (.Swap ⟨1,by decide⟩),
   opAt 8133 (.Dup ⟨14,by decide⟩),
   opAt 8134 .GT,
   opAt 8135 (.Dup ⟨2,by decide⟩),
   opAt 8136 .ADD,
   opAt 8137 .OR]
def blk3125Unc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2473 2 2080,
   opAt 2474 .MLOAD,
   opAt 2475 .ADD,
   opAt 2476 .SUB,
   pushAt 2477 2 3223,
   opAt 2478 .JUMPI,
   opAt 2486 .JUMPDEST,
   pushAt 2487 2 2080,
   opAt 2488 .MSTORE]
def blk3125hUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8240 2 2080,
   opAt 8241 .MLOAD,
   opAt 8242 .ADD,
   opAt 8243 .SUB,
   pushAt 8244 2 3223,
   opAt 8245 .JUMPI,
   opAt 2486 .JUMPDEST,
   pushAt 2487 2 2080,
   opAt 2488 .MSTORE]
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2473 2 2080,
   opAt 2474 .MLOAD,
   opAt 2475 .ADD,
   opAt 2476 .SUB,
   pushAt 2477 2 3223,
   opAt 2478 .JUMPI]
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  []
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2489 .JUMPDEST,
   pushAt 2490 0 0,
   pushAt 2491 2 2784,
   opAt 2492 .MLOAD]
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2493 .JUMPDEST,
   opAt 2494 (.Dup ⟨0,by decide⟩),
   opAt 2495 .MLOAD,
   pushAt 2496 2 2112,
   opAt 2497 (.Dup ⟨2,by decide⟩),
   opAt 2498 .SUB,
   opAt 2499 .MLOAD,
   opAt 2500 (.Dup ⟨1,by decide⟩),
   opAt 2501 .ADD,
   opAt 2502 (.Swap ⟨0,by decide⟩),
   opAt 2503 (.Dup ⟨1,by decide⟩),
   opAt 2504 .LT,
   opAt 2505 (.Swap ⟨0,by decide⟩),
   opAt 2506 (.Dup ⟨3,by decide⟩),
   opAt 2507 .ADD,
   opAt 2508 (.Swap ⟨2,by decide⟩),
   opAt 2509 (.Dup ⟨3,by decide⟩),
   opAt 2510 .LT,
   opAt 2511 .OR,
   opAt 2512 (.Swap ⟨1,by decide⟩),
   opAt 2513 (.Dup ⟨1,by decide⟩),
   opAt 2514 .MSTORE,
   pushAt 2515 1 31,
   opAt 2516 .NOT,
   opAt 2517 .ADD,
   pushAt 2518 2 2111,
   opAt 2519 (.Dup ⟨1,by decide⟩),
   opAt 2520 .GT,
   pushAt 2521 2 3234,
   opAt 2522 .JUMPI]
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2523 .POP,
   pushAt 2524 2 2080,
   opAt 2525 .MLOAD,
   opAt 2526 (.Dup ⟨1,by decide⟩),
   opAt 2527 .ADD,
   opAt 2528 (.Dup ⟨0,by decide⟩),
   pushAt 2529 2 2080,
   opAt 2530 .MSTORE,
   opAt 2531 .LT,
   opAt 2532 .ISZERO,
   pushAt 2533 2 3228,
   opAt 2534 .JUMPI]
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2535 2 2080,
   opAt 2536 .MLOAD,
   opAt 2537 (.Dup ⟨0,by decide⟩),
   opAt 2538 .ISZERO,
   opAt 2539 (.Swap ⟨0,by decide⟩),
   opAt 2540 .NOT,
   opAt 2541 (.Swap ⟨0,by decide⟩),
   pushAt 2542 2 10995,
   opAt 2543 .JUMPI]
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2479 .ADD,
   opAt 2480 (.Dup ⟨0,by decide⟩),
   opAt 2481 (.Dup ⟨2,by decide⟩),
   opAt 2482 .JUMPI]
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  []
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8240 2 2080,
   opAt 8241 .MLOAD,
   opAt 8242 .ADD,
   opAt 8243 .SUB,
   pushAt 8244 2 3223,
   opAt 8245 .JUMPI]
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8246 .ADD,
   opAt 8247 (.Dup ⟨0,by decide⟩),
   opAt 8248 (.Dup ⟨2,by decide⟩),
   opAt 8249 .JUMPI]
theorem jumpDestBigC : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 174 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 133 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 133 = 174 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest4657 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2554 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1997 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1997 = 2554 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestNeg4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2501 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1963 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1963 = 2501 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestNegT : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2612 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2033 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2033 = 2612 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest4839 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2862 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2206 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2206 = 2862 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestHead4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10714 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8085 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 8085 = 10714 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5115 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3228 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2489 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2489 = 3228 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5121 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3234 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2493 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2493 = 3234 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestLazyStore : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3223 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2486 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2486 = 3223 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestUnc : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3223 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2486 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2486 = 3223 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5311 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10995 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8286 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 8286 = 10995 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest2471 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2515 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1972 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1972 = 2515 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
end CycleSubmission.Global.Fast
namespace CycleSubmission.Global.Fast
open EvmSemantics EvmSemantics.EVM
end CycleSubmission.Global.Fast
