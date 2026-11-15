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
  [opAt 465 (.Dup ⟨0,by decide⟩),
   opAt 466 (.Dup ⟨3,by decide⟩),
   opAt 467 .XOR,
   pushAt 468 1 207,
   opAt 469 .JUMPI]
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 470 (.Dup ⟨0,by decide⟩),
   pushAt 471 1 96,
   pushAt 472 2 2112,
   opAt 473 .CALLDATACOPY]
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2012 (.Dup ⟨0,by decide⟩),
   pushAt 2013 1 128,
   opAt 2014 .EQ,
   pushAt 2015 2 2513,
   opAt 2016 .JUMPI]
def negS8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2017 1 224,
   opAt 2018 .MLOAD,
   pushAt 2019 0 0,
   opAt 2020 .SUB,
   pushAt 2021 2 1504,
   opAt 2022 .MSTORE]
def negN8a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2023 1 192,
   opAt 2024 .MLOAD,
   opAt 2025 .NOT,
   pushAt 2026 2 1472,
   opAt 2027 .MSTORE]
def negN8b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2028 1 160,
   opAt 2029 .MLOAD,
   opAt 2030 .NOT,
   pushAt 2031 2 1440,
   opAt 2032 .MSTORE]
def negN8c :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2033 1 128,
   opAt 2034 .MLOAD,
   opAt 2035 .NOT,
   pushAt 2036 2 1408,
   opAt 2037 .MSTORE]
def negN8d :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2038 1 96,
   opAt 2039 .MLOAD,
   opAt 2040 .NOT,
   pushAt 2041 2 1376,
   opAt 2042 .MSTORE]
def negS4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1974 1 96,
   opAt 1975 .MLOAD,
   pushAt 1976 0 0,
   opAt 1977 .SUB,
   pushAt 1978 2 1376,
   opAt 1979 .MSTORE]
def negJ4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1973 .JUMPDEST]
def negJ4b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1980 2 2624,
   opAt 1981 .JUMP]
def negJT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2043 .JUMPDEST]
def blkNeg8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negS8++negN8a++negN8b++negN8c++negN8d
def blkNeg4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negJ4++negS4++negJ4b
def blkNegT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2043 .JUMPDEST,
   pushAt 2044 1 64,
   opAt 2045 .MLOAD,
   opAt 2046 .NOT,
   pushAt 2047 2 1344,
   opAt 2048 .MSTORE,
   pushAt 2049 1 32,
   opAt 2050 .MLOAD,
   opAt 2051 .NOT,
   pushAt 2052 2 1312,
   opAt 2053 .MSTORE,
   pushAt 2054 0 0,
   opAt 2055 .MLOAD,
   opAt 2056 (.Dup ⟨0,by decide⟩),
   opAt 2057 .NOT,
   pushAt 2058 2 1280,
   opAt 2059 .MSTORE]
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2060 (.Dup ⟨0,by decide⟩),
   pushAt 2061 0 0,
   opAt 2062 .SUB,
   opAt 2063 (.Dup ⟨1,by decide⟩),
   opAt 2064 .AND]
def blk2919b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2066 (.Dup ⟨0,by decide⟩),
   pushAt 2067 1 1,
   opAt 2068 .ADD,
   pushAt 2069 2 1600,
   opAt 2070 .MSTORE,
   pushAt 2071 1 255,
   opAt 2072 .SUB,
   opAt 2073 (.Dup ⟨0,by decide⟩),
   pushAt 2074 2 1536,
   opAt 2075 .MSTORE,
   opAt 2076 .SHR,
   opAt 2077 (.Dup ⟨0,by decide⟩),
   pushAt 2078 2 1568,
   opAt 2079 .MSTORE,
   opAt 2080 (.Dup ⟨0,by decide⟩),
   opAt 2081 (.Dup ⟨0,by decide⟩),
   pushAt 2082 0 0,
   opAt 2083 .SUB,
   opAt 2084 .MOD,
   pushAt 2085 2 1632,
   opAt 2086 .MSTORE]
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2087 2 2752,
   opAt 2088 .MLOAD,
   opAt 2089 .MLOAD,
   opAt 2090 (.Dup ⟨0,by decide⟩),
   opAt 2091 (.Dup ⟨2,by decide⟩),
   opAt 2092 .MUL]
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2093 (.Dup ⟨0,by decide⟩),
   pushAt 2094 1 3,
   opAt 2095 .MUL,
   pushAt 2096 1 2,
   opAt 2097 .XOR,
   opAt 2098 (.Dup ⟨0,by decide⟩),
   opAt 2099 (.Dup ⟨2,by decide⟩),
   opAt 2100 .MUL,
   pushAt 2101 1 2,
   opAt 2102 .SUB,
   opAt 2103 .MUL,
   opAt 2104 (.Dup ⟨0,by decide⟩),
   opAt 2105 (.Dup ⟨2,by decide⟩),
   opAt 2106 .MUL,
   pushAt 2107 1 2,
   opAt 2108 .SUB,
   opAt 2109 .MUL,
   opAt 2110 (.Dup ⟨0,by decide⟩),
   opAt 2111 (.Dup ⟨2,by decide⟩),
   opAt 2112 .MUL,
   pushAt 2113 1 2,
   opAt 2114 .SUB,
   opAt 2115 .MUL,
   opAt 2116 (.Dup ⟨0,by decide⟩),
   opAt 2117 (.Dup ⟨2,by decide⟩),
   opAt 2118 .MUL,
   pushAt 2119 1 2,
   opAt 2120 .SUB,
   opAt 2121 .MUL,
   opAt 2122 (.Dup ⟨0,by decide⟩),
   opAt 2123 (.Dup ⟨2,by decide⟩),
   opAt 2124 .MUL,
   pushAt 2125 1 2,
   opAt 2126 .SUB,
   opAt 2127 .MUL,
   opAt 2128 (.Dup ⟨0,by decide⟩),
   opAt 2129 (.Swap ⟨1,by decide⟩),
   opAt 2130 .MUL,
   pushAt 2131 1 2,
   opAt 2132 .SUB,
   opAt 2133 .MUL]
def blkNbTailHead : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2134 (.Dup ⟨0,by decide⟩),
   opAt 2135 (.Swap ⟨1,by decide⟩),
   opAt 2136 .MUL,
   pushAt 2137 2 1664,
   opAt 2138 .MSTORE,
   opAt 2139 .MUL,
   pushAt 2140 0 0,
   opAt 2141 .SUB,
   pushAt 2142 2 2720,
   opAt 2143 .MSTORE,
   pushAt 2144 2 2534,
   opAt 2145 (.Dup ⟨4,by decide⟩),
   pushAt 2146 1 1,
   opAt 2147 .XOR,
   pushAt 2148 2 2783,
   opAt 2149 .JUMPI]
def blkNbTailByte : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2150 2 2656,
   opAt 2151 .MLOAD,
   opAt 2152 .CALLDATALOAD,
   pushAt 2153 0 0,
   opAt 2154 .BYTE,
   pushAt 2155 1 3,
   opAt 2156 .EQ,
   pushAt 2157 2 7877,
   opAt 2158 .MUL,
   opAt 2159 .ADD]
def blkNbTailJoin : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2160 .JUMPDEST,
   pushAt 2161 1 32,
   opAt 2162 .MLOAD,
   pushAt 2163 1 128,
   opAt 2164 .SHR,
   pushAt 2165 2 1536,
   opAt 2166 .MLOAD,
   pushAt 2167 2 1568,
   opAt 2168 .MLOAD,
   pushAt 2169 2 1664,
   opAt 2170 .MLOAD,
   pushAt 2171 2 1632,
   opAt 2172 .MLOAD,
   pushAt 2173 2 1504,
   opAt 2174 .MLOAD,
   pushAt 2175 2 1472,
   opAt 2176 .MLOAD,
   pushAt 2177 2 1440,
   opAt 2178 .MLOAD,
   pushAt 2179 2 1408,
   opAt 2180 .MLOAD,
   pushAt 2181 2 1376,
   opAt 2182 .MLOAD,
   pushAt 2183 2 1344,
   opAt 2184 .MLOAD,
   pushAt 2185 2 1312,
   opAt 2186 .MLOAD,
   opAt 2187 (.Dup ⟨14,by decide⟩)]
def blkNbTail (esize : Nat) : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  blkNbTailHead++(if UInt256.ofNat esize = UInt256.ofNat 1 then blkNbTailByte else [])++blkNbTailJoin
theorem jumpDestNbJoin : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2783 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2160 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
def blkZero8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 7832 .JUMPDEST,
   opAt 7833 (.Dup ⟨15,by decide⟩),
   pushAt 7834 2 2112,
   pushAt 7835 2 2080,
   opAt 7836 .MCOPY,
   pushAt 7837 2 2080,
   opAt 7838 .MLOAD,
   opAt 7839 (.Dup ⟨14,by decide⟩),
   pushAt 7840 2 2112,
   opAt 7841 .MLOAD,
   opAt 7842 (.Dup ⟨14,by decide⟩),
   opAt 7843 (.Dup ⟨0,by decide⟩),
   opAt 7844 (.Dup ⟨14,by decide⟩),
   opAt 7845 (.Dup ⟨5,by decide⟩),
   opAt 7846 .MULMOD,
   opAt 7847 (.Dup ⟨2,by decide⟩),
   opAt 7848 .ADDMOD,
   opAt 7849 (.Dup ⟨0,by decide⟩),
   opAt 7850 (.Swap ⟨1,by decide⟩),
   opAt 7851 .SUB,
   opAt 7852 (.Dup ⟨14,by decide⟩),
   opAt 7853 .MUL,
   opAt 7854 (.Swap ⟨1,by decide⟩),
   opAt 7855 (.Dup ⟨2,by decide⟩),
   pushAt 7856 1 128,
   opAt 7857 .SHR,
   opAt 7858 .MUL,
   opAt 7859 .GT,
   opAt 7860 (.Swap ⟨0,by decide⟩),
   opAt 7861 .SUB,
   pushAt 7862 2 2932,
   opAt 7863 .JUMP]
def blkZero4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 7865 .JUMPDEST,
   opAt 7866 (.Dup ⟨15,by decide⟩),
   pushAt 7867 2 2112,
   pushAt 7868 2 2080,
   opAt 7869 .MCOPY,
   pushAt 7870 2 2080,
   opAt 7871 .MLOAD,
   opAt 7872 (.Dup ⟨14,by decide⟩),
   pushAt 7873 2 2112,
   opAt 7874 .MLOAD,
   opAt 7875 (.Dup ⟨14,by decide⟩),
   opAt 7876 (.Dup ⟨0,by decide⟩),
   opAt 7877 (.Dup ⟨14,by decide⟩),
   opAt 7878 (.Dup ⟨5,by decide⟩),
   opAt 7879 .MULMOD,
   opAt 7880 (.Dup ⟨2,by decide⟩),
   opAt 7881 .ADDMOD,
   opAt 7882 (.Dup ⟨0,by decide⟩),
   opAt 7883 (.Swap ⟨1,by decide⟩),
   opAt 7884 .SUB,
   opAt 7885 (.Dup ⟨14,by decide⟩),
   opAt 7886 .MUL,
   opAt 7887 (.Swap ⟨1,by decide⟩),
   opAt 7888 (.Dup ⟨2,by decide⟩),
   pushAt 7889 1 128,
   opAt 7890 .SHR,
   opAt 7891 .MUL,
   opAt 7892 .GT,
   opAt 7893 (.Swap ⟨0,by decide⟩),
   opAt 7894 .SUB,
   pushAt 7895 2 10768,
   opAt 7896 .JUMP]
def blkEstimateSuffix8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2261 .JUMPDEST,
   pushAt 2262 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2263 (.Swap ⟨1,by decide⟩),
   opAt 2264 (.Dup ⟨14,by decide⟩),
   opAt 2265 .GT,
   opAt 2266 (.Dup ⟨2,by decide⟩),
   opAt 2267 .ADD,
   opAt 2268 .OR]
def blkEstimateSuffix4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8151 .JUMPDEST,
   pushAt 8152 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8153 (.Swap ⟨1,by decide⟩),
   opAt 8154 (.Dup ⟨14,by decide⟩),
   opAt 8155 .GT,
   opAt 8156 (.Dup ⟨2,by decide⟩),
   opAt 8157 .ADD,
   opAt 8158 .OR]
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2216 .JUMPDEST]
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2217 (.Dup ⟨15,by decide⟩),
   pushAt 2218 2 2112,
   pushAt 2219 2 2080,
   opAt 2220 .MCOPY]
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2221 2 2080,
   opAt 2222 .MLOAD,
   opAt 2223 (.Dup ⟨0,by decide⟩),
   opAt 2224 (.Dup ⟨14,by decide⟩),
   opAt 2225 .SHR,
   opAt 2226 (.Swap ⟨0,by decide⟩),
   pushAt 2227 2 1600,
   opAt 2228 .MLOAD,
   opAt 2229 .SHL,
   pushAt 2230 2 2112,
   opAt 2231 .MLOAD,
   opAt 2232 (.Dup ⟨15,by decide⟩),
   opAt 2233 .SHR,
   opAt 2234 .ADD,
   opAt 2235 (.Dup ⟨13,by decide⟩),
   opAt 2236 (.Dup ⟨0,by decide⟩),
   opAt 2237 (.Dup ⟨13,by decide⟩),
   opAt 2238 (.Dup ⟨4,by decide⟩),
   opAt 2239 .MULMOD,
   opAt 2240 (.Dup ⟨2,by decide⟩),
   opAt 2241 .ADDMOD,
   opAt 2242 (.Swap ⟨0,by decide⟩),
   opAt 2243 .SUB,
   opAt 2244 (.Dup ⟨12,by decide⟩),
   opAt 2245 .MUL,
   opAt 2246 (.Dup ⟨15,by decide⟩),
   opAt 2247 (.Dup ⟨1,by decide⟩),
   pushAt 2248 1 128,
   opAt 2249 .SHR,
   opAt 2250 .MUL,
   opAt 2251 (.Dup ⟨1,by decide⟩),
   pushAt 2252 0 0,
   opAt 2253 .MLOAD,
   opAt 2254 .MUL,
   pushAt 2255 2 2112,
   opAt 2256 .MLOAD,
   opAt 2257 .SUB,
   opAt 2258 .LT,
   opAt 2259 (.Swap ⟨0,by decide⟩),
   opAt 2260 .SUB,
   opAt 2261 .JUMPDEST,
   pushAt 2262 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2263 (.Swap ⟨1,by decide⟩),
   opAt 2264 (.Dup ⟨14,by decide⟩),
   opAt 2265 .GT,
   opAt 2266 (.Dup ⟨2,by decide⟩),
   opAt 2267 .ADD,
   opAt 2268 .OR]
def blk3013h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8106 .JUMPDEST]
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8107 (.Dup ⟨15,by decide⟩),
   pushAt 8108 2 2112,
   pushAt 8109 2 2080,
   opAt 8110 .MCOPY]
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8111 2 2080,
   opAt 8112 .MLOAD,
   opAt 8113 (.Dup ⟨0,by decide⟩),
   opAt 8114 (.Dup ⟨14,by decide⟩),
   opAt 8115 .SHR,
   opAt 8116 (.Swap ⟨0,by decide⟩),
   pushAt 8117 2 1600,
   opAt 8118 .MLOAD,
   opAt 8119 .SHL,
   pushAt 8120 2 2112,
   opAt 8121 .MLOAD,
   opAt 8122 (.Dup ⟨15,by decide⟩),
   opAt 8123 .SHR,
   opAt 8124 .ADD,
   opAt 8125 (.Dup ⟨13,by decide⟩),
   opAt 8126 (.Dup ⟨0,by decide⟩),
   opAt 8127 (.Dup ⟨13,by decide⟩),
   opAt 8128 (.Dup ⟨4,by decide⟩),
   opAt 8129 .MULMOD,
   opAt 8130 (.Dup ⟨2,by decide⟩),
   opAt 8131 .ADDMOD,
   opAt 8132 (.Swap ⟨0,by decide⟩),
   opAt 8133 .SUB,
   opAt 8134 (.Dup ⟨12,by decide⟩),
   opAt 8135 .MUL,
   opAt 8136 (.Dup ⟨15,by decide⟩),
   opAt 8137 (.Dup ⟨1,by decide⟩),
   pushAt 8138 1 128,
   opAt 8139 .SHR,
   opAt 8140 .MUL,
   opAt 8141 (.Dup ⟨1,by decide⟩),
   pushAt 8142 0 0,
   opAt 8143 .MLOAD,
   opAt 8144 .MUL,
   pushAt 8145 2 2112,
   opAt 8146 .MLOAD,
   opAt 8147 .SUB,
   opAt 8148 .LT,
   opAt 8149 (.Swap ⟨0,by decide⟩),
   opAt 8150 .SUB,
   opAt 8151 .JUMPDEST,
   pushAt 8152 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8153 (.Swap ⟨1,by decide⟩),
   opAt 8154 (.Dup ⟨14,by decide⟩),
   opAt 8155 .GT,
   opAt 8156 (.Dup ⟨2,by decide⟩),
   opAt 8157 .ADD,
   opAt 8158 .OR]
def blk3125Unc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2483 2 2080,
   opAt 2484 .MLOAD,
   opAt 2485 .ADD,
   opAt 2486 .SUB,
   pushAt 2487 2 3235,
   opAt 2488 .JUMPI,
   opAt 2496 .JUMPDEST,
   pushAt 2497 2 2080,
   opAt 2498 .MSTORE]
def blk3125hUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8261 2 2080,
   opAt 8262 .MLOAD,
   opAt 8263 .ADD,
   opAt 8264 .SUB,
   pushAt 8265 2 3235,
   opAt 8266 .JUMPI,
   opAt 2496 .JUMPDEST,
   pushAt 2497 2 2080,
   opAt 2498 .MSTORE]
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2483 2 2080,
   opAt 2484 .MLOAD,
   opAt 2485 .ADD,
   opAt 2486 .SUB,
   pushAt 2487 2 3235,
   opAt 2488 .JUMPI]
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  []
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2499 .JUMPDEST,
   pushAt 2500 0 0,
   pushAt 2501 2 2784,
   opAt 2502 .MLOAD]
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2503 .JUMPDEST,
   opAt 2504 (.Dup ⟨0,by decide⟩),
   opAt 2505 .MLOAD,
   pushAt 2506 2 2112,
   opAt 2507 (.Dup ⟨2,by decide⟩),
   opAt 2508 .SUB,
   opAt 2509 .MLOAD,
   opAt 2510 (.Dup ⟨1,by decide⟩),
   opAt 2511 .ADD,
   opAt 2512 (.Swap ⟨0,by decide⟩),
   opAt 2513 (.Dup ⟨1,by decide⟩),
   opAt 2514 .LT,
   opAt 2515 (.Swap ⟨0,by decide⟩),
   opAt 2516 (.Dup ⟨3,by decide⟩),
   opAt 2517 .ADD,
   opAt 2518 (.Swap ⟨2,by decide⟩),
   opAt 2519 (.Dup ⟨3,by decide⟩),
   opAt 2520 .LT,
   opAt 2521 .OR,
   opAt 2522 (.Swap ⟨1,by decide⟩),
   opAt 2523 (.Dup ⟨1,by decide⟩),
   opAt 2524 .MSTORE,
   pushAt 2525 1 31,
   opAt 2526 .NOT,
   opAt 2527 .ADD,
   pushAt 2528 2 2111,
   opAt 2529 (.Dup ⟨1,by decide⟩),
   opAt 2530 .GT,
   pushAt 2531 2 3246,
   opAt 2532 .JUMPI]
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2533 .POP,
   pushAt 2534 2 2080,
   opAt 2535 .MLOAD,
   opAt 2536 (.Dup ⟨1,by decide⟩),
   opAt 2537 .ADD,
   opAt 2538 (.Dup ⟨0,by decide⟩),
   pushAt 2539 2 2080,
   opAt 2540 .MSTORE,
   opAt 2541 .LT,
   opAt 2542 .ISZERO,
   pushAt 2543 2 3240,
   opAt 2544 .JUMPI]
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2545 2 2080,
   opAt 2546 .MLOAD,
   opAt 2547 (.Dup ⟨0,by decide⟩),
   opAt 2548 .ISZERO,
   opAt 2549 (.Swap ⟨0,by decide⟩),
   opAt 2550 .NOT,
   opAt 2551 (.Swap ⟨0,by decide⟩),
   pushAt 2552 2 10991,
   opAt 2553 .JUMPI]
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2489 .ADD,
   opAt 2490 (.Dup ⟨0,by decide⟩),
   opAt 2491 (.Dup ⟨2,by decide⟩),
   opAt 2492 .JUMPI]
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  []
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8261 2 2080,
   opAt 8262 .MLOAD,
   opAt 8263 .ADD,
   opAt 8264 .SUB,
   pushAt 8265 2 3235,
   opAt 8266 .JUMPI]
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8267 .ADD,
   opAt 8268 (.Dup ⟨0,by decide⟩),
   opAt 8269 (.Dup ⟨2,by decide⟩),
   opAt 8270 .JUMPI]
theorem jumpDestBigC : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 207 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 134 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 134 = 207 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest4657 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2566 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2007 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2007 = 2566 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestNeg4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2513 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1973 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1973 = 2513 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestNegT : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2624 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2043 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2043 = 2624 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest4839 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2874 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2216 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2216 = 2874 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestHead4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10710 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8106 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 8106 = 10710 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5115 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3240 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2499 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2499 = 3240 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5121 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3246 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2503 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2503 = 3246 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestLazyStore : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3235 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2496 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2496 = 3235 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestUnc : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3235 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2496 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2496 = 3235 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5311 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10991 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8307 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 8307 = 10991 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest2471 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2527 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1982 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1982 = 2527 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
end CycleSubmission.Global.Fast
namespace CycleSubmission.Global.Fast
open EvmSemantics EvmSemantics.EVM
end CycleSubmission.Global.Fast
