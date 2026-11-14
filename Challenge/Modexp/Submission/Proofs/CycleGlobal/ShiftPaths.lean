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
  [opAt 465 .JUMPDEST,
   opAt 466 (.Dup ⟨0,by decide⟩),
   opAt 467 (.Dup ⟨3,by decide⟩),
   opAt 468 .XOR,
   pushAt 469 1 207,
   opAt 470 .JUMPI]
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 471 (.Dup ⟨0,by decide⟩),
   pushAt 472 1 96,
   pushAt 473 2 2112,
   opAt 474 .CALLDATACOPY]
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2013 (.Dup ⟨0,by decide⟩),
   pushAt 2014 1 128,
   opAt 2015 .EQ,
   pushAt 2016 2 2513,
   opAt 2017 .JUMPI]
def negS8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2018 1 224,
   opAt 2019 .MLOAD,
   pushAt 2020 0 0,
   opAt 2021 .SUB,
   pushAt 2022 2 1504,
   opAt 2023 .MSTORE]
def negN8a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2024 1 192,
   opAt 2025 .MLOAD,
   opAt 2026 .NOT,
   pushAt 2027 2 1472,
   opAt 2028 .MSTORE]
def negN8b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2029 1 160,
   opAt 2030 .MLOAD,
   opAt 2031 .NOT,
   pushAt 2032 2 1440,
   opAt 2033 .MSTORE]
def negN8c :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2034 1 128,
   opAt 2035 .MLOAD,
   opAt 2036 .NOT,
   pushAt 2037 2 1408,
   opAt 2038 .MSTORE]
def negN8d :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2039 1 96,
   opAt 2040 .MLOAD,
   opAt 2041 .NOT,
   pushAt 2042 2 1376,
   opAt 2043 .MSTORE]
def negS4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1975 1 96,
   opAt 1976 .MLOAD,
   pushAt 1977 0 0,
   opAt 1978 .SUB,
   pushAt 1979 2 1376,
   opAt 1980 .MSTORE]
def negJ4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1974 .JUMPDEST]
def negJ4b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1981 2 2624,
   opAt 1982 .JUMP]
def negJT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2044 .JUMPDEST]
def blkNeg8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negS8++negN8a++negN8b++negN8c++negN8d
def blkNeg4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negJ4++negS4++negJ4b
def blkNegT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2044 .JUMPDEST,
   pushAt 2045 1 64,
   opAt 2046 .MLOAD,
   opAt 2047 .NOT,
   pushAt 2048 2 1344,
   opAt 2049 .MSTORE,
   pushAt 2050 1 32,
   opAt 2051 .MLOAD,
   opAt 2052 .NOT,
   pushAt 2053 2 1312,
   opAt 2054 .MSTORE,
   pushAt 2055 0 0,
   opAt 2056 .MLOAD,
   opAt 2057 (.Dup ⟨0,by decide⟩),
   opAt 2058 .NOT,
   pushAt 2059 2 1280,
   opAt 2060 .MSTORE]
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2061 (.Dup ⟨0,by decide⟩),
   pushAt 2062 0 0,
   opAt 2063 .SUB,
   opAt 2064 (.Dup ⟨1,by decide⟩),
   opAt 2065 .AND]
def blk2919b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2067 (.Dup ⟨0,by decide⟩),
   pushAt 2068 1 1,
   opAt 2069 .ADD,
   pushAt 2070 2 1600,
   opAt 2071 .MSTORE,
   pushAt 2072 1 255,
   opAt 2073 .SUB,
   opAt 2074 (.Dup ⟨0,by decide⟩),
   pushAt 2075 2 1536,
   opAt 2076 .MSTORE,
   opAt 2077 .SHR,
   opAt 2078 (.Dup ⟨0,by decide⟩),
   pushAt 2079 2 1568,
   opAt 2080 .MSTORE,
   opAt 2081 (.Dup ⟨0,by decide⟩),
   opAt 2082 (.Dup ⟨0,by decide⟩),
   pushAt 2083 0 0,
   opAt 2084 .SUB,
   opAt 2085 .MOD,
   pushAt 2086 2 1632,
   opAt 2087 .MSTORE]
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2088 2 2752,
   opAt 2089 .MLOAD,
   opAt 2090 .MLOAD,
   opAt 2091 (.Dup ⟨0,by decide⟩),
   opAt 2092 (.Dup ⟨2,by decide⟩),
   opAt 2093 .MUL]
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2094 (.Dup ⟨0,by decide⟩),
   pushAt 2095 1 3,
   opAt 2096 .MUL,
   pushAt 2097 1 2,
   opAt 2098 .XOR,
   opAt 2099 (.Dup ⟨0,by decide⟩),
   opAt 2100 (.Dup ⟨2,by decide⟩),
   opAt 2101 .MUL,
   pushAt 2102 1 2,
   opAt 2103 .SUB,
   opAt 2104 .MUL,
   opAt 2105 (.Dup ⟨0,by decide⟩),
   opAt 2106 (.Dup ⟨2,by decide⟩),
   opAt 2107 .MUL,
   pushAt 2108 1 2,
   opAt 2109 .SUB,
   opAt 2110 .MUL,
   opAt 2111 (.Dup ⟨0,by decide⟩),
   opAt 2112 (.Dup ⟨2,by decide⟩),
   opAt 2113 .MUL,
   pushAt 2114 1 2,
   opAt 2115 .SUB,
   opAt 2116 .MUL,
   opAt 2117 (.Dup ⟨0,by decide⟩),
   opAt 2118 (.Dup ⟨2,by decide⟩),
   opAt 2119 .MUL,
   pushAt 2120 1 2,
   opAt 2121 .SUB,
   opAt 2122 .MUL,
   opAt 2123 (.Dup ⟨0,by decide⟩),
   opAt 2124 (.Dup ⟨2,by decide⟩),
   opAt 2125 .MUL,
   pushAt 2126 1 2,
   opAt 2127 .SUB,
   opAt 2128 .MUL,
   opAt 2129 (.Dup ⟨0,by decide⟩),
   opAt 2130 (.Swap ⟨1,by decide⟩),
   opAt 2131 .MUL,
   pushAt 2132 1 2,
   opAt 2133 .SUB,
   opAt 2134 .MUL]
def blkNbTailHead : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2135 (.Dup ⟨0,by decide⟩),
   opAt 2136 (.Swap ⟨1,by decide⟩),
   opAt 2137 .MUL,
   pushAt 2138 2 1664,
   opAt 2139 .MSTORE,
   opAt 2140 .MUL,
   pushAt 2141 0 0,
   opAt 2142 .SUB,
   pushAt 2143 2 2720,
   opAt 2144 .MSTORE,
   pushAt 2145 2 2534,
   opAt 2146 (.Dup ⟨4,by decide⟩),
   pushAt 2147 1 1,
   opAt 2148 .XOR,
   pushAt 2149 2 2783,
   opAt 2150 .JUMPI]
def blkNbTailByte : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2151 2 2656,
   opAt 2152 .MLOAD,
   opAt 2153 .CALLDATALOAD,
   pushAt 2154 0 0,
   opAt 2155 .BYTE,
   pushAt 2156 1 3,
   opAt 2157 .EQ,
   pushAt 2158 2 7793,
   opAt 2159 .MUL,
   opAt 2160 .ADD]
def blkNbTailJoin : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2161 .JUMPDEST,
   pushAt 2162 1 32,
   opAt 2163 .MLOAD,
   pushAt 2164 1 128,
   opAt 2165 .SHR,
   pushAt 2166 2 1536,
   opAt 2167 .MLOAD,
   pushAt 2168 2 1568,
   opAt 2169 .MLOAD,
   pushAt 2170 2 1664,
   opAt 2171 .MLOAD,
   pushAt 2172 2 1632,
   opAt 2173 .MLOAD,
   pushAt 2174 2 1504,
   opAt 2175 .MLOAD,
   pushAt 2176 2 1472,
   opAt 2177 .MLOAD,
   pushAt 2178 2 1440,
   opAt 2179 .MLOAD,
   pushAt 2180 2 1408,
   opAt 2181 .MLOAD,
   pushAt 2182 2 1376,
   opAt 2183 .MLOAD,
   pushAt 2184 2 1344,
   opAt 2185 .MLOAD,
   pushAt 2186 2 1312,
   opAt 2187 .MLOAD,
   opAt 2188 (.Dup ⟨14,by decide⟩)]
def blkNbTail (esize : Nat) : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  blkNbTailHead++(if UInt256.ofNat esize = UInt256.ofNat 1 then blkNbTailByte else [])++blkNbTailJoin
theorem jumpDestNbJoin : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2783 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2161 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
def blkZero8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 7843 .JUMPDEST,
   opAt 7844 (.Dup ⟨15,by decide⟩),
   pushAt 7845 2 2112,
   pushAt 7846 2 2080,
   opAt 7847 .MCOPY,
   pushAt 7848 2 2080,
   opAt 7849 .MLOAD,
   opAt 7850 (.Dup ⟨14,by decide⟩),
   pushAt 7851 2 2112,
   opAt 7852 .MLOAD,
   opAt 7853 (.Dup ⟨14,by decide⟩),
   opAt 7854 (.Dup ⟨0,by decide⟩),
   opAt 7855 (.Dup ⟨14,by decide⟩),
   opAt 7856 (.Dup ⟨5,by decide⟩),
   opAt 7857 .MULMOD,
   opAt 7858 (.Dup ⟨2,by decide⟩),
   opAt 7859 .ADDMOD,
   opAt 7860 (.Dup ⟨0,by decide⟩),
   opAt 7861 (.Swap ⟨1,by decide⟩),
   opAt 7862 .SUB,
   opAt 7863 (.Dup ⟨14,by decide⟩),
   opAt 7864 .MUL,
   opAt 7865 (.Swap ⟨1,by decide⟩),
   opAt 7866 (.Dup ⟨2,by decide⟩),
   pushAt 7867 1 128,
   opAt 7868 .SHR,
   opAt 7869 .MUL,
   opAt 7870 .GT,
   opAt 7871 (.Swap ⟨0,by decide⟩),
   opAt 7872 .SUB,
   pushAt 7873 2 2932,
   opAt 7874 .JUMP]
def blkZero4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 7876 .JUMPDEST,
   opAt 7877 (.Dup ⟨15,by decide⟩),
   pushAt 7878 2 2112,
   pushAt 7879 2 2080,
   opAt 7880 .MCOPY,
   pushAt 7881 2 2080,
   opAt 7882 .MLOAD,
   opAt 7883 (.Dup ⟨14,by decide⟩),
   pushAt 7884 2 2112,
   opAt 7885 .MLOAD,
   opAt 7886 (.Dup ⟨14,by decide⟩),
   opAt 7887 (.Dup ⟨0,by decide⟩),
   opAt 7888 (.Dup ⟨14,by decide⟩),
   opAt 7889 (.Dup ⟨5,by decide⟩),
   opAt 7890 .MULMOD,
   opAt 7891 (.Dup ⟨2,by decide⟩),
   opAt 7892 .ADDMOD,
   opAt 7893 (.Dup ⟨0,by decide⟩),
   opAt 7894 (.Swap ⟨1,by decide⟩),
   opAt 7895 .SUB,
   opAt 7896 (.Dup ⟨14,by decide⟩),
   opAt 7897 .MUL,
   opAt 7898 (.Swap ⟨1,by decide⟩),
   opAt 7899 (.Dup ⟨2,by decide⟩),
   pushAt 7900 1 128,
   opAt 7901 .SHR,
   opAt 7902 .MUL,
   opAt 7903 .GT,
   opAt 7904 (.Swap ⟨0,by decide⟩),
   opAt 7905 .SUB,
   pushAt 7906 2 10684,
   opAt 7907 .JUMP]
def blkEstimateSuffix8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2262 .JUMPDEST,
   pushAt 2263 0 0,
   opAt 2264 .NOT,
   opAt 2265 (.Swap ⟨1,by decide⟩),
   opAt 2266 (.Dup ⟨14,by decide⟩),
   opAt 2267 .GT,
   opAt 2268 (.Dup ⟨2,by decide⟩),
   opAt 2269 .ADD,
   opAt 2270 .OR]
def blkEstimateSuffix4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8162 .JUMPDEST,
   pushAt 8163 0 0,
   opAt 8164 .NOT,
   opAt 8165 (.Swap ⟨1,by decide⟩),
   opAt 8166 (.Dup ⟨14,by decide⟩),
   opAt 8167 .GT,
   opAt 8168 (.Dup ⟨2,by decide⟩),
   opAt 8169 .ADD,
   opAt 8170 .OR]
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2217 .JUMPDEST]
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2218 (.Dup ⟨15,by decide⟩),
   pushAt 2219 2 2112,
   pushAt 2220 2 2080,
   opAt 2221 .MCOPY]
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2222 2 2080,
   opAt 2223 .MLOAD,
   opAt 2224 (.Dup ⟨0,by decide⟩),
   opAt 2225 (.Dup ⟨14,by decide⟩),
   opAt 2226 .SHR,
   opAt 2227 (.Swap ⟨0,by decide⟩),
   pushAt 2228 2 1600,
   opAt 2229 .MLOAD,
   opAt 2230 .SHL,
   pushAt 2231 2 2112,
   opAt 2232 .MLOAD,
   opAt 2233 (.Dup ⟨15,by decide⟩),
   opAt 2234 .SHR,
   opAt 2235 .ADD,
   opAt 2236 (.Dup ⟨13,by decide⟩),
   opAt 2237 (.Dup ⟨0,by decide⟩),
   opAt 2238 (.Dup ⟨13,by decide⟩),
   opAt 2239 (.Dup ⟨4,by decide⟩),
   opAt 2240 .MULMOD,
   opAt 2241 (.Dup ⟨2,by decide⟩),
   opAt 2242 .ADDMOD,
   opAt 2243 (.Swap ⟨0,by decide⟩),
   opAt 2244 .SUB,
   opAt 2245 (.Dup ⟨12,by decide⟩),
   opAt 2246 .MUL,
   opAt 2247 (.Dup ⟨15,by decide⟩),
   opAt 2248 (.Dup ⟨1,by decide⟩),
   pushAt 2249 1 128,
   opAt 2250 .SHR,
   opAt 2251 .MUL,
   opAt 2252 (.Dup ⟨1,by decide⟩),
   pushAt 2253 0 0,
   opAt 2254 .MLOAD,
   opAt 2255 .MUL,
   pushAt 2256 2 2112,
   opAt 2257 .MLOAD,
   opAt 2258 .SUB,
   opAt 2259 .LT,
   opAt 2260 (.Swap ⟨0,by decide⟩),
   opAt 2261 .SUB,
   opAt 2262 .JUMPDEST,
   pushAt 2263 0 0,
   opAt 2264 .NOT,
   opAt 2265 (.Swap ⟨1,by decide⟩),
   opAt 2266 (.Dup ⟨14,by decide⟩),
   opAt 2267 .GT,
   opAt 2268 (.Dup ⟨2,by decide⟩),
   opAt 2269 .ADD,
   opAt 2270 .OR]
def blk3013h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8117 .JUMPDEST]
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8118 (.Dup ⟨15,by decide⟩),
   pushAt 8119 2 2112,
   pushAt 8120 2 2080,
   opAt 8121 .MCOPY]
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8122 2 2080,
   opAt 8123 .MLOAD,
   opAt 8124 (.Dup ⟨0,by decide⟩),
   opAt 8125 (.Dup ⟨14,by decide⟩),
   opAt 8126 .SHR,
   opAt 8127 (.Swap ⟨0,by decide⟩),
   pushAt 8128 2 1600,
   opAt 8129 .MLOAD,
   opAt 8130 .SHL,
   pushAt 8131 2 2112,
   opAt 8132 .MLOAD,
   opAt 8133 (.Dup ⟨15,by decide⟩),
   opAt 8134 .SHR,
   opAt 8135 .ADD,
   opAt 8136 (.Dup ⟨13,by decide⟩),
   opAt 8137 (.Dup ⟨0,by decide⟩),
   opAt 8138 (.Dup ⟨13,by decide⟩),
   opAt 8139 (.Dup ⟨4,by decide⟩),
   opAt 8140 .MULMOD,
   opAt 8141 (.Dup ⟨2,by decide⟩),
   opAt 8142 .ADDMOD,
   opAt 8143 (.Swap ⟨0,by decide⟩),
   opAt 8144 .SUB,
   opAt 8145 (.Dup ⟨12,by decide⟩),
   opAt 8146 .MUL,
   opAt 8147 (.Dup ⟨15,by decide⟩),
   opAt 8148 (.Dup ⟨1,by decide⟩),
   pushAt 8149 1 128,
   opAt 8150 .SHR,
   opAt 8151 .MUL,
   opAt 8152 (.Dup ⟨1,by decide⟩),
   pushAt 8153 0 0,
   opAt 8154 .MLOAD,
   opAt 8155 .MUL,
   pushAt 8156 2 2112,
   opAt 8157 .MLOAD,
   opAt 8158 .SUB,
   opAt 8159 .LT,
   opAt 8160 (.Swap ⟨0,by decide⟩),
   opAt 8161 .SUB,
   opAt 8162 .JUMPDEST,
   pushAt 8163 0 0,
   opAt 8164 .NOT,
   opAt 8165 (.Swap ⟨1,by decide⟩),
   opAt 8166 (.Dup ⟨14,by decide⟩),
   opAt 8167 .GT,
   opAt 8168 (.Dup ⟨2,by decide⟩),
   opAt 8169 .ADD,
   opAt 8170 .OR]
def blk3125Unc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2485 2 2080,
   opAt 2486 .MLOAD,
   opAt 2487 .ADD,
   opAt 2488 .SUB,
   opAt 2489 (.Dup ⟨0,by decide⟩),
   pushAt 2490 2 3209,
   opAt 2491 .JUMPI,
   opAt 2503 .JUMPDEST,
   pushAt 2504 2 2080,
   opAt 2505 .MSTORE]
def blk3125hUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8273 2 2080,
   opAt 8274 .MLOAD,
   opAt 8275 .ADD,
   opAt 8276 .SUB,
   opAt 8277 (.Dup ⟨0,by decide⟩),
   pushAt 8278 2 3209,
   opAt 8279 .JUMPI,
   opAt 2503 .JUMPDEST,
   pushAt 2504 2 2080,
   opAt 2505 .MSTORE]
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2485 2 2080,
   opAt 2486 .MLOAD,
   opAt 2487 .ADD,
   opAt 2488 .SUB,
   opAt 2489 (.Dup ⟨0,by decide⟩),
   pushAt 2490 2 3209,
   opAt 2491 .JUMPI,
   opAt 2492 (.Swap ⟨0,by decide⟩),
   opAt 2493 .POP]
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2506 .POP]
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2507 .JUMPDEST,
   pushAt 2508 0 0,
   pushAt 2509 2 2784,
   opAt 2510 .MLOAD]
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2511 .JUMPDEST,
   opAt 2512 (.Dup ⟨0,by decide⟩),
   opAt 2513 .MLOAD,
   pushAt 2514 2 2112,
   opAt 2515 (.Dup ⟨2,by decide⟩),
   opAt 2516 .SUB,
   opAt 2517 .MLOAD,
   opAt 2518 (.Dup ⟨1,by decide⟩),
   opAt 2519 .ADD,
   opAt 2520 (.Swap ⟨0,by decide⟩),
   opAt 2521 (.Dup ⟨1,by decide⟩),
   opAt 2522 .LT,
   opAt 2523 (.Swap ⟨0,by decide⟩),
   opAt 2524 (.Dup ⟨3,by decide⟩),
   opAt 2525 .ADD,
   opAt 2526 (.Swap ⟨2,by decide⟩),
   opAt 2527 (.Dup ⟨3,by decide⟩),
   opAt 2528 .LT,
   opAt 2529 .OR,
   opAt 2530 (.Swap ⟨1,by decide⟩),
   opAt 2531 (.Dup ⟨1,by decide⟩),
   opAt 2532 .MSTORE,
   pushAt 2533 1 31,
   opAt 2534 .NOT,
   opAt 2535 .ADD,
   pushAt 2536 2 2111,
   opAt 2537 (.Dup ⟨1,by decide⟩),
   opAt 2538 .GT,
   pushAt 2539 2 3221,
   opAt 2540 .JUMPI]
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2541 .POP,
   pushAt 2542 2 2080,
   opAt 2543 .MLOAD,
   opAt 2544 (.Dup ⟨1,by decide⟩),
   opAt 2545 .ADD,
   opAt 2546 (.Dup ⟨0,by decide⟩),
   pushAt 2547 2 2080,
   opAt 2548 .MSTORE,
   opAt 2549 .LT,
   opAt 2550 .ISZERO,
   pushAt 2551 2 3215,
   opAt 2552 .JUMPI]
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2553 2 2080,
   opAt 2554 .MLOAD,
   opAt 2555 (.Dup ⟨0,by decide⟩),
   opAt 2556 .ISZERO,
   pushAt 2557 2 3200,
   opAt 2558 .JUMPI]
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2494 .JUMPDEST,
   opAt 2495 .NOT,
   opAt 2496 .ADD,
   opAt 2497 (.Dup ⟨0,by decide⟩),
   opAt 2498 (.Dup ⟨2,by decide⟩),
   opAt 2499 .JUMPI]
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  []
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8273 2 2080,
   opAt 8274 .MLOAD,
   opAt 8275 .ADD,
   opAt 8276 .SUB,
   opAt 8277 (.Dup ⟨0,by decide⟩),
   pushAt 8278 2 3209,
   opAt 8279 .JUMPI,
   opAt 8280 (.Swap ⟨0,by decide⟩),
   opAt 8281 .POP]
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8282 .NOT,
   opAt 8283 .ADD,
   opAt 8284 (.Dup ⟨0,by decide⟩),
   opAt 8285 (.Dup ⟨2,by decide⟩),
   opAt 8286 .JUMPI]
theorem jumpDest4608 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 660 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 465 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 465 = 660 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestBigC : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 207 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 134 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 134 = 207 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest4657 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2566 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2008 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2008 = 2566 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestNeg4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2513 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1974 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1974 = 2513 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestNegT : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2624 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2044 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2044 = 2624 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest4839 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2874 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2217 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2217 = 2874 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestHead4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10626 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8117 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 8117 = 10626 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5115 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3215 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2507 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2507 = 3215 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5121 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3221 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2511 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2511 = 3221 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestLazyStore : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3209 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2503 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2503 = 3209 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestUnc : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3209 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2503 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2503 = 3209 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5311 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3200 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2494 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2494 = 3200 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest2471 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2527 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1983 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1983 = 2527 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
end CycleSubmission.Global.Fast
namespace CycleSubmission.Global.Fast
open EvmSemantics EvmSemantics.EVM
end CycleSubmission.Global.Fast
