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
  [opAt 2014 (.Dup ⟨0,by decide⟩),
   pushAt 2015 1 128,
   opAt 2016 .EQ,
   pushAt 2017 2 2513,
   opAt 2018 .JUMPI]
def negS8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2019 1 224,
   opAt 2020 .MLOAD,
   pushAt 2021 0 0,
   opAt 2022 .SUB,
   pushAt 2023 2 1504,
   opAt 2024 .MSTORE]
def negN8a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2025 1 192,
   opAt 2026 .MLOAD,
   opAt 2027 .NOT,
   pushAt 2028 2 1472,
   opAt 2029 .MSTORE]
def negN8b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2030 1 160,
   opAt 2031 .MLOAD,
   opAt 2032 .NOT,
   pushAt 2033 2 1440,
   opAt 2034 .MSTORE]
def negN8c :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2035 1 128,
   opAt 2036 .MLOAD,
   opAt 2037 .NOT,
   pushAt 2038 2 1408,
   opAt 2039 .MSTORE]
def negN8d :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2040 1 96,
   opAt 2041 .MLOAD,
   opAt 2042 .NOT,
   pushAt 2043 2 1376,
   opAt 2044 .MSTORE]
def negS4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1976 1 96,
   opAt 1977 .MLOAD,
   pushAt 1978 0 0,
   opAt 1979 .SUB,
   pushAt 1980 2 1376,
   opAt 1981 .MSTORE]
def negJ4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1975 .JUMPDEST]
def negJ4b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1982 2 2624,
   opAt 1983 .JUMP]
def negJT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2045 .JUMPDEST]
def blkNeg8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negS8++negN8a++negN8b++negN8c++negN8d
def blkNeg4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negJ4++negS4++negJ4b
def blkNegT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2045 .JUMPDEST,
   pushAt 2046 1 64,
   opAt 2047 .MLOAD,
   opAt 2048 .NOT,
   pushAt 2049 2 1344,
   opAt 2050 .MSTORE,
   pushAt 2051 1 32,
   opAt 2052 .MLOAD,
   opAt 2053 .NOT,
   pushAt 2054 2 1312,
   opAt 2055 .MSTORE,
   pushAt 2056 0 0,
   opAt 2057 .MLOAD,
   opAt 2058 (.Dup ⟨0,by decide⟩),
   opAt 2059 .NOT,
   pushAt 2060 2 1280,
   opAt 2061 .MSTORE]
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2062 (.Dup ⟨0,by decide⟩),
   pushAt 2063 0 0,
   opAt 2064 .SUB,
   opAt 2065 (.Dup ⟨1,by decide⟩),
   opAt 2066 .AND]
def blk2919b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2068 (.Dup ⟨0,by decide⟩),
   pushAt 2069 1 1,
   opAt 2070 .ADD,
   pushAt 2071 2 1600,
   opAt 2072 .MSTORE,
   pushAt 2073 1 255,
   opAt 2074 .SUB,
   opAt 2075 (.Dup ⟨0,by decide⟩),
   pushAt 2076 2 1536,
   opAt 2077 .MSTORE,
   opAt 2078 .SHR,
   opAt 2079 (.Dup ⟨0,by decide⟩),
   pushAt 2080 2 1568,
   opAt 2081 .MSTORE,
   opAt 2082 (.Dup ⟨0,by decide⟩),
   opAt 2083 (.Dup ⟨0,by decide⟩),
   pushAt 2084 0 0,
   opAt 2085 .SUB,
   opAt 2086 .MOD,
   pushAt 2087 2 1632,
   opAt 2088 .MSTORE]
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2089 2 2752,
   opAt 2090 .MLOAD,
   opAt 2091 .MLOAD,
   opAt 2092 (.Dup ⟨0,by decide⟩),
   opAt 2093 (.Dup ⟨2,by decide⟩),
   opAt 2094 .MUL]
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2095 (.Dup ⟨0,by decide⟩),
   pushAt 2096 1 3,
   opAt 2097 .MUL,
   pushAt 2098 1 2,
   opAt 2099 .XOR,
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
   opAt 2119 (.Dup ⟨2,by decide⟩),
   opAt 2120 .MUL,
   pushAt 2121 1 2,
   opAt 2122 .SUB,
   opAt 2123 .MUL,
   opAt 2124 (.Dup ⟨0,by decide⟩),
   opAt 2125 (.Dup ⟨2,by decide⟩),
   opAt 2126 .MUL,
   pushAt 2127 1 2,
   opAt 2128 .SUB,
   opAt 2129 .MUL,
   opAt 2130 (.Dup ⟨0,by decide⟩),
   opAt 2131 (.Swap ⟨1,by decide⟩),
   opAt 2132 .MUL,
   pushAt 2133 1 2,
   opAt 2134 .SUB,
   opAt 2135 .MUL]
def blkNbTailHead : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2136 (.Dup ⟨0,by decide⟩),
   opAt 2137 (.Swap ⟨1,by decide⟩),
   opAt 2138 .MUL,
   pushAt 2139 2 1664,
   opAt 2140 .MSTORE,
   opAt 2141 .MUL,
   pushAt 2142 0 0,
   opAt 2143 .SUB,
   pushAt 2144 2 2720,
   opAt 2145 .MSTORE,
   pushAt 2146 2 2534,
   opAt 2147 (.Dup ⟨4,by decide⟩),
   pushAt 2148 1 1,
   opAt 2149 .XOR,
   pushAt 2150 2 2783,
   opAt 2151 .JUMPI]
def blkNbTailByte : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2152 2 2656,
   opAt 2153 .MLOAD,
   opAt 2154 .CALLDATALOAD,
   pushAt 2155 0 0,
   opAt 2156 .BYTE,
   pushAt 2157 1 3,
   opAt 2158 .EQ,
   pushAt 2159 2 7849,
   opAt 2160 .MUL,
   opAt 2161 .ADD]
def blkNbTailJoin : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2162 .JUMPDEST,
   pushAt 2163 1 32,
   opAt 2164 .MLOAD,
   pushAt 2165 1 128,
   opAt 2166 .SHR,
   pushAt 2167 2 1536,
   opAt 2168 .MLOAD,
   pushAt 2169 2 1568,
   opAt 2170 .MLOAD,
   pushAt 2171 2 1664,
   opAt 2172 .MLOAD,
   pushAt 2173 2 1632,
   opAt 2174 .MLOAD,
   pushAt 2175 2 1504,
   opAt 2176 .MLOAD,
   pushAt 2177 2 1472,
   opAt 2178 .MLOAD,
   pushAt 2179 2 1440,
   opAt 2180 .MLOAD,
   pushAt 2181 2 1408,
   opAt 2182 .MLOAD,
   pushAt 2183 2 1376,
   opAt 2184 .MLOAD,
   pushAt 2185 2 1344,
   opAt 2186 .MLOAD,
   pushAt 2187 2 1312,
   opAt 2188 .MLOAD,
   opAt 2189 (.Dup ⟨14,by decide⟩)]
def blkNbTail (esize : Nat) : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  blkNbTailHead++(if UInt256.ofNat esize = UInt256.ofNat 1 then blkNbTailByte else [])++blkNbTailJoin
theorem jumpDestNbJoin : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2783 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2162 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
def blkZero8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 7842 .JUMPDEST,
   opAt 7843 (.Dup ⟨15,by decide⟩),
   pushAt 7844 2 2112,
   pushAt 7845 2 2080,
   opAt 7846 .MCOPY,
   pushAt 7847 2 2080,
   opAt 7848 .MLOAD,
   opAt 7849 (.Dup ⟨14,by decide⟩),
   pushAt 7850 2 2112,
   opAt 7851 .MLOAD,
   opAt 7852 (.Dup ⟨14,by decide⟩),
   opAt 7853 (.Dup ⟨0,by decide⟩),
   opAt 7854 (.Dup ⟨14,by decide⟩),
   opAt 7855 (.Dup ⟨5,by decide⟩),
   opAt 7856 .MULMOD,
   opAt 7857 (.Dup ⟨2,by decide⟩),
   opAt 7858 .ADDMOD,
   opAt 7859 (.Dup ⟨0,by decide⟩),
   opAt 7860 (.Swap ⟨1,by decide⟩),
   opAt 7861 .SUB,
   opAt 7862 (.Dup ⟨14,by decide⟩),
   opAt 7863 .MUL,
   opAt 7864 (.Swap ⟨1,by decide⟩),
   opAt 7865 (.Dup ⟨2,by decide⟩),
   pushAt 7866 1 128,
   opAt 7867 .SHR,
   opAt 7868 .MUL,
   opAt 7869 .GT,
   opAt 7870 (.Swap ⟨0,by decide⟩),
   opAt 7871 .SUB,
   pushAt 7872 2 2932,
   opAt 7873 .JUMP]
def blkZero4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 7875 .JUMPDEST,
   opAt 7876 (.Dup ⟨15,by decide⟩),
   pushAt 7877 2 2112,
   pushAt 7878 2 2080,
   opAt 7879 .MCOPY,
   pushAt 7880 2 2080,
   opAt 7881 .MLOAD,
   opAt 7882 (.Dup ⟨14,by decide⟩),
   pushAt 7883 2 2112,
   opAt 7884 .MLOAD,
   opAt 7885 (.Dup ⟨14,by decide⟩),
   opAt 7886 (.Dup ⟨0,by decide⟩),
   opAt 7887 (.Dup ⟨14,by decide⟩),
   opAt 7888 (.Dup ⟨5,by decide⟩),
   opAt 7889 .MULMOD,
   opAt 7890 (.Dup ⟨2,by decide⟩),
   opAt 7891 .ADDMOD,
   opAt 7892 (.Dup ⟨0,by decide⟩),
   opAt 7893 (.Swap ⟨1,by decide⟩),
   opAt 7894 .SUB,
   opAt 7895 (.Dup ⟨14,by decide⟩),
   opAt 7896 .MUL,
   opAt 7897 (.Swap ⟨1,by decide⟩),
   opAt 7898 (.Dup ⟨2,by decide⟩),
   pushAt 7899 1 128,
   opAt 7900 .SHR,
   opAt 7901 .MUL,
   opAt 7902 .GT,
   opAt 7903 (.Swap ⟨0,by decide⟩),
   opAt 7904 .SUB,
   pushAt 7905 2 10740,
   opAt 7906 .JUMP]
def blkEstimateSuffix8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2263 .JUMPDEST,
   pushAt 2264 0 0,
   opAt 2265 .NOT,
   opAt 2266 (.Swap ⟨1,by decide⟩),
   opAt 2267 (.Dup ⟨14,by decide⟩),
   opAt 2268 .GT,
   opAt 2269 (.Dup ⟨2,by decide⟩),
   opAt 2270 .ADD,
   opAt 2271 .OR]
def blkEstimateSuffix4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8161 .JUMPDEST,
   pushAt 8162 0 0,
   opAt 8163 .NOT,
   opAt 8164 (.Swap ⟨1,by decide⟩),
   opAt 8165 (.Dup ⟨14,by decide⟩),
   opAt 8166 .GT,
   opAt 8167 (.Dup ⟨2,by decide⟩),
   opAt 8168 .ADD,
   opAt 8169 .OR]
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2218 .JUMPDEST]
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2219 (.Dup ⟨15,by decide⟩),
   pushAt 2220 2 2112,
   pushAt 2221 2 2080,
   opAt 2222 .MCOPY]
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2223 2 2080,
   opAt 2224 .MLOAD,
   opAt 2225 (.Dup ⟨0,by decide⟩),
   opAt 2226 (.Dup ⟨14,by decide⟩),
   opAt 2227 .SHR,
   opAt 2228 (.Swap ⟨0,by decide⟩),
   pushAt 2229 2 1600,
   opAt 2230 .MLOAD,
   opAt 2231 .SHL,
   pushAt 2232 2 2112,
   opAt 2233 .MLOAD,
   opAt 2234 (.Dup ⟨15,by decide⟩),
   opAt 2235 .SHR,
   opAt 2236 .ADD,
   opAt 2237 (.Dup ⟨13,by decide⟩),
   opAt 2238 (.Dup ⟨0,by decide⟩),
   opAt 2239 (.Dup ⟨13,by decide⟩),
   opAt 2240 (.Dup ⟨4,by decide⟩),
   opAt 2241 .MULMOD,
   opAt 2242 (.Dup ⟨2,by decide⟩),
   opAt 2243 .ADDMOD,
   opAt 2244 (.Swap ⟨0,by decide⟩),
   opAt 2245 .SUB,
   opAt 2246 (.Dup ⟨12,by decide⟩),
   opAt 2247 .MUL,
   opAt 2248 (.Dup ⟨15,by decide⟩),
   opAt 2249 (.Dup ⟨1,by decide⟩),
   pushAt 2250 1 128,
   opAt 2251 .SHR,
   opAt 2252 .MUL,
   opAt 2253 (.Dup ⟨1,by decide⟩),
   pushAt 2254 0 0,
   opAt 2255 .MLOAD,
   opAt 2256 .MUL,
   pushAt 2257 2 2112,
   opAt 2258 .MLOAD,
   opAt 2259 .SUB,
   opAt 2260 .LT,
   opAt 2261 (.Swap ⟨0,by decide⟩),
   opAt 2262 .SUB,
   opAt 2263 .JUMPDEST,
   pushAt 2264 0 0,
   opAt 2265 .NOT,
   opAt 2266 (.Swap ⟨1,by decide⟩),
   opAt 2267 (.Dup ⟨14,by decide⟩),
   opAt 2268 .GT,
   opAt 2269 (.Dup ⟨2,by decide⟩),
   opAt 2270 .ADD,
   opAt 2271 .OR]
def blk3013h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8116 .JUMPDEST]
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8117 (.Dup ⟨15,by decide⟩),
   pushAt 8118 2 2112,
   pushAt 8119 2 2080,
   opAt 8120 .MCOPY]
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8121 2 2080,
   opAt 8122 .MLOAD,
   opAt 8123 (.Dup ⟨0,by decide⟩),
   opAt 8124 (.Dup ⟨14,by decide⟩),
   opAt 8125 .SHR,
   opAt 8126 (.Swap ⟨0,by decide⟩),
   pushAt 8127 2 1600,
   opAt 8128 .MLOAD,
   opAt 8129 .SHL,
   pushAt 8130 2 2112,
   opAt 8131 .MLOAD,
   opAt 8132 (.Dup ⟨15,by decide⟩),
   opAt 8133 .SHR,
   opAt 8134 .ADD,
   opAt 8135 (.Dup ⟨13,by decide⟩),
   opAt 8136 (.Dup ⟨0,by decide⟩),
   opAt 8137 (.Dup ⟨13,by decide⟩),
   opAt 8138 (.Dup ⟨4,by decide⟩),
   opAt 8139 .MULMOD,
   opAt 8140 (.Dup ⟨2,by decide⟩),
   opAt 8141 .ADDMOD,
   opAt 8142 (.Swap ⟨0,by decide⟩),
   opAt 8143 .SUB,
   opAt 8144 (.Dup ⟨12,by decide⟩),
   opAt 8145 .MUL,
   opAt 8146 (.Dup ⟨15,by decide⟩),
   opAt 8147 (.Dup ⟨1,by decide⟩),
   pushAt 8148 1 128,
   opAt 8149 .SHR,
   opAt 8150 .MUL,
   opAt 8151 (.Dup ⟨1,by decide⟩),
   pushAt 8152 0 0,
   opAt 8153 .MLOAD,
   opAt 8154 .MUL,
   pushAt 8155 2 2112,
   opAt 8156 .MLOAD,
   opAt 8157 .SUB,
   opAt 8158 .LT,
   opAt 8159 (.Swap ⟨0,by decide⟩),
   opAt 8160 .SUB,
   opAt 8161 .JUMPDEST,
   pushAt 8162 0 0,
   opAt 8163 .NOT,
   opAt 8164 (.Swap ⟨1,by decide⟩),
   opAt 8165 (.Dup ⟨14,by decide⟩),
   opAt 8166 .GT,
   opAt 8167 (.Dup ⟨2,by decide⟩),
   opAt 8168 .ADD,
   opAt 8169 .OR]
def blk3125Unc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2486 2 2080,
   opAt 2487 .MLOAD,
   opAt 2488 .ADD,
   opAt 2489 .SUB,
   opAt 2490 (.Dup ⟨0,by decide⟩),
   pushAt 2491 2 3209,
   opAt 2492 .JUMPI,
   opAt 2504 .JUMPDEST,
   pushAt 2505 2 2080,
   opAt 2506 .MSTORE]
def blk3125hUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8272 2 2080,
   opAt 8273 .MLOAD,
   opAt 8274 .ADD,
   opAt 8275 .SUB,
   opAt 8276 (.Dup ⟨0,by decide⟩),
   pushAt 8277 2 3209,
   opAt 8278 .JUMPI,
   opAt 2504 .JUMPDEST,
   pushAt 2505 2 2080,
   opAt 2506 .MSTORE]
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2486 2 2080,
   opAt 2487 .MLOAD,
   opAt 2488 .ADD,
   opAt 2489 .SUB,
   opAt 2490 (.Dup ⟨0,by decide⟩),
   pushAt 2491 2 3209,
   opAt 2492 .JUMPI,
   opAt 2493 (.Swap ⟨0,by decide⟩),
   opAt 2494 .POP]
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2507 .POP]
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2508 .JUMPDEST,
   pushAt 2509 0 0,
   pushAt 2510 2 2784,
   opAt 2511 .MLOAD]
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2512 .JUMPDEST,
   opAt 2513 (.Dup ⟨0,by decide⟩),
   opAt 2514 .MLOAD,
   pushAt 2515 2 2112,
   opAt 2516 (.Dup ⟨2,by decide⟩),
   opAt 2517 .SUB,
   opAt 2518 .MLOAD,
   opAt 2519 (.Dup ⟨1,by decide⟩),
   opAt 2520 .ADD,
   opAt 2521 (.Swap ⟨0,by decide⟩),
   opAt 2522 (.Dup ⟨1,by decide⟩),
   opAt 2523 .LT,
   opAt 2524 (.Swap ⟨0,by decide⟩),
   opAt 2525 (.Dup ⟨3,by decide⟩),
   opAt 2526 .ADD,
   opAt 2527 (.Swap ⟨2,by decide⟩),
   opAt 2528 (.Dup ⟨3,by decide⟩),
   opAt 2529 .LT,
   opAt 2530 .OR,
   opAt 2531 (.Swap ⟨1,by decide⟩),
   opAt 2532 (.Dup ⟨1,by decide⟩),
   opAt 2533 .MSTORE,
   pushAt 2534 1 31,
   opAt 2535 .NOT,
   opAt 2536 .ADD,
   pushAt 2537 2 2111,
   opAt 2538 (.Dup ⟨1,by decide⟩),
   opAt 2539 .GT,
   pushAt 2540 2 3221,
   opAt 2541 .JUMPI]
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2542 .POP,
   pushAt 2543 2 2080,
   opAt 2544 .MLOAD,
   opAt 2545 (.Dup ⟨1,by decide⟩),
   opAt 2546 .ADD,
   opAt 2547 (.Dup ⟨0,by decide⟩),
   pushAt 2548 2 2080,
   opAt 2549 .MSTORE,
   opAt 2550 .LT,
   opAt 2551 .ISZERO,
   pushAt 2552 2 3215,
   opAt 2553 .JUMPI]
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2554 2 2080,
   opAt 2555 .MLOAD,
   opAt 2556 (.Dup ⟨0,by decide⟩),
   opAt 2557 .ISZERO,
   pushAt 2558 2 3200,
   opAt 2559 .JUMPI]
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2495 .JUMPDEST,
   opAt 2496 .NOT,
   opAt 2497 .ADD,
   opAt 2498 (.Dup ⟨0,by decide⟩),
   opAt 2499 (.Dup ⟨2,by decide⟩),
   opAt 2500 .JUMPI]
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  []
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8272 2 2080,
   opAt 8273 .MLOAD,
   opAt 8274 .ADD,
   opAt 8275 .SUB,
   opAt 8276 (.Dup ⟨0,by decide⟩),
   pushAt 8277 2 3209,
   opAt 8278 .JUMPI,
   opAt 8279 (.Swap ⟨0,by decide⟩),
   opAt 8280 .POP]
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8281 .NOT,
   opAt 8282 .ADD,
   opAt 8283 (.Dup ⟨0,by decide⟩),
   opAt 8284 (.Dup ⟨2,by decide⟩),
   opAt 8285 .JUMPI]
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
  have h := CycleSubmission.Global.Binding.jumpDest 2009 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2009 = 2566 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestNeg4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2513 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1975 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1975 = 2513 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestNegT : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2624 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2045 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2045 = 2624 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest4839 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2874 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2218 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2218 = 2874 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestHead4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10682 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8116 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 8116 = 10682 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5115 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3215 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2508 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2508 = 3215 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5121 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3221 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2512 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2512 = 3221 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestLazyStore : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3209 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2504 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2504 = 3209 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestUnc : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3209 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2504 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2504 = 3209 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5311 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3200 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2495 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2495 = 3200 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest2471 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2527 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1984 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1984 = 2527 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
end CycleSubmission.Global.Fast
namespace CycleSubmission.Global.Fast
open EvmSemantics EvmSemantics.EVM
end CycleSubmission.Global.Fast
