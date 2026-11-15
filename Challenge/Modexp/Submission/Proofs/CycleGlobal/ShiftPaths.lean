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
  [opAt 460 (.Dup ⟨0,by decide⟩),
   opAt 461 (.Dup ⟨3,by decide⟩),
   opAt 462 .XOR,
   pushAt 463 1 203,
   opAt 464 .JUMPI]
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 465 (.Dup ⟨0,by decide⟩),
   pushAt 466 1 96,
   pushAt 467 2 2112,
   opAt 468 .CALLDATACOPY]
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2000 (.Dup ⟨0,by decide⟩),
   pushAt 2001 1 128,
   opAt 2002 .EQ,
   pushAt 2003 2 2501,
   opAt 2004 .JUMPI]
def negS8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2005 1 224,
   opAt 2006 .MLOAD,
   pushAt 2007 0 0,
   opAt 2008 .SUB,
   pushAt 2009 2 1504,
   opAt 2010 .MSTORE]
def negN8a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2011 1 192,
   opAt 2012 .MLOAD,
   opAt 2013 .NOT,
   pushAt 2014 2 1472,
   opAt 2015 .MSTORE]
def negN8b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2016 1 160,
   opAt 2017 .MLOAD,
   opAt 2018 .NOT,
   pushAt 2019 2 1440,
   opAt 2020 .MSTORE]
def negN8c :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2021 1 128,
   opAt 2022 .MLOAD,
   opAt 2023 .NOT,
   pushAt 2024 2 1408,
   opAt 2025 .MSTORE]
def negN8d :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2026 1 96,
   opAt 2027 .MLOAD,
   opAt 2028 .NOT,
   pushAt 2029 2 1376,
   opAt 2030 .MSTORE]
def negS4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1962 1 96,
   opAt 1963 .MLOAD,
   pushAt 1964 0 0,
   opAt 1965 .SUB,
   pushAt 1966 2 1376,
   opAt 1967 .MSTORE]
def negJ4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1961 .JUMPDEST]
def negJ4b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1968 2 2612,
   opAt 1969 .JUMP]
def negJT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2031 .JUMPDEST]
def blkNeg8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negS8++negN8a++negN8b++negN8c++negN8d
def blkNeg4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negJ4++negS4++negJ4b
def blkNegT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2031 .JUMPDEST,
   pushAt 2032 1 64,
   opAt 2033 .MLOAD,
   opAt 2034 .NOT,
   pushAt 2035 2 1344,
   opAt 2036 .MSTORE,
   pushAt 2037 1 32,
   opAt 2038 .MLOAD,
   opAt 2039 .NOT,
   pushAt 2040 2 1312,
   opAt 2041 .MSTORE,
   pushAt 2042 0 0,
   opAt 2043 .MLOAD,
   opAt 2044 (.Dup ⟨0,by decide⟩),
   opAt 2045 .NOT,
   pushAt 2046 2 1280,
   opAt 2047 .MSTORE]
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2048 (.Dup ⟨0,by decide⟩),
   pushAt 2049 0 0,
   opAt 2050 .SUB,
   opAt 2051 (.Dup ⟨1,by decide⟩),
   opAt 2052 .AND]
def blk2919b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2054 (.Dup ⟨0,by decide⟩),
   pushAt 2055 1 1,
   opAt 2056 .ADD,
   pushAt 2057 2 1600,
   opAt 2058 .MSTORE,
   pushAt 2059 1 255,
   opAt 2060 .SUB,
   opAt 2061 (.Dup ⟨0,by decide⟩),
   pushAt 2062 2 1536,
   opAt 2063 .MSTORE,
   opAt 2064 .SHR,
   opAt 2065 (.Dup ⟨0,by decide⟩),
   pushAt 2066 2 1568,
   opAt 2067 .MSTORE,
   opAt 2068 (.Dup ⟨0,by decide⟩),
   opAt 2069 (.Dup ⟨0,by decide⟩),
   pushAt 2070 0 0,
   opAt 2071 .SUB,
   opAt 2072 .MOD,
   pushAt 2073 2 1632,
   opAt 2074 .MSTORE]
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2075 2 2752,
   opAt 2076 .MLOAD,
   opAt 2077 .MLOAD,
   opAt 2078 (.Dup ⟨0,by decide⟩),
   opAt 2079 (.Dup ⟨2,by decide⟩),
   opAt 2080 .MUL]
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2081 (.Dup ⟨0,by decide⟩),
   pushAt 2082 1 3,
   opAt 2083 .MUL,
   pushAt 2084 1 2,
   opAt 2085 .XOR,
   opAt 2086 (.Dup ⟨0,by decide⟩),
   opAt 2087 (.Dup ⟨2,by decide⟩),
   opAt 2088 .MUL,
   pushAt 2089 1 2,
   opAt 2090 .SUB,
   opAt 2091 .MUL,
   opAt 2092 (.Dup ⟨0,by decide⟩),
   opAt 2093 (.Dup ⟨2,by decide⟩),
   opAt 2094 .MUL,
   pushAt 2095 1 2,
   opAt 2096 .SUB,
   opAt 2097 .MUL,
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
   opAt 2117 (.Swap ⟨1,by decide⟩),
   opAt 2118 .MUL,
   pushAt 2119 1 2,
   opAt 2120 .SUB,
   opAt 2121 .MUL]
def blkNbTailHead : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2122 (.Dup ⟨0,by decide⟩),
   opAt 2123 (.Swap ⟨1,by decide⟩),
   opAt 2124 .MUL,
   pushAt 2125 2 1664,
   opAt 2126 .MSTORE,
   opAt 2127 .MUL,
   pushAt 2128 0 0,
   opAt 2129 .SUB,
   pushAt 2130 2 2720,
   opAt 2131 .MSTORE,
   pushAt 2132 2 2522,
   opAt 2133 (.Dup ⟨4,by decide⟩),
   pushAt 2134 1 1,
   opAt 2135 .XOR,
   pushAt 2136 2 2771,
   opAt 2137 .JUMPI]
def blkNbTailByte : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2138 2 2656,
   opAt 2139 .MLOAD,
   opAt 2140 .CALLDATALOAD,
   pushAt 2141 0 0,
   opAt 2142 .BYTE,
   pushAt 2143 1 3,
   opAt 2144 .EQ,
   pushAt 2145 2 7895,
   opAt 2146 .MUL,
   opAt 2147 .ADD]
def blkNbTailJoin : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2148 .JUMPDEST,
   pushAt 2149 1 32,
   opAt 2150 .MLOAD,
   pushAt 2151 1 128,
   opAt 2152 .SHR,
   pushAt 2153 2 1536,
   opAt 2154 .MLOAD,
   pushAt 2155 2 1568,
   opAt 2156 .MLOAD,
   pushAt 2157 2 1664,
   opAt 2158 .MLOAD,
   pushAt 2159 2 1632,
   opAt 2160 .MLOAD,
   pushAt 2161 2 1504,
   opAt 2162 .MLOAD,
   pushAt 2163 2 1472,
   opAt 2164 .MLOAD,
   pushAt 2165 2 1440,
   opAt 2166 .MLOAD,
   pushAt 2167 2 1408,
   opAt 2168 .MLOAD,
   pushAt 2169 2 1376,
   opAt 2170 .MLOAD,
   pushAt 2171 2 1344,
   opAt 2172 .MLOAD,
   pushAt 2173 2 1312,
   opAt 2174 .MLOAD,
   opAt 2175 (.Dup ⟨14,by decide⟩)]
def blkNbTail (esize : Nat) : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  blkNbTailHead++(if UInt256.ofNat esize = UInt256.ofNat 1 then blkNbTailByte else [])++blkNbTailJoin
theorem jumpDestNbJoin : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2771 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2148 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
def blkZero8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 7810 .JUMPDEST,
   opAt 7811 (.Dup ⟨15,by decide⟩),
   pushAt 7812 2 2112,
   pushAt 7813 2 2080,
   opAt 7814 .MCOPY,
   pushAt 7815 2 2080,
   opAt 7816 .MLOAD,
   opAt 7817 (.Dup ⟨14,by decide⟩),
   pushAt 7818 2 2112,
   opAt 7819 .MLOAD,
   opAt 7820 (.Dup ⟨14,by decide⟩),
   opAt 7821 (.Dup ⟨0,by decide⟩),
   opAt 7822 (.Dup ⟨14,by decide⟩),
   opAt 7823 (.Dup ⟨5,by decide⟩),
   opAt 7824 .MULMOD,
   opAt 7825 (.Dup ⟨2,by decide⟩),
   opAt 7826 .ADDMOD,
   opAt 7827 (.Dup ⟨0,by decide⟩),
   opAt 7828 (.Swap ⟨1,by decide⟩),
   opAt 7829 .SUB,
   opAt 7830 (.Dup ⟨14,by decide⟩),
   opAt 7831 .MUL,
   opAt 7832 (.Swap ⟨1,by decide⟩),
   opAt 7833 (.Dup ⟨2,by decide⟩),
   pushAt 7834 1 128,
   opAt 7835 .SHR,
   opAt 7836 .MUL,
   opAt 7837 .GT,
   opAt 7838 (.Swap ⟨0,by decide⟩),
   opAt 7839 .SUB,
   pushAt 7840 2 2920,
   opAt 7841 .JUMP]
def blkZero4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
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
   pushAt 7873 2 10772,
   opAt 7874 .JUMP]
def blkEstimateSuffix8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2249 .JUMPDEST,
   pushAt 2250 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2251 (.Swap ⟨1,by decide⟩),
   opAt 2252 (.Dup ⟨14,by decide⟩),
   opAt 2253 .GT,
   opAt 2254 (.Dup ⟨2,by decide⟩),
   opAt 2255 .ADD,
   opAt 2256 .OR]
def blkEstimateSuffix4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8128 .JUMPDEST,
   pushAt 8129 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8130 (.Swap ⟨1,by decide⟩),
   opAt 8131 (.Dup ⟨14,by decide⟩),
   opAt 8132 .GT,
   opAt 8133 (.Dup ⟨2,by decide⟩),
   opAt 8134 .ADD,
   opAt 8135 .OR]
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2204 .JUMPDEST]
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2205 (.Dup ⟨15,by decide⟩),
   pushAt 2206 2 2112,
   pushAt 2207 2 2080,
   opAt 2208 .MCOPY]
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2209 2 2080,
   opAt 2210 .MLOAD,
   opAt 2211 (.Dup ⟨0,by decide⟩),
   opAt 2212 (.Dup ⟨14,by decide⟩),
   opAt 2213 .SHR,
   opAt 2214 (.Swap ⟨0,by decide⟩),
   pushAt 2215 2 1600,
   opAt 2216 .MLOAD,
   opAt 2217 .SHL,
   pushAt 2218 2 2112,
   opAt 2219 .MLOAD,
   opAt 2220 (.Dup ⟨15,by decide⟩),
   opAt 2221 .SHR,
   opAt 2222 .ADD,
   opAt 2223 (.Dup ⟨13,by decide⟩),
   opAt 2224 (.Dup ⟨0,by decide⟩),
   opAt 2225 (.Dup ⟨13,by decide⟩),
   opAt 2226 (.Dup ⟨4,by decide⟩),
   opAt 2227 .MULMOD,
   opAt 2228 (.Dup ⟨2,by decide⟩),
   opAt 2229 .ADDMOD,
   opAt 2230 (.Swap ⟨0,by decide⟩),
   opAt 2231 .SUB,
   opAt 2232 (.Dup ⟨12,by decide⟩),
   opAt 2233 .MUL,
   opAt 2234 (.Dup ⟨15,by decide⟩),
   opAt 2235 (.Dup ⟨1,by decide⟩),
   pushAt 2236 1 128,
   opAt 2237 .SHR,
   opAt 2238 .MUL,
   opAt 2239 (.Dup ⟨1,by decide⟩),
   pushAt 2240 0 0,
   opAt 2241 .MLOAD,
   opAt 2242 .MUL,
   pushAt 2243 2 2112,
   opAt 2244 .MLOAD,
   opAt 2245 .SUB,
   opAt 2246 .LT,
   opAt 2247 (.Swap ⟨0,by decide⟩),
   opAt 2248 .SUB,
   opAt 2249 .JUMPDEST,
   pushAt 2250 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2251 (.Swap ⟨1,by decide⟩),
   opAt 2252 (.Dup ⟨14,by decide⟩),
   opAt 2253 .GT,
   opAt 2254 (.Dup ⟨2,by decide⟩),
   opAt 2255 .ADD,
   opAt 2256 .OR]
def blk3013h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8083 .JUMPDEST]
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8084 (.Dup ⟨15,by decide⟩),
   pushAt 8085 2 2112,
   pushAt 8086 2 2080,
   opAt 8087 .MCOPY]
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8088 2 2080,
   opAt 8089 .MLOAD,
   opAt 8090 (.Dup ⟨0,by decide⟩),
   opAt 8091 (.Dup ⟨14,by decide⟩),
   opAt 8092 .SHR,
   opAt 8093 (.Swap ⟨0,by decide⟩),
   pushAt 8094 2 1600,
   opAt 8095 .MLOAD,
   opAt 8096 .SHL,
   pushAt 8097 2 2112,
   opAt 8098 .MLOAD,
   opAt 8099 (.Dup ⟨15,by decide⟩),
   opAt 8100 .SHR,
   opAt 8101 .ADD,
   opAt 8102 (.Dup ⟨13,by decide⟩),
   opAt 8103 (.Dup ⟨0,by decide⟩),
   opAt 8104 (.Dup ⟨13,by decide⟩),
   opAt 8105 (.Dup ⟨4,by decide⟩),
   opAt 8106 .MULMOD,
   opAt 8107 (.Dup ⟨2,by decide⟩),
   opAt 8108 .ADDMOD,
   opAt 8109 (.Swap ⟨0,by decide⟩),
   opAt 8110 .SUB,
   opAt 8111 (.Dup ⟨12,by decide⟩),
   opAt 8112 .MUL,
   opAt 8113 (.Dup ⟨15,by decide⟩),
   opAt 8114 (.Dup ⟨1,by decide⟩),
   pushAt 8115 1 128,
   opAt 8116 .SHR,
   opAt 8117 .MUL,
   opAt 8118 (.Dup ⟨1,by decide⟩),
   pushAt 8119 0 0,
   opAt 8120 .MLOAD,
   opAt 8121 .MUL,
   pushAt 8122 2 2112,
   opAt 8123 .MLOAD,
   opAt 8124 .SUB,
   opAt 8125 .LT,
   opAt 8126 (.Swap ⟨0,by decide⟩),
   opAt 8127 .SUB,
   opAt 8128 .JUMPDEST,
   pushAt 8129 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8130 (.Swap ⟨1,by decide⟩),
   opAt 8131 (.Dup ⟨14,by decide⟩),
   opAt 8132 .GT,
   opAt 8133 (.Dup ⟨2,by decide⟩),
   opAt 8134 .ADD,
   opAt 8135 .OR]
def blk3125Unc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2471 2 2080,
   opAt 2472 .MLOAD,
   opAt 2473 .ADD,
   opAt 2474 .SUB,
   pushAt 2475 2 3223,
   opAt 2476 .JUMPI,
   opAt 2484 .JUMPDEST,
   pushAt 2485 2 2080,
   opAt 2486 .MSTORE]
def blk3125hUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8238 2 2080,
   opAt 8239 .MLOAD,
   opAt 8240 .ADD,
   opAt 8241 .SUB,
   pushAt 8242 2 3223,
   opAt 8243 .JUMPI,
   opAt 2484 .JUMPDEST,
   pushAt 2485 2 2080,
   opAt 2486 .MSTORE]
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2471 2 2080,
   opAt 2472 .MLOAD,
   opAt 2473 .ADD,
   opAt 2474 .SUB,
   pushAt 2475 2 3223,
   opAt 2476 .JUMPI]
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  []
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2487 .JUMPDEST,
   pushAt 2488 0 0,
   pushAt 2489 2 2784,
   opAt 2490 .MLOAD]
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2491 .JUMPDEST,
   opAt 2492 (.Dup ⟨0,by decide⟩),
   opAt 2493 .MLOAD,
   pushAt 2494 2 2112,
   opAt 2495 (.Dup ⟨2,by decide⟩),
   opAt 2496 .SUB,
   opAt 2497 .MLOAD,
   opAt 2498 (.Dup ⟨1,by decide⟩),
   opAt 2499 .ADD,
   opAt 2500 (.Swap ⟨0,by decide⟩),
   opAt 2501 (.Dup ⟨1,by decide⟩),
   opAt 2502 .LT,
   opAt 2503 (.Swap ⟨0,by decide⟩),
   opAt 2504 (.Dup ⟨3,by decide⟩),
   opAt 2505 .ADD,
   opAt 2506 (.Swap ⟨2,by decide⟩),
   opAt 2507 (.Dup ⟨3,by decide⟩),
   opAt 2508 .LT,
   opAt 2509 .OR,
   opAt 2510 (.Swap ⟨1,by decide⟩),
   opAt 2511 (.Dup ⟨1,by decide⟩),
   opAt 2512 .MSTORE,
   pushAt 2513 1 31,
   opAt 2514 .NOT,
   opAt 2515 .ADD,
   pushAt 2516 2 2111,
   opAt 2517 (.Dup ⟨1,by decide⟩),
   opAt 2518 .GT,
   pushAt 2519 2 3234,
   opAt 2520 .JUMPI]
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2521 .POP,
   pushAt 2522 2 2080,
   opAt 2523 .MLOAD,
   opAt 2524 (.Dup ⟨1,by decide⟩),
   opAt 2525 .ADD,
   opAt 2526 (.Dup ⟨0,by decide⟩),
   pushAt 2527 2 2080,
   opAt 2528 .MSTORE,
   opAt 2529 .LT,
   opAt 2530 .ISZERO,
   pushAt 2531 2 3228,
   opAt 2532 .JUMPI]
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2533 2 2080,
   opAt 2534 .MLOAD,
   opAt 2535 (.Dup ⟨0,by decide⟩),
   opAt 2536 .ISZERO,
   opAt 2537 (.Swap ⟨0,by decide⟩),
   opAt 2538 .NOT,
   opAt 2539 (.Swap ⟨0,by decide⟩),
   pushAt 2540 2 10995,
   opAt 2541 .JUMPI]
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2477 .ADD,
   opAt 2478 (.Dup ⟨0,by decide⟩),
   opAt 2479 (.Dup ⟨2,by decide⟩),
   opAt 2480 .JUMPI]
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  []
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8238 2 2080,
   opAt 8239 .MLOAD,
   opAt 8240 .ADD,
   opAt 8241 .SUB,
   pushAt 8242 2 3223,
   opAt 8243 .JUMPI]
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8244 .ADD,
   opAt 8245 (.Dup ⟨0,by decide⟩),
   opAt 8246 (.Dup ⟨2,by decide⟩),
   opAt 8247 .JUMPI]
theorem jumpDestBigC : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 203 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 130 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 130 = 203 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest4657 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2554 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1995 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1995 = 2554 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestNeg4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2501 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1961 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1961 = 2501 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestNegT : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2612 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2031 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2031 = 2612 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest4839 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2862 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2204 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2204 = 2862 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestHead4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10714 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8083 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 8083 = 10714 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5115 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3228 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2487 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2487 = 3228 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5121 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3234 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2491 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2491 = 3234 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestLazyStore : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3223 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2484 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2484 = 3223 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestUnc : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3223 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2484 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2484 = 3223 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5311 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10995 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8284 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 8284 = 10995 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest2471 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2515 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1970 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1970 = 2515 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
end CycleSubmission.Global.Fast
namespace CycleSubmission.Global.Fast
open EvmSemantics EvmSemantics.EVM
end CycleSubmission.Global.Fast
