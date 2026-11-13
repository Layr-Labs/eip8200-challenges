import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
open CycleSubmission.SharedStackArgs

noncomputable section
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
 

namespace CycleSubmission.Global.Fast
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast


open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

 
def blk2862 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1854 .JUMPDEST,
   opAt 1855 (.Dup ⟨0,by decide⟩),
   opAt 1856 (.Dup ⟨3,by decide⟩),
   opAt 1857 .XOR,
   pushAt 1858 1 207,
   opAt 1859 .JUMPI]

 
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1860 (.Dup ⟨0,by decide⟩),
   pushAt 1861 1 96,
   pushAt 1862 2 2112,
   opAt 1863 .CALLDATACOPY,
   pushAt 1864 2 2370,
   pushAt 1865 2 3472,
   opAt 1866 .JUMP]


 
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1872 (.Dup ⟨0,by decide⟩),
   pushAt 1873 1 128,
   opAt 1874 .EQ,
   pushAt 1875 2 2284,
   opAt 1876 .JUMPI]

 
def negS8 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1877 1 224,
   opAt 1878 .MLOAD,
   pushAt 1879 0 0,
   opAt 1880 .SUB,
   pushAt 1881 2 1504,
   opAt 1882 .MSTORE]

 
def negN8a :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1883 1 192,
   opAt 1884 .MLOAD,
   opAt 1885 .NOT,
   pushAt 1886 2 1472,
   opAt 1887 .MSTORE]

 
def negN8b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1888 1 160,
   opAt 1889 .MLOAD,
   opAt 1890 .NOT,
   pushAt 1891 2 1440,
   opAt 1892 .MSTORE]

 
def negN8c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1893 1 128,
   opAt 1894 .MLOAD,
   opAt 1895 .NOT,
   pushAt 1896 2 1408,
   opAt 1897 .MSTORE]

 
def negN8d :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1898 1 96,
   opAt 1899 .MLOAD,
   opAt 1900 .NOT,
   pushAt 1901 2 1376,
   opAt 1902 .MSTORE]

 


 


 


 
def negS4 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1813 1 96,
   opAt 1814 .MLOAD,
   pushAt 1815 0 0,
   opAt 1816 .SUB,
   pushAt 1817 2 1376,
   opAt 1818 .MSTORE]

 
def negJ4 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1812 .JUMPDEST]

 
def negJ4b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1819 2 2428,
   opAt 1820 .JUMP]

 
def negJT :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1903 .JUMPDEST]

 
def blkNeg8 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  negS8 ++ negN8a ++ negN8b ++ negN8c ++ negN8d

 
def blkNeg4 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  negJ4 ++ negS4 ++ negJ4b

 
def blkNegT :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1903 .JUMPDEST,
   pushAt 1904 1 64,
   opAt 1905 .MLOAD,
   opAt 1906 .NOT,
   pushAt 1907 2 1344,
   opAt 1908 .MSTORE,
   pushAt 1909 1 32,
   opAt 1910 .MLOAD,
   opAt 1911 .NOT,
   pushAt 1912 2 1312,
   opAt 1913 .MSTORE,
   pushAt 1914 0 0,
   opAt 1915 .MLOAD,
   opAt 1916 (.Dup ⟨0,by decide⟩),
   opAt 1917 .NOT,
   pushAt 1918 2 1280,
   opAt 1919 .MSTORE]


 
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1920 (.Dup ⟨0,by decide⟩),
   pushAt 1921 0 0,
   opAt 1922 .SUB,
   opAt 1923 (.Dup ⟨1,by decide⟩),
   opAt 1924 .AND,
   opAt 1925 .JUMPDEST]


 

def blk2919b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1927 (.Dup ⟨0,by decide⟩),
   pushAt 1928 1 1,
   opAt 1929 .ADD,
   pushAt 1930 2 1600,
   opAt 1931 .MSTORE,
   pushAt 1932 1 255,
   opAt 1933 .SUB,
   opAt 1934 (.Dup ⟨0,by decide⟩),
   pushAt 1935 2 1536,
   opAt 1936 .MSTORE,
   opAt 1937 .SHR,
   opAt 1938 (.Dup ⟨0,by decide⟩),
   pushAt 1939 2 1568,
   opAt 1940 .MSTORE,
   opAt 1941 (.Dup ⟨0,by decide⟩),
   opAt 1942 (.Dup ⟨0,by decide⟩),
   pushAt 1943 0 0,
   opAt 1944 .SUB,
   opAt 1945 .MOD,
   pushAt 1946 2 1632,
   opAt 1947 .MSTORE]

 
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1948 2 2752,
   opAt 1949 .MLOAD,
   opAt 1950 .MLOAD,
   opAt 1951 (.Dup ⟨0,by decide⟩),
   opAt 1952 (.Dup ⟨2,by decide⟩),
   opAt 1953 .MUL]

 
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1954 (.Dup ⟨0,by decide⟩),
   pushAt 1955 1 3,
   opAt 1956 .MUL,
   pushAt 1957 1 2,
   opAt 1958 .XOR,
   opAt 1959 (.Dup ⟨0,by decide⟩),
   opAt 1960 (.Dup ⟨2,by decide⟩),
   opAt 1961 .MUL,
   pushAt 1962 1 2,
   opAt 1963 .SUB,
   opAt 1964 .MUL,
   opAt 1965 (.Dup ⟨0,by decide⟩),
   opAt 1966 (.Dup ⟨2,by decide⟩),
   opAt 1967 .MUL,
   pushAt 1968 1 2,
   opAt 1969 .SUB,
   opAt 1970 .MUL,
   opAt 1971 (.Dup ⟨0,by decide⟩),
   opAt 1972 (.Dup ⟨2,by decide⟩),
   opAt 1973 .MUL,
   pushAt 1974 1 2,
   opAt 1975 .SUB,
   opAt 1976 .MUL,
   opAt 1977 (.Dup ⟨0,by decide⟩),
   opAt 1978 (.Dup ⟨2,by decide⟩),
   opAt 1979 .MUL,
   pushAt 1980 1 2,
   opAt 1981 .SUB,
   opAt 1982 .MUL,
   opAt 1983 (.Dup ⟨0,by decide⟩),
   opAt 1984 (.Dup ⟨2,by decide⟩),
   opAt 1985 .MUL,
   pushAt 1986 1 2,
   opAt 1987 .SUB,
   opAt 1988 .MUL,
   opAt 1989 (.Dup ⟨0,by decide⟩),
   opAt 1990 (.Swap ⟨1,by decide⟩),
   opAt 1991 .MUL,
   pushAt 1992 1 2,
   opAt 1993 .SUB,
   opAt 1994 .MUL]

 

def blkNbTailHead : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1995 (.Dup ⟨0,by decide⟩),
   opAt 1996 (.Swap ⟨1,by decide⟩),
   opAt 1997 .MUL,
   pushAt 1998 2 1664,
   opAt 1999 .MSTORE,
   opAt 2000 .MUL,
   pushAt 2001 0 0,
   opAt 2002 .SUB,
   pushAt 2003 2 2720,
   opAt 2004 .MSTORE,
   pushAt 2005 2 2306,
   opAt 2006 (.Dup ⟨4,by decide⟩),
   pushAt 2007 1 1,
   opAt 2008 .XOR,
   pushAt 2009 2 2588,
   opAt 2010 .JUMPI]
def blkNbTailByte : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2011 2 2656,
   opAt 2012 .MLOAD,
   opAt 2013 .CALLDATALOAD,
   pushAt 2014 0 0,
   opAt 2015 .BYTE,
   pushAt 2016 1 3,
   opAt 2017 .EQ,
   pushAt 2018 2 1621,
   opAt 2019 .MUL,
   opAt 2020 .ADD]
def blkNbTailJoin : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2021 .JUMPDEST,
   pushAt 2022 1 32,
   opAt 2023 .MLOAD,
   pushAt 2024 1 128,
   opAt 2025 .SHR,
   pushAt 2026 2 1536,
   opAt 2027 .MLOAD,
   pushAt 2028 2 1568,
   opAt 2029 .MLOAD,
   pushAt 2030 2 1664,
   opAt 2031 .MLOAD,
   pushAt 2032 2 1632,
   opAt 2033 .MLOAD,
   pushAt 2034 2 1504,
   opAt 2035 .MLOAD,
   pushAt 2036 2 1472,
   opAt 2037 .MLOAD,
   pushAt 2038 2 1440,
   opAt 2039 .MLOAD,
   pushAt 2040 2 1408,
   opAt 2041 .MLOAD,
   pushAt 2042 2 1376,
   opAt 2043 .MLOAD,
   pushAt 2044 2 1344,
   opAt 2045 .MLOAD,
   pushAt 2046 2 1312,
   opAt 2047 .MLOAD,
   opAt 2048 (.Dup ⟨14,by decide⟩)]
def blkNbTail (esize : Nat) : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  blkNbTailHead ++ (if UInt256.ofNat esize = UInt256.ofNat 1 then blkNbTailByte else []) ++ blkNbTailJoin
theorem jumpDestNbJoin : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2588 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2021 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h

 

def blkZero8 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2843 .JUMPDEST,
   pushAt 2844 2 256,
   pushAt 2845 2 2112,
   pushAt 2846 2 2080,
   opAt 2847 .MCOPY,
   pushAt 2848 2 2080,
   opAt 2849 .MLOAD,
   opAt 2850 (.Dup ⟨14,by decide⟩),
   pushAt 2851 2 2112,
   opAt 2852 .MLOAD,
   opAt 2853 (.Dup ⟨14,by decide⟩),
   opAt 2854 (.Dup ⟨0,by decide⟩),
   opAt 2855 (.Dup ⟨14,by decide⟩),
   opAt 2856 (.Dup ⟨5,by decide⟩),
   opAt 2857 .MULMOD,
   opAt 2858 (.Dup ⟨2,by decide⟩),
   opAt 2859 .ADDMOD,
   opAt 2860 (.Dup ⟨0,by decide⟩),
   opAt 2861 (.Swap ⟨1,by decide⟩),
   opAt 2862 .SUB,
   opAt 2863 (.Dup ⟨14,by decide⟩),
   opAt 2864 .MUL,
   opAt 2865 (.Swap ⟨1,by decide⟩),
   opAt 2866 (.Dup ⟨2,by decide⟩),
   pushAt 2867 1 128,
   opAt 2868 .SHR,
   opAt 2869 .MUL,
   opAt 2870 .GT,
   opAt 2871 (.Swap ⟨0,by decide⟩),
   opAt 2872 .SUB,
   pushAt 2873 2 2740,
   opAt 2874 .JUMP]

def blkZero4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2991 .JUMPDEST,
   pushAt 2992 1 128,
   pushAt 2993 2 2112,
   pushAt 2994 2 2080,
   opAt 2995 .MCOPY,
   pushAt 2996 2 2080,
   opAt 2997 .MLOAD,
   opAt 2998 (.Dup ⟨14,by decide⟩),
   pushAt 2999 2 2112,
   opAt 3000 .MLOAD,
   opAt 3001 (.Dup ⟨14,by decide⟩),
   opAt 3002 (.Dup ⟨0,by decide⟩),
   opAt 3003 (.Dup ⟨14,by decide⟩),
   opAt 3004 (.Dup ⟨5,by decide⟩),
   opAt 3005 .MULMOD,
   opAt 3006 (.Dup ⟨2,by decide⟩),
   opAt 3007 .ADDMOD,
   opAt 3008 (.Dup ⟨0,by decide⟩),
   opAt 3009 (.Swap ⟨1,by decide⟩),
   opAt 3010 .SUB,
   opAt 3011 (.Dup ⟨14,by decide⟩),
   opAt 3012 .MUL,
   opAt 3013 (.Swap ⟨1,by decide⟩),
   opAt 3014 (.Dup ⟨2,by decide⟩),
   pushAt 3015 1 128,
   opAt 3016 .SHR,
   opAt 3017 .MUL,
   opAt 3018 .GT,
   opAt 3019 (.Swap ⟨0,by decide⟩),
   opAt 3020 .SUB,
   pushAt 3021 2 10755,
   opAt 3022 .JUMP]

def blkEstimateSuffix8 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2122 .JUMPDEST,
   pushAt 2123 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2124 (.Swap ⟨1,by decide⟩),
   opAt 2125 (.Dup ⟨14,by decide⟩),
   opAt 2126 .GT,
   opAt 2127 (.Dup ⟨2,by decide⟩),
   opAt 2128 .ADD,
   opAt 2129 .OR]

def blkEstimateSuffix4 : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8298 .JUMPDEST,
   pushAt 8299 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8300 (.Swap ⟨1,by decide⟩),
   opAt 8301 (.Dup ⟨14,by decide⟩),
   opAt 8302 .GT,
   opAt 8303 (.Dup ⟨2,by decide⟩),
   opAt 8304 .ADD,
   opAt 8305 .OR]

def blk3013 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2077 .JUMPDEST]

 
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2078 2 256,
   pushAt 2079 2 2112,
   pushAt 2080 2 2080,
   opAt 2081 .MCOPY]

 
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2082 2 2080,
   opAt 2083 .MLOAD,
   opAt 2084 (.Dup ⟨0,by decide⟩),
   opAt 2085 (.Dup ⟨14,by decide⟩),
   opAt 2086 .SHR,
   opAt 2087 (.Swap ⟨0,by decide⟩),
   pushAt 2088 2 1600,
   opAt 2089 .MLOAD,
   opAt 2090 .SHL,
   pushAt 2091 2 2112,
   opAt 2092 .MLOAD,
   opAt 2093 (.Dup ⟨15,by decide⟩),
   opAt 2094 .SHR,
   opAt 2095 .ADD,
   opAt 2096 (.Dup ⟨13,by decide⟩),
   opAt 2097 (.Dup ⟨0,by decide⟩),
   opAt 2098 (.Dup ⟨13,by decide⟩),
   opAt 2099 (.Dup ⟨4,by decide⟩),
   opAt 2100 .MULMOD,
   opAt 2101 (.Dup ⟨2,by decide⟩),
   opAt 2102 .ADDMOD,
   opAt 2103 (.Swap ⟨0,by decide⟩),
   opAt 2104 .SUB,
   opAt 2105 (.Dup ⟨12,by decide⟩),
   opAt 2106 .MUL,
   opAt 2107 (.Dup ⟨15,by decide⟩),
   opAt 2108 (.Dup ⟨1,by decide⟩),
   pushAt 2109 1 128,
   opAt 2110 .SHR,
   opAt 2111 .MUL,
   opAt 2112 (.Dup ⟨1,by decide⟩),
   pushAt 2113 0 0,
   opAt 2114 .MLOAD,
   opAt 2115 .MUL,
   pushAt 2116 2 2112,
   opAt 2117 .MLOAD,
   opAt 2118 .SUB,
   opAt 2119 .LT,
   opAt 2120 (.Swap ⟨0,by decide⟩),
   opAt 2121 .SUB,
   opAt 2122 .JUMPDEST,
   pushAt 2123 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2124 (.Swap ⟨1,by decide⟩),
   opAt 2125 (.Dup ⟨14,by decide⟩),
   opAt 2126 .GT,
   opAt 2127 (.Dup ⟨2,by decide⟩),
   opAt 2128 .ADD,
   opAt 2129 .OR]



def blk3013h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8253 .JUMPDEST]

 
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8254 1 128,
   pushAt 8255 2 2112,
   pushAt 8256 2 2080,
   opAt 8257 .MCOPY]

 
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8258 2 2080,
   opAt 8259 .MLOAD,
   opAt 8260 (.Dup ⟨0,by decide⟩),
   opAt 8261 (.Dup ⟨14,by decide⟩),
   opAt 8262 .SHR,
   opAt 8263 (.Swap ⟨0,by decide⟩),
   pushAt 8264 2 1600,
   opAt 8265 .MLOAD,
   opAt 8266 .SHL,
   pushAt 8267 2 2112,
   opAt 8268 .MLOAD,
   opAt 8269 (.Dup ⟨15,by decide⟩),
   opAt 8270 .SHR,
   opAt 8271 .ADD,
   opAt 8272 (.Dup ⟨13,by decide⟩),
   opAt 8273 (.Dup ⟨0,by decide⟩),
   opAt 8274 (.Dup ⟨13,by decide⟩),
   opAt 8275 (.Dup ⟨4,by decide⟩),
   opAt 8276 .MULMOD,
   opAt 8277 (.Dup ⟨2,by decide⟩),
   opAt 8278 .ADDMOD,
   opAt 8279 (.Swap ⟨0,by decide⟩),
   opAt 8280 .SUB,
   opAt 8281 (.Dup ⟨12,by decide⟩),
   opAt 8282 .MUL,
   opAt 8283 (.Dup ⟨15,by decide⟩),
   opAt 8284 (.Dup ⟨1,by decide⟩),
   pushAt 8285 1 128,
   opAt 8286 .SHR,
   opAt 8287 .MUL,
   opAt 8288 (.Dup ⟨1,by decide⟩),
   pushAt 8289 0 0,
   opAt 8290 .MLOAD,
   opAt 8291 .MUL,
   pushAt 8292 2 2112,
   opAt 8293 .MLOAD,
   opAt 8294 .SUB,
   opAt 8295 .LT,
   opAt 8296 (.Swap ⟨0,by decide⟩),
   opAt 8297 .SUB,
   opAt 8298 .JUMPDEST,
   pushAt 8299 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8300 (.Swap ⟨1,by decide⟩),
   opAt 8301 (.Dup ⟨14,by decide⟩),
   opAt 8302 .GT,
   opAt 8303 (.Dup ⟨2,by decide⟩),
   opAt 8304 .ADD,
   opAt 8305 .OR]



 




def blk3125Unc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2344 2 2080,
   opAt 2345 .MLOAD,
   opAt 2346 .ADD,
   opAt 2347 .SUB,
   opAt 2348 (.Dup ⟨0,by decide⟩),
   opAt 2349 .JUMPDEST,
   opAt 2350 .JUMPDEST,
   pushAt 2351 3 3055,
   opAt 2352 .JUMPI,
   opAt 2367 .JUMPDEST,
   pushAt 2368 2 2080,
   opAt 2369 .MSTORE]

def blk3125hUnc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8408 2 2080,
   opAt 8409 .MLOAD,
   opAt 8410 .ADD,
   opAt 8411 .SUB,
   opAt 8412 (.Dup ⟨0,by decide⟩),
   opAt 8413 .JUMPDEST,
   opAt 8414 .JUMPDEST,
   pushAt 8415 2 3055,
   opAt 8416 .JUMPI,
   opAt 2367 .JUMPDEST,
   pushAt 2368 2 2080,
   opAt 2369 .MSTORE]

def blk3125 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2344 2 2080,
   opAt 2345 .MLOAD,
   opAt 2346 .ADD,
   opAt 2347 .SUB,
   opAt 2348 (.Dup ⟨0,by decide⟩),
   opAt 2349 .JUMPDEST,
   opAt 2350 .JUMPDEST,
   pushAt 2351 3 3055,
   opAt 2352 .JUMPI,
   opAt 2353 (.Swap ⟨0,by decide⟩),
   opAt 2354 .POP]

 
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2370 .POP]

 
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2371 .JUMPDEST,
   pushAt 2372 0 0,
   pushAt 2373 2 2784,
   opAt 2374 .MLOAD]

 
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2375 .JUMPDEST,
   opAt 2376 (.Dup ⟨0,by decide⟩),
   opAt 2377 .MLOAD,
   pushAt 2378 2 2112,
   opAt 2379 (.Dup ⟨2,by decide⟩),
   opAt 2380 .SUB,
   opAt 2381 .MLOAD,
   opAt 2382 (.Dup ⟨1,by decide⟩),
   opAt 2383 .ADD,
   opAt 2384 (.Swap ⟨0,by decide⟩),
   opAt 2385 (.Dup ⟨1,by decide⟩),
   opAt 2386 .LT,
   opAt 2387 (.Swap ⟨0,by decide⟩),
   opAt 2388 (.Dup ⟨3,by decide⟩),
   opAt 2389 .ADD,
   opAt 2390 (.Swap ⟨2,by decide⟩),
   opAt 2391 (.Dup ⟨3,by decide⟩),
   opAt 2392 .LT,
   opAt 2393 .OR,
   opAt 2394 (.Swap ⟨1,by decide⟩),
   opAt 2395 (.Dup ⟨1,by decide⟩),
   opAt 2396 .MSTORE,
   pushAt 2397 1 31,
   opAt 2398 .NOT,
   opAt 2399 .ADD,
   pushAt 2400 2 2111,
   opAt 2401 (.Dup ⟨1,by decide⟩),
   opAt 2402 .GT,
   pushAt 2403 2 3067,
   opAt 2404 .JUMPI]

 
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2405 .POP,
   pushAt 2406 2 2080,
   opAt 2407 .MLOAD,
   opAt 2408 (.Dup ⟨1,by decide⟩),
   opAt 2409 .ADD,
   opAt 2410 (.Dup ⟨0,by decide⟩),
   pushAt 2411 2 2080,
   opAt 2412 .MSTORE,
   opAt 2413 .LT,
   opAt 2414 .ISZERO,
   pushAt 2415 2 3061,
   opAt 2416 .JUMPI]

 
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2417 2 2080,
   opAt 2418 .MLOAD,
   opAt 2419 (.Dup ⟨0,by decide⟩),
   opAt 2420 .ISZERO,
   pushAt 2421 2 3042,
   opAt 2422 .JUMPI]

 
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2355 .JUMPDEST,
   opAt 2356 .NOT,
   opAt 2357 .JUMPDEST,
   opAt 2358 .ADD,
   opAt 2359 (.Dup ⟨0,by decide⟩),
   opAt 2360 (.Dup ⟨2,by decide⟩),
   opAt 2361 .JUMPI]


 

def blk3253x :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

 
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8408 2 2080,
   opAt 8409 .MLOAD,
   opAt 8410 .ADD,
   opAt 8411 .SUB,
   opAt 8412 (.Dup ⟨0,by decide⟩),
   opAt 8413 .JUMPDEST,
   opAt 8414 .JUMPDEST,
   pushAt 8415 2 3055,
   opAt 8416 .JUMPI,
   opAt 8417 (.Swap ⟨0,by decide⟩),
   opAt 8418 .POP]

 
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8419 .NOT,
   opAt 8420 .ADD,
   opAt 8421 (.Dup ⟨0,by decide⟩),
   opAt 8422 (.Dup ⟨2,by decide⟩),
   opAt 8423 .JUMPI]


theorem jumpDest4608 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2349 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1854 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 1854 = 2349 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestBigC : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 207 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 134 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 134 = 207 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest4657 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2370 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1867 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 1867 = 2370 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestNeg4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2284 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1812 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 1812 = 2284 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestNegT : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2428 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1903 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 1903 = 2428 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest4839 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2680 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2077 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2077 = 2680 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestHead4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10696 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8253 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 8253 = 10696 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5115 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3061 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2371 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2371 = 3061 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5121 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3067 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2375 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2375 = 3067 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestLazyStore : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3055 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2367 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2367 = 3055 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestUnc : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3055 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2367 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2367 = 3055 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5311 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3042 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2355 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2355 = 3042 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5366 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3049 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2362 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2362 = 3049 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest2471 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2298 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1821 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 1821 = 2298 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h



end CycleSubmission.Global.Fast

namespace CycleSubmission.Global.Fast
open EvmSemantics EvmSemantics.EVM
end CycleSubmission.Global.Fast
