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
  [opAt 1853 .JUMPDEST,
   opAt 1854 (.Dup ⟨0,by decide⟩),
   opAt 1855 (.Dup ⟨3,by decide⟩),
   opAt 1856 .XOR,
   pushAt 1857 1 207,
   opAt 1858 .JUMPI]

 
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1859 (.Dup ⟨0,by decide⟩),
   pushAt 1860 1 96,
   pushAt 1861 2 2112,
   opAt 1862 .CALLDATACOPY,
   pushAt 1863 2 2370,
   pushAt 1864 2 3472,
   opAt 1865 .JUMP]


 
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1871 (.Dup ⟨0,by decide⟩),
   pushAt 1872 1 128,
   opAt 1873 .EQ,
   pushAt 1874 2 2284,
   opAt 1875 .JUMPI]

 
def negS8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1876 1 224,
   opAt 1877 .MLOAD,
   pushAt 1878 0 0,
   opAt 1879 .SUB,
   pushAt 1880 2 1504,
   opAt 1881 .MSTORE]

 
def negN8a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1882 1 192,
   opAt 1883 .MLOAD,
   opAt 1884 .NOT,
   pushAt 1885 2 1472,
   opAt 1886 .MSTORE]

 
def negN8b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1887 1 160,
   opAt 1888 .MLOAD,
   opAt 1889 .NOT,
   pushAt 1890 2 1440,
   opAt 1891 .MSTORE]

 
def negN8c :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1892 1 128,
   opAt 1893 .MLOAD,
   opAt 1894 .NOT,
   pushAt 1895 2 1408,
   opAt 1896 .MSTORE]

 
def negN8d :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1897 1 96,
   opAt 1898 .MLOAD,
   opAt 1899 .NOT,
   pushAt 1900 2 1376,
   opAt 1901 .MSTORE]

 


 


 


 
def negS4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1813 1 96,
   opAt 1814 .MLOAD,
   pushAt 1815 0 0,
   opAt 1816 .SUB,
   pushAt 1817 2 1376,
   opAt 1818 .MSTORE]

 
def negJ4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1812 .JUMPDEST]

 
def negJ4b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1819 2 2428,
   opAt 1820 .JUMP]

 
def negJT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1902 .JUMPDEST]

 
def blkNeg8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negS8 ++ negN8a ++ negN8b ++ negN8c ++ negN8d

 
def blkNeg4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negJ4 ++ negS4 ++ negJ4b

 
def blkNegT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1902 .JUMPDEST,
   pushAt 1903 1 64,
   opAt 1904 .MLOAD,
   opAt 1905 .NOT,
   pushAt 1906 2 1344,
   opAt 1907 .MSTORE,
   pushAt 1908 1 32,
   opAt 1909 .MLOAD,
   opAt 1910 .NOT,
   pushAt 1911 2 1312,
   opAt 1912 .MSTORE,
   pushAt 1913 0 0,
   opAt 1914 .MLOAD,
   opAt 1915 (.Dup ⟨0,by decide⟩),
   opAt 1916 .NOT,
   pushAt 1917 2 1280,
   opAt 1918 .MSTORE]


 
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1919 (.Dup ⟨0,by decide⟩),
   pushAt 1920 0 0,
   opAt 1921 .SUB,
   opAt 1922 (.Dup ⟨1,by decide⟩),
   opAt 1923 .AND]


 

def blk2919b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1925 (.Dup ⟨0,by decide⟩),
   pushAt 1926 2 1,
   opAt 1927 .ADD,
   pushAt 1928 2 1600,
   opAt 1929 .MSTORE,
   pushAt 1930 1 255,
   opAt 1931 .SUB,
   opAt 1932 (.Dup ⟨0,by decide⟩),
   pushAt 1933 2 1536,
   opAt 1934 .MSTORE,
   opAt 1935 .SHR,
   opAt 1936 (.Dup ⟨0,by decide⟩),
   pushAt 1937 2 1568,
   opAt 1938 .MSTORE,
   opAt 1939 (.Dup ⟨0,by decide⟩),
   opAt 1940 (.Dup ⟨0,by decide⟩),
   pushAt 1941 0 0,
   opAt 1942 .SUB,
   opAt 1943 .MOD,
   pushAt 1944 2 1632,
   opAt 1945 .MSTORE]

 
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1946 2 2752,
   opAt 1947 .MLOAD,
   opAt 1948 .MLOAD,
   opAt 1949 (.Dup ⟨0,by decide⟩),
   opAt 1950 (.Dup ⟨2,by decide⟩),
   opAt 1951 .MUL]

 
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1952 (.Dup ⟨0,by decide⟩),
   pushAt 1953 1 3,
   opAt 1954 .MUL,
   pushAt 1955 1 2,
   opAt 1956 .XOR,
   opAt 1957 (.Dup ⟨0,by decide⟩),
   opAt 1958 (.Dup ⟨2,by decide⟩),
   opAt 1959 .MUL,
   pushAt 1960 1 2,
   opAt 1961 .SUB,
   opAt 1962 .MUL,
   opAt 1963 (.Dup ⟨0,by decide⟩),
   opAt 1964 (.Dup ⟨2,by decide⟩),
   opAt 1965 .MUL,
   pushAt 1966 1 2,
   opAt 1967 .SUB,
   opAt 1968 .MUL,
   opAt 1969 (.Dup ⟨0,by decide⟩),
   opAt 1970 (.Dup ⟨2,by decide⟩),
   opAt 1971 .MUL,
   pushAt 1972 1 2,
   opAt 1973 .SUB,
   opAt 1974 .MUL,
   opAt 1975 (.Dup ⟨0,by decide⟩),
   opAt 1976 (.Dup ⟨2,by decide⟩),
   opAt 1977 .MUL,
   pushAt 1978 1 2,
   opAt 1979 .SUB,
   opAt 1980 .MUL,
   opAt 1981 (.Dup ⟨0,by decide⟩),
   opAt 1982 (.Dup ⟨2,by decide⟩),
   opAt 1983 .MUL,
   pushAt 1984 1 2,
   opAt 1985 .SUB,
   opAt 1986 .MUL,
   opAt 1987 (.Dup ⟨0,by decide⟩),
   opAt 1988 (.Swap ⟨1,by decide⟩),
   opAt 1989 .MUL,
   pushAt 1990 1 2,
   opAt 1991 .SUB,
   opAt 1992 .MUL]

 

def blkNbTailHead : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1993 (.Dup ⟨0,by decide⟩),
   opAt 1994 (.Swap ⟨1,by decide⟩),
   opAt 1995 .MUL,
   pushAt 1996 2 1664,
   opAt 1997 .MSTORE,
   opAt 1998 .MUL,
   pushAt 1999 0 0,
   opAt 2000 .SUB,
   pushAt 2001 2 2720,
   opAt 2002 .MSTORE,
   pushAt 2003 2 2306,
   opAt 2004 (.Dup ⟨4,by decide⟩),
   pushAt 2005 1 1,
   opAt 2006 .XOR,
   pushAt 2007 2 2588,
   opAt 2008 .JUMPI]
def blkNbTailByte : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2009 2 2656,
   opAt 2010 .MLOAD,
   opAt 2011 .CALLDATALOAD,
   pushAt 2012 0 0,
   opAt 2013 .BYTE,
   pushAt 2014 1 3,
   opAt 2015 .EQ,
   pushAt 2016 2 1621,
   opAt 2017 .MUL,
   opAt 2018 .ADD]
def blkNbTailJoin : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2019 .JUMPDEST,
   pushAt 2020 1 32,
   opAt 2021 .MLOAD,
   pushAt 2022 1 128,
   opAt 2023 .SHR,
   pushAt 2024 2 1536,
   opAt 2025 .MLOAD,
   pushAt 2026 2 1568,
   opAt 2027 .MLOAD,
   pushAt 2028 2 1664,
   opAt 2029 .MLOAD,
   pushAt 2030 2 1632,
   opAt 2031 .MLOAD,
   pushAt 2032 2 1504,
   opAt 2033 .MLOAD,
   pushAt 2034 2 1472,
   opAt 2035 .MLOAD,
   pushAt 2036 2 1440,
   opAt 2037 .MLOAD,
   pushAt 2038 2 1408,
   opAt 2039 .MLOAD,
   pushAt 2040 2 1376,
   opAt 2041 .MLOAD,
   pushAt 2042 2 1344,
   opAt 2043 .MLOAD,
   pushAt 2044 2 1312,
   opAt 2045 .MLOAD,
   opAt 2046 (.Dup ⟨14,by decide⟩)]
def blkNbTail (esize : Nat) : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  blkNbTailHead ++ (if UInt256.ofNat esize = UInt256.ofNat 1 then blkNbTailByte else []) ++ blkNbTailJoin
theorem jumpDestNbJoin : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2588 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2019 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h

 

def blkZero8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2839 .JUMPDEST,
   pushAt 2840 2 256,
   pushAt 2841 2 2112,
   pushAt 2842 2 2080,
   opAt 2843 .MCOPY,
   pushAt 2844 2 2080,
   opAt 2845 .MLOAD,
   opAt 2846 (.Dup ⟨14,by decide⟩),
   pushAt 2847 2 2112,
   opAt 2848 .MLOAD,
   opAt 2849 (.Dup ⟨14,by decide⟩),
   opAt 2850 (.Dup ⟨0,by decide⟩),
   opAt 2851 (.Dup ⟨14,by decide⟩),
   opAt 2852 (.Dup ⟨5,by decide⟩),
   opAt 2853 .MULMOD,
   opAt 2854 (.Dup ⟨2,by decide⟩),
   opAt 2855 .ADDMOD,
   opAt 2856 (.Dup ⟨0,by decide⟩),
   opAt 2857 (.Swap ⟨1,by decide⟩),
   opAt 2858 .SUB,
   opAt 2859 (.Dup ⟨14,by decide⟩),
   opAt 2860 .MUL,
   opAt 2861 (.Swap ⟨1,by decide⟩),
   opAt 2862 (.Dup ⟨2,by decide⟩),
   pushAt 2863 1 128,
   opAt 2864 .SHR,
   opAt 2865 .MUL,
   opAt 2866 .GT,
   opAt 2867 (.Swap ⟨0,by decide⟩),
   opAt 2868 .SUB,
   pushAt 2869 2 2740,
   opAt 2870 .JUMP]

def blkZero4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2989 .JUMPDEST,
   pushAt 2990 1 128,
   pushAt 2991 2 2112,
   pushAt 2992 2 2080,
   opAt 2993 .MCOPY,
   pushAt 2994 2 2080,
   opAt 2995 .MLOAD,
   opAt 2996 (.Dup ⟨14,by decide⟩),
   pushAt 2997 2 2112,
   opAt 2998 .MLOAD,
   opAt 2999 (.Dup ⟨14,by decide⟩),
   opAt 3000 (.Dup ⟨0,by decide⟩),
   opAt 3001 (.Dup ⟨14,by decide⟩),
   opAt 3002 (.Dup ⟨5,by decide⟩),
   opAt 3003 .MULMOD,
   opAt 3004 (.Dup ⟨2,by decide⟩),
   opAt 3005 .ADDMOD,
   opAt 3006 (.Dup ⟨0,by decide⟩),
   opAt 3007 (.Swap ⟨1,by decide⟩),
   opAt 3008 .SUB,
   opAt 3009 (.Dup ⟨14,by decide⟩),
   opAt 3010 .MUL,
   opAt 3011 (.Swap ⟨1,by decide⟩),
   opAt 3012 (.Dup ⟨2,by decide⟩),
   pushAt 3013 1 128,
   opAt 3014 .SHR,
   opAt 3015 .MUL,
   opAt 3016 .GT,
   opAt 3017 (.Swap ⟨0,by decide⟩),
   opAt 3018 .SUB,
   pushAt 3019 2 10755,
   opAt 3020 .JUMP]

def blkEstimateSuffix8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2120 .JUMPDEST,
   pushAt 2121 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2122 (.Swap ⟨1,by decide⟩),
   opAt 2123 (.Dup ⟨14,by decide⟩),
   opAt 2124 .GT,
   opAt 2125 (.Dup ⟨2,by decide⟩),
   opAt 2126 .ADD,
   opAt 2127 .OR]

def blkEstimateSuffix4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8296 .JUMPDEST,
   pushAt 8297 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8298 (.Swap ⟨1,by decide⟩),
   opAt 8299 (.Dup ⟨14,by decide⟩),
   opAt 8300 .GT,
   opAt 8301 (.Dup ⟨2,by decide⟩),
   opAt 8302 .ADD,
   opAt 8303 .OR]

def blk3013 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2075 .JUMPDEST]

 
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2076 2 256,
   pushAt 2077 2 2112,
   pushAt 2078 2 2080,
   opAt 2079 .MCOPY]

 
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2080 2 2080,
   opAt 2081 .MLOAD,
   opAt 2082 (.Dup ⟨0,by decide⟩),
   opAt 2083 (.Dup ⟨14,by decide⟩),
   opAt 2084 .SHR,
   opAt 2085 (.Swap ⟨0,by decide⟩),
   pushAt 2086 2 1600,
   opAt 2087 .MLOAD,
   opAt 2088 .SHL,
   pushAt 2089 2 2112,
   opAt 2090 .MLOAD,
   opAt 2091 (.Dup ⟨15,by decide⟩),
   opAt 2092 .SHR,
   opAt 2093 .ADD,
   opAt 2094 (.Dup ⟨13,by decide⟩),
   opAt 2095 (.Dup ⟨0,by decide⟩),
   opAt 2096 (.Dup ⟨13,by decide⟩),
   opAt 2097 (.Dup ⟨4,by decide⟩),
   opAt 2098 .MULMOD,
   opAt 2099 (.Dup ⟨2,by decide⟩),
   opAt 2100 .ADDMOD,
   opAt 2101 (.Swap ⟨0,by decide⟩),
   opAt 2102 .SUB,
   opAt 2103 (.Dup ⟨12,by decide⟩),
   opAt 2104 .MUL,
   opAt 2105 (.Dup ⟨15,by decide⟩),
   opAt 2106 (.Dup ⟨1,by decide⟩),
   pushAt 2107 1 128,
   opAt 2108 .SHR,
   opAt 2109 .MUL,
   opAt 2110 (.Dup ⟨1,by decide⟩),
   pushAt 2111 0 0,
   opAt 2112 .MLOAD,
   opAt 2113 .MUL,
   pushAt 2114 2 2112,
   opAt 2115 .MLOAD,
   opAt 2116 .SUB,
   opAt 2117 .LT,
   opAt 2118 (.Swap ⟨0,by decide⟩),
   opAt 2119 .SUB,
   opAt 2120 .JUMPDEST,
   pushAt 2121 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2122 (.Swap ⟨1,by decide⟩),
   opAt 2123 (.Dup ⟨14,by decide⟩),
   opAt 2124 .GT,
   opAt 2125 (.Dup ⟨2,by decide⟩),
   opAt 2126 .ADD,
   opAt 2127 .OR]



def blk3013h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8251 .JUMPDEST]

 
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8252 1 128,
   pushAt 8253 2 2112,
   pushAt 8254 2 2080,
   opAt 8255 .MCOPY]

 
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8256 2 2080,
   opAt 8257 .MLOAD,
   opAt 8258 (.Dup ⟨0,by decide⟩),
   opAt 8259 (.Dup ⟨14,by decide⟩),
   opAt 8260 .SHR,
   opAt 8261 (.Swap ⟨0,by decide⟩),
   pushAt 8262 2 1600,
   opAt 8263 .MLOAD,
   opAt 8264 .SHL,
   pushAt 8265 2 2112,
   opAt 8266 .MLOAD,
   opAt 8267 (.Dup ⟨15,by decide⟩),
   opAt 8268 .SHR,
   opAt 8269 .ADD,
   opAt 8270 (.Dup ⟨13,by decide⟩),
   opAt 8271 (.Dup ⟨0,by decide⟩),
   opAt 8272 (.Dup ⟨13,by decide⟩),
   opAt 8273 (.Dup ⟨4,by decide⟩),
   opAt 8274 .MULMOD,
   opAt 8275 (.Dup ⟨2,by decide⟩),
   opAt 8276 .ADDMOD,
   opAt 8277 (.Swap ⟨0,by decide⟩),
   opAt 8278 .SUB,
   opAt 8279 (.Dup ⟨12,by decide⟩),
   opAt 8280 .MUL,
   opAt 8281 (.Dup ⟨15,by decide⟩),
   opAt 8282 (.Dup ⟨1,by decide⟩),
   pushAt 8283 1 128,
   opAt 8284 .SHR,
   opAt 8285 .MUL,
   opAt 8286 (.Dup ⟨1,by decide⟩),
   pushAt 8287 0 0,
   opAt 8288 .MLOAD,
   opAt 8289 .MUL,
   pushAt 8290 2 2112,
   opAt 8291 .MLOAD,
   opAt 8292 .SUB,
   opAt 8293 .LT,
   opAt 8294 (.Swap ⟨0,by decide⟩),
   opAt 8295 .SUB,
   opAt 8296 .JUMPDEST,
   pushAt 8297 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8298 (.Swap ⟨1,by decide⟩),
   opAt 8299 (.Dup ⟨14,by decide⟩),
   opAt 8300 .GT,
   opAt 8301 (.Dup ⟨2,by decide⟩),
   opAt 8302 .ADD,
   opAt 8303 .OR]



 




def blk3125Unc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2342 2 2080,
   opAt 2343 .MLOAD,
   opAt 2344 .ADD,
   opAt 2345 .SUB,
   opAt 2346 (.Dup ⟨0,by decide⟩),
   pushAt 2347 5 3055,
   opAt 2348 .JUMPI,
   opAt 2364 .JUMPDEST,
   pushAt 2365 2 2080,
   opAt 2366 .MSTORE]

def blk3125hUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8406 2 2080,
   opAt 8407 .MLOAD,
   opAt 8408 .ADD,
   opAt 8409 .SUB,
   opAt 8410 (.Dup ⟨0,by decide⟩),
   pushAt 8411 4 3055,
   opAt 8412 .JUMPI,
   opAt 2364 .JUMPDEST,
   pushAt 2365 2 2080,
   opAt 2366 .MSTORE]

def blk3125 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2342 2 2080,
   opAt 2343 .MLOAD,
   opAt 2344 .ADD,
   opAt 2345 .SUB,
   opAt 2346 (.Dup ⟨0,by decide⟩),
   pushAt 2347 5 3055,
   opAt 2348 .JUMPI,
   opAt 2349 (.Swap ⟨0,by decide⟩),
   opAt 2350 .POP]

 
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2367 .POP]

 
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2368 .JUMPDEST,
   pushAt 2369 0 0,
   pushAt 2370 2 2784,
   opAt 2371 .MLOAD]

 
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2372 .JUMPDEST,
   opAt 2373 (.Dup ⟨0,by decide⟩),
   opAt 2374 .MLOAD,
   pushAt 2375 2 2112,
   opAt 2376 (.Dup ⟨2,by decide⟩),
   opAt 2377 .SUB,
   opAt 2378 .MLOAD,
   opAt 2379 (.Dup ⟨1,by decide⟩),
   opAt 2380 .ADD,
   opAt 2381 (.Swap ⟨0,by decide⟩),
   opAt 2382 (.Dup ⟨1,by decide⟩),
   opAt 2383 .LT,
   opAt 2384 (.Swap ⟨0,by decide⟩),
   opAt 2385 (.Dup ⟨3,by decide⟩),
   opAt 2386 .ADD,
   opAt 2387 (.Swap ⟨2,by decide⟩),
   opAt 2388 (.Dup ⟨3,by decide⟩),
   opAt 2389 .LT,
   opAt 2390 .OR,
   opAt 2391 (.Swap ⟨1,by decide⟩),
   opAt 2392 (.Dup ⟨1,by decide⟩),
   opAt 2393 .MSTORE,
   pushAt 2394 1 31,
   opAt 2395 .NOT,
   opAt 2396 .ADD,
   pushAt 2397 2 2111,
   opAt 2398 (.Dup ⟨1,by decide⟩),
   opAt 2399 .GT,
   pushAt 2400 2 3067,
   opAt 2401 .JUMPI]

 
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2402 .POP,
   pushAt 2403 2 2080,
   opAt 2404 .MLOAD,
   opAt 2405 (.Dup ⟨1,by decide⟩),
   opAt 2406 .ADD,
   opAt 2407 (.Dup ⟨0,by decide⟩),
   pushAt 2408 2 2080,
   opAt 2409 .MSTORE,
   opAt 2410 .LT,
   opAt 2411 .ISZERO,
   pushAt 2412 2 3061,
   opAt 2413 .JUMPI]

 
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2414 2 2080,
   opAt 2415 .MLOAD,
   opAt 2416 (.Dup ⟨0,by decide⟩),
   opAt 2417 .ISZERO,
   pushAt 2418 2 3042,
   opAt 2419 .JUMPI]

 
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2351 .JUMPDEST,
   opAt 2352 .NOT,
   opAt 2353 .ADD,
   opAt 2354 (.Dup ⟨0,by decide⟩),
   opAt 2355 (.Dup ⟨2,by decide⟩),
   opAt 2356 .JUMPI]


 

def blk3253x :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  []

 
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8406 2 2080,
   opAt 8407 .MLOAD,
   opAt 8408 .ADD,
   opAt 8409 .SUB,
   opAt 8410 (.Dup ⟨0,by decide⟩),
   pushAt 8411 4 3055,
   opAt 8412 .JUMPI,
   opAt 8413 (.Swap ⟨0,by decide⟩),
   opAt 8414 .POP]

 
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8415 .NOT,
   opAt 8416 .ADD,
   opAt 8417 (.Dup ⟨0,by decide⟩),
   opAt 8418 (.Dup ⟨2,by decide⟩),
   opAt 8419 .JUMPI]


theorem jumpDest4608 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2349 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1853 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1853 = 2349 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestBigC : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 207 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 134 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 134 = 207 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest4657 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2370 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1866 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1866 = 2370 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestNeg4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2284 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1812 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1812 = 2284 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestNegT : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2428 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1902 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1902 = 2428 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest4839 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2680 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2075 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2075 = 2680 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestHead4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10696 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8251 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 8251 = 10696 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5115 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3061 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2368 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2368 = 3061 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5121 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3067 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2372 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2372 = 3067 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestLazyStore : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3055 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2364 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2364 = 3055 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestUnc : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3055 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2364 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2364 = 3055 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5311 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3042 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2351 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2351 = 3042 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h




theorem jumpDest2471 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2298 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1821 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1821 = 2298 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h



end CycleSubmission.Global.Fast

namespace CycleSubmission.Global.Fast
open EvmSemantics EvmSemantics.EVM
end CycleSubmission.Global.Fast
