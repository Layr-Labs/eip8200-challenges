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
  [opAt 1854 .JUMPDEST,
   opAt 1855 (.Dup ⟨0,by decide⟩),
   opAt 1856 (.Dup ⟨3,by decide⟩),
   opAt 1857 .XOR,
   pushAt 1858 1 207,
   opAt 1859 .JUMPI]

 
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1860 (.Dup ⟨0,by decide⟩),
   pushAt 1861 1 96,
   pushAt 1862 2 2112,
   opAt 1863 .CALLDATACOPY,
   pushAt 1864 2 2370,
   pushAt 1865 2 3472,
   opAt 1866 .JUMP]


 
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1872 (.Dup ⟨0,by decide⟩),
   pushAt 1873 1 128,
   opAt 1874 .EQ,
   pushAt 1875 2 2284,
   opAt 1876 .JUMPI]

 
def negS8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1877 1 224,
   opAt 1878 .MLOAD,
   pushAt 1879 0 0,
   opAt 1880 .SUB,
   pushAt 1881 2 1504,
   opAt 1882 .MSTORE]

 
def negN8a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1883 1 192,
   opAt 1884 .MLOAD,
   opAt 1885 .NOT,
   pushAt 1886 2 1472,
   opAt 1887 .MSTORE]

 
def negN8b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1888 1 160,
   opAt 1889 .MLOAD,
   opAt 1890 .NOT,
   pushAt 1891 2 1440,
   opAt 1892 .MSTORE]

 
def negN8c :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1893 1 128,
   opAt 1894 .MLOAD,
   opAt 1895 .NOT,
   pushAt 1896 2 1408,
   opAt 1897 .MSTORE]

 
def negN8d :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1898 1 96,
   opAt 1899 .MLOAD,
   opAt 1900 .NOT,
   pushAt 1901 2 1376,
   opAt 1902 .MSTORE]

 


 


 


 
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
  [opAt 1903 .JUMPDEST]

 
def blkNeg8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negS8 ++ negN8a ++ negN8b ++ negN8c ++ negN8d

 
def blkNeg4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negJ4 ++ negS4 ++ negJ4b

 
def blkNegT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
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
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1920 (.Dup ⟨0,by decide⟩),
   pushAt 1921 0 0,
   opAt 1922 .SUB,
   opAt 1923 (.Dup ⟨1,by decide⟩),
   opAt 1924 .AND]


 

def blk2919b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1926 (.Dup ⟨0,by decide⟩),
   pushAt 1927 2 1,
   opAt 1928 .ADD,
   pushAt 1929 2 1600,
   opAt 1930 .MSTORE,
   pushAt 1931 1 255,
   opAt 1932 .SUB,
   opAt 1933 (.Dup ⟨0,by decide⟩),
   pushAt 1934 2 1536,
   opAt 1935 .MSTORE,
   opAt 1936 .SHR,
   opAt 1937 (.Dup ⟨0,by decide⟩),
   pushAt 1938 2 1568,
   opAt 1939 .MSTORE,
   opAt 1940 (.Dup ⟨0,by decide⟩),
   opAt 1941 (.Dup ⟨0,by decide⟩),
   pushAt 1942 0 0,
   opAt 1943 .SUB,
   opAt 1944 .MOD,
   pushAt 1945 2 1632,
   opAt 1946 .MSTORE]

 
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1947 2 2752,
   opAt 1948 .MLOAD,
   opAt 1949 .MLOAD,
   opAt 1950 (.Dup ⟨0,by decide⟩),
   opAt 1951 (.Dup ⟨2,by decide⟩),
   opAt 1952 .MUL]

 
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1953 (.Dup ⟨0,by decide⟩),
   pushAt 1954 1 3,
   opAt 1955 .MUL,
   pushAt 1956 1 2,
   opAt 1957 .XOR,
   opAt 1958 (.Dup ⟨0,by decide⟩),
   opAt 1959 (.Dup ⟨2,by decide⟩),
   opAt 1960 .MUL,
   pushAt 1961 1 2,
   opAt 1962 .SUB,
   opAt 1963 .MUL,
   opAt 1964 (.Dup ⟨0,by decide⟩),
   opAt 1965 (.Dup ⟨2,by decide⟩),
   opAt 1966 .MUL,
   pushAt 1967 1 2,
   opAt 1968 .SUB,
   opAt 1969 .MUL,
   opAt 1970 (.Dup ⟨0,by decide⟩),
   opAt 1971 (.Dup ⟨2,by decide⟩),
   opAt 1972 .MUL,
   pushAt 1973 1 2,
   opAt 1974 .SUB,
   opAt 1975 .MUL,
   opAt 1976 (.Dup ⟨0,by decide⟩),
   opAt 1977 (.Dup ⟨2,by decide⟩),
   opAt 1978 .MUL,
   pushAt 1979 1 2,
   opAt 1980 .SUB,
   opAt 1981 .MUL,
   opAt 1982 (.Dup ⟨0,by decide⟩),
   opAt 1983 (.Dup ⟨2,by decide⟩),
   opAt 1984 .MUL,
   pushAt 1985 1 2,
   opAt 1986 .SUB,
   opAt 1987 .MUL,
   opAt 1988 (.Dup ⟨0,by decide⟩),
   opAt 1989 (.Swap ⟨1,by decide⟩),
   opAt 1990 .MUL,
   pushAt 1991 1 2,
   opAt 1992 .SUB,
   opAt 1993 .MUL]

 

def blkNbTailHead : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1994 (.Dup ⟨0,by decide⟩),
   opAt 1995 (.Swap ⟨1,by decide⟩),
   opAt 1996 .MUL,
   pushAt 1997 2 1664,
   opAt 1998 .MSTORE,
   opAt 1999 .MUL,
   pushAt 2000 0 0,
   opAt 2001 .SUB,
   pushAt 2002 2 2720,
   opAt 2003 .MSTORE,
   pushAt 2004 2 2306,
   opAt 2005 (.Dup ⟨4,by decide⟩),
   pushAt 2006 1 1,
   opAt 2007 .XOR,
   pushAt 2008 2 2588,
   opAt 2009 .JUMPI]
def blkNbTailByte : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2010 2 2656,
   opAt 2011 .MLOAD,
   opAt 2012 .CALLDATALOAD,
   pushAt 2013 0 0,
   opAt 2014 .BYTE,
   pushAt 2015 1 3,
   opAt 2016 .EQ,
   pushAt 2017 2 1621,
   opAt 2018 .MUL,
   opAt 2019 .ADD]
def blkNbTailJoin : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2020 .JUMPDEST,
   pushAt 2021 1 32,
   opAt 2022 .MLOAD,
   pushAt 2023 1 128,
   opAt 2024 .SHR,
   pushAt 2025 2 1536,
   opAt 2026 .MLOAD,
   pushAt 2027 2 1568,
   opAt 2028 .MLOAD,
   pushAt 2029 2 1664,
   opAt 2030 .MLOAD,
   pushAt 2031 2 1632,
   opAt 2032 .MLOAD,
   pushAt 2033 2 1504,
   opAt 2034 .MLOAD,
   pushAt 2035 2 1472,
   opAt 2036 .MLOAD,
   pushAt 2037 2 1440,
   opAt 2038 .MLOAD,
   pushAt 2039 2 1408,
   opAt 2040 .MLOAD,
   pushAt 2041 2 1376,
   opAt 2042 .MLOAD,
   pushAt 2043 2 1344,
   opAt 2044 .MLOAD,
   pushAt 2045 2 1312,
   opAt 2046 .MLOAD,
   opAt 2047 (.Dup ⟨14,by decide⟩)]
def blkNbTail (esize : Nat) : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  blkNbTailHead ++ (if UInt256.ofNat esize = UInt256.ofNat 1 then blkNbTailByte else []) ++ blkNbTailJoin
theorem jumpDestNbJoin : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2588 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2020 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h

 

def blkZero8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2841 .JUMPDEST,
   pushAt 2842 2 256,
   pushAt 2843 2 2112,
   pushAt 2844 2 2080,
   opAt 2845 .MCOPY,
   pushAt 2846 2 2080,
   opAt 2847 .MLOAD,
   opAt 2848 (.Dup ⟨14,by decide⟩),
   pushAt 2849 2 2112,
   opAt 2850 .MLOAD,
   opAt 2851 (.Dup ⟨14,by decide⟩),
   opAt 2852 (.Dup ⟨0,by decide⟩),
   opAt 2853 (.Dup ⟨14,by decide⟩),
   opAt 2854 (.Dup ⟨5,by decide⟩),
   opAt 2855 .MULMOD,
   opAt 2856 (.Dup ⟨2,by decide⟩),
   opAt 2857 .ADDMOD,
   opAt 2858 (.Dup ⟨0,by decide⟩),
   opAt 2859 (.Swap ⟨1,by decide⟩),
   opAt 2860 .SUB,
   opAt 2861 (.Dup ⟨14,by decide⟩),
   opAt 2862 .MUL,
   opAt 2863 (.Swap ⟨1,by decide⟩),
   opAt 2864 (.Dup ⟨2,by decide⟩),
   pushAt 2865 1 128,
   opAt 2866 .SHR,
   opAt 2867 .MUL,
   opAt 2868 .GT,
   opAt 2869 (.Swap ⟨0,by decide⟩),
   opAt 2870 .SUB,
   pushAt 2871 2 2740,
   opAt 2872 .JUMP]

def blkZero4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
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

def blkEstimateSuffix8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2121 .JUMPDEST,
   pushAt 2122 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2123 (.Swap ⟨1,by decide⟩),
   opAt 2124 (.Dup ⟨14,by decide⟩),
   opAt 2125 .GT,
   opAt 2126 (.Dup ⟨2,by decide⟩),
   opAt 2127 .ADD,
   opAt 2128 .OR]

def blkEstimateSuffix4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8298 .JUMPDEST,
   pushAt 8299 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8300 (.Swap ⟨1,by decide⟩),
   opAt 8301 (.Dup ⟨14,by decide⟩),
   opAt 8302 .GT,
   opAt 8303 (.Dup ⟨2,by decide⟩),
   opAt 8304 .ADD,
   opAt 8305 .OR]

def blk3013 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2076 .JUMPDEST]

 
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2077 2 256,
   pushAt 2078 2 2112,
   pushAt 2079 2 2080,
   opAt 2080 .MCOPY]

 
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2081 2 2080,
   opAt 2082 .MLOAD,
   opAt 2083 (.Dup ⟨0,by decide⟩),
   opAt 2084 (.Dup ⟨14,by decide⟩),
   opAt 2085 .SHR,
   opAt 2086 (.Swap ⟨0,by decide⟩),
   pushAt 2087 2 1600,
   opAt 2088 .MLOAD,
   opAt 2089 .SHL,
   pushAt 2090 2 2112,
   opAt 2091 .MLOAD,
   opAt 2092 (.Dup ⟨15,by decide⟩),
   opAt 2093 .SHR,
   opAt 2094 .ADD,
   opAt 2095 (.Dup ⟨13,by decide⟩),
   opAt 2096 (.Dup ⟨0,by decide⟩),
   opAt 2097 (.Dup ⟨13,by decide⟩),
   opAt 2098 (.Dup ⟨4,by decide⟩),
   opAt 2099 .MULMOD,
   opAt 2100 (.Dup ⟨2,by decide⟩),
   opAt 2101 .ADDMOD,
   opAt 2102 (.Swap ⟨0,by decide⟩),
   opAt 2103 .SUB,
   opAt 2104 (.Dup ⟨12,by decide⟩),
   opAt 2105 .MUL,
   opAt 2106 (.Dup ⟨15,by decide⟩),
   opAt 2107 (.Dup ⟨1,by decide⟩),
   pushAt 2108 1 128,
   opAt 2109 .SHR,
   opAt 2110 .MUL,
   opAt 2111 (.Dup ⟨1,by decide⟩),
   pushAt 2112 0 0,
   opAt 2113 .MLOAD,
   opAt 2114 .MUL,
   pushAt 2115 2 2112,
   opAt 2116 .MLOAD,
   opAt 2117 .SUB,
   opAt 2118 .LT,
   opAt 2119 (.Swap ⟨0,by decide⟩),
   opAt 2120 .SUB,
   opAt 2121 .JUMPDEST,
   pushAt 2122 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2123 (.Swap ⟨1,by decide⟩),
   opAt 2124 (.Dup ⟨14,by decide⟩),
   opAt 2125 .GT,
   opAt 2126 (.Dup ⟨2,by decide⟩),
   opAt 2127 .ADD,
   opAt 2128 .OR]



def blk3013h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8253 .JUMPDEST]

 
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8254 1 128,
   pushAt 8255 2 2112,
   pushAt 8256 2 2080,
   opAt 8257 .MCOPY]

 
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
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
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2343 2 2080,
   opAt 2344 .MLOAD,
   opAt 2345 .ADD,
   opAt 2346 .SUB,
   opAt 2347 (.Dup ⟨0,by decide⟩),
   pushAt 2348 5 3055,
   opAt 2349 .JUMPI,
   opAt 2365 .JUMPDEST,
   pushAt 2366 2 2080,
   opAt 2367 .MSTORE]

def blk3125hUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8408 2 2080,
   opAt 8409 .MLOAD,
   opAt 8410 .ADD,
   opAt 8411 .SUB,
   opAt 8412 (.Dup ⟨0,by decide⟩),
   pushAt 8413 4 3055,
   opAt 8414 .JUMPI,
   opAt 2365 .JUMPDEST,
   pushAt 2366 2 2080,
   opAt 2367 .MSTORE]

def blk3125 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2343 2 2080,
   opAt 2344 .MLOAD,
   opAt 2345 .ADD,
   opAt 2346 .SUB,
   opAt 2347 (.Dup ⟨0,by decide⟩),
   pushAt 2348 5 3055,
   opAt 2349 .JUMPI,
   opAt 2350 (.Swap ⟨0,by decide⟩),
   opAt 2351 .POP]

 
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2368 .POP]

 
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2369 .JUMPDEST,
   pushAt 2370 0 0,
   pushAt 2371 2 2784,
   opAt 2372 .MLOAD]

 
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2373 .JUMPDEST,
   opAt 2374 (.Dup ⟨0,by decide⟩),
   opAt 2375 .MLOAD,
   pushAt 2376 2 2112,
   opAt 2377 (.Dup ⟨2,by decide⟩),
   opAt 2378 .SUB,
   opAt 2379 .MLOAD,
   opAt 2380 (.Dup ⟨1,by decide⟩),
   opAt 2381 .ADD,
   opAt 2382 (.Swap ⟨0,by decide⟩),
   opAt 2383 (.Dup ⟨1,by decide⟩),
   opAt 2384 .LT,
   opAt 2385 (.Swap ⟨0,by decide⟩),
   opAt 2386 (.Dup ⟨3,by decide⟩),
   opAt 2387 .ADD,
   opAt 2388 (.Swap ⟨2,by decide⟩),
   opAt 2389 (.Dup ⟨3,by decide⟩),
   opAt 2390 .LT,
   opAt 2391 .OR,
   opAt 2392 (.Swap ⟨1,by decide⟩),
   opAt 2393 (.Dup ⟨1,by decide⟩),
   opAt 2394 .MSTORE,
   pushAt 2395 1 31,
   opAt 2396 .NOT,
   opAt 2397 .ADD,
   pushAt 2398 2 2111,
   opAt 2399 (.Dup ⟨1,by decide⟩),
   opAt 2400 .GT,
   pushAt 2401 2 3067,
   opAt 2402 .JUMPI]

 
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2403 .POP,
   pushAt 2404 2 2080,
   opAt 2405 .MLOAD,
   opAt 2406 (.Dup ⟨1,by decide⟩),
   opAt 2407 .ADD,
   opAt 2408 (.Dup ⟨0,by decide⟩),
   pushAt 2409 2 2080,
   opAt 2410 .MSTORE,
   opAt 2411 .LT,
   opAt 2412 .ISZERO,
   pushAt 2413 2 3061,
   opAt 2414 .JUMPI]

 
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2415 2 2080,
   opAt 2416 .MLOAD,
   opAt 2417 (.Dup ⟨0,by decide⟩),
   opAt 2418 .ISZERO,
   pushAt 2419 2 3042,
   opAt 2420 .JUMPI]

 
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2352 .JUMPDEST,
   opAt 2353 .NOT,
   opAt 2354 .ADD,
   opAt 2355 (.Dup ⟨0,by decide⟩),
   opAt 2356 (.Dup ⟨2,by decide⟩),
   opAt 2357 .JUMPI]


 

def blk3253x :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  []

 
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8408 2 2080,
   opAt 8409 .MLOAD,
   opAt 8410 .ADD,
   opAt 8411 .SUB,
   opAt 8412 (.Dup ⟨0,by decide⟩),
   pushAt 8413 4 3055,
   opAt 8414 .JUMPI,
   opAt 8415 (.Swap ⟨0,by decide⟩),
   opAt 8416 .POP]

 
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8417 .NOT,
   opAt 8418 .ADD,
   opAt 8419 (.Dup ⟨0,by decide⟩),
   opAt 8420 (.Dup ⟨2,by decide⟩),
   opAt 8421 .JUMPI]


theorem jumpDest4608 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2349 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1854 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1854 = 2349 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestBigC : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 207 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 134 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 134 = 207 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest4657 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2370 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1867 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1867 = 2370 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestNeg4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2284 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1812 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1812 = 2284 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestNegT : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2428 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1903 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1903 = 2428 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest4839 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2680 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2076 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2076 = 2680 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestHead4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10696 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8253 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 8253 = 10696 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5115 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3061 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2369 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2369 = 3061 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5121 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3067 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2373 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2373 = 3067 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestLazyStore : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3055 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2365 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2365 = 3055 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestUnc : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3055 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2365 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2365 = 3055 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5311 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3042 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2352 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2352 = 3042 := by
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
