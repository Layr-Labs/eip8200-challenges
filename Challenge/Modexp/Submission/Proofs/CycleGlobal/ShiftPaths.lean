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
  [opAt 1848 .JUMPDEST,
   opAt 1849 (.Dup ⟨0,by decide⟩),
   opAt 1850 (.Dup ⟨3,by decide⟩),
   opAt 1851 .XOR,
   pushAt 1852 1 207,
   opAt 1853 .JUMPI]

 
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1854 (.Dup ⟨0,by decide⟩),
   pushAt 1855 1 96,
   pushAt 1856 2 2112,
   opAt 1857 .CALLDATACOPY,
   pushAt 1858 2 2370,
   pushAt 1859 2 3472,
   opAt 1860 .JUMP]


 
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1866 (.Dup ⟨0,by decide⟩),
   pushAt 1867 1 128,
   opAt 1868 .EQ,
   pushAt 1869 2 2284,
   opAt 1870 .JUMPI]

 
def negS8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1871 1 224,
   opAt 1872 .MLOAD,
   pushAt 1873 0 0,
   opAt 1874 .SUB,
   pushAt 1875 2 1504,
   opAt 1876 .MSTORE]

 
def negN8a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1877 1 192,
   opAt 1878 .MLOAD,
   opAt 1879 .NOT,
   pushAt 1880 2 1472,
   opAt 1881 .MSTORE]

 
def negN8b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1882 1 160,
   opAt 1883 .MLOAD,
   opAt 1884 .NOT,
   pushAt 1885 2 1440,
   opAt 1886 .MSTORE]

 
def negN8c :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1887 1 128,
   opAt 1888 .MLOAD,
   opAt 1889 .NOT,
   pushAt 1890 2 1408,
   opAt 1891 .MSTORE]

 
def negN8d :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1892 1 96,
   opAt 1893 .MLOAD,
   opAt 1894 .NOT,
   pushAt 1895 2 1376,
   opAt 1896 .MSTORE]

 


 


 


 
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
  [opAt 1897 .JUMPDEST]

 
def blkNeg8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negS8 ++ negN8a ++ negN8b ++ negN8c ++ negN8d

 
def blkNeg4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negJ4 ++ negS4 ++ negJ4b

 
def blkNegT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1897 .JUMPDEST,
   pushAt 1898 1 64,
   opAt 1899 .MLOAD,
   opAt 1900 .NOT,
   pushAt 1901 2 1344,
   opAt 1902 .MSTORE,
   pushAt 1903 1 32,
   opAt 1904 .MLOAD,
   opAt 1905 .NOT,
   pushAt 1906 2 1312,
   opAt 1907 .MSTORE,
   pushAt 1908 0 0,
   opAt 1909 .MLOAD,
   opAt 1910 (.Dup ⟨0,by decide⟩),
   opAt 1911 .NOT,
   pushAt 1912 2 1280,
   opAt 1913 .MSTORE]


 
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1914 (.Dup ⟨0,by decide⟩),
   pushAt 1915 0 0,
   opAt 1916 .SUB,
   opAt 1917 (.Dup ⟨1,by decide⟩),
   opAt 1918 .AND]


 

def blk2919b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1920 (.Dup ⟨0,by decide⟩),
   pushAt 1921 2 1,
   opAt 1922 .ADD,
   pushAt 1923 2 1600,
   opAt 1924 .MSTORE,
   pushAt 1925 1 255,
   opAt 1926 .SUB,
   opAt 1927 (.Dup ⟨0,by decide⟩),
   pushAt 1928 2 1536,
   opAt 1929 .MSTORE,
   opAt 1930 .SHR,
   opAt 1931 (.Dup ⟨0,by decide⟩),
   pushAt 1932 2 1568,
   opAt 1933 .MSTORE,
   opAt 1934 (.Dup ⟨0,by decide⟩),
   opAt 1935 (.Dup ⟨0,by decide⟩),
   pushAt 1936 0 0,
   opAt 1937 .SUB,
   opAt 1938 .MOD,
   pushAt 1939 2 1632,
   opAt 1940 .MSTORE]

 
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1941 2 2752,
   opAt 1942 .MLOAD,
   opAt 1943 .MLOAD,
   opAt 1944 (.Dup ⟨0,by decide⟩),
   opAt 1945 (.Dup ⟨2,by decide⟩),
   opAt 1946 .MUL]

 
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1947 (.Dup ⟨0,by decide⟩),
   pushAt 1948 1 3,
   opAt 1949 .MUL,
   pushAt 1950 1 2,
   opAt 1951 .XOR,
   opAt 1952 (.Dup ⟨0,by decide⟩),
   opAt 1953 (.Dup ⟨2,by decide⟩),
   opAt 1954 .MUL,
   pushAt 1955 1 2,
   opAt 1956 .SUB,
   opAt 1957 .MUL,
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
   opAt 1983 (.Swap ⟨1,by decide⟩),
   opAt 1984 .MUL,
   pushAt 1985 1 2,
   opAt 1986 .SUB,
   opAt 1987 .MUL]

 

def blkNbTailHead : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1988 (.Dup ⟨0,by decide⟩),
   opAt 1989 (.Swap ⟨1,by decide⟩),
   opAt 1990 .MUL,
   pushAt 1991 2 1664,
   opAt 1992 .MSTORE,
   opAt 1993 .MUL,
   pushAt 1994 0 0,
   opAt 1995 .SUB,
   pushAt 1996 2 2720,
   opAt 1997 .MSTORE,
   pushAt 1998 2 2306,
   opAt 1999 (.Dup ⟨4,by decide⟩),
   pushAt 2000 1 1,
   opAt 2001 .XOR,
   pushAt 2002 2 2588,
   opAt 2003 .JUMPI]
def blkNbTailByte : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2004 2 2656,
   opAt 2005 .MLOAD,
   opAt 2006 .CALLDATALOAD,
   pushAt 2007 0 0,
   opAt 2008 .BYTE,
   pushAt 2009 1 3,
   opAt 2010 .EQ,
   pushAt 2011 2 1621,
   opAt 2012 .MUL,
   opAt 2013 .ADD]
def blkNbTailJoin : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2014 .JUMPDEST,
   pushAt 2015 1 32,
   opAt 2016 .MLOAD,
   pushAt 2017 1 128,
   opAt 2018 .SHR,
   pushAt 2019 2 1536,
   opAt 2020 .MLOAD,
   pushAt 2021 2 1568,
   opAt 2022 .MLOAD,
   pushAt 2023 2 1664,
   opAt 2024 .MLOAD,
   pushAt 2025 2 1632,
   opAt 2026 .MLOAD,
   pushAt 2027 2 1504,
   opAt 2028 .MLOAD,
   pushAt 2029 2 1472,
   opAt 2030 .MLOAD,
   pushAt 2031 2 1440,
   opAt 2032 .MLOAD,
   pushAt 2033 2 1408,
   opAt 2034 .MLOAD,
   pushAt 2035 2 1376,
   opAt 2036 .MLOAD,
   pushAt 2037 2 1344,
   opAt 2038 .MLOAD,
   pushAt 2039 2 1312,
   opAt 2040 .MLOAD,
   opAt 2041 (.Dup ⟨14,by decide⟩)]
def blkNbTail (esize : Nat) : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  blkNbTailHead ++ (if UInt256.ofNat esize = UInt256.ofNat 1 then blkNbTailByte else []) ++ blkNbTailJoin
theorem jumpDestNbJoin : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2588 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2014 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h

 

def blkZero8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2834 .JUMPDEST,
   pushAt 2835 2 256,
   pushAt 2836 2 2112,
   pushAt 2837 2 2080,
   opAt 2838 .MCOPY,
   pushAt 2839 2 2080,
   opAt 2840 .MLOAD,
   opAt 2841 (.Dup ⟨14,by decide⟩),
   pushAt 2842 2 2112,
   opAt 2843 .MLOAD,
   opAt 2844 (.Dup ⟨14,by decide⟩),
   opAt 2845 (.Dup ⟨0,by decide⟩),
   opAt 2846 (.Dup ⟨14,by decide⟩),
   opAt 2847 (.Dup ⟨5,by decide⟩),
   opAt 2848 .MULMOD,
   opAt 2849 (.Dup ⟨2,by decide⟩),
   opAt 2850 .ADDMOD,
   opAt 2851 (.Dup ⟨0,by decide⟩),
   opAt 2852 (.Swap ⟨1,by decide⟩),
   opAt 2853 .SUB,
   opAt 2854 (.Dup ⟨14,by decide⟩),
   opAt 2855 .MUL,
   opAt 2856 (.Swap ⟨1,by decide⟩),
   opAt 2857 (.Dup ⟨2,by decide⟩),
   pushAt 2858 1 128,
   opAt 2859 .SHR,
   opAt 2860 .MUL,
   opAt 2861 .GT,
   opAt 2862 (.Swap ⟨0,by decide⟩),
   opAt 2863 .SUB,
   pushAt 2864 2 2740,
   opAt 2865 .JUMP]

def blkZero4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2984 .JUMPDEST,
   pushAt 2985 1 128,
   pushAt 2986 2 2112,
   pushAt 2987 2 2080,
   opAt 2988 .MCOPY,
   pushAt 2989 2 2080,
   opAt 2990 .MLOAD,
   opAt 2991 (.Dup ⟨14,by decide⟩),
   pushAt 2992 2 2112,
   opAt 2993 .MLOAD,
   opAt 2994 (.Dup ⟨14,by decide⟩),
   opAt 2995 (.Dup ⟨0,by decide⟩),
   opAt 2996 (.Dup ⟨14,by decide⟩),
   opAt 2997 (.Dup ⟨5,by decide⟩),
   opAt 2998 .MULMOD,
   opAt 2999 (.Dup ⟨2,by decide⟩),
   opAt 3000 .ADDMOD,
   opAt 3001 (.Dup ⟨0,by decide⟩),
   opAt 3002 (.Swap ⟨1,by decide⟩),
   opAt 3003 .SUB,
   opAt 3004 (.Dup ⟨14,by decide⟩),
   opAt 3005 .MUL,
   opAt 3006 (.Swap ⟨1,by decide⟩),
   opAt 3007 (.Dup ⟨2,by decide⟩),
   pushAt 3008 1 128,
   opAt 3009 .SHR,
   opAt 3010 .MUL,
   opAt 3011 .GT,
   opAt 3012 (.Swap ⟨0,by decide⟩),
   opAt 3013 .SUB,
   pushAt 3014 2 10755,
   opAt 3015 .JUMP]

def blkEstimateSuffix8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2115 .JUMPDEST,
   pushAt 2116 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2117 (.Swap ⟨1,by decide⟩),
   opAt 2118 (.Dup ⟨14,by decide⟩),
   opAt 2119 .GT,
   opAt 2120 (.Dup ⟨2,by decide⟩),
   opAt 2121 .ADD,
   opAt 2122 .OR]

def blkEstimateSuffix4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8291 .JUMPDEST,
   pushAt 8292 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8293 (.Swap ⟨1,by decide⟩),
   opAt 8294 (.Dup ⟨14,by decide⟩),
   opAt 8295 .GT,
   opAt 8296 (.Dup ⟨2,by decide⟩),
   opAt 8297 .ADD,
   opAt 8298 .OR]

def blk3013 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2070 .JUMPDEST]

 
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2071 2 256,
   pushAt 2072 2 2112,
   pushAt 2073 2 2080,
   opAt 2074 .MCOPY]

 
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2075 2 2080,
   opAt 2076 .MLOAD,
   opAt 2077 (.Dup ⟨0,by decide⟩),
   opAt 2078 (.Dup ⟨14,by decide⟩),
   opAt 2079 .SHR,
   opAt 2080 (.Swap ⟨0,by decide⟩),
   pushAt 2081 2 1600,
   opAt 2082 .MLOAD,
   opAt 2083 .SHL,
   pushAt 2084 2 2112,
   opAt 2085 .MLOAD,
   opAt 2086 (.Dup ⟨15,by decide⟩),
   opAt 2087 .SHR,
   opAt 2088 .ADD,
   opAt 2089 (.Dup ⟨13,by decide⟩),
   opAt 2090 (.Dup ⟨0,by decide⟩),
   opAt 2091 (.Dup ⟨13,by decide⟩),
   opAt 2092 (.Dup ⟨4,by decide⟩),
   opAt 2093 .MULMOD,
   opAt 2094 (.Dup ⟨2,by decide⟩),
   opAt 2095 .ADDMOD,
   opAt 2096 (.Swap ⟨0,by decide⟩),
   opAt 2097 .SUB,
   opAt 2098 (.Dup ⟨12,by decide⟩),
   opAt 2099 .MUL,
   opAt 2100 (.Dup ⟨15,by decide⟩),
   opAt 2101 (.Dup ⟨1,by decide⟩),
   pushAt 2102 1 128,
   opAt 2103 .SHR,
   opAt 2104 .MUL,
   opAt 2105 (.Dup ⟨1,by decide⟩),
   pushAt 2106 0 0,
   opAt 2107 .MLOAD,
   opAt 2108 .MUL,
   pushAt 2109 2 2112,
   opAt 2110 .MLOAD,
   opAt 2111 .SUB,
   opAt 2112 .LT,
   opAt 2113 (.Swap ⟨0,by decide⟩),
   opAt 2114 .SUB,
   opAt 2115 .JUMPDEST,
   pushAt 2116 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2117 (.Swap ⟨1,by decide⟩),
   opAt 2118 (.Dup ⟨14,by decide⟩),
   opAt 2119 .GT,
   opAt 2120 (.Dup ⟨2,by decide⟩),
   opAt 2121 .ADD,
   opAt 2122 .OR]



def blk3013h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8246 .JUMPDEST]

 
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8247 1 128,
   pushAt 8248 2 2112,
   pushAt 8249 2 2080,
   opAt 8250 .MCOPY]

 
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8251 2 2080,
   opAt 8252 .MLOAD,
   opAt 8253 (.Dup ⟨0,by decide⟩),
   opAt 8254 (.Dup ⟨14,by decide⟩),
   opAt 8255 .SHR,
   opAt 8256 (.Swap ⟨0,by decide⟩),
   pushAt 8257 2 1600,
   opAt 8258 .MLOAD,
   opAt 8259 .SHL,
   pushAt 8260 2 2112,
   opAt 8261 .MLOAD,
   opAt 8262 (.Dup ⟨15,by decide⟩),
   opAt 8263 .SHR,
   opAt 8264 .ADD,
   opAt 8265 (.Dup ⟨13,by decide⟩),
   opAt 8266 (.Dup ⟨0,by decide⟩),
   opAt 8267 (.Dup ⟨13,by decide⟩),
   opAt 8268 (.Dup ⟨4,by decide⟩),
   opAt 8269 .MULMOD,
   opAt 8270 (.Dup ⟨2,by decide⟩),
   opAt 8271 .ADDMOD,
   opAt 8272 (.Swap ⟨0,by decide⟩),
   opAt 8273 .SUB,
   opAt 8274 (.Dup ⟨12,by decide⟩),
   opAt 8275 .MUL,
   opAt 8276 (.Dup ⟨15,by decide⟩),
   opAt 8277 (.Dup ⟨1,by decide⟩),
   pushAt 8278 1 128,
   opAt 8279 .SHR,
   opAt 8280 .MUL,
   opAt 8281 (.Dup ⟨1,by decide⟩),
   pushAt 8282 0 0,
   opAt 8283 .MLOAD,
   opAt 8284 .MUL,
   pushAt 8285 2 2112,
   opAt 8286 .MLOAD,
   opAt 8287 .SUB,
   opAt 8288 .LT,
   opAt 8289 (.Swap ⟨0,by decide⟩),
   opAt 8290 .SUB,
   opAt 8291 .JUMPDEST,
   pushAt 8292 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8293 (.Swap ⟨1,by decide⟩),
   opAt 8294 (.Dup ⟨14,by decide⟩),
   opAt 8295 .GT,
   opAt 8296 (.Dup ⟨2,by decide⟩),
   opAt 8297 .ADD,
   opAt 8298 .OR]



 




def blk3125Unc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2337 2 2080,
   opAt 2338 .MLOAD,
   opAt 2339 .ADD,
   opAt 2340 .SUB,
   opAt 2341 (.Dup ⟨0,by decide⟩),
   pushAt 2342 5 3055,
   opAt 2343 .JUMPI,
   opAt 2359 .JUMPDEST,
   pushAt 2360 2 2080,
   opAt 2361 .MSTORE]

def blk3125hUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8401 2 2080,
   opAt 8402 .MLOAD,
   opAt 8403 .ADD,
   opAt 8404 .SUB,
   opAt 8405 (.Dup ⟨0,by decide⟩),
   pushAt 8406 4 3055,
   opAt 8407 .JUMPI,
   opAt 2359 .JUMPDEST,
   pushAt 2360 2 2080,
   opAt 2361 .MSTORE]

def blk3125 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2337 2 2080,
   opAt 2338 .MLOAD,
   opAt 2339 .ADD,
   opAt 2340 .SUB,
   opAt 2341 (.Dup ⟨0,by decide⟩),
   pushAt 2342 5 3055,
   opAt 2343 .JUMPI,
   opAt 2344 (.Swap ⟨0,by decide⟩),
   opAt 2345 .POP]

 
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2362 .POP]

 
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2363 .JUMPDEST,
   pushAt 2364 0 0,
   pushAt 2365 2 2784,
   opAt 2366 .MLOAD]

 
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2367 .JUMPDEST,
   opAt 2368 (.Dup ⟨0,by decide⟩),
   opAt 2369 .MLOAD,
   pushAt 2370 2 2112,
   opAt 2371 (.Dup ⟨2,by decide⟩),
   opAt 2372 .SUB,
   opAt 2373 .MLOAD,
   opAt 2374 (.Dup ⟨1,by decide⟩),
   opAt 2375 .ADD,
   opAt 2376 (.Swap ⟨0,by decide⟩),
   opAt 2377 (.Dup ⟨1,by decide⟩),
   opAt 2378 .LT,
   opAt 2379 (.Swap ⟨0,by decide⟩),
   opAt 2380 (.Dup ⟨3,by decide⟩),
   opAt 2381 .ADD,
   opAt 2382 (.Swap ⟨2,by decide⟩),
   opAt 2383 (.Dup ⟨3,by decide⟩),
   opAt 2384 .LT,
   opAt 2385 .OR,
   opAt 2386 (.Swap ⟨1,by decide⟩),
   opAt 2387 (.Dup ⟨1,by decide⟩),
   opAt 2388 .MSTORE,
   pushAt 2389 1 31,
   opAt 2390 .NOT,
   opAt 2391 .ADD,
   pushAt 2392 2 2111,
   opAt 2393 (.Dup ⟨1,by decide⟩),
   opAt 2394 .GT,
   pushAt 2395 2 3067,
   opAt 2396 .JUMPI]

 
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2397 .POP,
   pushAt 2398 2 2080,
   opAt 2399 .MLOAD,
   opAt 2400 (.Dup ⟨1,by decide⟩),
   opAt 2401 .ADD,
   opAt 2402 (.Dup ⟨0,by decide⟩),
   pushAt 2403 2 2080,
   opAt 2404 .MSTORE,
   opAt 2405 .LT,
   opAt 2406 .ISZERO,
   pushAt 2407 2 3061,
   opAt 2408 .JUMPI]

 
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2409 2 2080,
   opAt 2410 .MLOAD,
   opAt 2411 (.Dup ⟨0,by decide⟩),
   opAt 2412 .ISZERO,
   pushAt 2413 2 3042,
   opAt 2414 .JUMPI]

 
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2346 .JUMPDEST,
   opAt 2347 .NOT,
   opAt 2348 .ADD,
   opAt 2349 (.Dup ⟨0,by decide⟩),
   opAt 2350 (.Dup ⟨2,by decide⟩),
   opAt 2351 .JUMPI]


 

def blk3253x :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  []

 
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8401 2 2080,
   opAt 8402 .MLOAD,
   opAt 8403 .ADD,
   opAt 8404 .SUB,
   opAt 8405 (.Dup ⟨0,by decide⟩),
   pushAt 8406 4 3055,
   opAt 8407 .JUMPI,
   opAt 8408 (.Swap ⟨0,by decide⟩),
   opAt 8409 .POP]

 
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8410 .NOT,
   opAt 8411 .ADD,
   opAt 8412 (.Dup ⟨0,by decide⟩),
   opAt 8413 (.Dup ⟨2,by decide⟩),
   opAt 8414 .JUMPI]


theorem jumpDest4608 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2349 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1848 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1848 = 2349 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestBigC : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 207 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 134 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 134 = 207 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest4657 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2370 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1861 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1861 = 2370 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestNeg4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2284 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1812 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1812 = 2284 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestNegT : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2428 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1897 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1897 = 2428 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest4839 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2680 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2070 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2070 = 2680 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestHead4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10696 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8246 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 8246 = 10696 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5115 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3061 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2363 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2363 = 3061 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5121 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3067 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2367 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2367 = 3067 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestLazyStore : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3055 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2359 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2359 = 3055 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestUnc : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3055 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2359 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2359 = 3055 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5311 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3042 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2346 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2346 = 3042 := by
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
