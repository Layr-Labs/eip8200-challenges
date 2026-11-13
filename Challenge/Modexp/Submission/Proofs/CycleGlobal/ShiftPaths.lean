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
  [opAt 1847 .JUMPDEST,
   opAt 1848 (.Dup ⟨0,by decide⟩),
   opAt 1849 (.Dup ⟨3,by decide⟩),
   opAt 1850 .XOR,
   pushAt 1851 1 207,
   opAt 1852 .JUMPI]

 
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1853 (.Dup ⟨0,by decide⟩),
   pushAt 1854 1 96,
   pushAt 1855 2 2112,
   opAt 1856 .CALLDATACOPY,
   pushAt 1857 2 2370,
   pushAt 1858 2 3472,
   opAt 1859 .JUMP]


 
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1865 (.Dup ⟨0,by decide⟩),
   pushAt 1866 1 128,
   opAt 1867 .EQ,
   pushAt 1868 2 2284,
   opAt 1869 .JUMPI]

 
def negS8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1870 1 224,
   opAt 1871 .MLOAD,
   pushAt 1872 0 0,
   opAt 1873 .SUB,
   pushAt 1874 2 1504,
   opAt 1875 .MSTORE]

 
def negN8a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1876 1 192,
   opAt 1877 .MLOAD,
   opAt 1878 .NOT,
   pushAt 1879 2 1472,
   opAt 1880 .MSTORE]

 
def negN8b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1881 1 160,
   opAt 1882 .MLOAD,
   opAt 1883 .NOT,
   pushAt 1884 2 1440,
   opAt 1885 .MSTORE]

 
def negN8c :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1886 1 128,
   opAt 1887 .MLOAD,
   opAt 1888 .NOT,
   pushAt 1889 2 1408,
   opAt 1890 .MSTORE]

 
def negN8d :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1891 1 96,
   opAt 1892 .MLOAD,
   opAt 1893 .NOT,
   pushAt 1894 2 1376,
   opAt 1895 .MSTORE]

 


 


 


 
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
  [opAt 1896 .JUMPDEST]

 
def blkNeg8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negS8 ++ negN8a ++ negN8b ++ negN8c ++ negN8d

 
def blkNeg4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negJ4 ++ negS4 ++ negJ4b

 
def blkNegT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1896 .JUMPDEST,
   pushAt 1897 1 64,
   opAt 1898 .MLOAD,
   opAt 1899 .NOT,
   pushAt 1900 2 1344,
   opAt 1901 .MSTORE,
   pushAt 1902 1 32,
   opAt 1903 .MLOAD,
   opAt 1904 .NOT,
   pushAt 1905 2 1312,
   opAt 1906 .MSTORE,
   pushAt 1907 0 0,
   opAt 1908 .MLOAD,
   opAt 1909 (.Dup ⟨0,by decide⟩),
   opAt 1910 .NOT,
   pushAt 1911 2 1280,
   opAt 1912 .MSTORE]


 
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1913 (.Dup ⟨0,by decide⟩),
   pushAt 1914 0 0,
   opAt 1915 .SUB,
   opAt 1916 (.Dup ⟨1,by decide⟩),
   opAt 1917 .AND]


 

def blk2919b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1919 (.Dup ⟨0,by decide⟩),
   pushAt 1920 2 1,
   opAt 1921 .ADD,
   pushAt 1922 2 1600,
   opAt 1923 .MSTORE,
   pushAt 1924 1 255,
   opAt 1925 .SUB,
   opAt 1926 (.Dup ⟨0,by decide⟩),
   pushAt 1927 2 1536,
   opAt 1928 .MSTORE,
   opAt 1929 .SHR,
   opAt 1930 (.Dup ⟨0,by decide⟩),
   pushAt 1931 2 1568,
   opAt 1932 .MSTORE,
   opAt 1933 (.Dup ⟨0,by decide⟩),
   opAt 1934 (.Dup ⟨0,by decide⟩),
   pushAt 1935 0 0,
   opAt 1936 .SUB,
   opAt 1937 .MOD,
   pushAt 1938 2 1632,
   opAt 1939 .MSTORE]

 
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1940 2 2752,
   opAt 1941 .MLOAD,
   opAt 1942 .MLOAD,
   opAt 1943 (.Dup ⟨0,by decide⟩),
   opAt 1944 (.Dup ⟨2,by decide⟩),
   opAt 1945 .MUL]

 
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1946 (.Dup ⟨0,by decide⟩),
   pushAt 1947 1 3,
   opAt 1948 .MUL,
   pushAt 1949 1 2,
   opAt 1950 .XOR,
   opAt 1951 (.Dup ⟨0,by decide⟩),
   opAt 1952 (.Dup ⟨2,by decide⟩),
   opAt 1953 .MUL,
   pushAt 1954 1 2,
   opAt 1955 .SUB,
   opAt 1956 .MUL,
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
   opAt 1982 (.Swap ⟨1,by decide⟩),
   opAt 1983 .MUL,
   pushAt 1984 1 2,
   opAt 1985 .SUB,
   opAt 1986 .MUL]

 

def blkNbTailHead : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1987 (.Dup ⟨0,by decide⟩),
   opAt 1988 (.Swap ⟨1,by decide⟩),
   opAt 1989 .MUL,
   pushAt 1990 2 1664,
   opAt 1991 .MSTORE,
   opAt 1992 .MUL,
   pushAt 1993 0 0,
   opAt 1994 .SUB,
   pushAt 1995 2 2720,
   opAt 1996 .MSTORE,
   pushAt 1997 2 2306,
   opAt 1998 (.Dup ⟨4,by decide⟩),
   pushAt 1999 1 1,
   opAt 2000 .XOR,
   pushAt 2001 2 2588,
   opAt 2002 .JUMPI]
def blkNbTailByte : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2003 2 2656,
   opAt 2004 .MLOAD,
   opAt 2005 .CALLDATALOAD,
   pushAt 2006 0 0,
   opAt 2007 .BYTE,
   pushAt 2008 1 3,
   opAt 2009 .EQ,
   pushAt 2010 2 1621,
   opAt 2011 .MUL,
   opAt 2012 .ADD]
def blkNbTailJoin : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2013 .JUMPDEST,
   pushAt 2014 1 32,
   opAt 2015 .MLOAD,
   pushAt 2016 1 128,
   opAt 2017 .SHR,
   pushAt 2018 2 1536,
   opAt 2019 .MLOAD,
   pushAt 2020 2 1568,
   opAt 2021 .MLOAD,
   pushAt 2022 2 1664,
   opAt 2023 .MLOAD,
   pushAt 2024 2 1632,
   opAt 2025 .MLOAD,
   pushAt 2026 2 1504,
   opAt 2027 .MLOAD,
   pushAt 2028 2 1472,
   opAt 2029 .MLOAD,
   pushAt 2030 2 1440,
   opAt 2031 .MLOAD,
   pushAt 2032 2 1408,
   opAt 2033 .MLOAD,
   pushAt 2034 2 1376,
   opAt 2035 .MLOAD,
   pushAt 2036 2 1344,
   opAt 2037 .MLOAD,
   pushAt 2038 2 1312,
   opAt 2039 .MLOAD,
   opAt 2040 (.Dup ⟨14,by decide⟩)]
def blkNbTail (esize : Nat) : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  blkNbTailHead ++ (if UInt256.ofNat esize = UInt256.ofNat 1 then blkNbTailByte else []) ++ blkNbTailJoin
theorem jumpDestNbJoin : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2588 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2013 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h

 

def blkZero8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2833 .JUMPDEST,
   pushAt 2834 2 256,
   pushAt 2835 2 2112,
   pushAt 2836 2 2080,
   opAt 2837 .MCOPY,
   pushAt 2838 2 2080,
   opAt 2839 .MLOAD,
   opAt 2840 (.Dup ⟨14,by decide⟩),
   pushAt 2841 2 2112,
   opAt 2842 .MLOAD,
   opAt 2843 (.Dup ⟨14,by decide⟩),
   opAt 2844 (.Dup ⟨0,by decide⟩),
   opAt 2845 (.Dup ⟨14,by decide⟩),
   opAt 2846 (.Dup ⟨5,by decide⟩),
   opAt 2847 .MULMOD,
   opAt 2848 (.Dup ⟨2,by decide⟩),
   opAt 2849 .ADDMOD,
   opAt 2850 (.Dup ⟨0,by decide⟩),
   opAt 2851 (.Swap ⟨1,by decide⟩),
   opAt 2852 .SUB,
   opAt 2853 (.Dup ⟨14,by decide⟩),
   opAt 2854 .MUL,
   opAt 2855 (.Swap ⟨1,by decide⟩),
   opAt 2856 (.Dup ⟨2,by decide⟩),
   pushAt 2857 1 128,
   opAt 2858 .SHR,
   opAt 2859 .MUL,
   opAt 2860 .GT,
   opAt 2861 (.Swap ⟨0,by decide⟩),
   opAt 2862 .SUB,
   pushAt 2863 2 2740,
   opAt 2864 .JUMP]

def blkZero4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2983 .JUMPDEST,
   pushAt 2984 1 128,
   pushAt 2985 2 2112,
   pushAt 2986 2 2080,
   opAt 2987 .MCOPY,
   pushAt 2988 2 2080,
   opAt 2989 .MLOAD,
   opAt 2990 (.Dup ⟨14,by decide⟩),
   pushAt 2991 2 2112,
   opAt 2992 .MLOAD,
   opAt 2993 (.Dup ⟨14,by decide⟩),
   opAt 2994 (.Dup ⟨0,by decide⟩),
   opAt 2995 (.Dup ⟨14,by decide⟩),
   opAt 2996 (.Dup ⟨5,by decide⟩),
   opAt 2997 .MULMOD,
   opAt 2998 (.Dup ⟨2,by decide⟩),
   opAt 2999 .ADDMOD,
   opAt 3000 (.Dup ⟨0,by decide⟩),
   opAt 3001 (.Swap ⟨1,by decide⟩),
   opAt 3002 .SUB,
   opAt 3003 (.Dup ⟨14,by decide⟩),
   opAt 3004 .MUL,
   opAt 3005 (.Swap ⟨1,by decide⟩),
   opAt 3006 (.Dup ⟨2,by decide⟩),
   pushAt 3007 1 128,
   opAt 3008 .SHR,
   opAt 3009 .MUL,
   opAt 3010 .GT,
   opAt 3011 (.Swap ⟨0,by decide⟩),
   opAt 3012 .SUB,
   pushAt 3013 2 10755,
   opAt 3014 .JUMP]

def blkEstimateSuffix8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2114 .JUMPDEST,
   pushAt 2115 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2116 (.Swap ⟨1,by decide⟩),
   opAt 2117 (.Dup ⟨14,by decide⟩),
   opAt 2118 .GT,
   opAt 2119 (.Dup ⟨2,by decide⟩),
   opAt 2120 .ADD,
   opAt 2121 .OR]

def blkEstimateSuffix4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8290 .JUMPDEST,
   pushAt 8291 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8292 (.Swap ⟨1,by decide⟩),
   opAt 8293 (.Dup ⟨14,by decide⟩),
   opAt 8294 .GT,
   opAt 8295 (.Dup ⟨2,by decide⟩),
   opAt 8296 .ADD,
   opAt 8297 .OR]

def blk3013 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2069 .JUMPDEST]

 
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2070 2 256,
   pushAt 2071 2 2112,
   pushAt 2072 2 2080,
   opAt 2073 .MCOPY]

 
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2074 2 2080,
   opAt 2075 .MLOAD,
   opAt 2076 (.Dup ⟨0,by decide⟩),
   opAt 2077 (.Dup ⟨14,by decide⟩),
   opAt 2078 .SHR,
   opAt 2079 (.Swap ⟨0,by decide⟩),
   pushAt 2080 2 1600,
   opAt 2081 .MLOAD,
   opAt 2082 .SHL,
   pushAt 2083 2 2112,
   opAt 2084 .MLOAD,
   opAt 2085 (.Dup ⟨15,by decide⟩),
   opAt 2086 .SHR,
   opAt 2087 .ADD,
   opAt 2088 (.Dup ⟨13,by decide⟩),
   opAt 2089 (.Dup ⟨0,by decide⟩),
   opAt 2090 (.Dup ⟨13,by decide⟩),
   opAt 2091 (.Dup ⟨4,by decide⟩),
   opAt 2092 .MULMOD,
   opAt 2093 (.Dup ⟨2,by decide⟩),
   opAt 2094 .ADDMOD,
   opAt 2095 (.Swap ⟨0,by decide⟩),
   opAt 2096 .SUB,
   opAt 2097 (.Dup ⟨12,by decide⟩),
   opAt 2098 .MUL,
   opAt 2099 (.Dup ⟨15,by decide⟩),
   opAt 2100 (.Dup ⟨1,by decide⟩),
   pushAt 2101 1 128,
   opAt 2102 .SHR,
   opAt 2103 .MUL,
   opAt 2104 (.Dup ⟨1,by decide⟩),
   pushAt 2105 0 0,
   opAt 2106 .MLOAD,
   opAt 2107 .MUL,
   pushAt 2108 2 2112,
   opAt 2109 .MLOAD,
   opAt 2110 .SUB,
   opAt 2111 .LT,
   opAt 2112 (.Swap ⟨0,by decide⟩),
   opAt 2113 .SUB,
   opAt 2114 .JUMPDEST,
   pushAt 2115 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2116 (.Swap ⟨1,by decide⟩),
   opAt 2117 (.Dup ⟨14,by decide⟩),
   opAt 2118 .GT,
   opAt 2119 (.Dup ⟨2,by decide⟩),
   opAt 2120 .ADD,
   opAt 2121 .OR]



def blk3013h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8245 .JUMPDEST]

 
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8246 1 128,
   pushAt 8247 2 2112,
   pushAt 8248 2 2080,
   opAt 8249 .MCOPY]

 
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8250 2 2080,
   opAt 8251 .MLOAD,
   opAt 8252 (.Dup ⟨0,by decide⟩),
   opAt 8253 (.Dup ⟨14,by decide⟩),
   opAt 8254 .SHR,
   opAt 8255 (.Swap ⟨0,by decide⟩),
   pushAt 8256 2 1600,
   opAt 8257 .MLOAD,
   opAt 8258 .SHL,
   pushAt 8259 2 2112,
   opAt 8260 .MLOAD,
   opAt 8261 (.Dup ⟨15,by decide⟩),
   opAt 8262 .SHR,
   opAt 8263 .ADD,
   opAt 8264 (.Dup ⟨13,by decide⟩),
   opAt 8265 (.Dup ⟨0,by decide⟩),
   opAt 8266 (.Dup ⟨13,by decide⟩),
   opAt 8267 (.Dup ⟨4,by decide⟩),
   opAt 8268 .MULMOD,
   opAt 8269 (.Dup ⟨2,by decide⟩),
   opAt 8270 .ADDMOD,
   opAt 8271 (.Swap ⟨0,by decide⟩),
   opAt 8272 .SUB,
   opAt 8273 (.Dup ⟨12,by decide⟩),
   opAt 8274 .MUL,
   opAt 8275 (.Dup ⟨15,by decide⟩),
   opAt 8276 (.Dup ⟨1,by decide⟩),
   pushAt 8277 1 128,
   opAt 8278 .SHR,
   opAt 8279 .MUL,
   opAt 8280 (.Dup ⟨1,by decide⟩),
   pushAt 8281 0 0,
   opAt 8282 .MLOAD,
   opAt 8283 .MUL,
   pushAt 8284 2 2112,
   opAt 8285 .MLOAD,
   opAt 8286 .SUB,
   opAt 8287 .LT,
   opAt 8288 (.Swap ⟨0,by decide⟩),
   opAt 8289 .SUB,
   opAt 8290 .JUMPDEST,
   pushAt 8291 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8292 (.Swap ⟨1,by decide⟩),
   opAt 8293 (.Dup ⟨14,by decide⟩),
   opAt 8294 .GT,
   opAt 8295 (.Dup ⟨2,by decide⟩),
   opAt 8296 .ADD,
   opAt 8297 .OR]



 




def blk3125Unc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2336 2 2080,
   opAt 2337 .MLOAD,
   opAt 2338 .ADD,
   opAt 2339 .SUB,
   opAt 2340 (.Dup ⟨0,by decide⟩),
   pushAt 2341 5 3055,
   opAt 2342 .JUMPI,
   opAt 2358 .JUMPDEST,
   pushAt 2359 2 2080,
   opAt 2360 .MSTORE]

def blk3125hUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8400 2 2080,
   opAt 8401 .MLOAD,
   opAt 8402 .ADD,
   opAt 8403 .SUB,
   opAt 8404 (.Dup ⟨0,by decide⟩),
   pushAt 8405 4 3055,
   opAt 8406 .JUMPI,
   opAt 2358 .JUMPDEST,
   pushAt 2359 2 2080,
   opAt 2360 .MSTORE]

def blk3125 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2336 2 2080,
   opAt 2337 .MLOAD,
   opAt 2338 .ADD,
   opAt 2339 .SUB,
   opAt 2340 (.Dup ⟨0,by decide⟩),
   pushAt 2341 5 3055,
   opAt 2342 .JUMPI,
   opAt 2343 (.Swap ⟨0,by decide⟩),
   opAt 2344 .POP]

 
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2361 .POP]

 
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2362 .JUMPDEST,
   pushAt 2363 0 0,
   pushAt 2364 2 2784,
   opAt 2365 .MLOAD]

 
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2366 .JUMPDEST,
   opAt 2367 (.Dup ⟨0,by decide⟩),
   opAt 2368 .MLOAD,
   pushAt 2369 2 2112,
   opAt 2370 (.Dup ⟨2,by decide⟩),
   opAt 2371 .SUB,
   opAt 2372 .MLOAD,
   opAt 2373 (.Dup ⟨1,by decide⟩),
   opAt 2374 .ADD,
   opAt 2375 (.Swap ⟨0,by decide⟩),
   opAt 2376 (.Dup ⟨1,by decide⟩),
   opAt 2377 .LT,
   opAt 2378 (.Swap ⟨0,by decide⟩),
   opAt 2379 (.Dup ⟨3,by decide⟩),
   opAt 2380 .ADD,
   opAt 2381 (.Swap ⟨2,by decide⟩),
   opAt 2382 (.Dup ⟨3,by decide⟩),
   opAt 2383 .LT,
   opAt 2384 .OR,
   opAt 2385 (.Swap ⟨1,by decide⟩),
   opAt 2386 (.Dup ⟨1,by decide⟩),
   opAt 2387 .MSTORE,
   pushAt 2388 1 31,
   opAt 2389 .NOT,
   opAt 2390 .ADD,
   pushAt 2391 2 2111,
   opAt 2392 (.Dup ⟨1,by decide⟩),
   opAt 2393 .GT,
   pushAt 2394 2 3067,
   opAt 2395 .JUMPI]

 
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2396 .POP,
   pushAt 2397 2 2080,
   opAt 2398 .MLOAD,
   opAt 2399 (.Dup ⟨1,by decide⟩),
   opAt 2400 .ADD,
   opAt 2401 (.Dup ⟨0,by decide⟩),
   pushAt 2402 2 2080,
   opAt 2403 .MSTORE,
   opAt 2404 .LT,
   opAt 2405 .ISZERO,
   pushAt 2406 2 3061,
   opAt 2407 .JUMPI]

 
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2408 2 2080,
   opAt 2409 .MLOAD,
   opAt 2410 (.Dup ⟨0,by decide⟩),
   opAt 2411 .ISZERO,
   pushAt 2412 2 3042,
   opAt 2413 .JUMPI]

 
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2345 .JUMPDEST,
   opAt 2346 .NOT,
   opAt 2347 .ADD,
   opAt 2348 (.Dup ⟨0,by decide⟩),
   opAt 2349 (.Dup ⟨2,by decide⟩),
   opAt 2350 .JUMPI]


 

def blk3253x :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  []

 
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8400 2 2080,
   opAt 8401 .MLOAD,
   opAt 8402 .ADD,
   opAt 8403 .SUB,
   opAt 8404 (.Dup ⟨0,by decide⟩),
   pushAt 8405 4 3055,
   opAt 8406 .JUMPI,
   opAt 8407 (.Swap ⟨0,by decide⟩),
   opAt 8408 .POP]

 
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8409 .NOT,
   opAt 8410 .ADD,
   opAt 8411 (.Dup ⟨0,by decide⟩),
   opAt 8412 (.Dup ⟨2,by decide⟩),
   opAt 8413 .JUMPI]


theorem jumpDest4608 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2349 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1847 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1847 = 2349 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestBigC : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 207 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 134 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 134 = 207 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest4657 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2370 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1860 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1860 = 2370 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestNeg4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2284 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1812 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1812 = 2284 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestNegT : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2428 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1896 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1896 = 2428 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest4839 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2680 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2069 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2069 = 2680 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestHead4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10696 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8245 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 8245 = 10696 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5115 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3061 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2362 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2362 = 3061 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5121 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3067 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2366 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2366 = 3067 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestLazyStore : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3055 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2358 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2358 = 3055 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestUnc : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3055 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2358 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2358 = 3055 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5311 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3042 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2345 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2345 = 3042 := by
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
