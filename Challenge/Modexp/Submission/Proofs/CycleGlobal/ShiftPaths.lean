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
  [opAt 1846 .JUMPDEST,
   opAt 1847 (.Dup ⟨0,by decide⟩),
   opAt 1848 (.Dup ⟨3,by decide⟩),
   opAt 1849 .XOR,
   pushAt 1850 1 207,
   opAt 1851 .JUMPI]

 
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1852 (.Dup ⟨0,by decide⟩),
   pushAt 1853 1 96,
   pushAt 1854 2 2112,
   opAt 1855 .CALLDATACOPY,
   pushAt 1856 2 2359,
   pushAt 1857 2 3363,
   opAt 1858 .JUMP]


 
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1864 (.Dup ⟨0,by decide⟩),
   pushAt 1865 1 128,
   opAt 1866 .EQ,
   pushAt 1867 2 2284,
   opAt 1868 .JUMPI]

 
def negS8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1869 1 224,
   opAt 1870 .MLOAD,
   pushAt 1871 0 0,
   opAt 1872 .SUB,
   pushAt 1873 2 1504,
   opAt 1874 .MSTORE]

 
def negN8a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1875 1 192,
   opAt 1876 .MLOAD,
   opAt 1877 .NOT,
   pushAt 1878 2 1472,
   opAt 1879 .MSTORE]

 
def negN8b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1880 1 160,
   opAt 1881 .MLOAD,
   opAt 1882 .NOT,
   pushAt 1883 2 1440,
   opAt 1884 .MSTORE]

 
def negN8c :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1885 1 128,
   opAt 1886 .MLOAD,
   opAt 1887 .NOT,
   pushAt 1888 2 1408,
   opAt 1889 .MSTORE]

 
def negN8d :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1890 1 96,
   opAt 1891 .MLOAD,
   opAt 1892 .NOT,
   pushAt 1893 2 1376,
   opAt 1894 .MSTORE]

 


 


 


 
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
  [pushAt 1819 2 2417,
   opAt 1820 .JUMP]

 
def negJT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1895 .JUMPDEST]

 
def blkNeg8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negS8 ++ negN8a ++ negN8b ++ negN8c ++ negN8d

 
def blkNeg4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negJ4 ++ negS4 ++ negJ4b

 
def blkNegT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1895 .JUMPDEST,
   pushAt 1896 1 64,
   opAt 1897 .MLOAD,
   opAt 1898 .NOT,
   pushAt 1899 2 1344,
   opAt 1900 .MSTORE,
   pushAt 1901 1 32,
   opAt 1902 .MLOAD,
   opAt 1903 .NOT,
   pushAt 1904 2 1312,
   opAt 1905 .MSTORE,
   pushAt 1906 0 0,
   opAt 1907 .MLOAD,
   opAt 1908 (.Dup ⟨0,by decide⟩),
   opAt 1909 .NOT,
   pushAt 1910 2 1280,
   opAt 1911 .MSTORE]


 
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1912 (.Dup ⟨0,by decide⟩),
   pushAt 1913 0 0,
   opAt 1914 .SUB,
   opAt 1915 (.Dup ⟨1,by decide⟩),
   opAt 1916 .AND]


 

def blk2919b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1918 (.Dup ⟨0,by decide⟩),
   pushAt 1919 1 1,
   opAt 1920 .ADD,
   pushAt 1921 2 1600,
   opAt 1922 .MSTORE,
   pushAt 1923 1 255,
   opAt 1924 .SUB,
   opAt 1925 (.Dup ⟨0,by decide⟩),
   pushAt 1926 2 1536,
   opAt 1927 .MSTORE,
   opAt 1928 .SHR,
   opAt 1929 (.Dup ⟨0,by decide⟩),
   pushAt 1930 2 1568,
   opAt 1931 .MSTORE,
   opAt 1932 (.Dup ⟨0,by decide⟩),
   opAt 1933 (.Dup ⟨0,by decide⟩),
   pushAt 1934 0 0,
   opAt 1935 .SUB,
   opAt 1936 .MOD,
   pushAt 1937 2 1632,
   opAt 1938 .MSTORE]

 
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1939 2 2752,
   opAt 1940 .MLOAD,
   opAt 1941 .MLOAD,
   opAt 1942 (.Dup ⟨0,by decide⟩),
   opAt 1943 (.Dup ⟨2,by decide⟩),
   opAt 1944 .MUL]

 
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1945 (.Dup ⟨0,by decide⟩),
   pushAt 1946 1 3,
   opAt 1947 .MUL,
   pushAt 1948 1 2,
   opAt 1949 .XOR,
   opAt 1950 (.Dup ⟨0,by decide⟩),
   opAt 1951 (.Dup ⟨2,by decide⟩),
   opAt 1952 .MUL,
   pushAt 1953 1 2,
   opAt 1954 .SUB,
   opAt 1955 .MUL,
   opAt 1956 (.Dup ⟨0,by decide⟩),
   opAt 1957 (.Dup ⟨2,by decide⟩),
   opAt 1958 .MUL,
   pushAt 1959 1 2,
   opAt 1960 .SUB,
   opAt 1961 .MUL,
   opAt 1962 (.Dup ⟨0,by decide⟩),
   opAt 1963 (.Dup ⟨2,by decide⟩),
   opAt 1964 .MUL,
   pushAt 1965 1 2,
   opAt 1966 .SUB,
   opAt 1967 .MUL,
   opAt 1968 (.Dup ⟨0,by decide⟩),
   opAt 1969 (.Dup ⟨2,by decide⟩),
   opAt 1970 .MUL,
   pushAt 1971 1 2,
   opAt 1972 .SUB,
   opAt 1973 .MUL,
   opAt 1974 (.Dup ⟨0,by decide⟩),
   opAt 1975 (.Dup ⟨2,by decide⟩),
   opAt 1976 .MUL,
   pushAt 1977 1 2,
   opAt 1978 .SUB,
   opAt 1979 .MUL,
   opAt 1980 (.Dup ⟨0,by decide⟩),
   opAt 1981 (.Swap ⟨1,by decide⟩),
   opAt 1982 .MUL,
   pushAt 1983 1 2,
   opAt 1984 .SUB,
   opAt 1985 .MUL]

 

def blkNbTailHead : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1986 (.Dup ⟨0,by decide⟩),
   opAt 1987 (.Swap ⟨1,by decide⟩),
   opAt 1988 .MUL,
   pushAt 1989 2 1664,
   opAt 1990 .MSTORE,
   opAt 1991 .MUL,
   pushAt 1992 0 0,
   opAt 1993 .SUB,
   pushAt 1994 2 2720,
   opAt 1995 .MSTORE,
   pushAt 1996 2 2306,
   opAt 1997 (.Dup ⟨4,by decide⟩),
   pushAt 1998 1 1,
   opAt 1999 .XOR,
   pushAt 2000 2 2576,
   opAt 2001 .JUMPI]
def blkNbTailByte : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2002 2 2656,
   opAt 2003 .MLOAD,
   opAt 2004 .CALLDATALOAD,
   pushAt 2005 0 0,
   opAt 2006 .BYTE,
   pushAt 2007 1 3,
   opAt 2008 .EQ,
   pushAt 2009 2 1497,
   opAt 2010 .MUL,
   opAt 2011 .ADD]
def blkNbTailJoin : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2012 .JUMPDEST,
   pushAt 2013 1 32,
   opAt 2014 .MLOAD,
   pushAt 2015 1 128,
   opAt 2016 .SHR,
   pushAt 2017 2 1536,
   opAt 2018 .MLOAD,
   pushAt 2019 2 1568,
   opAt 2020 .MLOAD,
   pushAt 2021 2 1664,
   opAt 2022 .MLOAD,
   pushAt 2023 2 1632,
   opAt 2024 .MLOAD,
   pushAt 2025 2 1504,
   opAt 2026 .MLOAD,
   pushAt 2027 2 1472,
   opAt 2028 .MLOAD,
   pushAt 2029 2 1440,
   opAt 2030 .MLOAD,
   pushAt 2031 2 1408,
   opAt 2032 .MLOAD,
   pushAt 2033 2 1376,
   opAt 2034 .MLOAD,
   pushAt 2035 2 1344,
   opAt 2036 .MLOAD,
   pushAt 2037 2 1312,
   opAt 2038 .MLOAD,
   opAt 2039 (.Dup ⟨14,by decide⟩)]
def blkNbTail (esize : Nat) : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  blkNbTailHead ++ (if UInt256.ofNat esize = UInt256.ofNat 1 then blkNbTailByte else []) ++ blkNbTailJoin
theorem jumpDestNbJoin : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2576 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2012 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h

 

def blkZero8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2803 .JUMPDEST,
   opAt 2804 (.Dup ⟨15,by decide⟩),
   pushAt 2805 2 2112,
   pushAt 2806 2 2080,
   opAt 2807 .MCOPY,
   pushAt 2808 2 2080,
   opAt 2809 .MLOAD,
   opAt 2810 (.Dup ⟨14,by decide⟩),
   pushAt 2811 2 2112,
   opAt 2812 .MLOAD,
   opAt 2813 (.Dup ⟨14,by decide⟩),
   opAt 2814 (.Dup ⟨0,by decide⟩),
   opAt 2815 (.Dup ⟨14,by decide⟩),
   opAt 2816 (.Dup ⟨5,by decide⟩),
   opAt 2817 .MULMOD,
   opAt 2818 (.Dup ⟨2,by decide⟩),
   opAt 2819 .ADDMOD,
   opAt 2820 (.Dup ⟨0,by decide⟩),
   opAt 2821 (.Swap ⟨1,by decide⟩),
   opAt 2822 .SUB,
   opAt 2823 (.Dup ⟨14,by decide⟩),
   opAt 2824 .MUL,
   opAt 2825 (.Swap ⟨1,by decide⟩),
   opAt 2826 (.Dup ⟨2,by decide⟩),
   pushAt 2827 1 128,
   opAt 2828 .SHR,
   opAt 2829 .MUL,
   opAt 2830 .GT,
   opAt 2831 (.Swap ⟨0,by decide⟩),
   opAt 2832 .SUB,
   pushAt 2833 2 2725,
   opAt 2834 .JUMP]

def blkZero4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2949 .JUMPDEST,
   opAt 2950 (.Dup ⟨15,by decide⟩),
   pushAt 2951 2 2112,
   pushAt 2952 2 2080,
   opAt 2953 .MCOPY,
   pushAt 2954 2 2080,
   opAt 2955 .MLOAD,
   opAt 2956 (.Dup ⟨14,by decide⟩),
   pushAt 2957 2 2112,
   opAt 2958 .MLOAD,
   opAt 2959 (.Dup ⟨14,by decide⟩),
   opAt 2960 (.Dup ⟨0,by decide⟩),
   opAt 2961 (.Dup ⟨14,by decide⟩),
   opAt 2962 (.Dup ⟨5,by decide⟩),
   opAt 2963 .MULMOD,
   opAt 2964 (.Dup ⟨2,by decide⟩),
   opAt 2965 .ADDMOD,
   opAt 2966 (.Dup ⟨0,by decide⟩),
   opAt 2967 (.Swap ⟨1,by decide⟩),
   opAt 2968 .SUB,
   opAt 2969 (.Dup ⟨14,by decide⟩),
   opAt 2970 .MUL,
   opAt 2971 (.Swap ⟨1,by decide⟩),
   opAt 2972 (.Dup ⟨2,by decide⟩),
   pushAt 2973 1 128,
   opAt 2974 .SHR,
   opAt 2975 .MUL,
   opAt 2976 .GT,
   opAt 2977 (.Swap ⟨0,by decide⟩),
   opAt 2978 .SUB,
   pushAt 2979 2 10741,
   opAt 2980 .JUMP]

def blkEstimateSuffix8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2113 .JUMPDEST,
   pushAt 2114 0 0,
   opAt 2115 .NOT,
   opAt 2116 (.Swap ⟨1,by decide⟩),
   opAt 2117 (.Dup ⟨14,by decide⟩),
   opAt 2118 .GT,
   opAt 2119 (.Dup ⟨2,by decide⟩),
   opAt 2120 .ADD,
   opAt 2121 .OR]

def blkEstimateSuffix4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8268 .JUMPDEST,
   pushAt 8269 0 0,
   opAt 8270 .NOT,
   opAt 8271 (.Swap ⟨1,by decide⟩),
   opAt 8272 (.Dup ⟨14,by decide⟩),
   opAt 8273 .GT,
   opAt 8274 (.Dup ⟨2,by decide⟩),
   opAt 8275 .ADD,
   opAt 8276 .OR]

def blk3013 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2068 .JUMPDEST]

 
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2069 (.Dup ⟨15,by decide⟩),
   pushAt 2070 2 2112,
   pushAt 2071 2 2080,
   opAt 2072 .MCOPY]

 
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2073 2 2080,
   opAt 2074 .MLOAD,
   opAt 2075 (.Dup ⟨0,by decide⟩),
   opAt 2076 (.Dup ⟨14,by decide⟩),
   opAt 2077 .SHR,
   opAt 2078 (.Swap ⟨0,by decide⟩),
   pushAt 2079 2 1600,
   opAt 2080 .MLOAD,
   opAt 2081 .SHL,
   pushAt 2082 2 2112,
   opAt 2083 .MLOAD,
   opAt 2084 (.Dup ⟨15,by decide⟩),
   opAt 2085 .SHR,
   opAt 2086 .ADD,
   opAt 2087 (.Dup ⟨13,by decide⟩),
   opAt 2088 (.Dup ⟨0,by decide⟩),
   opAt 2089 (.Dup ⟨13,by decide⟩),
   opAt 2090 (.Dup ⟨4,by decide⟩),
   opAt 2091 .MULMOD,
   opAt 2092 (.Dup ⟨2,by decide⟩),
   opAt 2093 .ADDMOD,
   opAt 2094 (.Swap ⟨0,by decide⟩),
   opAt 2095 .SUB,
   opAt 2096 (.Dup ⟨12,by decide⟩),
   opAt 2097 .MUL,
   opAt 2098 (.Dup ⟨15,by decide⟩),
   opAt 2099 (.Dup ⟨1,by decide⟩),
   pushAt 2100 1 128,
   opAt 2101 .SHR,
   opAt 2102 .MUL,
   opAt 2103 (.Dup ⟨1,by decide⟩),
   pushAt 2104 0 0,
   opAt 2105 .MLOAD,
   opAt 2106 .MUL,
   pushAt 2107 2 2112,
   opAt 2108 .MLOAD,
   opAt 2109 .SUB,
   opAt 2110 .LT,
   opAt 2111 (.Swap ⟨0,by decide⟩),
   opAt 2112 .SUB,
   opAt 2113 .JUMPDEST,
   pushAt 2114 0 0,
   opAt 2115 .NOT,
   opAt 2116 (.Swap ⟨1,by decide⟩),
   opAt 2117 (.Dup ⟨14,by decide⟩),
   opAt 2118 .GT,
   opAt 2119 (.Dup ⟨2,by decide⟩),
   opAt 2120 .ADD,
   opAt 2121 .OR]



def blk3013h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8223 .JUMPDEST]

 
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8224 (.Dup ⟨15,by decide⟩),
   pushAt 8225 2 2112,
   pushAt 8226 2 2080,
   opAt 8227 .MCOPY]

 
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8228 2 2080,
   opAt 8229 .MLOAD,
   opAt 8230 (.Dup ⟨0,by decide⟩),
   opAt 8231 (.Dup ⟨14,by decide⟩),
   opAt 8232 .SHR,
   opAt 8233 (.Swap ⟨0,by decide⟩),
   pushAt 8234 2 1600,
   opAt 8235 .MLOAD,
   opAt 8236 .SHL,
   pushAt 8237 2 2112,
   opAt 8238 .MLOAD,
   opAt 8239 (.Dup ⟨15,by decide⟩),
   opAt 8240 .SHR,
   opAt 8241 .ADD,
   opAt 8242 (.Dup ⟨13,by decide⟩),
   opAt 8243 (.Dup ⟨0,by decide⟩),
   opAt 8244 (.Dup ⟨13,by decide⟩),
   opAt 8245 (.Dup ⟨4,by decide⟩),
   opAt 8246 .MULMOD,
   opAt 8247 (.Dup ⟨2,by decide⟩),
   opAt 8248 .ADDMOD,
   opAt 8249 (.Swap ⟨0,by decide⟩),
   opAt 8250 .SUB,
   opAt 8251 (.Dup ⟨12,by decide⟩),
   opAt 8252 .MUL,
   opAt 8253 (.Dup ⟨15,by decide⟩),
   opAt 8254 (.Dup ⟨1,by decide⟩),
   pushAt 8255 1 128,
   opAt 8256 .SHR,
   opAt 8257 .MUL,
   opAt 8258 (.Dup ⟨1,by decide⟩),
   pushAt 8259 0 0,
   opAt 8260 .MLOAD,
   opAt 8261 .MUL,
   pushAt 8262 2 2112,
   opAt 8263 .MLOAD,
   opAt 8264 .SUB,
   opAt 8265 .LT,
   opAt 8266 (.Swap ⟨0,by decide⟩),
   opAt 8267 .SUB,
   opAt 8268 .JUMPDEST,
   pushAt 8269 0 0,
   opAt 8270 .NOT,
   opAt 8271 (.Swap ⟨1,by decide⟩),
   opAt 8272 (.Dup ⟨14,by decide⟩),
   opAt 8273 .GT,
   opAt 8274 (.Dup ⟨2,by decide⟩),
   opAt 8275 .ADD,
   opAt 8276 .OR]



 




def blk3125Unc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2336 2 2080,
   opAt 2337 .MLOAD,
   opAt 2338 .ADD,
   opAt 2339 .SUB,
   opAt 2340 (.Dup ⟨0,by decide⟩),
   pushAt 2341 2 3002,
   opAt 2342 .JUMPI,
   opAt 2354 .JUMPDEST,
   pushAt 2355 2 2080,
   opAt 2356 .MSTORE]

def blk3125hUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8379 2 2080,
   opAt 8380 .MLOAD,
   opAt 8381 .ADD,
   opAt 8382 .SUB,
   opAt 8383 (.Dup ⟨0,by decide⟩),
   pushAt 8384 2 3002,
   opAt 8385 .JUMPI,
   opAt 2354 .JUMPDEST,
   pushAt 2355 2 2080,
   opAt 2356 .MSTORE]

def blk3125 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2336 2 2080,
   opAt 2337 .MLOAD,
   opAt 2338 .ADD,
   opAt 2339 .SUB,
   opAt 2340 (.Dup ⟨0,by decide⟩),
   pushAt 2341 2 3002,
   opAt 2342 .JUMPI,
   opAt 2343 (.Swap ⟨0,by decide⟩),
   opAt 2344 .POP]

 
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2357 .POP]

 
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2358 .JUMPDEST,
   pushAt 2359 0 0,
   pushAt 2360 2 2784,
   opAt 2361 .MLOAD]

 
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2362 .JUMPDEST,
   opAt 2363 (.Dup ⟨0,by decide⟩),
   opAt 2364 .MLOAD,
   pushAt 2365 2 2112,
   opAt 2366 (.Dup ⟨2,by decide⟩),
   opAt 2367 .SUB,
   opAt 2368 .MLOAD,
   opAt 2369 (.Dup ⟨1,by decide⟩),
   opAt 2370 .ADD,
   opAt 2371 (.Swap ⟨0,by decide⟩),
   opAt 2372 (.Dup ⟨1,by decide⟩),
   opAt 2373 .LT,
   opAt 2374 (.Swap ⟨0,by decide⟩),
   opAt 2375 (.Dup ⟨3,by decide⟩),
   opAt 2376 .ADD,
   opAt 2377 (.Swap ⟨2,by decide⟩),
   opAt 2378 (.Dup ⟨3,by decide⟩),
   opAt 2379 .LT,
   opAt 2380 .OR,
   opAt 2381 (.Swap ⟨1,by decide⟩),
   opAt 2382 (.Dup ⟨1,by decide⟩),
   opAt 2383 .MSTORE,
   pushAt 2384 1 31,
   opAt 2385 .NOT,
   opAt 2386 .ADD,
   pushAt 2387 2 2111,
   opAt 2388 (.Dup ⟨1,by decide⟩),
   opAt 2389 .GT,
   pushAt 2390 2 3014,
   opAt 2391 .JUMPI]

 
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2392 .POP,
   pushAt 2393 2 2080,
   opAt 2394 .MLOAD,
   opAt 2395 (.Dup ⟨1,by decide⟩),
   opAt 2396 .ADD,
   opAt 2397 (.Dup ⟨0,by decide⟩),
   pushAt 2398 2 2080,
   opAt 2399 .MSTORE,
   opAt 2400 .LT,
   opAt 2401 .ISZERO,
   pushAt 2402 2 3008,
   opAt 2403 .JUMPI]

 
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2404 2 2080,
   opAt 2405 .MLOAD,
   opAt 2406 (.Dup ⟨0,by decide⟩),
   opAt 2407 .ISZERO,
   pushAt 2408 2 2993,
   opAt 2409 .JUMPI]

 
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
  [pushAt 8379 2 2080,
   opAt 8380 .MLOAD,
   opAt 8381 .ADD,
   opAt 8382 .SUB,
   opAt 8383 (.Dup ⟨0,by decide⟩),
   pushAt 8384 2 3002,
   opAt 8385 .JUMPI,
   opAt 8386 (.Swap ⟨0,by decide⟩),
   opAt 8387 .POP]

 
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8388 .NOT,
   opAt 8389 .ADD,
   opAt 8390 (.Dup ⟨0,by decide⟩),
   opAt 8391 (.Dup ⟨2,by decide⟩),
   opAt 8392 .JUMPI]


theorem jumpDest4608 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2338 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1846 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1846 = 2338 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestBigC : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 207 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 134 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 134 = 207 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest4657 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2359 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1859 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1859 = 2359 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestNeg4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2284 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1812 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1812 = 2284 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestNegT : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2417 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1895 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1895 = 2417 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest4839 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2667 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2068 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2068 = 2667 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestHead4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10683 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8223 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 8223 = 10683 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5115 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3008 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2358 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2358 = 3008 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5121 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3014 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2362 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2362 = 3014 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestLazyStore : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3002 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2354 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2354 = 3002 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestUnc : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3002 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2354 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2354 = 3002 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5311 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2993 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2345 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2345 = 2993 := by
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
