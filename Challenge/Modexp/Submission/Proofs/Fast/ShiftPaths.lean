import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the appended shift-reduce base conversion (generated). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Located block of the selected shift-reduce program. -/
def blk2862 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1730 .JUMPDEST,
   opAt 1731 (.Dup ⟨0, by decide⟩),
   opAt 1732 (.Dup ⟨3, by decide⟩),
   opAt 1733 .EQ,
   pushAt 1734 0 0,
   opAt 1735 .MLOAD,
   pushAt 1736 1 255,
   opAt 1737 .SHR,
   opAt 1738 .AND,
   opAt 1739 .ISZERO,
   pushAt 1740 2 2373,
   opAt 1741 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1742 (.Dup ⟨0, by decide⟩),
   pushAt 1743 1 96,
   pushAt 1744 2 2112,
   opAt 1745 .CALLDATACOPY,
   pushAt 1746 0 0,
   pushAt 1747 2 2080,
   opAt 1748 .MSTORE,
   pushAt 1749 2 2390,
   pushAt 1750 2 4115,
   opAt 1751 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1752 .JUMPDEST,
   pushAt 1753 1 1,
   pushAt 1754 2 1024,
   opAt 1755 .MSTORE,
   pushAt 1756 2 782,
   pushAt 1757 2 1024,
   pushAt 1758 2 1278,
   opAt 1759 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1765 1 1,
   pushAt 1766 2 2752,
   opAt 1767 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1789 .POP,
   opAt 1790 .POP,
   pushAt 1791 0 0,
   opAt 1792 .MLOAD,
   opAt 1793 (.Dup ⟨0, by decide⟩),
   pushAt 1794 0 0,
   opAt 1795 .SUB,
   opAt 1796 (.Dup ⟨1, by decide⟩),
   opAt 1797 .AND,
   opAt 1798 (.Dup ⟨0, by decide⟩),
   pushAt 1799 2 1536,
   opAt 1800 .MSTORE,
   opAt 1801 (.Dup ⟨0, by decide⟩),
   opAt 1802 (.Dup ⟨2, by decide⟩),
   opAt 1803 .DIV,
   opAt 1804 (.Dup ⟨0, by decide⟩),
   pushAt 1805 2 1568,
   opAt 1806 .MSTORE,
   opAt 1807 (.Dup ⟨1, by decide⟩),
   opAt 1808 (.Dup ⟨0, by decide⟩),
   pushAt 1809 0 0,
   opAt 1810 .SUB,
   opAt 1811 .DIV,
   pushAt 1812 1 1,
   opAt 1813 .ADD,
   pushAt 1814 2 1600,
   opAt 1815 .MSTORE,
   opAt 1816 (.Dup ⟨0, by decide⟩),
   opAt 1817 (.Dup ⟨0, by decide⟩),
   pushAt 1818 0 0,
   opAt 1819 .SUB,
   opAt 1820 .MOD,
   pushAt 1821 2 1632,
   opAt 1822 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1823 (.Dup ⟨0, by decide⟩),
   pushAt 1824 1 3,
   opAt 1825 .MUL,
   pushAt 1826 1 2,
   opAt 1827 .XOR,
   opAt 1828 (.Dup ⟨0, by decide⟩),
   opAt 1829 (.Dup ⟨2, by decide⟩),
   opAt 1830 .MUL,
   pushAt 1831 1 2,
   opAt 1832 .SUB,
   opAt 1833 .MUL,
   opAt 1834 (.Dup ⟨0, by decide⟩),
   opAt 1835 (.Dup ⟨2, by decide⟩),
   opAt 1836 .MUL,
   pushAt 1837 1 2,
   opAt 1838 .SUB,
   opAt 1839 .MUL,
   opAt 1840 (.Dup ⟨0, by decide⟩),
   opAt 1841 (.Dup ⟨2, by decide⟩),
   opAt 1842 .MUL,
   pushAt 1843 1 2,
   opAt 1844 .SUB,
   opAt 1845 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1846 (.Dup ⟨0, by decide⟩),
   opAt 1847 (.Dup ⟨2, by decide⟩),
   opAt 1848 .MUL,
   pushAt 1849 1 2,
   opAt 1850 .SUB,
   opAt 1851 .MUL,
   opAt 1852 (.Dup ⟨0, by decide⟩),
   opAt 1853 (.Dup ⟨2, by decide⟩),
   opAt 1854 .MUL,
   pushAt 1855 1 2,
   opAt 1856 .SUB,
   opAt 1857 .MUL,
   opAt 1858 (.Dup ⟨0, by decide⟩),
   opAt 1859 (.Dup ⟨2, by decide⟩),
   opAt 1860 .MUL,
   pushAt 1861 1 2,
   opAt 1862 .SUB,
   opAt 1863 .MUL,
   pushAt 1864 2 1664,
   opAt 1865 .MSTORE,
   opAt 1866 .POP,
   opAt 1867 .POP,
   opAt 1868 .POP,
   opAt 1869 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1899 .JUMPDEST,
   opAt 1900 (.Dup ⟨0, by decide⟩),
   opAt 1901 .ISZERO,
   pushAt 1902 2 3156,
   opAt 1903 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1904 (.Dup ⟨1, by decide⟩),
   pushAt 1905 2 2112,
   pushAt 1906 2 2080,
   opAt 1907 .MCOPY,
   pushAt 1908 0 0,
   pushAt 1909 2 2784,
   opAt 1910 .MLOAD,
   opAt 1911 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1912 2 2080,
   opAt 1913 .MLOAD,
   pushAt 1914 2 1536,
   opAt 1915 .MLOAD,
   opAt 1916 (.Dup ⟨1, by decide⟩),
   opAt 1917 .DIV,
   opAt 1918 (.Swap ⟨0, by decide⟩),
   pushAt 1919 2 1600,
   opAt 1920 .MLOAD,
   opAt 1921 .MUL,
   pushAt 1922 2 1536,
   opAt 1923 .MLOAD,
   pushAt 1924 2 2112,
   opAt 1925 .MLOAD,
   opAt 1926 .DIV,
   opAt 1927 .ADD,
   pushAt 1928 2 1568,
   opAt 1929 .MLOAD,
   opAt 1930 (.Dup ⟨0, by decide⟩),
   pushAt 1931 2 1632,
   opAt 1932 .MLOAD,
   opAt 1933 (.Dup ⟨4, by decide⟩),
   opAt 1934 .MULMOD,
   opAt 1935 (.Dup ⟨2, by decide⟩),
   opAt 1936 .ADDMOD,
   opAt 1937 (.Swap ⟨0, by decide⟩),
   opAt 1938 .SUB,
   pushAt 1939 2 1664,
   opAt 1940 .MLOAD,
   opAt 1941 .MUL,
   opAt 1942 (.Dup ⟨0, by decide⟩),
   pushAt 1943 0 0,
   opAt 1944 .MLOAD,
   opAt 1945 .MUL,
   pushAt 1946 2 2112,
   opAt 1947 .MLOAD,
   opAt 1948 .SUB,
   pushAt 1949 1 32,
   opAt 1950 .MLOAD,
   pushAt 1951 1 128,
   opAt 1952 .SHR,
   opAt 1953 (.Dup ⟨2, by decide⟩),
   pushAt 1954 1 128,
   opAt 1955 .SHR,
   opAt 1956 .MUL,
   opAt 1957 .GT,
   opAt 1958 (.Swap ⟨0, by decide⟩),
   opAt 1959 .SUB,
   opAt 1960 (.Swap ⟨0, by decide⟩),
   pushAt 1961 2 1568,
   opAt 1962 .MLOAD,
   opAt 1963 .GT,
   opAt 1964 .ISZERO,
   pushAt 1965 0 0,
   opAt 1966 .SUB,
   opAt 1967 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `TN` alone
(`neg ≠ 0` already forces `TN ≠ 0`, so the old `neg ||| TN` was redundant). -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2220 2 2080,
   opAt 2221 .MLOAD,
   opAt 2222 (.Dup ⟨1, by decide⟩),
   opAt 2223 .ADD,
   opAt 2224 (.Dup ⟨0, by decide⟩),
   opAt 2225 (.Swap ⟨1, by decide⟩),
   opAt 2226 .GT,
   opAt 2227 (.Dup ⟨1, by decide⟩),
   opAt 2228 (.Dup ⟨3, by decide⟩),
   opAt 2229 .GT,
   opAt 2230 .GT,
   opAt 2231 (.Swap ⟨1, by decide⟩),
   opAt 2232 (.Swap ⟨0, by decide⟩),
   opAt 2233 .SUB,
   opAt 2234 (.Dup ⟨0, by decide⟩),
   pushAt 2235 2 2080,
   opAt 2236 .MSTORE,
   -- the `DUP2; OR` that widened the exit test to `neg ||| TN` is gone: `neg ≠ 0` already
   -- forces `TN ≠ 0` (see `ShiftTrace3.tn_ne_zero_of_neg`), so `TN` alone decides the branch
   -- and the two bytes are spent on `JUMPDEST`s, leaving every later pc where it was.
   opAt 2237 .JUMPDEST,
   opAt 2238 .JUMPDEST,
   pushAt 2239 2 3012,
   opAt 2240 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2247 .JUMPDEST,
   opAt 2248 .ISZERO,
   pushAt 2249 2 3097,
   opAt 2250 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2251 .JUMPDEST,
   pushAt 2252 0 0,
   pushAt 2253 2 2784,
   opAt 2254 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2255 .JUMPDEST,
   opAt 2256 (.Dup ⟨0, by decide⟩),
   opAt 2257 .MLOAD,
   pushAt 2258 3 2112,
   opAt 2259 (.Dup ⟨2, by decide⟩),
   opAt 2260 .SUB,
   opAt 2261 .MLOAD,
   opAt 2262 (.Dup ⟨1, by decide⟩),
   opAt 2263 .ADD,
   opAt 2264 (.Swap ⟨0, by decide⟩),
   opAt 2265 (.Dup ⟨1, by decide⟩),
   opAt 2266 .LT,
   opAt 2267 (.Swap ⟨0, by decide⟩),
   opAt 2268 (.Dup ⟨3, by decide⟩),
   opAt 2269 .ADD,
   opAt 2270 (.Swap ⟨2, by decide⟩),
   opAt 2271 (.Dup ⟨3, by decide⟩),
   opAt 2272 .LT,
   opAt 2273 .OR,
   opAt 2274 (.Swap ⟨1, by decide⟩),
   opAt 2275 (.Dup ⟨1, by decide⟩),
   opAt 2276 .MSTORE,
   pushAt 2277 1 31,
   opAt 2278 .NOT,
   opAt 2279 .ADD,
   pushAt 2280 2 2111,
   opAt 2281 (.Dup ⟨1, by decide⟩),
   opAt 2282 .GT,
   pushAt 2283 2 3024,
   opAt 2284 .JUMPI,
   opAt 2285 .JUMPDEST,
   opAt 2286 .JUMPDEST,
   opAt 2287 .JUMPDEST,
   opAt 2288 .JUMPDEST,
   opAt 2289 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2290 .POP,
   pushAt 2291 2 2080,
   opAt 2292 .MLOAD,
   opAt 2293 (.Dup ⟨1, by decide⟩),
   opAt 2294 .ADD,
   opAt 2295 (.Dup ⟨0, by decide⟩),
   pushAt 2296 2 2080,
   opAt 2297 .MSTORE,
   opAt 2298 .LT,
   opAt 2299 .ISZERO,
   pushAt 2300 2 3018,
   opAt 2301 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2302 .JUMPDEST,
   pushAt 2303 2 2080,
   opAt 2304 .MLOAD,
   opAt 2305 (.Dup ⟨0, by decide⟩),
   opAt 2306 .ISZERO,
   pushAt 2307 2 3002,
   opAt 2308 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2302 .JUMPDEST,
   pushAt 2303 2 2080,
   opAt 2304 .MLOAD,
   opAt 2305 (.Dup ⟨0, by decide⟩),
   opAt 2306 .ISZERO,
   pushAt 2307 2 3002,
   opAt 2308 .JUMPI,
   opAt 2309 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2310 .JUMPDEST,
   pushAt 2311 0 0,
   pushAt 2312 2 2784,
   opAt 2313 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2314 .JUMPDEST,
   opAt 2315 (.Dup ⟨0, by decide⟩),
   opAt 2316 .MLOAD,
   pushAt 2317 2 2112,
   opAt 2318 (.Dup ⟨2, by decide⟩),
   opAt 2319 .SUB,
   opAt 2320 .MLOAD,
   opAt 2321 (.Dup ⟨1, by decide⟩),
   opAt 2322 (.Dup ⟨1, by decide⟩),
   opAt 2323 .GT,
   opAt 2324 (.Swap ⟨1, by decide⟩),
   opAt 2325 .SUB,
   opAt 2326 (.Dup ⟨3, by decide⟩),
   opAt 2327 (.Dup ⟨1, by decide⟩),
   opAt 2328 .LT,
   opAt 2329 (.Swap ⟨0, by decide⟩),
   opAt 2330 (.Dup ⟨4, by decide⟩),
   opAt 2331 (.Swap ⟨0, by decide⟩),
   opAt 2332 .SUB,
   opAt 2333 (.Dup ⟨3, by decide⟩),
   opAt 2334 .MSTORE,
   opAt 2335 .OR,
   opAt 2336 (.Swap ⟨1, by decide⟩),
   opAt 2337 .POP,
   pushAt 2338 1 31,
   opAt 2339 .NOT,
   opAt 2340 .ADD,
   pushAt 2341 2 2111,
   opAt 2342 (.Dup ⟨1, by decide⟩),
   opAt 2343 .GT,
   pushAt 2344 2 3103,
   opAt 2345 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2346 .POP,
   pushAt 2347 2 2080,
   opAt 2348 .MLOAD,
   opAt 2349 .SUB,
   pushAt 2350 2 2080,
   opAt 2351 .MSTORE,
   pushAt 2352 2 3085,
   opAt 2353 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2241 .JUMPDEST,
   opAt 2242 .NOT,
   opAt 2243 .ADD,
   pushAt 2244 2 2573,
   pushAt 2245 2 4115,
   opAt 2246 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2374 (.Dup ⟨0, by decide⟩),
   pushAt 2375 2 2112,
   pushAt 2376 2 512,
   opAt 2377 .MCOPY,
   opAt 2378 (.Dup ⟨0, by decide⟩),
   pushAt 2379 2 1280,
   pushAt 2380 2 1024,
   opAt 2381 .MCOPY,
   pushAt 2382 2 2182,
   opAt 2383 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2339 = true :=
  Artifact.isValidJumpDest_index 1730 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2373 = true :=
  Artifact.isValidJumpDest_index 1752 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2390 = true :=
  Artifact.isValidJumpDest_index 1760 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2405 = true :=
  Artifact.isValidJumpDest_index 1768 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2573 = true :=
  Artifact.isValidJumpDest_index 1899 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3018 = true :=
  Artifact.isValidJumpDest_index 2251 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3024 = true :=
  Artifact.isValidJumpDest_index 2255 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3085 = true :=
  Artifact.isValidJumpDest_index 2302 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3103 = true :=
  Artifact.isValidJumpDest_index 2314 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3012 = true :=
  Artifact.isValidJumpDest_index 2247 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3097 = true :=
  Artifact.isValidJumpDest_index 2310 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3002 = true :=
  Artifact.isValidJumpDest_index 2241 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3156 = true :=
  Artifact.isValidJumpDest_index 2354 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
