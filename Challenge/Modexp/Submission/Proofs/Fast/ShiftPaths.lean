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
  [opAt 1732 .JUMPDEST,
   opAt 1733 (.Dup ⟨0, by decide⟩),
   opAt 1734 (.Dup ⟨3, by decide⟩),
   opAt 1735 .EQ,
   pushAt 1736 0 0,
   opAt 1737 .MLOAD,
   pushAt 1738 1 255,
   opAt 1739 .SHR,
   opAt 1740 .AND,
   opAt 1741 .ISZERO,
   pushAt 1742 2 2373,
   opAt 1743 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1744 (.Dup ⟨0, by decide⟩),
   pushAt 1745 1 96,
   pushAt 1746 2 2112,
   opAt 1747 .CALLDATACOPY,
   pushAt 1748 0 0,
   pushAt 1749 2 2080,
   opAt 1750 .MSTORE,
   pushAt 1751 2 2390,
   pushAt 1752 2 4115,
   opAt 1753 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1754 .JUMPDEST,
   pushAt 1755 1 1,
   pushAt 1756 2 1024,
   opAt 1757 .MSTORE,
   pushAt 1758 2 782,
   pushAt 1759 2 1024,
   pushAt 1760 2 1278,
   opAt 1761 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1767 1 1,
   pushAt 1768 2 2752,
   opAt 1769 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1791 .POP,
   opAt 1792 .POP,
   pushAt 1793 0 0,
   opAt 1794 .MLOAD,
   opAt 1795 (.Dup ⟨0, by decide⟩),
   pushAt 1796 0 0,
   opAt 1797 .SUB,
   opAt 1798 (.Dup ⟨1, by decide⟩),
   opAt 1799 .AND,
   opAt 1800 (.Dup ⟨0, by decide⟩),
   pushAt 1801 2 1536,
   opAt 1802 .MSTORE,
   opAt 1803 (.Dup ⟨0, by decide⟩),
   opAt 1804 (.Dup ⟨2, by decide⟩),
   opAt 1805 .DIV,
   opAt 1806 (.Dup ⟨0, by decide⟩),
   pushAt 1807 2 1568,
   opAt 1808 .MSTORE,
   opAt 1809 (.Dup ⟨1, by decide⟩),
   opAt 1810 (.Dup ⟨0, by decide⟩),
   pushAt 1811 0 0,
   opAt 1812 .SUB,
   opAt 1813 .DIV,
   pushAt 1814 1 1,
   opAt 1815 .ADD,
   pushAt 1816 2 1600,
   opAt 1817 .MSTORE,
   opAt 1818 (.Dup ⟨0, by decide⟩),
   opAt 1819 (.Dup ⟨0, by decide⟩),
   pushAt 1820 0 0,
   opAt 1821 .SUB,
   opAt 1822 .MOD,
   pushAt 1823 2 1632,
   opAt 1824 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1825 (.Dup ⟨0, by decide⟩),
   pushAt 1826 1 3,
   opAt 1827 .MUL,
   pushAt 1828 1 2,
   opAt 1829 .XOR,
   opAt 1830 (.Dup ⟨0, by decide⟩),
   opAt 1831 (.Dup ⟨2, by decide⟩),
   opAt 1832 .MUL,
   pushAt 1833 1 2,
   opAt 1834 .SUB,
   opAt 1835 .MUL,
   opAt 1836 (.Dup ⟨0, by decide⟩),
   opAt 1837 (.Dup ⟨2, by decide⟩),
   opAt 1838 .MUL,
   pushAt 1839 1 2,
   opAt 1840 .SUB,
   opAt 1841 .MUL,
   opAt 1842 (.Dup ⟨0, by decide⟩),
   opAt 1843 (.Dup ⟨2, by decide⟩),
   opAt 1844 .MUL,
   pushAt 1845 1 2,
   opAt 1846 .SUB,
   opAt 1847 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1848 (.Dup ⟨0, by decide⟩),
   opAt 1849 (.Dup ⟨2, by decide⟩),
   opAt 1850 .MUL,
   pushAt 1851 1 2,
   opAt 1852 .SUB,
   opAt 1853 .MUL,
   opAt 1854 (.Dup ⟨0, by decide⟩),
   opAt 1855 (.Dup ⟨2, by decide⟩),
   opAt 1856 .MUL,
   pushAt 1857 1 2,
   opAt 1858 .SUB,
   opAt 1859 .MUL,
   opAt 1860 (.Dup ⟨0, by decide⟩),
   opAt 1861 (.Dup ⟨2, by decide⟩),
   opAt 1862 .MUL,
   pushAt 1863 1 2,
   opAt 1864 .SUB,
   opAt 1865 .MUL,
   pushAt 1866 2 1664,
   opAt 1867 .MSTORE,
   opAt 1868 .POP,
   opAt 1869 .POP,
   opAt 1870 .POP,
   opAt 1871 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1901 .JUMPDEST,
   opAt 1902 (.Dup ⟨0, by decide⟩),
   opAt 1903 .ISZERO,
   pushAt 1904 2 3156,
   opAt 1905 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1906 (.Dup ⟨1, by decide⟩),
   pushAt 1907 2 2112,
   pushAt 1908 2 2080,
   opAt 1909 .MCOPY,
   pushAt 1910 0 0,
   pushAt 1911 2 2784,
   opAt 1912 .MLOAD,
   opAt 1913 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1914 2 2080,
   opAt 1915 .MLOAD,
   pushAt 1916 2 1536,
   opAt 1917 .MLOAD,
   opAt 1918 (.Dup ⟨1, by decide⟩),
   opAt 1919 .DIV,
   opAt 1920 (.Swap ⟨0, by decide⟩),
   pushAt 1921 2 1600,
   opAt 1922 .MLOAD,
   opAt 1923 .MUL,
   pushAt 1924 2 1536,
   opAt 1925 .MLOAD,
   pushAt 1926 2 2112,
   opAt 1927 .MLOAD,
   opAt 1928 .DIV,
   opAt 1929 .ADD,
   pushAt 1930 2 1568,
   opAt 1931 .MLOAD,
   opAt 1932 (.Dup ⟨0, by decide⟩),
   pushAt 1933 2 1632,
   opAt 1934 .MLOAD,
   opAt 1935 (.Dup ⟨4, by decide⟩),
   opAt 1936 .MULMOD,
   opAt 1937 (.Dup ⟨2, by decide⟩),
   opAt 1938 .ADDMOD,
   opAt 1939 (.Swap ⟨0, by decide⟩),
   opAt 1940 .SUB,
   pushAt 1941 2 1664,
   opAt 1942 .MLOAD,
   opAt 1943 .MUL,
   opAt 1944 (.Dup ⟨0, by decide⟩),
   pushAt 1945 0 0,
   opAt 1946 .MLOAD,
   opAt 1947 .MUL,
   pushAt 1948 2 2112,
   opAt 1949 .MLOAD,
   opAt 1950 .SUB,
   pushAt 1951 1 32,
   opAt 1952 .MLOAD,
   pushAt 1953 1 128,
   opAt 1954 .SHR,
   opAt 1955 (.Dup ⟨2, by decide⟩),
   pushAt 1956 1 128,
   opAt 1957 .SHR,
   opAt 1958 .MUL,
   opAt 1959 .GT,
   opAt 1960 (.Swap ⟨0, by decide⟩),
   opAt 1961 .SUB,
   opAt 1962 (.Swap ⟨0, by decide⟩),
   pushAt 1963 2 1568,
   opAt 1964 .MLOAD,
   opAt 1965 .GT,
   opAt 1966 .ISZERO,
   pushAt 1967 0 0,
   opAt 1968 .SUB,
   opAt 1969 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks.
  --
  -- The exit test reads `TN` ALONE: the `DUP2; OR` that computed `neg ||| TN` is deleted and its
  -- two bytes are absorbed into the widened `PUSH4` below.  That is sound unconditionally, not
  -- merely on the corpus: `neg = GT bwOf cwOf` with both flags in `{0,1}`, so `neg != 0` forces
  -- `bwOf = 1`, i.e. `wN < q`; then `TN = wN - q` wraps to `2^256 - (q - wN)`, which is nonzero
  -- because `q < 2^256`.  So `neg != 0 -> TN != 0`, hence `neg ||| TN` and `TN` have the same
  -- truth value for every `wN`, `q`.  `tnOf_ne_zero_of_negOf` in ShiftTrace3 is that argument in
  -- Lean, and `run_mid_unc` discharges the exit condition through it.
  [pushAt 2222 2 2080,
   opAt 2223 .MLOAD,
   opAt 2224 (.Dup ⟨1, by decide⟩),
   opAt 2225 .ADD,
   opAt 2226 (.Dup ⟨0, by decide⟩),
   opAt 2227 (.Swap ⟨1, by decide⟩),
   opAt 2228 .GT,
   opAt 2229 (.Dup ⟨1, by decide⟩),
   opAt 2230 (.Dup ⟨3, by decide⟩),
   opAt 2231 .GT,
   opAt 2232 .GT,
   opAt 2233 (.Swap ⟨1, by decide⟩),
   opAt 2234 (.Swap ⟨0, by decide⟩),
   opAt 2235 .SUB,
   opAt 2236 (.Dup ⟨0, by decide⟩),
   pushAt 2237 2 2080,
   opAt 2238 .MSTORE,
   pushAt 2239 4 3012,
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
  Artifact.isValidJumpDest_index 1732 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2373 = true :=
  Artifact.isValidJumpDest_index 1754 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2390 = true :=
  Artifact.isValidJumpDest_index 1762 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2405 = true :=
  Artifact.isValidJumpDest_index 1770 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2573 = true :=
  Artifact.isValidJumpDest_index 1901 (by rfl)

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
