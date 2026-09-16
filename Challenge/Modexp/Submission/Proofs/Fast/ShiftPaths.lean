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
   -- the quotient-estimator saturation tail (`PUSH2 PRE_DODD; MLOAD; GT; ISZERO;
   -- PUSH0; SUB; OR`, which clamped a wrapping guess to `2^256 - 1`) is gone: the
   -- correction proof below accepts every UInt256 quotient, so the clamp only ever
   -- bought gas on the `r_top = m_top` path.  `SWAP1; POP` drops the spare `hi` and
   -- the `PUSH6` is inert filler holding the block at its original ten bytes, so
   -- every later pc is exactly where it was.
   opAt 1961 .POP,
   pushAt 1962 6 2207646876162,
   opAt 1963 .POP]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `TN` alone
(`neg ≠ 0` already forces `TN ≠ 0`, so the old `neg ||| TN` was redundant). -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2216 2 2080,
   opAt 2217 .MLOAD,
   opAt 2218 (.Dup ⟨1, by decide⟩),
   opAt 2219 .ADD,
   opAt 2220 (.Dup ⟨0, by decide⟩),
   opAt 2221 (.Swap ⟨1, by decide⟩),
   opAt 2222 .GT,
   opAt 2223 (.Dup ⟨1, by decide⟩),
   opAt 2224 (.Dup ⟨3, by decide⟩),
   opAt 2225 .GT,
   opAt 2226 .GT,
   opAt 2227 (.Swap ⟨1, by decide⟩),
   opAt 2228 (.Swap ⟨0, by decide⟩),
   opAt 2229 .SUB,
   opAt 2230 (.Dup ⟨0, by decide⟩),
   pushAt 2231 2 2080,
   opAt 2232 .MSTORE,
   -- the `DUP2; OR` that widened the exit test to `neg ||| TN` is gone: `neg ≠ 0` already
   -- forces `TN ≠ 0` (see `ShiftTrace3.tn_ne_zero_of_neg`), so `TN` alone decides the branch
   -- and the two bytes are spent on `JUMPDEST`s, leaving every later pc where it was.
   opAt 2233 .JUMPDEST,
   opAt 2234 .JUMPDEST,
   pushAt 2235 2 3012,
   opAt 2236 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2243 .JUMPDEST,
   opAt 2244 .ISZERO,
   pushAt 2245 2 3097,
   opAt 2246 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2247 .JUMPDEST,
   pushAt 2248 0 0,
   pushAt 2249 2 2784,
   opAt 2250 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2251 .JUMPDEST,
   opAt 2252 (.Dup ⟨0, by decide⟩),
   opAt 2253 .MLOAD,
   pushAt 2254 3 2112,
   opAt 2255 (.Dup ⟨2, by decide⟩),
   opAt 2256 .SUB,
   opAt 2257 .MLOAD,
   opAt 2258 (.Dup ⟨1, by decide⟩),
   opAt 2259 .ADD,
   opAt 2260 (.Swap ⟨0, by decide⟩),
   opAt 2261 (.Dup ⟨1, by decide⟩),
   opAt 2262 .LT,
   opAt 2263 (.Swap ⟨0, by decide⟩),
   opAt 2264 (.Dup ⟨3, by decide⟩),
   opAt 2265 .ADD,
   opAt 2266 (.Swap ⟨2, by decide⟩),
   opAt 2267 (.Dup ⟨3, by decide⟩),
   opAt 2268 .LT,
   opAt 2269 .OR,
   opAt 2270 (.Swap ⟨1, by decide⟩),
   opAt 2271 (.Dup ⟨1, by decide⟩),
   opAt 2272 .MSTORE,
   pushAt 2273 1 31,
   opAt 2274 .NOT,
   opAt 2275 .ADD,
   pushAt 2276 2 2111,
   opAt 2277 (.Dup ⟨1, by decide⟩),
   opAt 2278 .GT,
   pushAt 2279 2 3024,
   opAt 2280 .JUMPI,
   opAt 2281 .JUMPDEST,
   opAt 2282 .JUMPDEST,
   opAt 2283 .JUMPDEST,
   opAt 2284 .JUMPDEST,
   opAt 2285 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2286 .POP,
   pushAt 2287 2 2080,
   opAt 2288 .MLOAD,
   opAt 2289 (.Dup ⟨1, by decide⟩),
   opAt 2290 .ADD,
   opAt 2291 (.Dup ⟨0, by decide⟩),
   pushAt 2292 2 2080,
   opAt 2293 .MSTORE,
   opAt 2294 .LT,
   opAt 2295 .ISZERO,
   pushAt 2296 2 3018,
   opAt 2297 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2298 .JUMPDEST,
   pushAt 2299 2 2080,
   opAt 2300 .MLOAD,
   opAt 2301 (.Dup ⟨0, by decide⟩),
   opAt 2302 .ISZERO,
   pushAt 2303 2 3002,
   opAt 2304 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2298 .JUMPDEST,
   pushAt 2299 2 2080,
   opAt 2300 .MLOAD,
   opAt 2301 (.Dup ⟨0, by decide⟩),
   opAt 2302 .ISZERO,
   pushAt 2303 2 3002,
   opAt 2304 .JUMPI,
   opAt 2305 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2306 .JUMPDEST,
   pushAt 2307 0 0,
   pushAt 2308 2 2784,
   opAt 2309 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2310 .JUMPDEST,
   opAt 2311 (.Dup ⟨0, by decide⟩),
   opAt 2312 .MLOAD,
   pushAt 2313 2 2112,
   opAt 2314 (.Dup ⟨2, by decide⟩),
   opAt 2315 .SUB,
   opAt 2316 .MLOAD,
   opAt 2317 (.Dup ⟨1, by decide⟩),
   opAt 2318 (.Dup ⟨1, by decide⟩),
   opAt 2319 .GT,
   opAt 2320 (.Swap ⟨1, by decide⟩),
   opAt 2321 .SUB,
   opAt 2322 (.Dup ⟨3, by decide⟩),
   opAt 2323 (.Dup ⟨1, by decide⟩),
   opAt 2324 .LT,
   opAt 2325 (.Swap ⟨0, by decide⟩),
   opAt 2326 (.Dup ⟨4, by decide⟩),
   opAt 2327 (.Swap ⟨0, by decide⟩),
   opAt 2328 .SUB,
   opAt 2329 (.Dup ⟨3, by decide⟩),
   opAt 2330 .MSTORE,
   opAt 2331 .OR,
   opAt 2332 (.Swap ⟨1, by decide⟩),
   opAt 2333 .POP,
   pushAt 2334 1 31,
   opAt 2335 .NOT,
   opAt 2336 .ADD,
   pushAt 2337 2 2111,
   opAt 2338 (.Dup ⟨1, by decide⟩),
   opAt 2339 .GT,
   pushAt 2340 2 3103,
   opAt 2341 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2342 .POP,
   pushAt 2343 2 2080,
   opAt 2344 .MLOAD,
   opAt 2345 .SUB,
   pushAt 2346 2 2080,
   opAt 2347 .MSTORE,
   pushAt 2348 2 3085,
   opAt 2349 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2237 .JUMPDEST,
   opAt 2238 .NOT,
   opAt 2239 .ADD,
   pushAt 2240 2 2573,
   pushAt 2241 2 4115,
   opAt 2242 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2370 (.Dup ⟨0, by decide⟩),
   pushAt 2371 2 2112,
   pushAt 2372 2 512,
   opAt 2373 .MCOPY,
   opAt 2374 (.Dup ⟨0, by decide⟩),
   pushAt 2375 2 1280,
   pushAt 2376 2 1024,
   opAt 2377 .MCOPY,
   pushAt 2378 2 2182,
   opAt 2379 .JUMP]

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
  Artifact.isValidJumpDest_index 2247 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3024 = true :=
  Artifact.isValidJumpDest_index 2251 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3085 = true :=
  Artifact.isValidJumpDest_index 2298 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3103 = true :=
  Artifact.isValidJumpDest_index 2310 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3012 = true :=
  Artifact.isValidJumpDest_index 2243 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3097 = true :=
  Artifact.isValidJumpDest_index 2306 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3002 = true :=
  Artifact.isValidJumpDest_index 2237 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3156 = true :=
  Artifact.isValidJumpDest_index 2350 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
