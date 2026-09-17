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
  [opAt 1728 .JUMPDEST,
   opAt 1729 (.Dup ⟨0, by decide⟩),
   opAt 1730 (.Dup ⟨3, by decide⟩),
   opAt 1731 .EQ,
   pushAt 1732 0 0,
   opAt 1733 .MLOAD,
   pushAt 1734 1 255,
   opAt 1735 .SHR,
   opAt 1736 .AND,
   opAt 1737 .ISZERO,
   pushAt 1738 2 2373,
   opAt 1739 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1740 (.Dup ⟨0, by decide⟩),
   pushAt 1741 1 96,
   pushAt 1742 2 2112,
   opAt 1743 .CALLDATACOPY,
   pushAt 1744 0 0,
   pushAt 1745 2 2080,
   opAt 1746 .MSTORE,
   pushAt 1747 2 2390,
   pushAt 1748 2 4115,
   opAt 1749 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1750 .JUMPDEST,
   pushAt 1751 1 1,
   pushAt 1752 2 1024,
   opAt 1753 .MSTORE,
   pushAt 1754 2 782,
   pushAt 1755 2 1024,
   pushAt 1756 2 1278,
   opAt 1757 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1763 1 1,
   pushAt 1764 2 2752,
   opAt 1765 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1787 .POP,
   opAt 1788 .POP,
   pushAt 1789 0 0,
   opAt 1790 .MLOAD,
   opAt 1791 (.Dup ⟨0, by decide⟩),
   pushAt 1792 0 0,
   opAt 1793 .SUB,
   opAt 1794 (.Dup ⟨1, by decide⟩),
   opAt 1795 .AND,
   opAt 1796 (.Dup ⟨0, by decide⟩),
   pushAt 1797 2 1536,
   opAt 1798 .MSTORE,
   opAt 1799 (.Dup ⟨0, by decide⟩),
   opAt 1800 (.Dup ⟨2, by decide⟩),
   opAt 1801 .DIV,
   opAt 1802 (.Dup ⟨0, by decide⟩),
   pushAt 1803 2 1568,
   opAt 1804 .MSTORE,
   opAt 1805 (.Dup ⟨1, by decide⟩),
   opAt 1806 (.Dup ⟨0, by decide⟩),
   pushAt 1807 0 0,
   opAt 1808 .SUB,
   opAt 1809 .DIV,
   pushAt 1810 1 1,
   opAt 1811 .ADD,
   pushAt 1812 2 1600,
   opAt 1813 .MSTORE,
   opAt 1814 (.Dup ⟨0, by decide⟩),
   opAt 1815 (.Dup ⟨0, by decide⟩),
   pushAt 1816 0 0,
   opAt 1817 .SUB,
   opAt 1818 .MOD,
   pushAt 1819 2 1632,
   opAt 1820 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1821 (.Dup ⟨0, by decide⟩),
   pushAt 1822 1 3,
   opAt 1823 .MUL,
   pushAt 1824 1 2,
   opAt 1825 .XOR,
   opAt 1826 (.Dup ⟨0, by decide⟩),
   opAt 1827 (.Dup ⟨2, by decide⟩),
   opAt 1828 .MUL,
   pushAt 1829 1 2,
   opAt 1830 .SUB,
   opAt 1831 .MUL,
   opAt 1832 (.Dup ⟨0, by decide⟩),
   opAt 1833 (.Dup ⟨2, by decide⟩),
   opAt 1834 .MUL,
   pushAt 1835 1 2,
   opAt 1836 .SUB,
   opAt 1837 .MUL,
   opAt 1838 (.Dup ⟨0, by decide⟩),
   opAt 1839 (.Dup ⟨2, by decide⟩),
   opAt 1840 .MUL,
   pushAt 1841 1 2,
   opAt 1842 .SUB,
   opAt 1843 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1844 (.Dup ⟨0, by decide⟩),
   opAt 1845 (.Dup ⟨2, by decide⟩),
   opAt 1846 .MUL,
   pushAt 1847 1 2,
   opAt 1848 .SUB,
   opAt 1849 .MUL,
   opAt 1850 (.Dup ⟨0, by decide⟩),
   opAt 1851 (.Dup ⟨2, by decide⟩),
   opAt 1852 .MUL,
   pushAt 1853 1 2,
   opAt 1854 .SUB,
   opAt 1855 .MUL,
   opAt 1856 (.Dup ⟨0, by decide⟩),
   opAt 1857 (.Dup ⟨2, by decide⟩),
   opAt 1858 .MUL,
   pushAt 1859 1 2,
   opAt 1860 .SUB,
   opAt 1861 .MUL,
   pushAt 1862 2 1664,
   opAt 1863 .MSTORE,
   opAt 1864 .POP,
   opAt 1865 .POP,
   opAt 1866 .POP,
   opAt 1867 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1897 .JUMPDEST,
   opAt 1898 (.Dup ⟨0, by decide⟩),
   opAt 1899 .ISZERO,
   pushAt 1900 2 3156,
   opAt 1901 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1902 (.Dup ⟨1, by decide⟩),
   pushAt 1903 2 2112,
   pushAt 1904 2 2080,
   opAt 1905 .MCOPY,
   pushAt 1906 0 0,
   pushAt 1907 2 2784,
   opAt 1908 .MLOAD,
   opAt 1909 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1910 2 2080,
   opAt 1911 .MLOAD,
   pushAt 1912 2 1536,
   opAt 1913 .MLOAD,
   opAt 1914 (.Dup ⟨1, by decide⟩),
   opAt 1915 .DIV,
   opAt 1916 (.Swap ⟨0, by decide⟩),
   pushAt 1917 2 1600,
   opAt 1918 .MLOAD,
   opAt 1919 .MUL,
   pushAt 1920 2 1536,
   opAt 1921 .MLOAD,
   pushAt 1922 2 2112,
   opAt 1923 .MLOAD,
   opAt 1924 .DIV,
   opAt 1925 .ADD,
   pushAt 1926 2 1568,
   opAt 1927 .MLOAD,
   opAt 1928 (.Dup ⟨0, by decide⟩),
   pushAt 1929 2 1632,
   opAt 1930 .MLOAD,
   opAt 1931 (.Dup ⟨4, by decide⟩),
   opAt 1932 .MULMOD,
   opAt 1933 (.Dup ⟨2, by decide⟩),
   opAt 1934 .ADDMOD,
   opAt 1935 (.Swap ⟨0, by decide⟩),
   opAt 1936 .SUB,
   pushAt 1937 2 1664,
   opAt 1938 .MLOAD,
   opAt 1939 .MUL,
   opAt 1940 (.Dup ⟨0, by decide⟩),
   pushAt 1941 0 0,
   opAt 1942 .MLOAD,
   opAt 1943 .MUL,
   pushAt 1944 2 2112,
   opAt 1945 .MLOAD,
   opAt 1946 .SUB,
   pushAt 1947 1 32,
   opAt 1948 .MLOAD,
   pushAt 1949 1 128,
   opAt 1950 .SHR,
   opAt 1951 (.Dup ⟨2, by decide⟩),
   pushAt 1952 1 128,
   opAt 1953 .SHR,
   opAt 1954 .MUL,
   opAt 1955 .GT,
   opAt 1956 (.Swap ⟨0, by decide⟩),
   opAt 1957 .SUB,
   opAt 1958 (.Swap ⟨0, by decide⟩),
   pushAt 1959 2 1568,
   opAt 1960 .MLOAD,
   opAt 1961 .GT,
   opAt 1962 .ISZERO,
   pushAt 1963 0 0,
   opAt 1964 .SUB,
   opAt 1965 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2218 2 2080,
   opAt 2219 .MLOAD,
   opAt 2220 (.Dup ⟨1, by decide⟩),
   opAt 2221 .ADD,
   opAt 2222 (.Dup ⟨0, by decide⟩),
   opAt 2223 (.Swap ⟨1, by decide⟩),
   opAt 2224 .GT,
   opAt 2225 (.Dup ⟨1, by decide⟩),
   opAt 2226 (.Dup ⟨3, by decide⟩),
   opAt 2227 .GT,
   opAt 2228 .GT,
   opAt 2229 (.Swap ⟨1, by decide⟩),
   opAt 2230 (.Swap ⟨0, by decide⟩),
   opAt 2231 .SUB,
   opAt 2232 (.Dup ⟨0, by decide⟩),
   pushAt 2233 2 2080,
   opAt 2234 .MSTORE,
   opAt 2235 (.Dup ⟨1, by decide⟩),
   opAt 2236 .OR,
   pushAt 2237 2 3012,
   opAt 2238 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2245 .JUMPDEST,
   opAt 2246 .ISZERO,
   pushAt 2247 2 3097,
   opAt 2248 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2249 .JUMPDEST,
   pushAt 2250 0 0,
   pushAt 2251 2 2784,
   opAt 2252 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2253 .JUMPDEST,
   opAt 2254 (.Dup ⟨0, by decide⟩),
   opAt 2255 .MLOAD,
   pushAt 2256 3 2112,
   opAt 2257 (.Dup ⟨2, by decide⟩),
   opAt 2258 .SUB,
   opAt 2259 .MLOAD,
   opAt 2260 (.Dup ⟨1, by decide⟩),
   opAt 2261 .ADD,
   opAt 2262 (.Swap ⟨0, by decide⟩),
   opAt 2263 (.Dup ⟨1, by decide⟩),
   opAt 2264 .LT,
   opAt 2265 (.Swap ⟨0, by decide⟩),
   opAt 2266 (.Dup ⟨3, by decide⟩),
   opAt 2267 .ADD,
   opAt 2268 (.Swap ⟨2, by decide⟩),
   opAt 2269 (.Dup ⟨3, by decide⟩),
   opAt 2270 .LT,
   opAt 2271 .OR,
   opAt 2272 (.Swap ⟨1, by decide⟩),
   opAt 2273 (.Dup ⟨1, by decide⟩),
   opAt 2274 .MSTORE,
   pushAt 2275 1 31,
   opAt 2276 .NOT,
   opAt 2277 .ADD,
   pushAt 2278 2 2111,
   opAt 2279 (.Dup ⟨1, by decide⟩),
   opAt 2280 .GT,
   pushAt 2281 2 3024,
   opAt 2282 .JUMPI,
   opAt 2283 .JUMPDEST,
   opAt 2284 .JUMPDEST,
   opAt 2285 .JUMPDEST,
   opAt 2286 .JUMPDEST,
   opAt 2287 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2288 .POP,
   pushAt 2289 2 2080,
   opAt 2290 .MLOAD,
   opAt 2291 (.Dup ⟨1, by decide⟩),
   opAt 2292 .ADD,
   opAt 2293 (.Dup ⟨0, by decide⟩),
   pushAt 2294 2 2080,
   opAt 2295 .MSTORE,
   opAt 2296 .LT,
   opAt 2297 .ISZERO,
   pushAt 2298 2 3018,
   opAt 2299 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2300 .JUMPDEST,
   pushAt 2301 2 2080,
   opAt 2302 .MLOAD,
   opAt 2303 (.Dup ⟨0, by decide⟩),
   opAt 2304 .ISZERO,
   pushAt 2305 2 3002,
   opAt 2306 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2300 .JUMPDEST,
   pushAt 2301 2 2080,
   opAt 2302 .MLOAD,
   opAt 2303 (.Dup ⟨0, by decide⟩),
   opAt 2304 .ISZERO,
   pushAt 2305 2 3002,
   opAt 2306 .JUMPI,
   opAt 2307 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2308 .JUMPDEST,
   pushAt 2309 0 0,
   pushAt 2310 2 2784,
   opAt 2311 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2312 .JUMPDEST,
   opAt 2313 (.Dup ⟨0, by decide⟩),
   opAt 2314 .MLOAD,
   pushAt 2315 2 2112,
   opAt 2316 (.Dup ⟨2, by decide⟩),
   opAt 2317 .SUB,
   opAt 2318 .MLOAD,
   opAt 2319 (.Dup ⟨1, by decide⟩),
   opAt 2320 (.Dup ⟨1, by decide⟩),
   opAt 2321 .GT,
   opAt 2322 (.Swap ⟨1, by decide⟩),
   opAt 2323 .SUB,
   opAt 2324 (.Dup ⟨3, by decide⟩),
   opAt 2325 (.Dup ⟨1, by decide⟩),
   opAt 2326 .LT,
   opAt 2327 (.Swap ⟨0, by decide⟩),
   opAt 2328 (.Dup ⟨4, by decide⟩),
   opAt 2329 (.Swap ⟨0, by decide⟩),
   opAt 2330 .SUB,
   opAt 2331 (.Dup ⟨3, by decide⟩),
   opAt 2332 .MSTORE,
   opAt 2333 .OR,
   opAt 2334 (.Swap ⟨1, by decide⟩),
   opAt 2335 .POP,
   pushAt 2336 1 31,
   opAt 2337 .NOT,
   opAt 2338 .ADD,
   pushAt 2339 2 2111,
   opAt 2340 (.Dup ⟨1, by decide⟩),
   opAt 2341 .GT,
   pushAt 2342 2 3103,
   opAt 2343 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2344 .POP,
   pushAt 2345 2 2080,
   opAt 2346 .MLOAD,
   opAt 2347 .SUB,
   pushAt 2348 2 2080,
   opAt 2349 .MSTORE,
   pushAt 2350 2 3085,
   opAt 2351 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2239 .JUMPDEST,
   opAt 2240 .NOT,
   opAt 2241 .ADD,
   pushAt 2242 2 2573,
   pushAt 2243 2 4115,
   opAt 2244 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2372 (.Dup ⟨0, by decide⟩),
   pushAt 2373 2 2112,
   pushAt 2374 2 512,
   opAt 2375 .MCOPY,
   opAt 2376 (.Dup ⟨0, by decide⟩),
   pushAt 2377 2 1280,
   pushAt 2378 2 1024,
   opAt 2379 .MCOPY,
   pushAt 2380 2 2182,
   opAt 2381 .JUMP]

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
  Artifact.isValidJumpDest_index 2253 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3024 = true :=
  Artifact.isValidJumpDest_index 2257 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3085 = true :=
  Artifact.isValidJumpDest_index 2304 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3103 = true :=
  Artifact.isValidJumpDest_index 2316 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3012 = true :=
  Artifact.isValidJumpDest_index 2249 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3097 = true :=
  Artifact.isValidJumpDest_index 2312 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3002 = true :=
  Artifact.isValidJumpDest_index 2243 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3156 = true :=
  Artifact.isValidJumpDest_index 2356 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
