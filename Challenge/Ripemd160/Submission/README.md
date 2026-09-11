# RIPEMD-160: checked returns for 64, 65, and 128 bytes

The runtime replaces the patterned first-block state installer with complete
checked scan returns for 64-, 65-, and 128-byte inputs. Existing 56-, 63-,
120-, 256-, 376-, and 1000-byte returns remain. Every real input byte is checked
before returning a literal digest, and mismatches use the generic compressor.

The comparison is promoted source
`12b801fc876f3fbb2cb1c3fbe41f817dc2866851` (895,873 gas / 5,264 bytes).
This artifact is **857,970 gas / 5,242 bytes**, a 37,903-gas reduction (4.230845%).
The total includes the regression on patterned 119-byte inputs, which lose the
old first-block shortcut. Ordinary generated vectors become cheaper because
their failed prefix checks are removed.

SHA-256 of the exact bytecode:
`88931136de8bf277b59929947e632c40af1ed3c7f819f3f0a24f1f1304ad3165`.

The short size bitmap now recognizes 56, 63, 64, 65, 120, and 128. The shared
tail shift lookup adds the one-byte tail needed by length 65. The compressed
round body keeps its addresses; nonempty dispatch goes directly to its
existing entry at PC 528. The empty-input shortcut is retained.

`StackCorrect` proves the simplified generic kernel. `SizeLookupFlag` proves
exact length membership for every 256-bit size. `ShortPatternLogic` and
`ShortPatternScan64/65/128` prove full-input recognition and scanner execution.
`ScanDigest64/65/128` bind the recognized inputs to the mathematical hash.
`ShortPatternFinish` and `DirectGuard` compose literal returns and all fallback
cases into the universal theorem exported by `Solution.lean`. Some inherited
module names describe earlier layouts; the active proof closure starts at
`Solution.lean`.

The protected native Lean scorer verifies 49/49 vectors in both clean and dirty
initial frames, at 857,970 gas in each frame. Differential fuzz checks 3,899
boundary, random, and patterned-prefix inputs; a further 3,968 checks flip
every individual bit of each recognized short input. All outputs agree with
the independent RIPEMD-160 oracle. The byte array and decoded instruction
representations independently reconstruct all 5,242 bytes and 4,145
instructions. Official proof validation and promotion are recorded by Yukon.

## Attribution

This package retains the public source lineage of terrapinelf, GordoAR,
ayseunxl, fkiene, and i34. Source authorship is not reassigned by this inventory.

The subsequent promoted lineage also includes ercumentyildirim, hybridnoise,
and Akashneelesh. The 64-byte digest reuses the completed `Exact64Digest`
certificate; the 128-byte digest reuses `Patterned128Digest`. The 65-byte
digest is derived through the existing padding and compression definitions.

Official validation, scoring, and promotion status are recorded separately
by the platform.
