# Credited reuse

Source: https://github.com/Layr-Labs/eip8200-challenges/tree/e638a7a3e1d0afea4389d8748055a867a31cb3d9
Original submitter: @ercumentyildirim
Yukon source: 1c21ab97-04ca-470f-ae2d-57e5fa08dc78
Executable SHA-256: ad60d3dac181092e39562b72c2003578a87e3734cffecc962593cd33f56332f7

Executable bytes and Lean proof terms are reused unchanged. One source-attribution line comment is appended to Solution.lean. Local comparison is described in the public submission note.


---

# Credited reuse by this submission (sleepdefic1t, 2026-09-18T22:03Z)

- Window route: bytes [827, 2351) of the promoted image of Yukon submission
  19524bd4-c48f-49e9-8937-81be4fb279c1 (solver terrapinelf, on top of
  500a727f-0f85-416c-94e3-8d6dddf18488 by i34-9 and ercumentyildirim), placed at
  offset 866 of this image with its unreached filler re-spelled; the route's proof
  modules (WindowTwentyOne*, Fermat*, ArtifactWindowPaths) re-addressed by +39
  program counters and +34 instruction indices.
- Shift-loop cut and kernel cuts: from the promoted tree of Yukon submission
  500a727f-0f85-416c-94e3-8d6dddf18488; QHatBound.lean and the PreOK development in
  ShiftModel.lean are copied verbatim; the four-limb row's filler move follows
  19524bd4.
- Packaging base, eight-limb kernel with the modulus word cached on the stack and
  the e = 3 root path: the promoted tree of Yukon submission
  c99fd371-b90c-4864-9adc-bf3f14aa2795 (solver Meganpark980320), whose own credited
  chain above is retained verbatim.
Everything else in this tree (fast-path narrowing, recogniser placement, compact
relayout, instruction-count-preserving spellings, the joining proofs) is this
submission's own work.
