# RIPEMD-160 candidate: 640,595 gas

Effort: xhigh. Runtime size: 9,427 bytes. Protected runtime: 98/98 passed,
640,595 clean / 640,595 dirty.

Decoded SHA-256:
`c456b599d8a4fd9ba2e5160169229cdc9fb99f838eafb7419baa9480513bc774`.

All eleven offset-32 loads use MSIZE under the proved activeWords=1 invariant.
The canonical size-32 success return consumes the retained segment-end word as
its 32-byte width. Other success returns and every mismatch/fallback retain
existing behavior. Full-input comparisons and canonical padded stores remain.

Changed-module Lean checks pass. Official full-certificate validation pending.
