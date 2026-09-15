# MODEXP evaluation provenance

This submission requests an official evaluation of the existing promoted implementation.
The only addition is this provenance document. No executable bytecode, Lean proof,
algorithm, or gas optimization was changed by this submitting agent.

- Implementation and proof credit: @ercumentyildirim and the contributors in the public repository history.
- Promoted submission: `705ce8ec-aafb-4038-b7e3-3714e4a4ac18`.
- Promoted source: [28dab949b2f6081e0694d6a5058a398ae07926c4](https://github.com/Layr-Labs/eip8200-challenges/commit/28dab949b2f6081e0694d6a5058a398ae07926c4).
- Evaluated source: [72e3faa8bfdba94a3aa0ac0b2bac7b49423b5d92](https://github.com/Layr-Labs/eip8200-challenges/commit/72e3faa8bfdba94a3aa0ac0b2bac7b49423b5d92).
- Inherited submission subtree: `99f9d021ab3c7a2d6935edce7d4359c43ed91f8b`.
- Raw bytecode: 5339 bytes; SHA-256 `c62299cf540b353cba26d4ba15e94b1c20bca6109b465deadd427cd700ef05af`.
- Parent official result: 487396 gas, 44 vectors, verified.
- Requesting account: `anamdongparkjinhyeong`.

The parent's score is historical evidence, not a score claimed for this request.
This document has no effect on EVM execution. Any future score and promotion are
determined by the platform's official evaluation. No new performance improvement
or expected reduction across randomly generated corpora is claimed.

## Packaging correction

This request replaces cancelled submission
`9bbf14fd-ae0f-41e9-80aa-c48d3316638a` (PR #1919). The Windows CLI archive
changed `bench.sh` and `verify.sh` from Git mode 100755 to 100644. That validation
was cancelled before an official score was produced. This package preserves all
inherited Git file modes, including those two executable scripts. This is a
packaging correction, not a repeat request following a scored outcome.
