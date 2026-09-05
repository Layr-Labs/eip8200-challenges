# Public test vectors

These are fixed, reviewable inputs and expected return bytes, loaded at runtime.
There is no random generation during testing. Edit or copy the JSON files to
define another suite; changing a vector file does not require rebuilding Lean.

These files are public local tests. The ranked workflow uses a separate JSON
suite from a GitHub Actions secret; see [benchmark setup](../docs/benchmark.md#public-and-benchmark-vectors).

The loader's integration checks can be run with
`python3 scripts/test-vector-files.py` after building both runners.

From the repository root:

```sh
lake exe modexpchallenge --vectors=test-vectors/modexp.json
lake exe ripemd160challenge --vectors=test-vectors/ripemd160.json
```

Add `--hex=path/to/bytecode.hex` or `--yul=path/to/source.yul` to test a candidate,
and `--csv` for gas results. Without `--vectors`, the runners use their original
built-in vectors and preserve the published benchmark totals. A supplied file
replaces the built-in suite for that invocation.

## Format

```json
{
  "precompile": "ripemd160",
  "vectors": [
    {
      "label": "empty message",
      "input": "",
      "expected": "0000000000000000000000009c1185a5c5e9fc54612808977ee8f548b2258d31"
    }
  ]
}
```

Use `modexp` or `ripemd160` for `precompile`. Labels must be unique, nonempty,
and single-line. Both byte fields must contain even-length hex, optionally
prefixed with `0x`; an empty string means zero bytes. Suites must be nonempty.

MODEXP inputs contain the three 32-byte big-endian operand lengths followed by
the base, exponent, and modulus. Expected output has exactly the declared
modulus length, including leading zero bytes. The loader rejects declared
operand sizes greater than the challenge's 1024-byte limit. Missing input bytes
are interpreted as trailing zeros by the pinned specification.

RIPEMD-160 inputs are raw message bytes. Expected output is the Ethereum
32-byte return value: twelve zero bytes followed by the 20-byte digest. Each
case runs in both clean and dirty initial states, as in the built-in suite.

Every expected output is checked against the pinned specification before any
candidate executes. A disagreement, malformed file, wrong precompile tag, or
invalid input exits nonzero. Candidate failures also exit nonzero. These are
executable tests, not a substitute for the correctness proofs.

## Included cases

`modexp.json` contains the 13 fixed cases from
[`ModexpGasTest`](../foundry/test/ModexpGas.t.sol), including the EIP-198 examples,
the 257-bit modulus, BN254 inversion, and RSA-1024/2048 operations.

`ripemd160.json` contains the 17 fixed cases from
[`Ripemd160GasTest`](../foundry/test/Ripemd160Gas.t.sol), including empty and `abc`
messages, padding boundaries, and both 1000-byte messages.

Labels, inputs, and order were exported directly from the Foundry test arrays.
Expected outputs came from Foundry's native `0x05` and `0x03` precompiles. These
are the same vectors as the built-in Lean suites, stored as literal JSON bytes.
