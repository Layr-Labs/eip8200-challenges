# MODEXP: one conditional subtraction for the radix residue

Parent SHA: `534ae7328e1c565e4b48a241b37217f70169d1a3`

## Attribution and summary

This submission incorporates the verified radix residue shortcut on top of the Montgomery/CIOS implementation.
The base Montgomery architecture was originally developed by @ercumentyildirim, with subsequent contributions
by @terrapinelf, @GordoAR, and @exakoss.

The artifact `Challenge/Modexp/Submission/bytecode.hex` is 2922 bytes / 1781 instructions.

It is based on the 2901-byte direct Montgomery artifact with two exact architectural updates:
1. The `PUSH2` operand of instruction 1136 (bytes 1530..1531) targets `2901` in place of `1911`, retargeting the radix setup tail call to the `R1B` dispatcher;
2. 21 bytes are appended at offsets 2901..2921 (instruction indices 1768..1780), establishing the conditional subtraction logic.

Every other byte, instruction index, and jump destination across offsets 0..2900 is preserved verbatim.

## What the appended block computes

With `n = ceil(msize/32)`, `radix = 2^256` and `R = radix^n`, the memory block at `R1 = 0x1000` must hold `R mod m`.

`R1B` (pc 2901) is entered with the stack `[px, ret]` — matching the exact calling convention of `DOUBLE256` which it stands in front of — and dispatches conditionally on the most significant bit of the modulus's most significant limb:

```text
2901  JUMPDEST                          ; stack [4096, 1533]
2902  PUSH0 ; MLOAD                     ; load modulus's most significant limb at M = 0x0000
2904  PUSH1 255 ; SHR ; ISZERO          ; check if top bit is clear
2908  PUSH2 1911 ; JUMPI                ; if clear, branch to DOUBLE256 with stack and memory untouched
2912  PUSH1 1 ; PUSH2 0x2020 ; MSTORE   ; if set, store carry t[n] := 1 at TN = 0x2020
2918  PUSH2 2642 ; JUMP                 ; tail call into CSUB with same [px, ret] frame
```

Instruction decomposition:
- Indices 1768..1775 (`blk1768`): top-bit test and conditional branch to `DOUBLE256`.
- Indices 1776..1780 (`blk1776`): store `t[n] := 1` at `TN = 0x2020` and tail jump into `CSUB`.

`CSUB` (pc 2642) is entered with `[pd, ret]` and the multi-limb value `t = t[n] * radix^n + t_low`, held as `t[n]` at `TN = 0x2020` and `t_low` in the `n`-limb buffer at `TS = 0x2040`. It computes `t - m` with exact borrow propagation across all limbs and copies the reduced result to destination `pd`. At this point during initialization, the `t` buffer is completely unwritten and holds zeroes, yielding $t_{\text{low}} = 0$, so $t[n] = 1$ establishes the operand value as exactly $\text{radix}^n$.

`CSUB`'s correctness side condition requires $t[n] \cdot \text{radix}^n + t_{\text{low}} < 2m$. This bound is guaranteed by the top-bit guard: any $n$-limb modulus whose top limb has its most significant bit set satisfies $m \ge \frac{1}{2} \text{radix}^n$, and because $m$ is verified odd while $\text{radix}^n / 2$ is a power of two, the inequality $2m > \text{radix}^n$ is strictly satisfied.

Both branches preserve the `[px, ret]` frame, leaving the return continuation untouched. `TN = 0x2020` lies well within the 296 active memory words, incurring zero dynamic memory expansion gas. When the modulus top bit is clear, execution falls back seamlessly into the 256 modular doubling chain of `DOUBLE256`.

## Exact measured result

Evaluation across the 13 protected vectors demonstrates:

| Vector | Gas |
|---|---:|
| empty tuple | 107 |
| 2^5 mod 13 | 2,327 |
| zero exponent | 1,117 |
| zero modulus | 874 |
| zero modulus size | 107 |
| EIP-198 example 1 | 39,837 |
| EIP-198 example 2 | 39,697 |
| trailing-zero normalization | 3,537 |
| 257-bit modulus | 254,500 |
| BN254 modular inversion | 44,177 |
| random 256-bit modexp | 44,177 |
| RSA-1024 e=3 | 229,694 |
| RSA-2048 e=65537 | 1,264,970 |
| **Total** | **1,925,121** |

The exact measured total across all vectors is 1,925,121 gas. This represents a substantial 362,400 gas reduction relative to the prior 2,287,521 frontier and an over 600,000 gas reduction compared to 2,528,876.
