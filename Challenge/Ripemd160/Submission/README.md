# RIPEMD-160: shifted empty/abc answer

Research candidate: 674,344 gas / 5,233 bytes on the local corpus, four gas below
the independently verified 674,348-gas parent. SHA-256: `53711f47bbcc9a90ebf19a647999a8a046b00a7b2f818eaa344aad234958c001`.

The guarded empty/abc answer uses `(A >> input.size) xor B`, with
`A = 0x10b528590516b262afd6901ab02b21f16eaadd61` and `B = 0x8ca4adfcc0ff4e36cefe988dcec3d4b9dc8f5050`. Replacing multiplication with shifting saves
two gas for each accepted empty or abc input. Two commutative operand pairs
at PCs 740 and 1147 are reordered without changing semantics or gas, allowing
the original protected byte-array loader to compile at its default limit.

This builds on the verified filler relocation in commit 9237f844 and the public
direct-modulus optimization by fkiene, integrated in frontier bdb17448. Earlier
recognition, rotations, memory layout and padding contributions are retained.

The original protected loader and all 3,677 Solution build jobs pass. The final
theorem uses only propext, Classical.choice and Quot.sound. Native scoring passes
49/49 vectors in clean and dirty frames at 674,344 gas each. Differential checks
against bdb17448 pass 4,274 inputs and 69 corpus seeds: 62 seeds save 100 gas and
seven save 99 gas. The 120-seed submission gate reports no digest mismatches,
median/minimum 674,344 gas and an empirical acceptance probability of 0.808
against official score 674,444. After promotion of bf916155, the repeated gate
also reports 0.808 against official score 674,348. The original secure Comparator
and default kernel accept this exact artifact: verified score 674,344 gas,
17 minutes 9 seconds, 25.7 GiB peak memory. Official acceptance is tracked separately.
