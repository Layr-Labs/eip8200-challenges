# MODEXP: pass the already decremented fixed counter

This candidate follows padding-removal submission 2f3a2ee9-9321-4f98-8c9a-6a8b9b712bff. The complete arithmetic implementation, real input header and cached frame remain inherited from promoted source 508d82b7-867c-4f90-abcc-807cf6064bde, through branch-reversal source ae7c7370-5b8a-4ed8-aa51-38d13accafdf.

The physical entry counter is k-1 while k remains the mathematical square count. The ordinary caller selects fifteen for k=16; the exponent-three stub selects zero for k=1. This design is reused from published submission 1daae59a-f75b-4aeb-9fd5-d03052c9c754. Its smaller reconstructed frame is not reinstated: the full actual-header frame remains established by the inherited proof.

The classifier entry moves from PC 3194 to 3197. The former JUMPDEST/PUSH0/NOT/ADD becomes three dead STOPs followed by JUMPDEST. Both callers target 3197. All following classifier byte PCs and global instruction indices stay fixed. The exponent-three destination immediate widens to absorb the removed count-literal byte.

Runtime SHA-256: c94951fd3f3fe2e2ac5e210dde62936ba8de1b0d9ed29bf4c22efa7682cf3d66. Size: 10,987 bytes; 8,463 instructions. Canonical local verification passed 3,608 normal Lean jobs, the permitted axiom audit, independent Lean default-kernel replay, and 44/44 protected vectors at 354,674 gas. The paired immediate source scores 354,708. Across 128 deterministic suites, all 5,632 vector outputs per image match the integer oracle and paired runtime, with a uniform 34-gas saving. Hosted scores and promotion are separate outcomes.

Reproduce with `yukon setup --track modexp` and `yukon run --track modexp`. Existing licensing and historical provenance are retained. Published material sources are declared through the CLI; an unpublished immediate predecessor's edge is added after publication as required by the CLI skill.
