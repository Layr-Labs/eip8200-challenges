// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

/// @title Vectors
/// @notice Rebuilds the Lean scorers' test vectors in Solidity.
///
/// @dev The cross-check is only meaningful if both sides run byte-identical
///      inputs, so these generators mirror the definitions in
///      `Challenge/*/Scorer.lean` exactly. Each test asserts the byte length
///      of every vector it builds, which catches a drifted generator before it
///      can silently change a gas number.
library Vectors {
    /// @notice `Scorer.patterned`: byte `i` is `(i * 37 + (i / 251) * 11 + 7) % 256`.
    /// @dev The `i / 251` term makes the sequence non-periodic in 256, so a
    ///      block-boundary bug cannot be masked by a repeating pattern.
    function patterned(uint256 n) internal pure returns (bytes memory out) {
        out = new bytes(n);
        for (uint256 i = 0; i < n; i++) {
            out[i] = bytes1(uint8((i * 37 + (i / 251) * 11 + 7) % 256));
        }
    }

    /// @notice `Scorer.repeated`: `n` copies of `b`.
    function repeated(uint256 n, bytes1 b) internal pure returns (bytes memory out) {
        out = new bytes(n);
        for (uint256 i = 0; i < n; i++) {
            out[i] = b;
        }
    }

    /// @notice `Scorer.word`: a 32-byte big-endian length header.
    function word(uint256 n) internal pure returns (bytes memory) {
        return abi.encodePacked(bytes32(n));
    }

    /// @notice `Scorer.operand`: `value` big-endian, zero-padded to `width`
    ///         bytes. `width` must be at most 32; wider operands are built
    ///         directly by the caller.
    function operand(uint256 value, uint256 width) internal pure returns (bytes memory out) {
        require(width <= 32, "Vectors: operand too wide");
        out = new bytes(width);
        for (uint256 i = 0; i < width; i++) {
            out[width - 1 - i] = bytes1(uint8(value >> (8 * i)));
        }
    }

    /// @notice `Scorer.makeInput`: the padded EIP-198 tuple.
    function makeInput(
        uint256 base,
        uint256 exponent,
        uint256 modulus,
        uint256 bsize,
        uint256 esize,
        uint256 msize
    ) internal pure returns (bytes memory) {
        return abi.encodePacked(
            word(bsize),
            word(esize),
            word(msize),
            operand(base, bsize),
            operand(exponent, esize),
            operand(modulus, msize)
        );
    }

    /// @notice `Scorer.makeInput` with operands supplied as raw bytes, for the
    ///         tuple whose base and modulus exceed 256 bits.
    function makeInputBytes(bytes memory base, bytes memory exponent, bytes memory modulus)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encodePacked(
            word(base.length), word(exponent.length), word(modulus.length), base, exponent, modulus
        );
    }
}
