// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

import {console2} from "forge-std/Test.sol";
import {GasCrossCheck} from "./GasCrossCheck.sol";
import {Vectors} from "../src/Vectors.sol";
import {ModexpDeployed} from "evmification/modexp/ModexpDeployed.sol";

/// @notice Cross-checks the MODEXP challenge's published gas against a real EVM.
///
/// @dev The `leanGas` column is what `Challenge/Modexp/Scorer.lean` reports for
///      the frozen reference, as printed by `lake exe modexpchallenge` and
///      summarized in that challenge's README gas table. The same 9 vectors run
///      here against the same bytecode under revm.
///
///      MODEXP is the sharpest of the three cross-checks. Its cost is
///      branch-sensitive rather than a function of calldata length alone, the
///      reference switches between a `MULMOD` fast path and a 32-limb fallback,
///      and the precompile's own price follows the Osaka/EIP-7883 schedule. The
///      precompile column therefore also checks the Lean side's model of that
///      schedule against revm's.
contract ModexpGasTest is GasCrossCheck {
    /// @dev One scored vector, plus the gas `Scorer.lean` reports the Osaka
    ///      MODEXP precompile would charge for the same tuple.
    struct ModexpCase {
        string label;
        bytes input;
        uint256 leanGas;
        uint256 leanPrecompileGas;
    }

    ModexpCase[] internal cases;
    address internal refAddr;
    address internal evmification;

    function setUp() public override {
        super.setUp();
        refAddr = _etchReference("../Challenge/Modexp/Reference");
        evmification = address(new ModexpDeployed());

        // Challenge/Modexp/Scorer.lean, `vectors`, in order.
        cases.push(ModexpCase("empty tuple", "", 183, 500));
        cases.push(ModexpCase("2^5 mod 13", Vectors.makeInput(2, 5, 13, 1, 1, 1), 2403, 500));
        cases.push(ModexpCase("zero exponent", Vectors.makeInput(42, 0, 97, 1, 0, 1), 1193, 500));
        cases.push(ModexpCase("zero modulus", Vectors.makeInput(42, 7, 0, 1, 1, 12), 950, 500));
        cases.push(ModexpCase("zero modulus size", Vectors.makeInput(42, 7, 0, 1, 1, 0), 183, 500));
        cases.push(ModexpCase("EIP-198 example 1", _eipExample1(), 39913, 4080));
        cases.push(ModexpCase("EIP-198 example 2", _eipExample2(), 39773, 4080));
        cases.push(ModexpCase("trailing-zero normalization", _truncatedModulus(), 3613, 500));
        cases.push(ModexpCase("257-bit modulus", _wideModulus(), 18958693, 500));
    }

    /// @dev `Scorer.eipExample1`.
    function _eipExample1() private pure returns (bytes memory) {
        return hex"0000000000000000000000000000000000000000000000000000000000000001"
            hex"0000000000000000000000000000000000000000000000000000000000000020"
            hex"0000000000000000000000000000000000000000000000000000000000000020" hex"03"
            hex"fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e"
            hex"fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f";
    }

    /// @dev `Scorer.eipExample2`.
    function _eipExample2() private pure returns (bytes memory) {
        return hex"0000000000000000000000000000000000000000000000000000000000000000"
            hex"0000000000000000000000000000000000000000000000000000000000000020"
            hex"0000000000000000000000000000000000000000000000000000000000000020"
            hex"fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e"
            hex"fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f";
    }

    /// @dev `Scorer.truncatedModulus`: EIP-198's truncated-input example, where
    ///      the single supplied modulus byte reads as `0x80` followed by 31
    ///      zero bytes.
    function _truncatedModulus() private pure returns (bytes memory) {
        return hex"0000000000000000000000000000000000000000000000000000000000000001"
            hex"0000000000000000000000000000000000000000000000000000000000000002"
            hex"0000000000000000000000000000000000000000000000000000000000000020" hex"03ffff80";
    }

    /// @dev `Scorer`'s 257-bit tuple: `makeInput (2^256 + 5) 3 (2^256 + 7) 33 1 33`.
    ///      Both operands exceed 256 bits, so they are built byte-wise.
    function _wideModulus() private pure returns (bytes memory) {
        bytes memory base = abi.encodePacked(bytes1(0x01), bytes32(uint256(5)));
        bytes memory exponent = abi.encodePacked(bytes1(0x03));
        bytes memory modulus = abi.encodePacked(bytes1(0x01), bytes32(uint256(7)));
        return Vectors.makeInputBytes(base, exponent, modulus);
    }

    function test_vectors_match_scorer() public view {
        assertEq(cases.length, 9, "vector count");
        assertEq(pin.provedSize, 1284, "reference bytecode size");
        assertEq(refAddr.code.length, 1284, "etched code size");

        uint256[9] memory sizes = [uint256(0), 99, 98, 110, 98, 161, 160, 100, 163];
        for (uint256 i = 0; i < cases.length; i++) {
            assertEq(cases[i].input.length, sizes[i], cases[i].label);
        }
    }

    /// @dev The reference must return what the `0x05` precompile returns, so
    ///      the gas comparison is between implementations of one function.
    function test_reference_returns_precompile_result() public view {
        for (uint256 i = 0; i < cases.length; i++) {
            (, bytes memory ret) = _gas(refAddr, cases[i].input);
            (, bytes memory expected) = _gas(address(0x05), cases[i].input);
            assertEq(ret, expected, cases[i].label);
        }
    }

    /// @notice The cross-check: revm must charge what `Scorer.lean` reports.
    function test_reference_gas_matches_lean_scorer() public view {
        uint256 leanTotal;
        uint256 forgeTotal;
        _header("MODEXP reference: Lean scorer vs revm");
        for (uint256 i = 0; i < cases.length; i++) {
            (uint256 gasUsed,) = _gas(refAddr, cases[i].input);
            _row(cases[i].label, cases[i].input.length, cases[i].leanGas, gasUsed);
            assertEq(gasUsed, cases[i].leanGas, cases[i].label);
            leanTotal += cases[i].leanGas;
            forgeTotal += gasUsed;
        }
        _row("all vectors", 0, leanTotal, forgeTotal);
        assertEq(forgeTotal, 19046904, "README suite total");
    }

    /// @dev The scorer's `precompile` column comes from the pinned semantics'
    ///      own Osaka MODEXP pricing. Measuring `0x05` through the same probe
    ///      checks that model against revm's implementation of EIP-7883.
    function test_precompile_schedule_matches_lean_model() public view {
        uint256 leanTotal;
        uint256 forgeTotal;
        _header("MODEXP precompile (0x05): Lean gas model vs revm");
        for (uint256 i = 0; i < cases.length; i++) {
            (uint256 precompileGas,) = _gas(address(0x05), cases[i].input);
            _row(cases[i].label, cases[i].input.length, cases[i].leanPrecompileGas, precompileGas);
            assertEq(precompileGas, cases[i].leanPrecompileGas, cases[i].label);
            leanTotal += cases[i].leanPrecompileGas;
            forgeTotal += precompileGas;
        }
        _row("all vectors", 0, leanTotal, forgeTotal);
        assertEq(forgeTotal, 11660, "README precompile total");
    }

    /// @dev The scorer scores from a fixed initial state; the reference's gas
    ///      must not depend on the account's storage or balance either.
    function test_gas_is_state_independent() public {
        _assertGasIsStateIndependent(refAddr, cases[0].input, "empty tuple");
        _assertGasIsStateIndependent(refAddr, cases[8].input, "257-bit modulus");
    }

    /// @dev Recomputes the README's `vs precompile` ratio from measured gas.
    function test_precompile_ratio_matches_readme() public view {
        uint256 referenceTotal;
        uint256 precompileTotal;
        for (uint256 i = 0; i < cases.length; i++) {
            (uint256 gasUsed,) = _gas(refAddr, cases[i].input);
            (uint256 precompileGas,) = _gas(address(0x05), cases[i].input);
            referenceTotal += gasUsed;
            precompileTotal += precompileGas;
        }
        console2.log(
            string.concat(
                "reference vs precompile: ", _ratio(referenceTotal, precompileTotal), " (README: 1633.53x)"
            )
        );
        assertEq(_ratio(referenceTotal, precompileTotal), "1633.53x", "vs precompile ratio");
    }

    /// @notice Measures eth-act/evmification's Solidity implementation on the
    ///         same vectors, through the same probe.
    function test_evmification_comparison() public view {
        uint256 referenceTotal;
        uint256 evmificationTotal;
        uint256 precompileTotal;

        console2.log("");
        console2.log("MODEXP on the Lean scorer's vectors (frame gas, revm)");
        console2.log(
            string.concat(
                _rpad("vector", 30),
                _rpad("bytes", 7),
                _rpad("reference", 12),
                _rpad("evmification", 14),
                "precompile"
            )
        );
        for (uint256 i = 0; i < cases.length; i++) {
            (uint256 referenceGas,) = _gas(refAddr, cases[i].input);
            (uint256 evmificationGas, bytes memory ret) = _gas(evmification, cases[i].input);
            (uint256 precompileGas, bytes memory expected) = _gas(address(0x05), cases[i].input);

            assertEq(ret, expected, cases[i].label);

            console2.log(
                string.concat(
                    _rpad(cases[i].label, 30),
                    _rpad(vm.toString(cases[i].input.length), 7),
                    _rpad(vm.toString(referenceGas), 12),
                    _rpad(vm.toString(evmificationGas), 14),
                    vm.toString(precompileGas)
                )
            );
            referenceTotal += referenceGas;
            evmificationTotal += evmificationGas;
            precompileTotal += precompileGas;
        }
        console2.log(
            string.concat(
                _rpad("all vectors", 30),
                _rpad("-", 7),
                _rpad(vm.toString(referenceTotal), 12),
                _rpad(vm.toString(evmificationTotal), 14),
                vm.toString(precompileTotal)
            )
        );
        console2.log(
            string.concat(
                "vs precompile: reference ",
                _ratio(referenceTotal, precompileTotal),
                ", evmification ",
                _ratio(evmificationTotal, precompileTotal)
            )
        );
    }
}
