// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

import {console2} from "forge-std/Test.sol";
import {GasCrossCheck} from "./GasCrossCheck.sol";
import {Vectors} from "../src/Vectors.sol";
import {Sha256Deployed} from "evmification/sha256/Sha256Deployed.sol";

/// @notice Cross-checks the SHA-256 challenge's published gas against a real EVM.
///
/// @dev The `leanGas` column is what `Challenge/Sha256/Scorer.lean` reports for
///      the frozen reference, as printed by `lake exe sha256challenge` and
///      summarized in that challenge's README gas table. The same 19 vectors run
///      here against the same bytecode under revm.
contract Sha256GasTest is GasCrossCheck {
    Case[] internal cases;
    address internal refAddr;
    address internal evmification;

    /// @dev Gas the SHA-256 precompile would charge: `60 + 12 * ceil(n / 32)`.
    function _precompileGas(uint256 len) private pure returns (uint256) {
        return 60 + 12 * ((len + 31) / 32);
    }

    function setUp() public override {
        super.setUp();
        refAddr = _etchReference("../Challenge/Sha256/Reference");
        evmification = address(new Sha256Deployed());

        // Challenge/Sha256/Scorer.lean, `vectors`, in order, each with the gas
        // that scorer reports for the reference bytecode.
        cases.push(Case("empty", "", 158035));
        cases.push(Case("abc", "abc", 158038));
        cases.push(Case("1-byte", Vectors.patterned(1), 158038));
        cases.push(Case("31-byte", Vectors.patterned(31), 158038));
        cases.push(Case("32-byte", Vectors.patterned(32), 158038));
        cases.push(Case("54-byte", Vectors.patterned(54), 158041));
        cases.push(Case("55-byte (last one-block)", Vectors.patterned(55), 158041));
        cases.push(Case("56-byte (length spills)", Vectors.patterned(56), 314044));
        cases.push(
            Case("fips-b2 (56-byte)", "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", 314044)
        );
        cases.push(Case("63-byte", Vectors.patterned(63), 314044));
        cases.push(Case("64-byte (exact block)", Vectors.patterned(64), 314044));
        cases.push(Case("65-byte", Vectors.patterned(65), 314047));
        cases.push(Case("119-byte", Vectors.patterned(119), 314050));
        cases.push(Case("120-byte", Vectors.patterned(120), 470053));
        cases.push(Case("127-byte", Vectors.patterned(127), 470053));
        cases.push(Case("128-byte (two blocks)", Vectors.patterned(128), 470053));
        cases.push(Case("256-byte", Vectors.patterned(256), 782070));
        cases.push(Case("1000-byte", Vectors.patterned(1000), 2498174));
        cases.push(Case("1000 a's", Vectors.repeated(1000, "a"), 2498174));
    }

    function test_vectors_match_scorer() public view {
        assertEq(cases.length, 19, "vector count");
        assertEq(pin.provedSize, 1524, "reference bytecode size");
        assertEq(refAddr.code.length, 1524, "etched code size");

        uint256[19] memory sizes =
            [uint256(0), 3, 1, 31, 32, 54, 55, 56, 56, 63, 64, 65, 119, 120, 127, 128, 256, 1000, 1000];
        for (uint256 i = 0; i < cases.length; i++) {
            assertEq(cases[i].input.length, sizes[i], cases[i].label);
        }

        // The FIPS 180-2 B.2 message is a fixed string, not a generated one.
        assertEq(
            keccak256(cases[8].input),
            keccak256(bytes("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")),
            "fips-b2 message"
        );
    }

    /// @dev The reference returns the 32-byte digest, so gas is being compared
    ///      between implementations of the same function.
    function test_reference_returns_precompile_result() public view {
        for (uint256 i = 0; i < cases.length; i++) {
            (, bytes memory ret) = _gas(refAddr, cases[i].input);
            assertEq(ret, abi.encodePacked(sha256(cases[i].input)), cases[i].label);
        }
    }

    /// @notice The cross-check: revm must charge what `Scorer.lean` reports.
    function test_reference_gas_matches_lean_scorer() public view {
        uint256 leanTotal;
        uint256 forgeTotal;
        _header("SHA-256 reference: Lean scorer vs revm");
        for (uint256 i = 0; i < cases.length; i++) {
            (uint256 gasUsed,) = _gas(refAddr, cases[i].input);
            _row(cases[i].label, cases[i].input.length, cases[i].leanGas, gasUsed);
            assertEq(gasUsed, cases[i].leanGas, cases[i].label);
            leanTotal += cases[i].leanGas;
            forgeTotal += gasUsed;
        }
        _row("all vectors", 0, leanTotal, forgeTotal);
        assertEq(forgeTotal, 10179119, "README suite total");
    }

    /// @dev The scorers score every vector from a clean and a dirty initial
    ///      state and report the same gas for both. Two representative vectors
    ///      are re-checked here against a dirtied account.
    function test_gas_is_state_independent() public {
        _assertGasIsStateIndependent(refAddr, cases[0].input, "empty");
        _assertGasIsStateIndependent(refAddr, cases[17].input, "1000-byte");
    }

    /// @dev Recomputes the README's `vs precompile` ratio from measured gas.
    function test_precompile_ratio_matches_readme() public view {
        uint256 referenceTotal;
        uint256 precompileTotal;
        for (uint256 i = 0; i < cases.length; i++) {
            (uint256 gasUsed,) = _gas(refAddr, cases[i].input);
            referenceTotal += gasUsed;

            (uint256 precompileGas,) = _gas(address(0x02), cases[i].input);
            assertEq(precompileGas, _precompileGas(cases[i].input.length), "precompile schedule");
            precompileTotal += precompileGas;
        }
        console2.log(
            string.concat(
                "reference vs precompile: ", _ratio(referenceTotal, precompileTotal), " (README: 4199.31x)"
            )
        );
        assertEq(_ratio(referenceTotal, precompileTotal), "4199.31x", "vs precompile ratio");
    }

    /// @notice Measures eth-act/evmification's Solidity implementation on the
    ///         same vectors, through the same probe.
    function test_evmification_comparison() public view {
        uint256 referenceTotal;
        uint256 evmificationTotal;
        uint256 precompileTotal;

        console2.log("");
        console2.log("SHA-256 on the Lean scorer's vectors (frame gas, revm)");
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
            (uint256 precompileGas,) = _gas(address(0x02), cases[i].input);

            assertEq(ret, abi.encodePacked(sha256(cases[i].input)), cases[i].label);

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
