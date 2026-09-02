// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.20;

import {console2} from "forge-std/Test.sol";
import {GasCrossCheck} from "./GasCrossCheck.sol";
import {Vectors} from "../src/Vectors.sol";
import {Ripemd160Deployed} from "evmification/ripemd160/Ripemd160Deployed.sol";

/// @notice Cross-checks the RIPEMD-160 challenge's published gas against a real EVM.
///
/// @dev The `leanGas` column below is what
///      `Challenge/Ripemd160/Scorer.lean` reports for the frozen reference, as
///      printed by `lake exe ripemd160challenge` and summarized in that
///      challenge's README gas table. This suite re-measures the same 17
///      vectors against the same bytecode under revm and asserts agreement, so
///      the README's numbers are checked by an EVM that shares no code with the
///      one that produced them.
///
///      `Ripemd160Deployed` from eth-act/evmification is measured alongside it.
///      It presents the same interface — raw calldata in, 32 bytes out — so the
///      two numbers are directly comparable, and it shows what the reference's
///      deliberately proof-friendly shape costs.
contract Ripemd160GasTest is GasCrossCheck {
    Case[] internal cases;
    address internal refAddr;
    address internal evmification;

    /// @dev Gas the RIPEMD-160 precompile would charge: `600 + 120 * ceil(n / 32)`.
    function _precompileGas(uint256 len) private pure returns (uint256) {
        return 600 + 120 * ((len + 31) / 32);
    }

    function setUp() public override {
        super.setUp();
        refAddr = _etchReference("../Challenge/Ripemd160/Reference");
        evmification = address(new Ripemd160Deployed());

        // Challenge/Ripemd160/Scorer.lean, `vectors`, in order, each with the
        // gas that scorer reports for the reference bytecode.
        cases.push(Case("empty", "", 152450));
        cases.push(Case("abc", "abc", 152453));
        cases.push(Case("1-byte", Vectors.patterned(1), 152453));
        cases.push(Case("31-byte", Vectors.patterned(31), 152453));
        cases.push(Case("32-byte", Vectors.patterned(32), 152453));
        cases.push(Case("55-byte", Vectors.patterned(55), 152456));
        cases.push(Case("56-byte", Vectors.patterned(56), 300827));
        cases.push(Case("63-byte", Vectors.patterned(63), 300827));
        cases.push(Case("64-byte", Vectors.patterned(64), 300827));
        cases.push(Case("65-byte", Vectors.patterned(65), 300830));
        cases.push(Case("119-byte", Vectors.patterned(119), 300833));
        cases.push(Case("120-byte", Vectors.patterned(120), 449203));
        cases.push(Case("128-byte", Vectors.patterned(128), 449203));
        cases.push(Case("256-byte", Vectors.patterned(256), 745956));
        cases.push(Case("376-byte", Vectors.patterned(376), 1042710));
        cases.push(Case("1000-byte", Vectors.patterned(1000), 2378106));
        cases.push(Case("1000 a's", Vectors.repeated(1000, "a"), 2378106));
    }

    /// @dev The vector set must stay the one the Lean scorer scores; a dropped
    ///      or added vector would silently change the suite total.
    function test_vectors_match_scorer() public view {
        assertEq(cases.length, 17, "vector count");
        assertEq(pin.provedSize, 1671, "reference bytecode size");
        assertEq(refAddr.code.length, 1671, "etched code size");

        uint256[17] memory sizes =
            [uint256(0), 3, 1, 31, 32, 55, 56, 63, 64, 65, 119, 120, 128, 256, 376, 1000, 1000];
        for (uint256 i = 0; i < cases.length; i++) {
            assertEq(cases[i].input.length, sizes[i], cases[i].label);
        }
    }

    /// @dev A gas comparison is only meaningful if both sides compute the same
    ///      function, so the returned bytes are checked against the precompile
    ///      interface: twelve zero bytes then the digest.
    function test_reference_returns_precompile_result() public view {
        for (uint256 i = 0; i < cases.length; i++) {
            (, bytes memory ret) = _gas(refAddr, cases[i].input);
            assertEq(ret, abi.encodePacked(bytes12(0), ripemd160(cases[i].input)), cases[i].label);
        }
    }

    /// @notice The cross-check: revm must charge what `Scorer.lean` reports.
    function test_reference_gas_matches_lean_scorer() public view {
        uint256 leanTotal;
        uint256 forgeTotal;
        _header("RIPEMD-160 reference: Lean scorer vs revm");
        for (uint256 i = 0; i < cases.length; i++) {
            (uint256 gasUsed,) = _gas(refAddr, cases[i].input);
            _row(cases[i].label, cases[i].input.length, cases[i].leanGas, gasUsed);
            assertEq(gasUsed, cases[i].leanGas, cases[i].label);
            leanTotal += cases[i].leanGas;
            forgeTotal += gasUsed;
        }
        _row("all vectors", 0, leanTotal, forgeTotal);
        assertEq(forgeTotal, 9862146, "README suite total");
    }

    /// @dev The scorers score every vector from a clean and a dirty initial
    ///      state and report the same gas for both. Two representative vectors
    ///      are re-checked here against a dirtied account.
    function test_gas_is_state_independent() public {
        _assertGasIsStateIndependent(refAddr, cases[0].input, "empty");
        _assertGasIsStateIndependent(refAddr, cases[15].input, "1000-byte");
    }

    /// @dev The README's `vs precompile` ratio is a claim about the suite
    ///      totals; it is recomputed here from measured gas.
    function test_precompile_ratio_matches_readme() public view {
        uint256 referenceTotal;
        uint256 precompileTotal;
        for (uint256 i = 0; i < cases.length; i++) {
            (uint256 gasUsed,) = _gas(refAddr, cases[i].input);
            referenceTotal += gasUsed;

            (uint256 precompileGas,) = _gas(address(0x03), cases[i].input);
            assertEq(precompileGas, _precompileGas(cases[i].input.length), "precompile schedule");
            precompileTotal += precompileGas;
        }
        console2.log(
            string.concat(
                "reference vs precompile: ", _ratio(referenceTotal, precompileTotal), " (README: 419.31x)"
            )
        );
        assertEq(_ratio(referenceTotal, precompileTotal), "419.31x", "vs precompile ratio");
    }

    /// @notice Measures eth-act/evmification's Solidity implementation on the
    ///         same vectors, through the same probe.
    function test_evmification_comparison() public view {
        uint256 referenceTotal;
        uint256 evmificationTotal;
        uint256 precompileTotal;
        uint256 atOrBelowPrecompile;

        console2.log("");
        console2.log("RIPEMD-160 on the Lean scorer's vectors (frame gas, revm)");
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
            (uint256 precompileGas,) = _gas(address(0x03), cases[i].input);

            assertEq(ret, abi.encodePacked(bytes12(0), ripemd160(cases[i].input)), cases[i].label);

            console2.log(
                string.concat(
                    _rpad(cases[i].label, 30),
                    _rpad(vm.toString(cases[i].input.length), 7),
                    _rpad(vm.toString(referenceGas), 12),
                    _rpad(vm.toString(evmificationGas), 14),
                    vm.toString(precompileGas)
                )
            );
            if (evmificationGas <= precompileGas) atOrBelowPrecompile++;
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
        console2.log(
            string.concat(
                "evmification at or below the precompile's price on ",
                vm.toString(atOrBelowPrecompile),
                " of ",
                vm.toString(cases.length),
                " vectors"
            )
        );
    }
}
