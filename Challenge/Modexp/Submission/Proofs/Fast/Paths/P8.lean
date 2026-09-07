import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 8 (instructions 1421..1468). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- The divisibility dispatcher at pc 1993. -/
def blk1421 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1421 .JUMPDEST,
   pushAt 1422 2 9344,
   opAt 1423 .MLOAD,
   opAt 1424 (.Dup ⟨0, by decide⟩),
   pushAt 1425 1 127,
   opAt 1426 .AND,
   opAt 1427 .ISZERO,
   opAt 1428 (.Swap ⟨0, by decide⟩),
   opAt 1429 .POP,
   pushAt 1430 2 3921,
   opAt 1431 .JUMPI]

/- The original one-core P8 body, entered after the dispatcher. -/
def blk1421Core :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1432 .JUMPDEST,
   opAt 1433 (.Dup ⟨3, by decide⟩),
   opAt 1434 (.Dup ⟨1, by decide⟩),
   opAt 1435 .MLOAD,
   opAt 1436 (.Dup ⟨1, by decide⟩),
   opAt 1437 (.Dup ⟨1, by decide⟩),
   opAt 1438 .MUL,
   opAt 1439 (.Swap ⟨1, by decide⟩),
   pushAt 1440 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 1441 (.Swap ⟨1, by decide⟩),
   opAt 1442 .MULMOD,
   opAt 1443 (.Dup ⟨1, by decide⟩),
   opAt 1444 (.Dup ⟨1, by decide⟩),
   opAt 1445 .LT,
   opAt 1446 (.Dup ⟨2, by decide⟩),
   opAt 1447 .ADD,
   opAt 1448 (.Swap ⟨0, by decide⟩),
   opAt 1449 .SUB,
   opAt 1450 (.Dup ⟨3, by decide⟩),
   opAt 1451 .MLOAD,
   opAt 1452 (.Swap ⟨1, by decide⟩),
   opAt 1453 (.Dup ⟨2, by decide⟩),
   opAt 1454 .ADD,
   opAt 1455 (.Swap ⟨1, by decide⟩),
   opAt 1456 (.Dup ⟨2, by decide⟩),
   opAt 1457 .LT,
   opAt 1458 .ADD,
   opAt 1459 (.Swap ⟨0, by decide⟩),
   opAt 1460 (.Dup ⟨4, by decide⟩),
   opAt 1461 .ADD,
   opAt 1462 (.Swap ⟨3, by decide⟩),
   opAt 1463 (.Dup ⟨4, by decide⟩),
   opAt 1464 .LT,
   opAt 1465 .ADD,
   opAt 1466 (.Swap ⟨2, by decide⟩),
   opAt 1467 (.Dup ⟨2, by decide⟩),
   opAt 1468 .MSTORE,
   pushAt 1469 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1470 .ADD,
   opAt 1471 (.Swap ⟨0, by decide⟩),
   pushAt 1472 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 1473 .ADD,
   opAt 1474 (.Swap ⟨0, by decide⟩),
   opAt 1475 (.Dup ⟨5, by decide⟩),
   opAt 1476 (.Dup ⟨1, by decide⟩),
   opAt 1477 .GT,
   pushAt 1478 2 2009,
   opAt 1479 .JUMPI]

/- The four-core P8 body at pc 3921. -/
def blk1421Unroll :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2597 .JUMPDEST,
   opAt 2598 (.Dup ⟨3, by decide⟩), opAt 2599 (.Dup ⟨1, by decide⟩),
   opAt 2600 .MLOAD, opAt 2601 (.Dup ⟨1, by decide⟩),
   opAt 2602 (.Dup ⟨1, by decide⟩), opAt 2603 .MUL,
   opAt 2604 (.Swap ⟨1, by decide⟩),
   pushAt 2605 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2606 (.Swap ⟨1, by decide⟩), opAt 2607 .MULMOD,
   opAt 2608 (.Dup ⟨1, by decide⟩), opAt 2609 (.Dup ⟨1, by decide⟩), opAt 2610 .LT,
   opAt 2611 (.Dup ⟨2, by decide⟩), opAt 2612 .ADD, opAt 2613 (.Swap ⟨0, by decide⟩),
   opAt 2614 .SUB, opAt 2615 (.Dup ⟨3, by decide⟩), opAt 2616 .MLOAD,
   opAt 2617 (.Swap ⟨1, by decide⟩), opAt 2618 (.Dup ⟨2, by decide⟩), opAt 2619 .ADD,
   opAt 2620 (.Swap ⟨1, by decide⟩), opAt 2621 (.Dup ⟨2, by decide⟩), opAt 2622 .LT,
   opAt 2623 .ADD, opAt 2624 (.Swap ⟨0, by decide⟩), opAt 2625 (.Dup ⟨4, by decide⟩),
   opAt 2626 .ADD, opAt 2627 (.Swap ⟨3, by decide⟩), opAt 2628 (.Dup ⟨4, by decide⟩),
   opAt 2629 .LT, opAt 2630 .ADD, opAt 2631 (.Swap ⟨2, by decide⟩),
   opAt 2632 (.Dup ⟨2, by decide⟩), opAt 2633 .MSTORE,
   pushAt 2634 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2635 .ADD, opAt 2636 (.Swap ⟨0, by decide⟩),
   pushAt 2637 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2638 .ADD, opAt 2639 (.Swap ⟨0, by decide⟩),
   opAt 2640 (.Dup ⟨3, by decide⟩), opAt 2641 (.Dup ⟨1, by decide⟩),
   opAt 2642 .MLOAD, opAt 2643 (.Dup ⟨1, by decide⟩),
   opAt 2644 (.Dup ⟨1, by decide⟩), opAt 2645 .MUL,
   opAt 2646 (.Swap ⟨1, by decide⟩),
   pushAt 2647 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2648 (.Swap ⟨1, by decide⟩), opAt 2649 .MULMOD,
   opAt 2650 (.Dup ⟨1, by decide⟩), opAt 2651 (.Dup ⟨1, by decide⟩), opAt 2652 .LT,
   opAt 2653 (.Dup ⟨2, by decide⟩), opAt 2654 .ADD, opAt 2655 (.Swap ⟨0, by decide⟩),
   opAt 2656 .SUB, opAt 2657 (.Dup ⟨3, by decide⟩), opAt 2658 .MLOAD,
   opAt 2659 (.Swap ⟨1, by decide⟩), opAt 2660 (.Dup ⟨2, by decide⟩), opAt 2661 .ADD,
   opAt 2662 (.Swap ⟨1, by decide⟩), opAt 2663 (.Dup ⟨2, by decide⟩), opAt 2664 .LT,
   opAt 2665 .ADD, opAt 2666 (.Swap ⟨0, by decide⟩), opAt 2667 (.Dup ⟨4, by decide⟩),
   opAt 2668 .ADD, opAt 2669 (.Swap ⟨3, by decide⟩), opAt 2670 (.Dup ⟨4, by decide⟩),
   opAt 2671 .LT, opAt 2672 .ADD, opAt 2673 (.Swap ⟨2, by decide⟩),
   opAt 2674 (.Dup ⟨2, by decide⟩), opAt 2675 .MSTORE,
   pushAt 2676 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2677 .ADD, opAt 2678 (.Swap ⟨0, by decide⟩),
   pushAt 2679 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2680 .ADD, opAt 2681 (.Swap ⟨0, by decide⟩),
   opAt 2682 (.Dup ⟨3, by decide⟩), opAt 2683 (.Dup ⟨1, by decide⟩),
   opAt 2684 .MLOAD, opAt 2685 (.Dup ⟨1, by decide⟩),
   opAt 2686 (.Dup ⟨1, by decide⟩), opAt 2687 .MUL,
   opAt 2688 (.Swap ⟨1, by decide⟩),
   pushAt 2689 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2690 (.Swap ⟨1, by decide⟩), opAt 2691 .MULMOD,
   opAt 2692 (.Dup ⟨1, by decide⟩), opAt 2693 (.Dup ⟨1, by decide⟩), opAt 2694 .LT,
   opAt 2695 (.Dup ⟨2, by decide⟩), opAt 2696 .ADD, opAt 2697 (.Swap ⟨0, by decide⟩),
   opAt 2698 .SUB, opAt 2699 (.Dup ⟨3, by decide⟩), opAt 2700 .MLOAD,
   opAt 2701 (.Swap ⟨1, by decide⟩), opAt 2702 (.Dup ⟨2, by decide⟩), opAt 2703 .ADD,
   opAt 2704 (.Swap ⟨1, by decide⟩), opAt 2705 (.Dup ⟨2, by decide⟩), opAt 2706 .LT,
   opAt 2707 .ADD, opAt 2708 (.Swap ⟨0, by decide⟩), opAt 2709 (.Dup ⟨4, by decide⟩),
   opAt 2710 .ADD, opAt 2711 (.Swap ⟨3, by decide⟩), opAt 2712 (.Dup ⟨4, by decide⟩),
   opAt 2713 .LT, opAt 2714 .ADD, opAt 2715 (.Swap ⟨2, by decide⟩),
   opAt 2716 (.Dup ⟨2, by decide⟩), opAt 2717 .MSTORE,
   pushAt 2718 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2719 .ADD, opAt 2720 (.Swap ⟨0, by decide⟩),
   pushAt 2721 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2722 .ADD, opAt 2723 (.Swap ⟨0, by decide⟩),
   opAt 2724 (.Dup ⟨3, by decide⟩), opAt 2725 (.Dup ⟨1, by decide⟩),
   opAt 2726 .MLOAD, opAt 2727 (.Dup ⟨1, by decide⟩),
   opAt 2728 (.Dup ⟨1, by decide⟩), opAt 2729 .MUL,
   opAt 2730 (.Swap ⟨1, by decide⟩),
   pushAt 2731 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2732 (.Swap ⟨1, by decide⟩), opAt 2733 .MULMOD,
   opAt 2734 (.Dup ⟨1, by decide⟩), opAt 2735 (.Dup ⟨1, by decide⟩), opAt 2736 .LT,
   opAt 2737 (.Dup ⟨2, by decide⟩), opAt 2738 .ADD, opAt 2739 (.Swap ⟨0, by decide⟩),
   opAt 2740 .SUB, opAt 2741 (.Dup ⟨3, by decide⟩), opAt 2742 .MLOAD,
   opAt 2743 (.Swap ⟨1, by decide⟩), opAt 2744 (.Dup ⟨2, by decide⟩), opAt 2745 .ADD,
   opAt 2746 (.Swap ⟨1, by decide⟩), opAt 2747 (.Dup ⟨2, by decide⟩), opAt 2748 .LT,
   opAt 2749 .ADD, opAt 2750 (.Swap ⟨0, by decide⟩), opAt 2751 (.Dup ⟨4, by decide⟩),
   opAt 2752 .ADD, opAt 2753 (.Swap ⟨3, by decide⟩), opAt 2754 (.Dup ⟨4, by decide⟩),
   opAt 2755 .LT, opAt 2756 .ADD, opAt 2757 (.Swap ⟨2, by decide⟩),
   opAt 2758 (.Dup ⟨2, by decide⟩), opAt 2759 .MSTORE,
   pushAt 2760 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2761 .ADD, opAt 2762 (.Swap ⟨0, by decide⟩),
   pushAt 2763 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2764 .ADD, opAt 2765 (.Swap ⟨0, by decide⟩),
   opAt 2766 (.Dup ⟨5, by decide⟩), opAt 2767 (.Dup ⟨1, by decide⟩),
   opAt 2768 .GT, pushAt 2769 2 3921, opAt 2770 .JUMPI,
   pushAt 2771 2 2155, opAt 2772 .JUMP]

/- The true branch ends at the conditional jump to the next four-core pass.
The false branch continues through the landing jump to P9. -/
def blk1421UnrollContinue := blk1421Unroll.take 174

def blk1421UnrollExit := blk1421Unroll

end Challenge.Modexp.Submission.Proofs.Fast
