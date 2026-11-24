The RSA path packs three scratch words into existing gaps and lowers its
highest live word from index 87 to index 86. This saves four gas on each of
the four RSA vectors in the public benchmark. The pinned execution scorer
passes all 44 vectors at 352,749 gas, 16 below the immediate parent.
