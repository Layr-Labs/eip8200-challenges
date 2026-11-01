import Challenge.Modexp.Submission.Proofs.Cycle.KernelContract
    set_option warningAsError true
    set_option linter.unusedVariables false
    set_option maxRecDepth 20000
    set_option maxHeartbeats 6000000
    namespace CycleSubmission.WordHistory
    open EvmSemantics CycleSubmission.WordArithmetic CycleSubmission.ColumnWords
    open CycleSubmission.KernelContract
    
def squareC0 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := UInt256.ofNat 0

def squareQ0 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (inv * ((a 0) * (a 0))))

def squareC1 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (n 0) (squareQ0 inv a b n) P) + (UInt256.mulMod (a 0) (a 0) P)) P)

def squareQ1 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) ((((squareQ0 inv a b n) * (n 1)) + ((squareC1 inv a b n) + (((a 1) * (a 0)) + ((a 1) * (a 0))))) * inv))

def squareC2 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (squareQ1 inv a b n) (n 0) P) + ((UInt256.mulMod (squareQ0 inv a b n) (n 1) P) + ((squareC1 inv a b n) + ((UInt256.mulMod (a 1) (a 0) P) + (UInt256.mulMod (a 1) (a 0) P))))) P)

def squareQ2 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) ((((squareQ1 inv a b n) * (n 1)) + (((squareQ0 inv a b n) * (n 2)) + (((a 1) * (a 1)) + ((squareC2 inv a b n) + (((a 2) * (a 0)) + ((a 2) * (a 0))))))) * inv))

def squareC3 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (squareQ2 inv a b n) (n 0) P) + ((UInt256.mulMod (squareQ1 inv a b n) (n 1) P) + ((UInt256.mulMod (squareQ0 inv a b n) (n 2) P) + ((UInt256.mulMod (a 1) (a 1) P) + ((squareC2 inv a b n) + ((UInt256.mulMod (a 2) (a 0) P) + (UInt256.mulMod (a 2) (a 0) P))))))) P)

def squareQ3 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) ((((squareQ2 inv a b n) * (n 1)) + (((squareQ1 inv a b n) * (n 2)) + (((squareQ0 inv a b n) * (n 3)) + ((squareC3 inv a b n) + ((((a 1) * (a 2)) + ((a 3) * (a 0))) + (((a 1) * (a 2)) + ((a 3) * (a 0)))))))) * inv))

def squareC4 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (squareQ3 inv a b n) (n 0) P) + ((UInt256.mulMod (squareQ2 inv a b n) (n 1) P) + ((UInt256.mulMod (squareQ1 inv a b n) (n 2) P) + ((UInt256.mulMod (squareQ0 inv a b n) (n 3) P) + ((squareC3 inv a b n) + (((UInt256.mulMod (a 1) (a 2) P) + (UInt256.mulMod (a 3) (a 0) P)) + ((UInt256.mulMod (a 1) (a 2) P) + (UInt256.mulMod (a 3) (a 0) P)))))))) P)

def squareQ4 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) ((((squareQ3 inv a b n) * (n 1)) + (((squareQ2 inv a b n) * (n 2)) + (((squareQ1 inv a b n) * (n 3)) + (((squareQ0 inv a b n) * (n 4)) + (((a 2) * (a 2)) + ((squareC4 inv a b n) + ((((a 1) * (a 3)) + ((a 4) * (a 0))) + (((a 1) * (a 3)) + ((a 4) * (a 0)))))))))) * inv))

def squareC5 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (squareQ4 inv a b n) (n 0) P) + ((UInt256.mulMod (squareQ3 inv a b n) (n 1) P) + ((UInt256.mulMod (squareQ2 inv a b n) (n 2) P) + ((UInt256.mulMod (squareQ1 inv a b n) (n 3) P) + ((UInt256.mulMod (squareQ0 inv a b n) (n 4) P) + ((UInt256.mulMod (a 2) (a 2) P) + ((squareC4 inv a b n) + (((UInt256.mulMod (a 1) (a 3) P) + (UInt256.mulMod (a 4) (a 0) P)) + ((UInt256.mulMod (a 1) (a 3) P) + (UInt256.mulMod (a 4) (a 0) P)))))))))) P)

def squareQ5 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) ((((squareQ4 inv a b n) * (n 1)) + (((squareQ3 inv a b n) * (n 2)) + (((squareQ2 inv a b n) * (n 3)) + (((squareQ1 inv a b n) * (n 4)) + (((squareQ0 inv a b n) * (n 5)) + ((squareC5 inv a b n) + ((((a 2) * (a 3)) + (((a 1) * (a 4)) + ((a 5) * (a 0)))) + (((a 2) * (a 3)) + (((a 1) * (a 4)) + ((a 5) * (a 0))))))))))) * inv))

def squareC6 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (squareQ5 inv a b n) (n 0) P) + ((UInt256.mulMod (squareQ4 inv a b n) (n 1) P) + ((UInt256.mulMod (squareQ3 inv a b n) (n 2) P) + ((UInt256.mulMod (squareQ2 inv a b n) (n 3) P) + ((UInt256.mulMod (squareQ1 inv a b n) (n 4) P) + ((UInt256.mulMod (squareQ0 inv a b n) (n 5) P) + ((squareC5 inv a b n) + (((UInt256.mulMod (a 2) (a 3) P) + ((UInt256.mulMod (a 1) (a 4) P) + (UInt256.mulMod (a 5) (a 0) P))) + ((UInt256.mulMod (a 2) (a 3) P) + ((UInt256.mulMod (a 1) (a 4) P) + (UInt256.mulMod (a 5) (a 0) P))))))))))) P)

def squareQ6 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) ((((squareQ5 inv a b n) * (n 1)) + (((squareQ4 inv a b n) * (n 2)) + (((squareQ3 inv a b n) * (n 3)) + (((squareQ2 inv a b n) * (n 4)) + (((squareQ1 inv a b n) * (n 5)) + (((squareQ0 inv a b n) * (n 6)) + (((a 3) * (a 3)) + ((squareC6 inv a b n) + ((((a 2) * (a 4)) + (((a 1) * (a 5)) + ((a 6) * (a 0)))) + (((a 2) * (a 4)) + (((a 1) * (a 5)) + ((a 6) * (a 0))))))))))))) * inv))

def squareC7 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (squareQ6 inv a b n) (n 0) P) + ((UInt256.mulMod (squareQ5 inv a b n) (n 1) P) + ((UInt256.mulMod (squareQ4 inv a b n) (n 2) P) + ((UInt256.mulMod (squareQ3 inv a b n) (n 3) P) + ((UInt256.mulMod (squareQ2 inv a b n) (n 4) P) + ((UInt256.mulMod (squareQ1 inv a b n) (n 5) P) + ((UInt256.mulMod (squareQ0 inv a b n) (n 6) P) + ((UInt256.mulMod (a 3) (a 3) P) + ((squareC6 inv a b n) + (((UInt256.mulMod (a 2) (a 4) P) + ((UInt256.mulMod (a 1) (a 5) P) + (UInt256.mulMod (a 6) (a 0) P))) + ((UInt256.mulMod (a 2) (a 4) P) + ((UInt256.mulMod (a 1) (a 5) P) + (UInt256.mulMod (a 6) (a 0) P))))))))))))) P)

def squareQ7 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) ((((squareQ6 inv a b n) * (n 1)) + (((squareQ5 inv a b n) * (n 2)) + (((squareQ4 inv a b n) * (n 3)) + (((squareQ3 inv a b n) * (n 4)) + (((squareQ2 inv a b n) * (n 5)) + (((squareQ1 inv a b n) * (n 6)) + (((n 7) * (squareQ0 inv a b n)) + ((squareC7 inv a b n) + ((((a 3) * (a 4)) + (((a 2) * (a 5)) + (((a 6) * (a 1)) + ((a 7) * (a 0))))) + (((a 3) * (a 4)) + (((a 2) * (a 5)) + (((a 6) * (a 1)) + ((a 7) * (a 0)))))))))))))) * inv))

def squareC8 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (squareQ7 inv a b n) (n 0) P) + ((UInt256.mulMod (squareQ6 inv a b n) (n 1) P) + ((UInt256.mulMod (squareQ5 inv a b n) (n 2) P) + ((UInt256.mulMod (squareQ4 inv a b n) (n 3) P) + ((UInt256.mulMod (squareQ3 inv a b n) (n 4) P) + ((UInt256.mulMod (squareQ2 inv a b n) (n 5) P) + ((UInt256.mulMod (squareQ1 inv a b n) (n 6) P) + ((UInt256.mulMod (n 7) (squareQ0 inv a b n) P) + ((squareC7 inv a b n) + (((UInt256.mulMod (a 3) (a 4) P) + ((UInt256.mulMod (a 2) (a 5) P) + ((UInt256.mulMod (a 1) (a 6) P) + (UInt256.mulMod (a 7) (a 0) P)))) + ((UInt256.mulMod (a 3) (a 4) P) + ((UInt256.mulMod (a 2) (a 5) P) + ((UInt256.mulMod (a 1) (a 6) P) + (UInt256.mulMod (a 7) (a 0) P)))))))))))))) P)

def squareQ8 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (inv * (((squareQ7 inv a b n) * (n 1)) + (((squareQ6 inv a b n) * (n 2)) + (((squareQ5 inv a b n) * (n 3)) + (((squareQ4 inv a b n) * (n 4)) + (((squareQ3 inv a b n) * (n 5)) + (((squareQ2 inv a b n) * (n 6)) + (((n 7) * (squareQ1 inv a b n)) + (((n 8) * (squareQ0 inv a b n)) + (((a 4) * (a 4)) + ((squareC8 inv a b n) + ((((a 3) * (a 5)) + (((a 2) * (a 6)) + (((a 7) * (a 1)) + ((a 8) * (a 0))))) + (((a 3) * (a 5)) + (((a 2) * (a 6)) + (((a 7) * (a 1)) + ((a 8) * (a 0))))))))))))))))))

def squareC9 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (n 0) (squareQ8 inv a b n) P) + ((UInt256.mulMod (squareQ7 inv a b n) (n 1) P) + ((UInt256.mulMod (squareQ6 inv a b n) (n 2) P) + ((UInt256.mulMod (squareQ5 inv a b n) (n 3) P) + ((UInt256.mulMod (squareQ4 inv a b n) (n 4) P) + ((UInt256.mulMod (squareQ3 inv a b n) (n 5) P) + ((UInt256.mulMod (squareQ2 inv a b n) (n 6) P) + ((UInt256.mulMod (n 7) (squareQ1 inv a b n) P) + ((UInt256.mulMod (a 4) (a 4) P) + ((UInt256.mulMod (n 8) (squareQ0 inv a b n) P) + ((squareC8 inv a b n) + (((UInt256.mulMod (a 3) (a 5) P) + ((UInt256.mulMod (a 2) (a 6) P) + ((UInt256.mulMod (a 1) (a 7) P) + (UInt256.mulMod (a 8) (a 0) P)))) + ((UInt256.mulMod (a 3) (a 5) P) + ((UInt256.mulMod (a 2) (a 6) P) + ((UInt256.mulMod (a 1) (a 7) P) + (UInt256.mulMod (a 8) (a 0) P)))))))))))))))) P)

def squareD0 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (((squareQ8 inv a b n) * (n 1)) + (((squareQ7 inv a b n) * (n 2)) + (((squareQ6 inv a b n) * (n 3)) + (((squareQ5 inv a b n) * (n 4)) + (((squareQ4 inv a b n) * (n 5)) + (((squareQ3 inv a b n) * (n 6)) + (((n 7) * (squareQ2 inv a b n)) + (((n 8) * (squareQ1 inv a b n)) + ((squareC9 inv a b n) + ((((a 4) * (a 5)) + (((a 3) * (a 6)) + (((a 2) * (a 7)) + ((a 8) * (a 1))))) + (((a 4) * (a 5)) + (((a 3) * (a 6)) + (((a 2) * (a 7)) + ((a 8) * (a 1))))))))))))))))

def squareC10 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (CycleSubmission.DirectRecovery.carry ((UInt256.mulMod (squareQ8 inv a b n) (n 1) P) + ((UInt256.mulMod (squareQ7 inv a b n) (n 2) P) + ((UInt256.mulMod (squareQ6 inv a b n) (n 3) P) + ((UInt256.mulMod (squareQ5 inv a b n) (n 4) P) + ((UInt256.mulMod (squareQ4 inv a b n) (n 5) P) + ((UInt256.mulMod (squareQ3 inv a b n) (n 6) P) + ((UInt256.mulMod (n 7) (squareQ2 inv a b n) P) + ((UInt256.mulMod (n 8) (squareQ1 inv a b n) P) + ((squareC9 inv a b n) + (((UInt256.mulMod (a 4) (a 5) P) + ((UInt256.mulMod (a 3) (a 6) P) + ((UInt256.mulMod (a 2) (a 7) P) + (UInt256.mulMod (a 8) (a 1) P)))) + ((UInt256.mulMod (a 4) (a 5) P) + ((UInt256.mulMod (a 3) (a 6) P) + ((UInt256.mulMod (a 2) (a 7) P) + (UInt256.mulMod (a 8) (a 1) P)))))))))))))) (((squareQ8 inv a b n) * (n 1)) + (((squareQ7 inv a b n) * (n 2)) + (((squareQ6 inv a b n) * (n 3)) + (((squareQ5 inv a b n) * (n 4)) + (((squareQ4 inv a b n) * (n 5)) + (((squareQ3 inv a b n) * (n 6)) + (((n 7) * (squareQ2 inv a b n)) + (((n 8) * (squareQ1 inv a b n)) + ((squareC9 inv a b n) + ((((a 4) * (a 5)) + (((a 3) * (a 6)) + (((a 2) * (a 7)) + ((a 8) * (a 1))))) + (((a 4) * (a 5)) + (((a 3) * (a 6)) + (((a 2) * (a 7)) + ((a 8) * (a 1))))))))))))))))

def squareD1 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (((squareQ8 inv a b n) * (n 2)) + (((n 3) * (squareQ7 inv a b n)) + (((squareQ6 inv a b n) * (n 4)) + (((squareQ5 inv a b n) * (n 5)) + (((squareQ4 inv a b n) * (n 6)) + (((n 7) * (squareQ3 inv a b n)) + (((n 8) * (squareQ2 inv a b n)) + (((a 5) * (a 5)) + ((squareC10 inv a b n) + ((((a 4) * (a 6)) + (((a 3) * (a 7)) + ((a 8) * (a 2)))) + (((a 4) * (a 6)) + (((a 3) * (a 7)) + ((a 8) * (a 2)))))))))))))))

def squareC11 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (CycleSubmission.DirectRecovery.carry ((UInt256.mulMod (squareQ8 inv a b n) (n 2) P) + ((UInt256.mulMod (squareQ7 inv a b n) (n 3) P) + ((UInt256.mulMod (squareQ6 inv a b n) (n 4) P) + ((UInt256.mulMod (squareQ5 inv a b n) (n 5) P) + ((UInt256.mulMod (squareQ4 inv a b n) (n 6) P) + ((UInt256.mulMod (n 7) (squareQ3 inv a b n) P) + ((UInt256.mulMod (n 8) (squareQ2 inv a b n) P) + ((UInt256.mulMod (a 5) (a 5) P) + ((squareC10 inv a b n) + (((UInt256.mulMod (a 4) (a 6) P) + ((UInt256.mulMod (a 3) (a 7) P) + (UInt256.mulMod (a 8) (a 2) P))) + ((UInt256.mulMod (a 4) (a 6) P) + ((UInt256.mulMod (a 3) (a 7) P) + (UInt256.mulMod (a 8) (a 2) P))))))))))))) (((squareQ8 inv a b n) * (n 2)) + (((n 3) * (squareQ7 inv a b n)) + (((squareQ6 inv a b n) * (n 4)) + (((squareQ5 inv a b n) * (n 5)) + (((squareQ4 inv a b n) * (n 6)) + (((n 7) * (squareQ3 inv a b n)) + (((n 8) * (squareQ2 inv a b n)) + (((a 5) * (a 5)) + ((squareC10 inv a b n) + ((((a 4) * (a 6)) + (((a 3) * (a 7)) + ((a 8) * (a 2)))) + (((a 4) * (a 6)) + (((a 3) * (a 7)) + ((a 8) * (a 2)))))))))))))))

def squareD2 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (((squareQ8 inv a b n) * (n 3)) + (((n 4) * (squareQ7 inv a b n)) + (((squareQ6 inv a b n) * (n 5)) + (((squareQ5 inv a b n) * (n 6)) + (((n 7) * (squareQ4 inv a b n)) + (((n 8) * (squareQ3 inv a b n)) + ((squareC11 inv a b n) + ((((a 5) * (a 6)) + (((a 4) * (a 7)) + ((a 8) * (a 3)))) + (((a 5) * (a 6)) + (((a 4) * (a 7)) + ((a 8) * (a 3)))))))))))))

def squareC12 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (CycleSubmission.DirectRecovery.carry ((UInt256.mulMod (squareQ8 inv a b n) (n 3) P) + ((UInt256.mulMod (squareQ7 inv a b n) (n 4) P) + ((UInt256.mulMod (squareQ6 inv a b n) (n 5) P) + ((UInt256.mulMod (squareQ5 inv a b n) (n 6) P) + ((UInt256.mulMod (n 7) (squareQ4 inv a b n) P) + ((UInt256.mulMod (n 8) (squareQ3 inv a b n) P) + ((squareC11 inv a b n) + (((UInt256.mulMod (a 5) (a 6) P) + ((UInt256.mulMod (a 4) (a 7) P) + (UInt256.mulMod (a 8) (a 3) P))) + ((UInt256.mulMod (a 5) (a 6) P) + ((UInt256.mulMod (a 4) (a 7) P) + (UInt256.mulMod (a 8) (a 3) P))))))))))) (((squareQ8 inv a b n) * (n 3)) + (((n 4) * (squareQ7 inv a b n)) + (((squareQ6 inv a b n) * (n 5)) + (((squareQ5 inv a b n) * (n 6)) + (((n 7) * (squareQ4 inv a b n)) + (((n 8) * (squareQ3 inv a b n)) + ((squareC11 inv a b n) + ((((a 5) * (a 6)) + (((a 4) * (a 7)) + ((a 8) * (a 3)))) + (((a 5) * (a 6)) + (((a 4) * (a 7)) + ((a 8) * (a 3)))))))))))))

def squareD3 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (((squareQ8 inv a b n) * (n 4)) + (((n 5) * (squareQ7 inv a b n)) + (((squareQ6 inv a b n) * (n 6)) + (((n 7) * (squareQ5 inv a b n)) + (((n 8) * (squareQ4 inv a b n)) + (((a 6) * (a 6)) + ((squareC12 inv a b n) + ((((a 5) * (a 7)) + ((a 8) * (a 4))) + (((a 5) * (a 7)) + ((a 8) * (a 4))))))))))))

def squareC13 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (CycleSubmission.DirectRecovery.carry ((UInt256.mulMod (squareQ8 inv a b n) (n 4) P) + ((UInt256.mulMod (n 5) (squareQ7 inv a b n) P) + ((UInt256.mulMod (squareQ6 inv a b n) (n 6) P) + ((UInt256.mulMod (n 7) (squareQ5 inv a b n) P) + ((UInt256.mulMod (n 8) (squareQ4 inv a b n) P) + ((UInt256.mulMod (a 6) (a 6) P) + ((squareC12 inv a b n) + (((UInt256.mulMod (a 5) (a 7) P) + (UInt256.mulMod (a 8) (a 4) P)) + ((UInt256.mulMod (a 5) (a 7) P) + (UInt256.mulMod (a 8) (a 4) P)))))))))) (((squareQ8 inv a b n) * (n 4)) + (((n 5) * (squareQ7 inv a b n)) + (((squareQ6 inv a b n) * (n 6)) + (((n 7) * (squareQ5 inv a b n)) + (((n 8) * (squareQ4 inv a b n)) + (((a 6) * (a 6)) + ((squareC12 inv a b n) + ((((a 5) * (a 7)) + ((a 8) * (a 4))) + (((a 5) * (a 7)) + ((a 8) * (a 4))))))))))))

def squareD4 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (((squareQ8 inv a b n) * (n 5)) + (((n 6) * (squareQ7 inv a b n)) + (((n 7) * (squareQ6 inv a b n)) + (((n 8) * (squareQ5 inv a b n)) + ((squareC13 inv a b n) + ((((a 6) * (a 7)) + ((a 8) * (a 5))) + (((a 6) * (a 7)) + ((a 8) * (a 5))))))))))

def squareC14 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (CycleSubmission.DirectRecovery.carry ((UInt256.mulMod (squareQ8 inv a b n) (n 5) P) + ((UInt256.mulMod (squareQ7 inv a b n) (n 6) P) + ((UInt256.mulMod (n 7) (squareQ6 inv a b n) P) + ((UInt256.mulMod (n 8) (squareQ5 inv a b n) P) + ((squareC13 inv a b n) + (((UInt256.mulMod (a 6) (a 7) P) + (UInt256.mulMod (a 8) (a 5) P)) + ((UInt256.mulMod (a 6) (a 7) P) + (UInt256.mulMod (a 8) (a 5) P)))))))) (((squareQ8 inv a b n) * (n 5)) + (((n 6) * (squareQ7 inv a b n)) + (((n 7) * (squareQ6 inv a b n)) + (((n 8) * (squareQ5 inv a b n)) + ((squareC13 inv a b n) + ((((a 6) * (a 7)) + ((a 8) * (a 5))) + (((a 6) * (a 7)) + ((a 8) * (a 5))))))))))

def squareD5 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (((squareQ8 inv a b n) * (n 6)) + (((n 7) * (squareQ7 inv a b n)) + (((n 8) * (squareQ6 inv a b n)) + (((a 7) * (a 7)) + ((squareC14 inv a b n) + (((a 8) * (a 6)) + ((a 8) * (a 6)))))))))

def squareC15 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (CycleSubmission.DirectRecovery.carry ((UInt256.mulMod (n 6) (squareQ8 inv a b n) P) + ((UInt256.mulMod (n 7) (squareQ7 inv a b n) P) + ((UInt256.mulMod (n 8) (squareQ6 inv a b n) P) + ((UInt256.mulMod (a 7) (a 7) P) + ((squareC14 inv a b n) + ((UInt256.mulMod (a 8) (a 6) P) + (UInt256.mulMod (a 8) (a 6) P))))))) (((squareQ8 inv a b n) * (n 6)) + (((n 7) * (squareQ7 inv a b n)) + (((n 8) * (squareQ6 inv a b n)) + (((a 7) * (a 7)) + ((squareC14 inv a b n) + (((a 8) * (a 6)) + ((a 8) * (a 6)))))))))

def squareD6 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (((n 7) * (squareQ8 inv a b n)) + (((n 8) * (squareQ7 inv a b n)) + ((squareC15 inv a b n) + (((a 8) * (a 7)) + ((a 8) * (a 7)))))))

def squareC16 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (CycleSubmission.DirectRecovery.carry ((UInt256.mulMod (n 7) (squareQ8 inv a b n) P) + ((UInt256.mulMod (n 8) (squareQ7 inv a b n) P) + ((squareC15 inv a b n) + ((UInt256.mulMod (a 8) (a 7) P) + (UInt256.mulMod (a 8) (a 7) P))))) (((n 7) * (squareQ8 inv a b n)) + (((n 8) * (squareQ7 inv a b n)) + ((squareC15 inv a b n) + (((a 8) * (a 7)) + ((a 8) * (a 7)))))))

def squareD7 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (((squareQ8 inv a b n) * (n 8)) + ((squareC16 inv a b n) + ((a 8) * (a 8)))))

def squareC17 (inv : UInt256) (a b n : Nat → UInt256) : UInt256 := (CycleSubmission.DirectRecovery.carry ((UInt256.mulMod (n 8) (squareQ8 inv a b n) P) + ((squareC16 inv a b n) + (UInt256.mulMod (a 8) (a 8) P))) (((squareQ8 inv a b n) * (n 8)) + ((squareC16 inv a b n) + ((a 8) * (a 8)))))

def squareq (inv : UInt256) (a b n : Nat → UInt256) (i : Nat) : UInt256 :=
  match i with
  | 0 => squareQ0 inv a b n
  | 1 => squareQ1 inv a b n
  | 2 => squareQ2 inv a b n
  | 3 => squareQ3 inv a b n
  | 4 => squareQ4 inv a b n
  | 5 => squareQ5 inv a b n
  | 6 => squareQ6 inv a b n
  | 7 => squareQ7 inv a b n
  | 8 => squareQ8 inv a b n
  | _ => UInt256.ofNat 0

def squarec (inv : UInt256) (a b n : Nat → UInt256) (i : Nat) : UInt256 :=
  match i with
  | 0 => squareC0 inv a b n
  | 1 => squareC1 inv a b n
  | 2 => squareC2 inv a b n
  | 3 => squareC3 inv a b n
  | 4 => squareC4 inv a b n
  | 5 => squareC5 inv a b n
  | 6 => squareC6 inv a b n
  | 7 => squareC7 inv a b n
  | 8 => squareC8 inv a b n
  | 9 => squareC9 inv a b n
  | 10 => squareC10 inv a b n
  | 11 => squareC11 inv a b n
  | 12 => squareC12 inv a b n
  | 13 => squareC13 inv a b n
  | 14 => squareC14 inv a b n
  | 15 => squareC15 inv a b n
  | 16 => squareC16 inv a b n
  | 17 => squareC17 inv a b n
  | _ => UInt256.ofNat 0

def squared (inv : UInt256) (a b n : Nat → UInt256) (i : Nat) : UInt256 :=
  match i with
  | 0 => squareD0 inv a b n
  | 1 => squareD1 inv a b n
  | 2 => squareD2 inv a b n
  | 3 => squareD3 inv a b n
  | 4 => squareD4 inv a b n
  | 5 => squareD5 inv a b n
  | 6 => squareD6 inv a b n
  | 7 => squareD7 inv a b n
  | 8 => squareC17 inv a b n
  | _ => UInt256.ofNat 0

def squareTrace (inv : UInt256) (a b n : Nat → UInt256) : Trace .square inv a b n where
      q := squareq inv a b n
      c := squarec inv a b n
      d := squared inv a b n
      zero := rfl
      quotient := by intro i hi; interval_cases i <;> rfl
      carry := by intro i hi; interval_cases i <;> rfl
      digit := by intro i h9 h17; interval_cases i <;> rfl
      top := rfl
    #print axioms squareTrace
    end CycleSubmission.WordHistory
    