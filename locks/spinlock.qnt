module Spinlock {
    /*
    We implement the following protocol for a n-process mutex:

    Vars:
        X: bool
    
    Try(p: process)
        T: await CAS(X, false, true)
    
    Exit(p: process)
        E: X <- false
    */    

    // Each process will be denoted by some ID
    type Process = int

    type Line = T | E

    pure val proc_amount: int = 6 // the algorithm does not actually need knowing in advance, but it will make things easier
    pure val processes = 1.to(proc_amount)

    var X: bool
    var pc: Process -> Line

    action ExecT(p: Process): bool = {
        all {
            pc.get(p) == T,
            if (X == false) {
                all {
                    X' = true,
                    pc' = pc.set(p, E)
                }
            } else {
                all {
                    X' = X,
                    pc' = pc
                }
            }
        }
    }

    action ExecE(p: Process): bool = {
        all {
            pc.get(p) == E,
            X' = false,
            pc' = pc.set(p, T)
        }
    }

    action init = {
        all {
            X' = false,
            pc' = processes.mapBy(p => T)
        }
    }   

    action step = {
        nondet p = oneOf(processes)
        any {
            ExecT(p),
            ExecE(p)
        }
    }

    val mutex = processes.filter(p => pc.get(p) == E).size() <= 1

    // for the inductive invariant:
    val x_if_cs_full = processes.exists(p => pc.get(p) == E) implies X == true

    val TypeOK = all {
        pc.in(setOfMaps(processes, Set(T, E))),
        X.in(Set(true, false))
    }

    val inv = and {
        TypeOK,
        mutex,
        x_if_cs_full
    }
    
}