module Peterson {
    /*
    We implement the following protocol for a 2-process mutex:
    
    Vars:
        interested: process -> bool
        turn: process
    
    Try(p: process)
        T1: interested[p] <- true
        T2: turn <- other(p)
        T3a: if turn = p: goto CS
        T3b: if interested[other(p)]: goto T3a

    Exit(p: process):
        E: interested[p] <- false
    
    */

    // Each process will be denoted by some ID
    type Process = int

    // 2-process version of the lock
    pure val processes = Set(0, 1)
    pure def other(p : Process): Process = if (p == 0) 1 else 0

    type Line = T1 | T2 | T3A | T3B | E

    var interested: Process -> bool
    var turn: Process
    var pc: Process -> Line

    action ExecT1(p: Process): bool = {
        all {
            pc.get(p) == T1,
            interested' = interested.set(p, true),
            pc' = pc.set(p, T2),
            turn' = turn
        }
    }

    action ExecT2(p: Process): bool = {
        all {
            pc.get(p) == T2,
            turn' = other(p),
            pc' = pc.set(p, T3A),
            interested' = interested
        }
    }

    action ExecT3a(p: Process): bool = {
        all {
            pc.get(p) == T3A,

            if (turn == p) {
                pc' = pc.set(p, E)
            } else {
                pc' = pc.set(p, T3B)
            },

            interested' = interested,
            turn' = turn
        }
    }

    action ExecT3b(p: Process): bool = {
        all {
            pc.get(p) == T3B,

            if (not(interested.get(other(p)))) {
                pc' = pc.set(p, E)
            } else {
                pc' = pc.set(p, T3A)
            },

            interested' = interested,
            turn' = turn
        }
    }

    action ExecE(p: Process): bool = {
        all {
            pc.get(p) == E,
            interested' = interested.set(p, false),
            pc' = pc.set(p, T1),
            turn' = turn
        }
    }

    action init = {
        all {
            interested' = processes.mapBy(p => false),
            turn' = 0,
            pc' = processes.mapBy(p => T1),
        }
    }

    action step = {
        nondet p = oneOf(processes)
        any {
            ExecT1(p),
            ExecT2(p),
            ExecT3a(p),
            ExecT3b(p),
            ExecE(p)
        }
    }

    // we generalize to n processes, but it would be easier to write not(pc.get(0) == E and pc.get(1) == E)
    val mutex = Set(processes.filter(p => pc.get(p) == E)).size() <= 1 // this verifies!

    // for the inductive invariant:
    // not sure how idiomatic this is, translating directly from TLA
    val i1 = processes.forall(p => (pc.get(p) == E and Set(T3A, T3B).contains(pc.get(other(p)))) implies turn == p)

    val i2 = processes.forall(p => (pc.get(p) != T1) implies interested.get(p))

    val TypeOK = all {
        turn.in(processes),
        pc.in(processes.setOfMaps(Set(T1, T2, T3A, T3B, E))), // not sure if there is a better way of doing this?
        interested.in(processes.setOfMaps(Set(true, false)))
    }

    // the inductive invariant is now:
    val inv = and {
        TypeOK,
        mutex,
        i1,
        i2
    }
}