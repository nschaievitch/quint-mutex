------------------------------ MODULE spinlock ------------------------------
(***************************************************************************
1. Proof for Spin Lock Mutex
 ***************************************************************************)

EXTENDS Naturals, Sequences, TLAPS

CONSTANT Pi
Lines == {"T", "E"}


VARIABLES X, pc
vars == << X, pc >>

Init ==
  /\ X = 0
  /\ pc = [pi \in Pi |-> "T"]

T(pi) ==
  /\ pc[pi] = "T"
  /\ IF X = 0 THEN
        /\ X' = 1
        /\ pc' = [pc EXCEPT ![pi] = "E"]
     ELSE
        /\ X' = 1
        /\ pc' = pc

E(pi) ==
  /\ pc[pi] = "E"
  /\ X' = 0
  /\ pc' = [pc EXCEPT ![pi] = "T"]

Next ==
  \E pi \in Pi : T(pi) \/ E(pi)

Spec ==
  Init /\ [] [Next]_vars
  
-------------------------------

(*
  At most one process is in "E".
*)
Mutex ==
  \A pi \in Pi : \A pj \in Pi :
      (pc[pi] = "E" /\ pc[pj] = "E") => pi = pj

(*
  If someone is in "E", then X = 1.
*)
XIfCSFull ==
  (\E pi \in Pi : pc[pi] = "E") => X = 1

(*
  Simple type invariant.
*)
TypeOK ==
  /\ X \in {0, 1}
  /\ pc \in [Pi -> Lines]

(*
  Main invariant to be checked under Spec.
*)

Inv == Mutex /\ XIfCSFull /\ TypeOK

LEMMA InitTypeSafety == Init => TypeOK
  <1> SUFFICES ASSUME Init
               PROVE  TypeOK
    OBVIOUS
  <1>1. pc \in [Pi -> Lines]
    BY DEF Init, Lines
  <1>2. X \in {0,1}
    BY DEF Init
  <1>3. QED
    BY <1>1, <1>2 DEF TypeOK

LEMMA NextTypeSafety == TypeOK /\ [Next]_vars => TypeOK' 
  <1> USE DEF TypeOK, Next, Lines, vars
  <1> SUFFICES ASSUME TypeOK, [Next]_vars
               PROVE  TypeOK'
    OBVIOUS
  <1>1. ASSUME NEW p \in Pi, T(p)
        PROVE TypeOK'
     BY <1>1 DEF T
  <1>2. ASSUME NEW p \in Pi, E(p)
        PROVE TypeOK'
     BY <1>2 DEF E
  <1>3. CASE UNCHANGED vars
    BY <1>3
  <1> QED
    BY <1>1, <1>2 DEF Next, TypeOK

THEOREM TypeSafety == Spec => []TypeOK
  <1> SUFFICES ASSUME Spec
               PROVE  []TypeOK
    OBVIOUS
  <1> QED
    BY PTL, NextTypeSafety, InitTypeSafety DEF Spec

LEMMA InitInv == Init => Inv
  <1> USE DEF TypeOK, Next, Inv, Mutex, XIfCSFull, TypeOK
  <1> SUFFICES ASSUME Init
               PROVE  Inv
    OBVIOUS
  <1> QED
    <2>1. Mutex
      BY DEF Init
    <2>2. XIfCSFull
      BY DEF Init
    <2>3. TypeOK
      BY InitTypeSafety
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF Inv
    
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> USE DEF Mutex, XIfCSFull, TypeOK, Next, Inv, T, E
  <1> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <1>1. ASSUME NEW pi \in Pi,
               T(pi)
        PROVE  Inv'
    <2>1. USE <1>1
    <2>2. Mutex'
        OBVIOUS
    <2>3. XIfCSFull'
        OBVIOUS
    <2>4. TypeOK'
        BY NextTypeSafety
    <2>5. QED
      BY <2>2, <2>3, <2>4 DEF Inv
  <1>2. ASSUME NEW pi \in Pi,
               E(pi)
        PROVE  Inv'
    <2> USE <1>2
    <2>1. Mutex'
        OBVIOUS
    <2>2. XIfCSFull'
        OBVIOUS
    <2>3. TypeOK'
        BY NextTypeSafety
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF Inv
  <1>3. CASE UNCHANGED vars
    BY <1>3 DEF vars
  <1>4. QED
    BY <1>1, <1>2, <1>3 DEF Next
    
THEOREM AlwaysInv == Spec => []Inv
  BY PTL, InitInv, NextInv DEF Spec
  
THEOREM AlwaysMutex == Spec => []Mutex
  BY PTL, AlwaysInv DEF Inv, Mutex
  
=============================================================================
