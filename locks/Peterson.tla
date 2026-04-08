------------------------------ MODULE Peterson ------------------------------
EXTENDS Naturals, TLAPS

VARIABLES interested, turn, pc
vars == <<interested, turn, pc>>

Processes == {0, 1}
Not(p)  == IF p = 0 THEN 1 ELSE 0

Lines == {"T1", "T2", "T3A", "T3B", "E"}


Init ==
  /\ interested = [i \in Processes |-> FALSE]
  /\ turn = 0
  /\ pc = [p \in Processes |-> "T1"]


T1(p) ==
  /\ pc[p] = "T1"
  /\ interested' = [interested EXCEPT ![p] = TRUE]
  /\ pc'         = [pc EXCEPT ![p] = "T2"]
  /\ UNCHANGED <<turn>>

T2(p) ==
  /\ pc[p] = "T2"
  /\ turn' = Not(p)
  /\ pc'   = [pc EXCEPT ![p] = "T3A"]
  /\ UNCHANGED <<interested>>

T3A(p) ==
  /\ pc[p] = "T3A"
  /\ IF turn = p THEN
        /\ pc' = [pc EXCEPT ![p] = "E"]
     ELSE
        /\ pc' = [pc EXCEPT ![p] = "T3B"]
  /\ UNCHANGED <<interested, turn>>

T3B(p) ==
  /\ pc[p] = "T3B"
  /\ IF ~interested[Not(p)] THEN
        /\ pc' = [pc EXCEPT ![p] = "E"]
     ELSE
        /\ pc' = [pc EXCEPT ![p] = "T3A"]
  /\ UNCHANGED <<interested, turn>>

E(p) ==
  /\ pc[p] = "E"
  /\ interested' = [interested EXCEPT ![p] = FALSE]
  /\ pc'         = [pc EXCEPT ![p] = "T1"]
  /\ UNCHANGED <<turn>>


-------------------

Next ==
  \E p \in Processes :
       T1(p) \/ T2(p) \/ T3A(p) \/ T3B(p) \/ E(p)

Spec ==
  Init /\ [] [Next]_vars


Mutex ==
  ~(pc[0] = "E" /\ pc[1] = "E")

TypeOK ==
  /\ pc \in [Processes -> Lines]
  /\ turn \in Processes
  /\ interested \in [Processes -> {TRUE, FALSE}]

I1 == \A p \in Processes : (pc[p] = "E" /\ pc[Not(p)] \in {"T3A", "T3B"}) => turn = p
I2 == \A p \in Processes : (pc[p] # "T1") => interested[p]

Inv == Mutex /\ I1 /\ I2 /\ TypeOK
-------------------

LEMMA InitTypeOK == Init => TypeOK
    BY DEF Init, TypeOK, Lines, Processes

LEMMA NextTypeOK == TypeOK /\ [Next]_vars => TypeOK'
  <1> USE DEF TypeOK, Next, vars, T1, T2, T3A, T3B, E, Processes, Lines, Not
  <1> SUFFICES ASSUME TypeOK /\ [Next]_vars
               PROVE  TypeOK'
    OBVIOUS
  <1>1. (pc \in [Processes -> Lines])'
    OBVIOUS
  <1>2. (turn \in Processes)'
    OBVIOUS
  <1>3. (interested \in [Processes -> {TRUE, FALSE}])'
    OBVIOUS
  <1>4. QED
    BY <1>1, <1>2, <1>3 DEF TypeOK

THEOREM TypeSafety == Spec => []TypeOK
  <1> SUFFICES ASSUME Spec
               PROVE  []TypeOK
    OBVIOUS
  <1> QED
    BY PTL, InitTypeOK, NextTypeOK DEF Spec

LEMMA InitInv == Init => Inv
    BY DEF Init, Inv, Mutex, I1, I2, Processes

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> USE NextTypeOK DEF TypeOK, Next, vars, T1, T2, T3A, T3B, E, Processes, Lines, Not, Inv, Mutex, I1, I2
  <1> SUFFICES ASSUME Inv /\ [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <1>1. Mutex'
    OBVIOUS
  <1>2. I1'
    OBVIOUS
  <1>3. I2'
    OBVIOUS
  <1>4. TypeOK'
    OBVIOUS
  <1>5. QED
    BY <1>1, <1>2, <1>3, <1>4 DEF Inv
  
THEOREM AlwaysInv == Spec => []Inv
  BY PTL, InitInv, NextInv DEF Spec
  
THEOREM AlwaysMutex == Spec => []Mutex
  BY PTL, AlwaysInv DEF Mutex, Inv

===============================================================