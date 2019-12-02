---- MODULE misscan ----

\* Just trying my own version of Missionaries - Cannibals.

\* I need a Set (that can contain duplicates) for both banks. If
\* the left set (where everybody starts) becomes empty, then that
\* means we are done.

EXTENDS Naturals, FiniteSets

\* Depends on Set miss != cans
CONSTANTS miss, cans

VARIABLES bank, boat


\* See Note 1
TypeInfo == /\ bank \in [{"l", "r"} -> SUBSET (miss \cup cans)]
            /\ boat \in {"l", "r"}

InitCond == /\ bank["l"] = miss \cup cans
            /\ bank["r"] = {}
            /\ boat = "l"

IsSideSafe(group) ==
        \/ Cardinality(group \cap miss) = 0
        \/ Cardinality(group \cap miss) >= Cardinality(group \cap cans)


OtherSide(side) == IF side = "l" THEN "r" ELSE "l"

CanM(group, side) == /\ boat = side
                     /\
                        \/ Cardinality(group) = 1
                        \/ Cardinality(group) = 2
                     /\ Cardinality(group) = Cardinality(bank[boat] \cap group)
                     /\ IsSideSafe(bank[boat] \ group)
                     /\ IsSideSafe(bank[OtherSide(boat)] \cup group)
                     



Move(group) ==
    LET newboat == OtherSide(boat)
    IN
        /\ boat' = newboat
        /\ bank' = [i \in {"l", "r"} |->
                        IF i = boat THEN (bank[boat] \ group) ELSE (bank[newboat] \cup group)]
                        \* See Note 2


Next == \E group \in SUBSET (miss \cup cans) :
               /\ CanM(group, boat)
               /\ Move(group)

Solved == Cardinality(bank["l"]) > 0

====