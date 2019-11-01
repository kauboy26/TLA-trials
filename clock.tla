---- MODULE clock ----

EXTENDS Naturals

VARIABLE hour


InitCond == /\ hour \in (0 .. 11)

TimeStep == /\ hour' = (hour + 1) % 12 

THEOREM InitCond /\ [][TimeStep]_hour => []InitCond

====