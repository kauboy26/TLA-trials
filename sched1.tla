---- MODULE sched1 ----

\* Demonstrates what happens if you run the scheduler without
\* a process table lock.
EXTENDS Naturals

CONSTANTS numProcs, numCPUS

VARIABLES procTable, rrHead, cpus

TypeInfo ==
    /\ procTable \in [(1 .. numProcs) -> ({0, 1} \X {0, 1})]
    /\ rrHead \in (1 .. numProcs)
    /\ cpus \in [(1 .. numCPUS) -> (1 .. numProcs)]

Init ==
    /\ procTable = [p \in (1 .. numProcs) |-> 0]
    /\ rrHead = 0





========