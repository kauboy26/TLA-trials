---- MODULE squirrelcount ----


EXTENDS Naturals, FiniteSets
\* A concurrent counter with a broken lock. "num" below is
\* the number of counters.
\* Each counter performs a READ of a global count variable,
\* performs a local addition, and then WRITES the updated value
\* to the global count variable. As this is non-atomic, the
\* operation breaks.

CONSTANT num

VARIABLE counters, count, truth

TypeInfo ==
    /\ counters \in [(1 .. num) -> (0 .. 5) \X {0, 1}]
    /\ count \in (0 .. 25)
    /\ truth \in (0 .. 25)

Init ==
    /\ counters = [i \in (1 .. num) |-> <<0, 0>>]
    /\ count = 0
    /\ truth = 0

\* Assuming counter "i" is read-ready.
Read(i) ==
    /\ counters[i][2] = 0
    /\ counters' = [k \in (1 .. num) |->
                        IF k = i THEN <<count, 1>> ELSE counters[k]]
    /\ count' = count
    /\ truth' = truth
    
Write(i) ==
    /\ counters[i][2] = 1
    /\ count' = counters[i][1] + 1
    /\ truth' = truth + 1
    /\ counters' = [k \in (1 .. num) |->
                        IF k = i THEN <<0, 0>> ELSE counters[k]]

Next == \E i \in (1 .. num) :
            \/ Read(i)
            \/ Write(i)


Invariant ==
    /\ truth = count
    
====