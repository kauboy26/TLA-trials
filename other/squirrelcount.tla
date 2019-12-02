---- MODULE squirrelcount ----


EXTENDS Naturals, FiniteSets
\* A concurrent counter with a broken lock. "num" below is
\* the number of counters.
\* Each counter performs a READ of a global count variable,
\* performs a local addition, and then WRITES the updated value
\* to the global count variable. As this is non-atomic, the
\* operation breaks when two counters perform a READ concurrently
\* and then later write. This results in a lost update.

CONSTANT BLUE, RED, ADDING, READY, STATUS, VALUE, N
VARIABLES cameras, truth, datastore

TypeInfo ==
    /\ cameras \in [{BLUE, RED} -> {READY, ADDING} \X (0 .. N)]
    /\ truth \in (0 .. N)
    /\ datastore \in (0 .. N)

Init ==
    /\ cameras = [col \in {BLUE, RED} |->
                    <<READY, 0>>]
    /\ truth = 0
    /\ datastore = 0
    

Read ==
    \E cam \in {BLUE, RED}:
        /\ cameras[cam][STATUS] = READY
        /\ cameras' = [col \in {BLUE, RED} |->
            IF col = cam THEN <<ADDING, datastore>> ELSE cameras[col]]
        /\ UNCHANGED truth
        /\ UNCHANGED datastore

Store ==
    \E cam \in {BLUE, RED}:
        /\ cameras[cam][STATUS] = ADDING
        /\ datastore' = cameras[cam][VALUE] + 1
        /\ truth' = truth + 1
        /\ cameras' = [col \in {BLUE, RED} |->
            IF col = cam THEN <<READY, 0>> ELSE cameras[col]]

Next ==
    \/ Read
    \/ Store


        
InvariantTruthMatchesDatastore ==
    \/ \E cam \in {BLUE, RED}:
        cameras[cam][STATUS] = ADDING
    \/ truth = datastore                

====