---- MODULE sched1 ----

\* Demonstrates what happens if you run the scheduler without
\* a process table lock.
EXTENDS Naturals, TLC

CONSTANTS numProcs, numCPUS


\* procTable: a mapping from process number to active status and the CPU running it.
\* rrHead: a pointer to the next process to be run.
\* cpus: a mapping from CPU number to the process it is running.
VARIABLES procTable, rrHead, cpus


\* The proc table has a field that denotes whether the corresponding process
\* "is active". There is also a map back to the current CPU that is running the process.
\* In case it the process is inactive, the CPU field contains a "0".
TypeInfo ==
    /\ procTable \in [(1 .. numProcs) -> {0, 1} \X (0 .. numCPUS)]
    /\ rrHead \in (1 .. numProcs)
    /\ cpus \in [(1 .. numCPUS) -> (1 .. numProcs)]
    /\ numProcs > numCPUS

\* Initially, the first "numCPUS" processes are active, and the rrHead
\* is set to the very next slot available in the table.
Init ==
    /\ procTable = [p \in (1 .. numProcs) |->
                            IF p <= numCPUS THEN <<1, p>> ELSE <<0, 0>>]
    /\ rrHead = (numCPUS % numProcs) + 1
    /\ cpus = [c \in (1 .. numCPUS) |-> c]
    

\* The right way to update the rrHead: pick the next inactive process.
nextHead(currHead) ==
            (((CHOOSE p \in ((currHead + 1) .. (numProcs + currHead - 1)) :
                /\ procTable[((p - 1) % numProcs) + 1][1] = 0
                /\ (\A i \in ((currHead + 1) .. (numProcs + currHead - 1)) :
                    \/ procTable[((i - 1) % numProcs) + 1][1] = 1
                    \/ p <= i)) - 1) % numProcs) + 1


\* Simply move from one active process to another in RR fashion.
\* Note that we update the process table and increment all in one step.
\* Due to the atomicity of this procedure, even with multiple processors
\* There shouldn't be a bug.
Next ==
    \E proc \in (1 .. numProcs) :
        /\ procTable[proc][1] = 1 \* The proc is active.
        /\ procTable' = [p \in (1 .. numProcs) |->
                            IF p = proc THEN <<0, 0>>
                            ELSE IF p = rrHead THEN <<1, procTable[proc][2]>>
                            ELSE procTable[p]]
        /\ rrHead' = nextHead(rrHead)
        /\ cpus' = [c \in (1 .. numCPUS) |->
                        IF c = procTable[proc][2] THEN rrHead
                        ELSE cpus[c]]
\*        /\ Print(JavaTime, TRUE)
\*        /\ Print(rrHead, TRUE)
\*        /\ Print(nextHead(rrHead), TRUE)
\*        /\ Print(procTable, TRUE)
    
\* There should always be an active process.
ActiveExists ==
    /\ \E p \in (1 .. numProcs) :
        /\ procTable[p][1] = 1
        
\* True if there are two CPUs in the table that map to the same process.
SameProc ==
    /\ \E i \in (1 .. numCPUS) : (\E j \in (1 .. numCPUS) : i # j /\ cpus[i] = cpus[j])


\* No two CPUs should be running the same process
NotSameProc ==
    /\ ~ SameProc


        

========