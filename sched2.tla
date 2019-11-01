---- MODULE sched2 ----

\* There are some number of processes that can be run, say numProcs. Each process table
\* entry is marked as NOT-RUNNABLE (it doesn't exist or it is asleep), RUNNABLE, or RUNNING.
\* A process that exists may transition while it is RUNNING to either NOT-RUNNABLE (it decides
\* to die or sleep), or can be pre-empted and transition to RUNNABLE. In both cases, the scheduler
\* will be invoked. A process entry marked as NOT-RUNNABLE can transition to RUNNABLE at any time.
\* This is the case if the task a process is waiting on completes (i.e. the process wakes up), or
\* a new process is spawned, and needs to be scheduled. A RUNNABLE process cannot transition to
\* NOT-RUNNABLE. Although this could happen via the "kill" command, in this model we will not allow it.
\*
\* The model will be instantiated as a snapshot in the middle of Xv6's operation. In other words, we
\* are not going to model the Xv6 startup routine, which includes (keep in mind this is after bootloading)
\* instantiating kernel memory, starting up the other processors and their associated data structures,
\* instantiating user memory, running the first user process, etc. Instead, we will assume that initially,
\* a single process exists that is running on the first CPU. Other processes may be spawned (and when they
\* are, we will take care to place them in particular places on the process table, so as to limit the
\* model checking state-space).
\*
\* According to the transition rules mentioned previously, it should now be possible to have no RUNNABLE
\* processes. This would happen if the only running process there was chose to die / sleep. It's also possible
\* for the process table to fill up completely. We don't need to worry about the process table to "overflow",
\* since we only allow (and the Xv6 only allows) a fixed maximum number of processes anyway.
\*
\* The procTable lock, the TLB, and kernel, user modes are also modeled.
\* 
\* These are the steps for pre-emption:
\* - A RUNNING process goes from user to kernel mode (the timer TRAP causes this).
\* - The process acquires (or tries to acquire) the ptable lock. If it is unavailable, then the process simply
\* waits. The process's state is still RUNNING.
\* - If the process acquires the ptable lock, it then changes its state from RUNNING to RUNNABLE. At this point,
\* it is the only process running the scheduler (it has acquired the ptable lock). The TLB is changed to reflect
\* the kernel's page table.
\* - The process, or now scheduler, finds a free process to run. There should be at least one (itself: it should
\* be in the RUNNABLE state). The process is chosen, the TLB is is refreshed (via loading %cr3), and the ptable
\* lock is released.
\* 
\* To create a new process, the ptable lock is acquired magically, and a process is spawned. The reason I'm going
\* with this approach is to cap the model checking state-space. In real life, a process may spawn another process
\* via "fork" or some other syscall. That call would then have to be modeled, and I'd rather not do that. It shouldn't
\* be too complex; it would involve modifying the ptable and setting up the new process's memory. But my goal isn't to
\* model check the "fork" syscall, it's to model check the scheduler. And so I'll pass.
\* 
\* The process spawned will take on the lowest ptable index entry available. This happens in the actual Xv6 scheduler,
\* and greatly benefits me by once again limiting the state-space.
\*
\* Finally, the steps for dying / sleeping are similar to the pre-emption steps. Once again, the process tries to acquire
\* the ptable lock, and when it finally does, it marks itself off as NOT-RUNNABLE instead. It then does everything else
\* from step three onwards described under pre-emption. The only difference is that there may not be a single process
\* to run. And what happens when there isn't? If the other process tried to sleep, it wouldn't be able to, since it
\* would require the ptable lock -- DEADLOCK! This is avoided in the way the scheduler algorithm works, described below.
\*
\* Information about the Scheduler Algorithm (Round Robin)
\* The scheduler runs the round robin algorithm to pick the next process to run. There isn't a global round robin "head",
\* that points at the next process to run. Instead, whenever the scheduler is run after the death / falling asleep
\* / pre-emption of a process, the search is performed starting at the process immediately after the unlucky process.
\* When there are no processes to run, the scheduler relinquishes the ptable lock briefly, before trying to starting to
\* search again. This allows another process to call the scheduler and do whatever crap. -- TODO: explain this properly.

EXTENDS Naturals, TLC

\* Probably going to run with numProcs as 4, numCPUs
\* set to 2.
CONSTANTS numProcs, numCPUs

\* The various process entry states:
CONSTANTS RUNNABLE, NOTRUNNABLE, RUNNING


\* procTable: a mapping from process number to process state and the CPU RUNNING it.
\* cpus: a mapping from CPU number to the process it is RUNNING.
\* pTableLock: a lock on the process table. When not held, 0.
               TODO: Make this lock reflect who's holding it?
\* tlb: a mapping from CPU to the page table the CPU is using. Kernel's (0) or a process's (PID).
VARIABLES procTable, cpus, pTableLock, tlb



\* The classes to which each variable belongs.
TypeInfo ==
    /\ procTable \in [(1 .. numProcs) -> {RUNNABLE, NOTRUNNABLE, RUNNING} \X (0 .. numCPUs)]
    /\ cpus \in [(1 .. numCPUs) -> (1 .. numProcs)]
    /\ numProcs > numCPUs
    /\ pTableLock \in {0, 1}
    /\ tlb \in [(1 .. numCPUs) -> (0 .. numProcs)]



\* Initially, only one process, the very first in the table, is active. All the other processes
\* don't exist. New processes will be magically spawned later.
Init ==
    /\ procTable = [p \in (1 .. numProcs) |->
                            IF p = 1 THEN <<RUNNING, p>> ELSE <<NOTRUNNABLE, 0>>]
    /\ cpus = [c \in (1 .. numCPUS) |->
                    IF c = 1 THEN 1 ELSE 0]
    

\* The right way to update the rrHead: pick the next inactive process.
\* BUG: This should actually include the PID that was just freed. Consider
\* the situation with four CPUs and five processes: The current rrHead points
\* to the free PID (which is the only free PID). Below, we are trying to choose
\* the next rrHead that excludes the current rrHead.
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


\* When there are more processes than there are CPUs, at least one
\* process must be inactive.
FreeExists ==
    \/ numProcs <= numCPUS
    \/ \E p \in (1 .. numProcs) : procTable[p][1] = 0


\* True if there are two CPUs in the table that map to the same process.
SameProc ==
    /\ \E i \in (1 .. numCPUS) : (\E j \in (1 .. numCPUS) : i # j /\ cpus[i] = cpus[j])


\* No two CPUs should be RUNNING the same process
NotSameProc ==
    /\ ~ SameProc


        

========