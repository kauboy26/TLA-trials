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
\*                TODO: Make this lock reflect who's holding it?
\* tlb: a mapping from CPU to the page table the CPU is using. Kernel's (0) or a process's (PID).
\* scheduling: denotes when the scheduler is active, 0 when inactive. Otherwise contains CPU ID.
\* head: where the RR search starts from.
VARIABLES procTable, cpus, pTableLock, tlb, scheduling, head



\* The classes to which each variable belongs.
TypeInfo ==
    /\ procTable \in [(1 .. numProcs) -> {RUNNABLE, NOTRUNNABLE, RUNNING} \X (0 .. numCPUs)]
    /\ cpus \in [(1 .. numCPUs) -> (1 .. numProcs)]
    /\ numProcs > numCPUs
    /\ pTableLock \in {0, 1}
    /\ tlb \in [(1 .. numCPUs) -> (0 .. numProcs)]
    /\ scheduling \in {0, 1}
    /\ head \in (1 .. numProcs)



\* Initially, only one process, the very first in the table, is active. All the other processes
\* don't exist. New processes will be magically spawned later. cpus is initialized so that only
\* the first CPU is running something: the first process. The tlb is initialized to reflect that,
\* and the ptable lock is not held.
Init ==
    /\ procTable = [p \in (1 .. numProcs) |->
                            IF p = 1 THEN <<RUNNING, p>> ELSE <<NOTRUNNABLE, 0>>]
    /\ cpus = [c \in (1 .. numCPUs) |->
                    IF c = 1 THEN 1 ELSE 0]
    /\ pTableLock = 0
    /\ tlb = [c \in (1 .. numCPUs) |-> IF c = 1 THEN 1 ELSE 0]
    /\ scheduling = 0
    /\ head = 1
    

\* The next process to be run.
\* IMPORTANT: This operator is valid ONLY when there exists a RUNNABLE process.
\* TODO : for now, just choose the first free process on the ptable.
ChooseProc(p) ==
    CHOOSE i \in (1 .. numProcs) :
        /\ \A x \in (1 .. numProcs):
            \/ procTable[x][1] # RUNNABLE
            \/ i <= x



\* The transition from RUNNING to RUNNABLE. The scheduler can now be invoked.
Preemption ==
    /\ \E c \in (1 .. numCPUs):
        /\ cpus[c] # 0
        /\ pTableLock = 0
        /\ pTableLock' = 1
        /\ scheduling' = c
        /\ procTable' = [i \in (1 .. numProcs) |->
                            IF i = cpus[c] THEN <<RUNNABLE, 0>> ELSE procTable[i]]
        /\ cpus' = [i \in (1 .. numCPUs) |->
                        IF i = c THEN 0 ELSE cpus[i]]
        /\ tlb' = [i \in (1 .. numCPUs) |->
                        IF i = c THEN 0 ELSE tlb[i]]
        /\ head' = cpus[c]
    

\* The pTableLock should be held, but we will check only for the "scheduling" condition, as
\* within the scheduler, we don't perform an actual check on the pTableLock.   
Schedule ==
    /\ scheduling # 0
    /\
        \/
            /\ \E p \in (1 .. numProcs) : procTable[p][1] = RUNNABLE
            /\ LET newProc == ChooseProc(head) IN
                /\ procTable' = [i \in (1 .. numProcs) |->
                                    IF i = newProc THEN <<RUNNING, scheduling>> ELSE procTable[i]]
                /\ tlb' = [i \in (1 .. numCPUs) |->
                            IF i = scheduling THEN newProc ELSE tlb[i]]
                /\ cpus' = [i \in (1 .. numCPUs) |->
                            IF i = scheduling THEN newProc ELSE cpus[i]]
            
        \/
            /\ \A p \in (1 .. numProcs) : procTable[p][1] # RUNNABLE
            /\ UNCHANGED tlb
            /\ UNCHANGED cpus
            /\ UNCHANGED procTable
    /\ scheduling' = 0
    /\ pTableLock' = 0
    /\ UNCHANGED head


            
\* The transition from RUNNING to NOTRUNNABLE. This is very similar to Preemption above,
\* except for the small change that RUNNING goes to NOTRUNNABLE instead of RUNNABLE.
\* The scheduler is invoked, and it will deal with whether there is a running process.
Sleep == 
    /\ \E c \in (1 .. numCPUs):
        /\ cpus[c] # 0
        /\ pTableLock = 0
        /\ pTableLock' = 1
        /\ scheduling' = c
        /\ procTable' = [i \in (1 .. numProcs) |->
                            IF i = cpus[c] THEN <<NOTRUNNABLE, 0>> ELSE procTable[i]]
        /\ cpus' = [i \in (1 .. numCPUs) |->
                        IF i = c THEN 0 ELSE cpus[i]]
        /\ tlb' = [i \in (1 .. numCPUs) |->
                        IF i = c THEN 0 ELSE tlb[i]]
        /\ head' = cpus[c]

    
\* The magic transition from NOTRUNNABLE to RUNNABLE. Choose the first available procTable entry.
MagicRunnable ==
    /\ pTableLock = 0
    /\ \E p \in (1 .. numProcs) :
        /\ procTable[p][1] = NOTRUNNABLE
        /\ \A x \in (1 .. numProcs):
            \/ p <= x
            \/ procTable[x][1] # NOTRUNNABLE
        /\ procTable' = [i \in (1 .. numProcs) |->
                            IF i = p THEN <<RUNNABLE, 0>> ELSE procTable[i]]
    /\ UNCHANGED cpus
    /\ UNCHANGED tlb
    /\ UNCHANGED pTableLock
    /\ UNCHANGED scheduling
    /\ UNCHANGED head
                        

\* The scheduler can come alive magically, from the first idle CPU.
MagicSchedule ==
    /\ pTableLock = 0
    /\ \E c \in (1 .. numCPUs):
        /\ cpus[c] = 0
        /\ \A x \in (1 .. numCPUs):
            \/ c <= x
            \/ cpus[c] # 0
        /\ head' = numProcs
        /\ scheduling' = c
        /\ pTableLock' = 1
        /\ UNCHANGED cpus
        /\ UNCHANGED tlb
        /\ UNCHANGED procTable



\* One of the following actions can happen. The actions lead to processes coming alive,
\* dying, being scheduled, being preempted, etc.
Next ==
    \/ Preemption
    \/ Sleep
    \/ Schedule
    \/ MagicRunnable
    \/ MagicSchedule


\* Every RUNNING process is using the right TLB.
TLBValid ==
    /\ TRUE \* TODO


\* The CPU running the scheduler must not have a process associated with it
SchedCPUIsFree ==
    \/ scheduling = 0
    \/ cpus[scheduling] = 0

\* If the scheduler is active, the pTableLock must be held.
\* scheduler active implies pTableLock is held.
SchedulerHasLock ==
    /\ (scheduling # 0) => (pTableLock = 1)

\* True if there are two CPUs that map to the same process.
SameProc ==
    /\ \E i \in (1 .. numCPUs) : (\E j \in (1 .. numCPUs) : i # j /\ cpus[i] = cpus[j])


\* No two CPUs should be running the same process
NotSameProc ==
    /\ ~ SameProc

========