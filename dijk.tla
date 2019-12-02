---- MODULE dijk ----
\* This my attempt to model the algorithm given in the paper
\* "Solution of a Problem in Concurrent Programming Protocol".
\* The paper can be found here:
\*      https://www.di.ens.fr/~pouzet/cours/systeme/bib/dijkstra.pdf
\* 
\* Unlike the previous TLA+ specs I've written, this time the 
\* granularity of atomicity matters a lot. Compressing a few steps into
\* a single step, or even compressing an entire line into a single step,
\* could end up proving a trivial algorithm instead of the one given in
\* the paper.
\* 
\* I plan to prove my own solution to a similar problem. The similar problem
\* I "solved" (I will remove the double quotes after I have proved that my
\* proposed solution is correct) is as follows:
\* 1) There are N cyclic processes. No static priority may be assigned.
\* 2) There cannot be an initial random variable that allows for one
\* process to go before others. (In Prof. Dijkstra's solution, the variable "k"
\* performs this function.)
\* 3) There is a critical section each must execute periodically. Each process
\* alternates between executing the critical section and a non critical section.
\* 4) Reads and writes are atomic. They are instantaneous, and thus, it is not
\* possible to have an overlapping write; one write will occur before the other.
\* 5) Nothing can be assumed about the relative speeds of the computers.
\* 6) A blocked process in its non-critical section IS ALLOWED to block other processes.
\*
\* Clearly, the problem I solved is much easier to solve than the one Prof. Dijkstra
\* proposed, because of 6). This is not allowed in the original problem.
\*
\* Anyway, here is my solution:
\*
\* N processes
\* Shared int array: a[1 .. N - 1]
\*
\*
\* Program on process 'i':
\*
\* while TRUE:
\*      j = 1;
\*      
\*      while j != N:
\*          a[j] = i;
\*
\*          while a[j] == i:
\*              ;
\*
\*          j += 1;
\*      
\*      critical section;
\*      non-critical section;
\*
EXTENDS Naturals

CONSTANTS N

\* I'm writing algorithm in PlusCal, which is transpiled to TLA+:
(* --algorithm handslap
{
    variables c = 0; b = [i \in (1 .. N) |-> 1] ;
        process (Proc \in (1 .. N))
            variable j;
            {
            s:  while (TRUE) {
                    j := 1;
                t:  while (j < N) {
                        b[j] := self;
                    u:  while (b[j] = self) {
                            skip;
                        };
                        j := j + 1;
                    };
                    
                    enter_critic: c := c + 1;
                    exit_critic:  c := c - 1;
                    
                }
            
            }
} *)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES c, b, pc, j

vars == << c, b, pc, j >>

ProcSet == ((1 .. N))

Init == (* Global variables *)
        /\ c = 0
        /\ b = [i \in (1 .. N) |-> 1]
        (* Process Proc *)
        /\ j = [self \in (1 .. N) |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "s"]

s(self) == /\ pc[self] = "s"
           /\ j' = [j EXCEPT ![self] = 1]
           /\ pc' = [pc EXCEPT ![self] = "t"]
           /\ UNCHANGED << c, b >>

t(self) == /\ pc[self] = "t"
           /\ IF j[self] < N
                 THEN /\ b' = [b EXCEPT ![j[self]] = self]
                      /\ pc' = [pc EXCEPT ![self] = "u"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "enter_critic"]
                      /\ b' = b
           /\ UNCHANGED << c, j >>

u(self) == /\ pc[self] = "u"
           /\ IF b[j[self]] = self
                 THEN /\ TRUE
                      /\ pc' = [pc EXCEPT ![self] = "u"]
                      /\ j' = j
                 ELSE /\ j' = [j EXCEPT ![self] = j[self] + 1]
                      /\ pc' = [pc EXCEPT ![self] = "t"]
           /\ UNCHANGED << c, b >>

enter_critic(self) == /\ pc[self] = "enter_critic"
                      /\ c' = c + 1
                      /\ pc' = [pc EXCEPT ![self] = "exit_critic"]
                      /\ UNCHANGED << b, j >>

exit_critic(self) == /\ pc[self] = "exit_critic"
                     /\ c' = c - 1
                     /\ pc' = [pc EXCEPT ![self] = "s"]
                     /\ UNCHANGED << b, j >>

Proc(self) == s(self) \/ t(self) \/ u(self) \/ enter_critic(self)
                 \/ exit_critic(self)

Next == (\E self \in (1 .. N): Proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

\* Can only have one process in the critical section at a time
CriticalSection ==
    /\ c \in {0, 1} 

====
