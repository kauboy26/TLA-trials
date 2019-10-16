---- MODULE trial ----

\* Just trying my own version of Missionaries - Cannibals.

\* I need a Set (that can contain duplicates) for both banks. If
\* the left set (where everybody starts) becomes empty, then that
\* means we are done.

EXTENDS Naturals

VARIABLE banks


TypeInfo == banks \in [left: [mis: (0 .. 3), can: (0 .. 3)],
                        right: [mis: (0 .. 3), can: (0 .. 3)],
                        boat: {"left", "right"}]

\* Kind of screwed up how you use quotes below when you say "left"
\* and "mis" but not above when you define the type.
InitCond == /\ banks["left"]["mis"] = 3
            /\ banks["left"]["can"] = 3
            /\ banks["right"]["mis"] = 0
            /\ banks["right"]["can"] = 0
            /\ banks["boat"] = "left"


Invariant1 == /\ banks["left"]["mis"] <= banks["left"]["can"]
              /\ banks["right"]["mis"] <= banks["right"]["can"]

PInvariant == /\ banks["left"]["mis"] <= banks["left"]["can"]
              /\ banks["right"]["mis"] <= banks["right"]["can"]

Going == /\ banks.boat = "left"
         /\
            \/ banks.left.mis > 0 /\ banks' = [banks EXCEPT !.boat = "right", !.left.mis = banks.left.mis - 1, !.right.mis = banks.right.mis + 1]
            \/ banks.left.mis > 1 /\ banks' = [banks EXCEPT !.boat = "right", !.left.mis = banks.left.mis - 2, !.right.mis = banks.right.mis + 2]
            \/ banks.left.can > 0 /\ banks' = [banks EXCEPT !.boat = "right", !.left.can = banks.left.can - 1, !.right.can = banks.right.can + 1]
            \/ banks.left.can > 1 /\ banks' = [banks EXCEPT !.boat = "right", !.left.can = banks.left.can - 2, !.right.can = banks.right.can + 2]
            \/ banks.left.mis > 0 /\ banks.left.can > 0 /\ banks' = [banks EXCEPT !.boat = "right", !.left.mis = banks.left.mis - 1, !.right.mis = banks.right.mis + 1,
                                                        !.left.can = banks.left.can - 1, !.right.can = banks.right.can + 1]


Coming == /\ banks.boat = "right"
          /\
            \/ banks.right.mis > 0 /\ banks' = [banks EXCEPT !.boat = "left", !.left.mis = banks.left.mis + 1, !.right.mis = banks.right.mis - 1]
            \/ banks.right.mis > 1 /\ banks' = [banks EXCEPT !.boat = "left", !.left.mis = banks.left.mis + 2, !.right.mis = banks.right.mis - 2]
            \/ banks.right.can > 0 /\ banks' = [banks EXCEPT !.boat = "left", !.left.can = banks.left.can + 1, !.right.can = banks.right.can - 1]
            \/ banks.right.can > 1 /\ banks' = [banks EXCEPT !.boat = "left", !.left.can = banks.left.can + 2, !.right.can = banks.right.can - 2]
            \/ banks.right.mis > 0 /\ banks.right.can > 0 /\ banks' = [banks EXCEPT !.boat = "left", !.left.mis = banks.left.mis + 1, !.right.mis = banks.right.mis - 1,
                                                        !.left.can = banks.left.can + 1, !.right.can = banks.right.can - 1]

Step == /\ TypeInfo
        /\ Invariant1
        /\ Going \/ Coming

Solved == banks["left"]["mis"] > 0 \/ banks["left"]["can"] > 0

====