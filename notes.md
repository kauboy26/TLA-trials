# Notes
I just have my notes here to record all the big and small mistakes I've made that have cost me a lot of time.

## Note 1 (on record definitions):
There is a differences between "|->" and "->". The difference is basically that the latter is used in function definitions (type definitions) when one wants to specify that a function 'f' maps domain 'D' to range 'R'. Essentially, "->" results in a Set of records, whereas "|->" is used to map single values to the corresponding image.

## Note 2 (on temporally reassigning records):
Unfortunately, it looks like the best way to do so is the "i \in Domain" syntax. Looks pretty ugly, but directly saying [var |-> value] ends up mapping the variable to some value. I'm unsure of what to do in case only a few of the values changed rather than all of them. I guess I'd be screwed then.

## Note 3 (deadlock):
If you encounter a deadlock, examine the state that TLC complains about. Evaluate the "Next" step condition, whatever it is, at that state (it should fail - that's why we're getting a deadlock). I guess peer into why it's failing. I pray that the Next step you're examining isn't massive, otherwise, GG. In the Missionaries-Cannibals file, I screwed up by typing an ">" instead of ">=" (under the IsSideSafe(side)). Luckily it was easy enough to find.