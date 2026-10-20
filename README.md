# Elementary matching results for Erdos problem 710

This project packages supporting lemmas supplied by AItoBit in
`Erdos710_Research.lean`. It does not prove the proposed asymptotic formula
or claim to solve Erdos problem 710.

The divisors are 1 through n, indexed by `Fin n`. Candidate multiples lie
strictly between n and n+h, and are pairwise distinct. `f n` is the least
natural-number length admitting such a matching.

The compared results characterize matchings by Hall inequalities and their
finite obstructions, construct a matching at length n*n+1, establish existence
and minimality of f, prove n+1 <= f(n) <= n*n+1 for n>0, and compute f(1)=2.
At n=0 the matching is empty and f(0)=0.

These are elementary consequences of Hall's theorem and a direct construction.
No novelty or independent expert review is claimed. Palomar's research-interest
requirement remains an editorial question.

Challenge.lean contains deliberate proof holes. Solution.lean must contain none.
The original asymptotic proposition and unproved fractional-certificate proposal
are omitted from this submission. The author confirmed authorship in the chat.

Submission endpoint: https://submit.palomar-registry.org/
