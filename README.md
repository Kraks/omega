## Omega Test

A Omega test implementation in Scala. Omega test is an algorithm that can determine whether exists integer solutions of a set of integer constraints[1].

For examples, given constraints
```
7 - 3x - 2y >= 0
15 - 6x - 4y >= 0
1 >= x
2y >= 0
```

the Omega test will figure out it is satisfiable by some integers of `x` and `y`.

While another example,
```
45 - 11x - 13y >= 0
-27 + 11x + 13y >= 0
4 + -7x + 9y >= 0
10 + 7x - 9y >= 0
```

the Omega test determines that there is no assignments of `x` and `y` can make them satisfied.

### References 

[1] Pugh, William. "The Omega test: a fast and practical integer programming algorithm for dependence analysis." Proceedings of the 1991 ACM/IEEE conference on Supercomputing. ACM, 1991.
