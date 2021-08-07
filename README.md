# ADG2021

This repository contains the code source for the examples stated in our ADG 2021 paper entitled "Mechanization of incidence projective geometry in higher dimensions, a combinatorial approach".

The source of Bip can be found here:

https://github.com/pascalschreck/MatroidIncidenceProver 

A Linux version (Ubuntu 20.4, but it should work with other distributions) is provided in this repository.

## Intersection of two planes in 3D
This is our first example in the paper. As explained, Bip is unable to add new points in a proof. Prolog programmers would say that it works with the closed word hypothesis.

This is why we only give the proof that *if the intersection of two different planes contains at least two points*, this intersection is a line. The existence of that points is proved by hand in the paper. To do this existential axiomes are applied (by hand).
## Dandelin-Gallucci's theorem
We already published a paper about this theorem, this is why it is not explained with great details in our paper.
## Desargues's theorems
Again, the proof of Desargues's theorem in 2D has been described earlier. This is not the case of the 3D and 4D versions.
### In the 2D plane (enbedded in a 3D space)
The proof includes two lemmas (and thentwo subproofs): 

* it is true in the so-called 3D configuration (or sometimes 2.5 configuration or a 3-complete hypertetrahedron in the paper)
* it is true in a 2D plane embedded in a 3D space

Note that we take the Cevian case into account, that is the case where A' is on BC, B' is on AC and C' is on AB.
## In 3D
We discuss precisely some cases and, in particular, we retrieve another method to prove the 2D case
### In 4D
This a long example : long to express, long to compute, with a long proof.
We also explore the definition of a 3-complete hypertrahedron (from the colineartiy of the triple of points to properties expressed by the definition given in the paper)
## Intersection of two hypeplanes in 5D
Again, the existence of crucial points is omitted.
## More examples
See the repository (and contact me if you want more information)