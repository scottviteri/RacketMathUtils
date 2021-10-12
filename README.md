# RacketMathUtils
Unorganized utilities for linear algebra, abstract algebra, and modular arithmetic.

Creates and verifies embeddings of dihedral groups into 2-by-2 matrices over Z/nZ.

To embed the dth dihedral group, we search x,y in Z/nZ such that (x,y) is a kth root of unity and x^2+y^2=1.
This seems to work for all dihedral groups -- not just those constructible with a ruler and compass for instance.
