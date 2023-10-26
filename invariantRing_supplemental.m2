needsPackage "InvariantRing"

--Some examples of things I have used the invariant ring package for

------------------------------------------------------------------------------------------------
--1. Getting the polynomial ring on which a group acts as a module over the ring of invariants

--In: *Finite* group action G
--Out: the polynomial ring S as a module over S^G
--This could easily be modified to include non-finite actions (just remove the DegreeBound)
SOverSG = G -> (
    S := ring G;
    inv := invariants(G, DegreeBound => length group G + 1);
    A := QQ[y_1..y_(length inv), Degrees => for i to length inv - 1 list degree inv#i];
    f := map(S, A, inv);
    R := A/ker f;
    f' := map(S, R, f);
    prune pushForward(f', S^1)
    )

--Demo:
S = QQ[x_1..x_4]
G = finiteAction({matrix{{0,1,0,0},{1,0,0,0},{0,0,0,1},{0,0,1,0}}}, S)
M = SOverSG G
R = ring M
res(M, LengthLimit=>6)
------------------------------------------------------------------------------------------------


------------------------------------------------------------------------------------------------
--2. Making the transfer map S-->S^G which sends a polynomial f to \sum_{g\in G} g(f)
--This is just the Reynolds operator without dividing by |G|

--In: a ring element (usually a monomial) f
--Out: the sum over all w in S_n of w*f
----------------------------------------------
transferMap=method()

--default to symmetric group
--this option does not require base ring to be a field (good for working over ZZ)
transferMap(RingElement) := f -> (
    R:=ring f;
    n:=numgens R;
    I:=id_(R^n); --n*n identity matrix
    L:= for p in permutations n list(
	map(R,R,(vars R)*(I_p)));
    sum(apply(L, l -> l(f)))
    ) 

--maybe will use in the future for other types
--input is a Finite Action, so need to be working over a field
transferMap(RingElement, FiniteGroupAction) := (f,G) -> (
    R:= ring G;
    if not instance(f,R) then (error "transferMap: expected an element from the ring on which the group acts.");
    sum apply(group G, g -> sub(f, (vars R)*(transpose g)))
    )

--Demo:
S = ZZ[x_1..x_4]
f = x_1*x_2
t = transferMap(f) --over full symmetric group
needsPackage "SymmetricPolynomials"
elementarySymmetric(t) --can convert t into an expression in terms of elementary symmetrics


S = QQ[x_1..x_4]
f = x_1*x_2
transferMap(f, finiteAction({matrix{{0,1,0,0},{1,0,0,0},{0,0,0,1},{0,0,1,0}}}, S))
------------------------------------------------------------------------------------------------


------------------------------------------------------------------------------------------------
--3. Just a question about the error message
S = QQ[x_1..x_4]
G = finiteAction({matrix{{0,1,0,0},{1,0,0,0},{0,0,0,1},{0,0,1,0}}}, S)
invariants G --warning about stopping condition not met
invariants(G, DegreeBound=>3) --shouldn't this warning not appear? we have a group of order 2
------------------------------------------------------------------------------------------------


------------------------------------------------------------------------------------------------
--4. Matt Mastroeni example
--Let D be the dihedral group of order 2k act on S = k[x_1..x_n, y_1..y_n]
--The rotation generator acts by scaling x_i by \zeta, y_i by \zeta^{-1}, for \zeta primitive
--kth root of unity
--The reflection generator swaps x_i with y_i
--So this is a mix of finiteAction and diagonalAction
--Below is how Matt showed me how to do this, let's let n = 2 and k = 3

S = QQ[x_1,x_2, y_1, y_2]

--first, get the invariants of the cyclic subgroup C_k of D
C = diagonalAction(matrix{{1,1,2,2}}, {3}, S)
R = invariantRing C 

--present R as a quotient of a standard graded polynomial ring
I = definingIdeal R
R' = coefficientRing(ring I)[(ring I)_*]
I = sub(I, R')
f = map(S, R', invariants C)

--R is a toric ring and C is a normal subgroup of D
--this means the action of the reflection generator s lifts to the polynomial ring R' so that
--the map R -> R' is s-equivariant
B = matrix{{0,0,1,0}, {0,0,0,1}, {1,0,0,0}, {0,1,0,0}}
B' = transpose matrix apply(gens R, m->
    apply(gens R, m' -> (m'':= sub(m, (vars S)*(transpose B));
	if m'' == m' then 1 else 0)))
refl = finiteAction({B'}, R')

(ideal mingens ideal apply(invariants refl, h -> f h))_*
--these are output as elements of S
------------------------------------------------------------------------------------------------


------------------------------------------------------------------------------------------------
--5. Isotypic components example

--Input: a cyclic group action G acting on a multigraded polynomial ring 
--Output: a hashtable relating basis elements of the coinvariant algebra and the power of zeta obtained when acting by g
--Note: needs multigrading
--definiitely could use some work...

isotypics= G -> (
    S := ring G;
    I := ideal invariants G;
    R := S/I;
    B :=flatten entries basis R; --basis for coinvariant alg
    n :=numgens R; --number of variables in R
    h :=new MutableHashTable; --for recording character value of each monomial in the basis
    for j to length B-1 do(
	d:=degree B_j;
	b:=B_j;
	h#b=(sum(0..n-1, i -> (i*d_i)))%n; --computes power of zeta in front of the monomial after action by cyclic gen
	);
    new HashTable from h
    )

--Demo
S = QQ[x_1..x_3, Degrees => entries id_(ZZ^3)]
D = diagonalAction( matrix{{1,1,2}}, {5}, S)
isotypics D
------------------------------------------------------------------------------------------------
