loadPackage "Posets"; loadPackage "Polyhedra";

A = P -> (
    n := #P_*;
    A1 := matrix table(P_*, P_*, (rho, p) -> 
    	if p == rho then 1
    	else if compare(P, p, rho) then #maximalChains(closedInterval(P, p, rho))
    	else 0
	);
    A1 ++ transpose(A1) | (id_(ZZ^n) || id_(ZZ^n)))


--computing facets and Hilbert bases for the cones associated with various posets
-- m-corolla
m = 2; P = poset for i from 1 to m list {0, i};
C = coneFromVData A(P);
hilbertBasis C
facets C

--linear poset
m = 3; P = poset for i from 1 to m list {i-1,i};
P = coneFromVData A(P);
hilbertBasis C
facets C

--Y-poset
P = poset {{a,b}, {b,c}, {b,d}};
C = coneFromVData A(P);
hilbertBasis C
facets C

--diamond poset
m = 3; P = poset flatten for i from 1 to m list {{0,i},{i,m+1}};
C = coneFromVData A(P);
hilbertBasis C
facets C


--
loadPackage "Posets"; loadPackage "Polyhedra";
-- f(as) <= f(bs)
H = (P,as,bs) -> (
    f := for p in P_* list (
	if member(p, as) then -1
	else if member(p,bs) then 1
	else 0);
    id_(ZZ^(2*(#P_*))) || matrix{f | -f})
   
P = poset{{a,b}, {a,c}}
H1 = H(P, {a}, {b})
H2 = H(P, {a}, {c})
H3 = H(P, {a}, {b,c})

rays coneFromHData(H1 || H2 || H3)
