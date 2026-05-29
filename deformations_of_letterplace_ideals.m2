--checking ker phi == I for the linear poset a < b < c 
R = QQ[a_1,b_1,c_1,a_2,b_2,c_2,v,t,u, MonomialOrder=>{Weights=>{3,2,1}, Lex}];
I = ideal(a_1*a_2 - b_1*v, a_1*b_2 - c_1*v*t, a_1*c_2 - v*t*u,
    b_1*b_2 - a_2*c_1*t, b_1*c_2 - a_2*u*t, c_1*c_2 - b_2*u);
S = QQ[alpha_1, alpha_2, beta_1, beta_2, gamma_1, gamma_2];
op = {a_1 => alpha_1*beta_1*gamma_1, b_1 => beta_1*gamma_1, c_1 => gamma_1,
    a_2 => alpha_2, b_2 => alpha_2*beta_2, c_2 => alpha_2*beta_2*gamma_2,
    v => alpha_1*alpha_2, t => beta_1*beta_2, u => gamma_1*gamma_2 };
phi = map(S,R,op);
I == kernel phi


--checking ker phi == I for the V poset a < b,c
R = QQ[a_1,b_1,c_1,a_2,b_2,c_2,t,u,v, MonomialOrder=>{Weights => {2,1,1}, Lex}]
I = ideal(a_1*a_2 - b_1*c_1*t, a_1*b_2 - u*c_1*t, a_1*c_2 - v*b_1*t,
    b_1*b_2 - u*a_2, c_1*c_2 - v*a_2);
S = QQ[alpha_1, beta_1, gamma_1, alpha_2, beta_2, gamma_2];
op = {a_1 => alpha_1*beta_1*gamma_1, b_1 => beta_1, c_1 => gamma_1,
    a_2 => alpha_2, b_2 => alpha_2*beta_2, c_2 => alpha_2*gamma_2,
    t => alpha_1*alpha_2, u => beta_1*beta_2, v => gamma_1*gamma_2 };
phi = map(S,R,op);
I == kernel phi


--------------------------
--    GENERALIZATION	--
--------------------------

loadPackage "Posets";

--function to initialize the rings and some lookup tables
init = () -> (
    n = #(P_*);
    pred = hashTable for p in P_* list(
    	p => for q in P_* list (if member({q,p}, coveringRelations P) 
	    then q else continue));
    succ = hashTable for p in P_* list(
    	p => for q in P_* list (if member({p,q}, coveringRelations P) 
	    then q else continue));
    isPred = (p, q) -> member(p, pred#q);
    isSucc = (p, q) -> member(p, succ#q);
    
    weight = p -> (if #(succ#p) == 0 
	then 1 else sum(apply(succ#p, weight))+1);
    R = QQ[x_(1,1)..x_(2,n), t_1..t_n,
        MonomialOrder=>{Weights=>for p in P_* list weight(p)}];
    S = QQ[rho_(1,1)..rho_(2,n)];
    
    X1 = hashTable(for i from 1 to n list P_*_(i-1) => x_(1,i));
    X2 = hashTable(for i from 1 to n list P_*_(i-1) => x_(2,i));
    T = hashTable(for i from 1 to n list P_*_(i-1) => t_i);
    Rho1 = hashTable(for i from 1 to n list P_*_(i-1) => rho_(1,i));
    Rho2 = hashTable(for i from 1 to n list P_*_(i-1) => rho_(2,i));
    );

--general definitions of phiTilde and phi
phiTilde = () -> (
    op := flatten(for p in P_* list {
	X1#p => Rho1#p,
	X2#p => Rho2#p, 
	T#p => ((Rho1#p)*(Rho2#p)) / product(for q in P_* list (
		if isPred(q, p) then Rho2#q
		else if isSucc(q, p) then Rho1#q
	    	else continue))
	});
    map(frac(S), R, op));

phi = () -> (
    op := flatten(for p in P_* list {
	X1#p => (Rho1#p) * product(for eta in P_* list(
		  (Rho1#eta)^(sum(for r in pred#eta list(
		    if compare(P,p,r)
            then #maximalChains(closedInterval(P,p,r)) 
            else continue))))),
    	X2#p => (Rho2#p) * product(for eta in P_* list(
		  (Rho2#eta)^(sum(for r in succ#eta list(
		    if compare(P,r,p)
            then #maximalChains(closedInterval(P,r,p)) 
            else continue))))),
    	T#p => (Rho1#p)*(Rho2#p)
	});
    map(S,R,op));


--two different formulas for the binomials generating the toric ideal
binomialsChains = () -> (
    for pq in allRelations P list (
	p := pq_0; q := pq_1; int := closedInterval(P,p,q);
	tprod := product(for r in int_* list T#r * 
    	    product(for s in (succ#r)-set(int_*) list X1#s) * 
	    product(for s in (pred#r)-set(int_*) list X2#s));
	
    	C := maximalChains int; CRest := set(C_0);
    	pprod := product(for i from 1 to (#C)-1 list 
    	    product(apply(pred#(first(C_i - CRest)), r -> X2#r)) * 
	    product(apply(succ#(last(C_i - CRest)), r -> X1#r))
	    do CRest = CRest + set(C_i));
    	(X1#p)*(X2#q) - tprod*pprod
));

binomialsExponents = () -> (
    for pq in allRelations P list (
	charF := (A, x) -> if member(x,A) then 1 else 0;
	p := pq_0; q := pq_1; int := closedInterval(P,p,q);
	(X1#p)*(X2#q) - product(for r in P_* list (
		(T#r)^(charF(int_*, r)) * 
 		(X1#r)^(max(#(set(int_*)*set(pred#r)) - charF(int_*, r), 0)) * 
		(X2#r)^(max(#(set(int_*)*set(succ#r)) - charF(int_*, r), 0))))
));


--S-polynomials
Spair = (f, g) -> (
    (lcm(leadTerm f, leadTerm g) // leadTerm f) * f 
    - (lcm(leadTerm f, leadTerm g) // leadTerm g) * g
);

buchberger = (G) -> (
    I := ideal G;
    spairs := flatten(for i from 0 to #G-2 list (
	for j from i+1 to #G-1 list Spair(G_i, G_j) % I));
    all(spairs, s -> s == 0)
);


--Examples
P = poset {{a,b}, {a,c}, {a,d}, {b,f}, {c,e}, {d,e}, {e,f}}; init();
I1 = ideal binomialsChains(); I2 = ideal binomialsExponents();
grBasis = set(flatten entries gens gb ker phi());

ker phiTilde() == ker phi()
buchberger(binomialsChains())
buchberger(binomialsExponents())
I1 == ker phi()
I1 == I2
set binomialsChains() === grBasis
set binomialsExponents() === grBasis


--Y-poset
P = poset {{a,b}, {b,c}, {b,d}}; init();
I1 = ideal binomialsChains(); I2 = ideal binomialsExponents();
grBasis = set(flatten entries gens gb ker phi());

ker phiTilde() == ker phi()
buchberger(binomialsChains())
buchberger(binomialsExponents())
I1 == ker phi()
I1 == I2
set binomialsChains() === grBasis
set binomialsExponents() === grBasis


--general diamond poset
m = 2;
P = poset flatten for i from 1 to m list {{0,i},{i,m+1}}; init();
I1 = ideal binomialsChains(); I2 = ideal binomialsExponents();
grBasis = set(flatten entries gens gb ker phi());

ker phiTilde() == ker phi()
buchberger(binomialsChains())
buchberger(binomialsExponents())
I1 == ker phi()
I1 == I2
set binomialsChains() === grBasis
set binomialsExponents() === grBasis
