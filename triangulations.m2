loadPackage "SimplicialComplexes"; loadPackage "Quasidegrees";

--lexicographic triangulation of the hexagon
A = matrix transpose {{1,2,3}, {1,3,2}, {2,1,3}, {2,3,1}, {3,1,2}, {3,2,1}};
R = QQ[x_1..x_6, MonomialOrder=>Lex];
I = toricIdeal(A,R);
Δ = simplicialComplex(radical monomialIdeal leadTerm I)


--function to compute general triangulations
triangulation = I -> simplicialComplex(radical monomialIdeal leadTerm I);


--reverse lexicographic triangulation of the hexagon
R = QQ[x_1..x_6, MonomialOrder=>GRevLex];
triangulation toricIdeal(A,R)


--triangulation of the square
A = matrix transpose(({1} ** {(0,0), (0,1), (1,0), (1,1)})/splice/toList)
triangulation toricIdeal(A, QQ[x_1..x_4, MonomialOrder=>Lex])
triangulation toricIdeal(A, QQ[x_1..x_4, MonomialOrder=>GRevLex])



--triangulation of the 3-cube
A = matrix transpose(({1} ** {(0,0,0), (0,0,1), (0,1,0), (0,1,1), (1,0,0), (1,0,1), (1,1,0), (1,1,1)})/splice/toList)
triangulation toricIdeal(A, QQ[x_1..x_8, MonomialOrder=>Lex])
triangulation toricIdeal(A, QQ[x_1..x_8, MonomialOrder=>GRevLex])



--triangulation by a diagonal monomial order of the 2-minors of an n x 2 -matrix, e.g. n = 4
n=4;
variables = x_1..x_n | y_1..y_n;
R = QQ[variables,MonomialOrder=>(Weights=>reverse(1..n))];
M = genericMatrix(R,n,2);
I = minors(2,M);
triangulation I
