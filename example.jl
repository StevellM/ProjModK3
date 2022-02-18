o,b,d,t,nvar = 192,1493,2,3,6;
psr, char_gap, lin_oscar, lin_gap = proj_suit_rep(o, b, nvar);
F = base_ring(psr[1][1]);
R,x = PolynomialRing(F,"x"=>(1:nvar));
B = homog_basis(R,d);
basis = basis_ext_power(B,t);
ct = GG.CharacterTable(GG.UnderlyingGroup(char_gap[1]));
rep_homo, char_homo_gap  = homo_poly_rep(psr,d, (char_gap,ct));
char_ext_gap = GG.AntiSymmetricParts(ct, char_homo_gap,t);
rep = ext_power_rep(rep_homo[7],t);
chi = lin_oscar[2];
INVS = _inv_space(rep, chi, basis);
V = INVS[1][1];
M = _matrix_multivec_star(V, B, t);
Mfact = _sparse_matrix_fact(M);
X = Spec(parent(Mfact[1][1])); 

I = _ideal_degeneracy(X, Mfact, t+1)


