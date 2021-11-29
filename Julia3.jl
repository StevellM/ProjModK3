GG = GAP.Globals
GG.LoadPackage(GAP.julia_to_gap("repsn"))

function convert_gap_to_julia(w_gap,F::AnticNumberField,z::nf_elem,n::Int64)
    L = GAP.gap_to_julia(GG.CoeffsCyc(w_gap,n))   
    w = F(0)
    for l=1:(length(L))
        L[l] == 0 || w += L[l]*z^(l-1)
    end
    return w
end

function convert_julia_to_gap(N::Vector{AbstractAlgebra.Generic.MatSpaceElem{nf_elem}}, F::AnticNumberField, z::nf_elem, d::Int64)
    N_gap = GAP.julia_to_gap([], recursive=true)
    for n in N
        M_gap = GG.NullMat(size(n)[1], size(n)[2])
	for i =1:(size(n))[1]
	    for j=1:(size(n))[2]
	        c = GAP.julia_to_gap(coordinates(F(n[i,j])), recursive=true)
                s = 0
                for l=1:(length(c))
                    s = s+c[l]*GG.E(d)^(l-1)
                end
                M_gap[i,j]=s
	    end
        end
    GG.Add(N_gap,M_gap)
    end
    return N_gap
end

function direct_sum_matrices(M::Union{MatElem{T},GroupElem} ,N::Union{MatElem{T},GroupElem}) where T <:SetElem 
    typeof(M) <: GroupElem && M = matrix(M)
    typeof(N) <: GroupElem && N = matrix(N)
    MI,MJ = size(M)
    NI,NJ = size(N)
    I = MI+NI
    J = MJ+NJ
    Mat = zeros(parent(M[1,1]),I,J)
    Mat[1:MI,1:MJ] .= M
    Mat[(MI+1):I,(MJ+1):J] .= N
    return matrix(Mat)
end

function dimrpz(rpz::Vector{MatrixGroup{nf_elem, AbstractAlgebra.Generic.MatSpaceElem{nf_elem}}})
    return Int64[degree(rpz[i]) for i=1:(length(rpz))]
end

function  rec(A::Vector{Vector{Int64}},L::Vector{Int64},k::Int64)
    Ind_inter = typeof(A[1])[]
    Bool = false
    for t in A
        L_inter = Int64[]
        for l =1:length(t)
            push!(L_inter,L[t[l]])
        end
        if sum(L_inter) == k
            push!(Ind_inter,t)
        else
            for l = (t[end]):(length(L))
                if sum(L_inter) + L[l] <= k
                    U = deepcopy(t)
                    Bool = true
                    push!(U,l)
                    push!(Ind_inter, U)
                else
                    continue
                end
            end
        end
    end
    if Bool == false
        return Ind_inter
    else
        return rec(Ind_inter, L,k)
    end
end

function corec(A::Vector{Vector{Int64}},L::Vector{Int64},k::Int64)
    Ind_inter = typeof(A[1])[]
    Bool = false
    for t in A
	L_inter = Int64[]
	for l=1:length(t)
	    push!(L_inter,L[t[l]])
	end
	if length(L_inter) == k
	    push!(Ind_inter,t)
	else
	    for l=(t[end]):(length(L))
	        if L[l] > maximum(L[t]) 
		    U = deepcopy(t)
		    Bool = true
		    push!(U,l)
		    push!(Ind_inter,U)
		end
	    end
	end
    end
    if Bool == false
	return Ind_inter
    else
	return corec(Ind_inter,L,k)
    end
end

function elev(L::Vector{Int64}, k::Int64)
    L == sort(L) || throw(ArgumentError("L has to be a sorted list of integers"))
    Ind = [[i] for i = 1:(length(L))]
    return rec(Ind,L,k)
end

function coelev(L::Vector{Int64},k::Int64, minb = false, maxb = false)
    L == sort(L) || throw(ArgumentError("L has to be a sorted list of integers"))
    k >= maximum(L) || return Int64[]
    if (minb == false) || (minb<=minimum(L))
        minb = minimum(L)
    end
    if (maxb ==false) || (maxb >= maximum(L))
        maxb = maximum(L)
    end
    Ind = Vector{Int64}[]
    for i =1:length(L)
	if L[i] in minb:maxb
	    push!(Ind,[i])
	end
    end 
    return corec(Ind,L,k)
end

function quo_proj(G::GAP.GapObj)
    e = GG.Exponent(G)
    Elem = GG.Elements(GG.Center(G))
    multid = GAP.julia_to_gap([], recursive=true)
    for elem in Elem
	if GG.IsDiagonalMat(elem) && GG.Size(GG.Eigenvalues(GG.CyclotomicField(e),elem)) == 1
	    GG.Add(multid,elem)
	end
    end
    return GG.FactorGroup(G,GG.Group(multid))
end

function lift_proj_faith_rpz(o::Int64, n::Int64, dim::Int64)
    G_gap = GG.SmallGroup(o,n)
    f = GG.EpimorphismSchurCover(G_gap)
    f = GG.InverseGeneralMapping(GG.IsomorphismPermGroup(GG.Source(f)))*f
    G_cover = GG.Source(f)
    e = GG.Exponent(G_cover)
    F,z = cyclotomic_field(Int(e))
    H_cover = GG.GeneratorsOfGroup(G_cover)
    Rpz = MatrixGroup{nf_elem, AbstractAlgebra.Generic.MatSpaceElem{nf_elem}}[]
    ch = Vector{AbstractAlgebra.Generic.MatSpaceElem{nf_elem}}[]
    ct = GG.CharacterTable(G_cover)
    Irr = GG.Irr(ct)
    ch_cover = [Irr[i] for i=1:(GG.Size(Irr)) if Irr[i][1] == 1]
    for irr in Irr
	if irr[1] <= dim
	    rep = GG.IrreducibleAffordingRepresentation(irr)
            Mat_cover = [GG.Image(rep,h) for h in H_cover]
            Mat = AbstractAlgebra.Generic.MatSpaceElem{nf_elem}[]
            for u =1:(length(Mat_cover))
                M_cover = Mat_cover[u]
                k = length(M_cover)
                M = [convert_gap_to_julia(M_cover[i,j],F,z,Int(e)) for i=1:k, j =1:k]
                push!(Mat, matrix(F,M))
            end
            Mat = [m for m in Mat]
            GM = matrix_group(Mat)
            push!(Rpz,GM)
            if degree(GM) == 1
                push!(ch,Mat)
            end
	end
    end
    L = dimrpz(Rpz)
    El = elev(L,dim)
    char = GAP.GapObj[]
    lpfr = Vector{AbstractAlgebra.Generic.MatSpaceElem{nf_elem}}[]
    for l in El
	QQ = length(l)
	Mat = [matrix(g) for g in gens(Rpz[l[end]])]
	chara = GG.Character(G_cover, Irr[l[end]])
	while QQ != 1
	    Mat = direct_sum_matrices.(Mat, gens(Rpz[l[QQ-1]]))
	    chara = GG.Character(G_cover, chara+Irr[l[QQ-1]])
	    QQ-=1
	end
	Facto = GG.FactorGroup(G_cover, GG.CenterOfCharacter(chara))
	if GG.Size(Facto) == GG.Size(G_gap)
	    if GG.IdGroup(Facto) == GG.IdGroup(G_gap)
		bool = true
		for irrec in ch_cover
		    if irrec*chara in char
			bool = false
		    end
		end
		for Matinter in lpfr
		    G_inter = GG.Group(convert_julia_to_gap(Matinter,F,z,e))
		    Mat_gap = convert_julia_to_gap(Mat,F,z,e)
		    it2=0
		    for mat in Mat_gap
			if (mat in G_inter) == true
			    it2 +=1
			end
		    end
		    if it2 == length(Mat)
			bool = false
		    end
		end
		if bool == true 
	            push!(lpfr, Mat)
	            push!(char,chara)
		end
	    end
	end
    end
    return ((lpfr, char), (F,ch, ch_cover,ct))
end

function dual_rpz(Rpz::Vector{Vector{AbstractAlgebra.Generic.MatSpaceElem{nf_elem}}})
    return [[transpose(inv(M)) for M in rep] for rep in Rpz]
end

function homog_basis(R::AbstractAlgebra.Generic.MPolyRing{nf_elem},d::Int64)
    n = nvars(R)
    L = Int64[1 for i =1:n]
    E = elev(L,d)
    G = gens(R)
    dict = Dict{typeof(G[1])}{Int64}()
    B = typeof(G[1])[]
    c = 1
    for e in E
        mon = prod([G[i] for i in e])
	dict[mon] = c
	c+=1
	push!(B,mon)
    end
    return (dict,B)
end

function mat_to_poly(M::AbstractAlgebra.Generic.MatSpaceElem{nf_elem},R::AbstractAlgebra.Generic.MPolyRing{nf_elem})
    size(M)[1] == nvars(R) || throw(ArgumentError("The number of rows of M has to be the same as the number of variables of R"))
    G = gens(R)
    return typeof(G[1])[(change_base_ring(R,transpose(M)[i,:])*matrix(G))[1] for i=1:(size(M)[2])]
end

function action_poly_ring(M::AbstractAlgebra.Generic.MatSpaceElem{nf_elem},R::AbstractAlgebra.Generic.MPolyRing{nf_elem},d::Int64)
    size(M)[1] == nvars(R) || throw(ArgumentError("The number of rows of $M has to be the same as the number of variables of $R"))
    dict, B = homog_basis(R,d)
    v = mat_to_poly(M,R)
    MM = zeros(parent(M[1,1]), length(B), length(B))
    for i =1:(length(B))
        W = evaluate(B[i],v)
        T = collect(terms(W))
        for t in T
            MM[dict[collect(monomials(t))[1]],i] = collect(coeffs(t))[1]
        end
    end
    return matrix(MM)
end

function homo_poly_rpz(Rpz::Vector{Vector{AbstractAlgebra.Generic.MatSpaceElem{nf_elem}}},d::Int64, (char_gap ,ct)::Tuple{Vector{GAP.GapObj},GAP.GapObj})
    rpzhomo = Vector{AbstractAlgebra.Generic.MatSpaceElem{nf_elem}}[]
    rpzdual = dual_rpz(Rpz)
    dual_char_gap = GAP.Globals.ComplexConjugate(GAP.julia_to_gap(char_gap))
    for rep in rpzdual
        R,x = PolynomialRing(parent(rep[1][1,1]), "x"=>(1:(size(rep[1])[1])))
        push!(rpzhomo, [action_poly_ring(m,R,d) for m in rep])
    end
    homo_char_gap = GAP.Globals.SymmetricParts(ct, dual_char_gap,d)
    return (rpzhomo, homo_char_gap)
end

function rec_perm(n::Int64,k::Int64)
    if n==0 || k>n || k <= 0
	return Int64[]
    elseif k == 1
	return [[i] for i=1:n]
    elseif k == n
	return [[i for i=1:n]]
    else
	L = Vector{Int64}[]
	for j =k:n
   	    list1 = rec_perm(j-1,k-1)
	    for l in list1
		push!(l,j)
		push!(L,l)
	    end
	end
	return L
    end
end

function ext_power(M::AbstractAlgebra.Generic.MatSpaceElem{nf_elem},t::Int64)
    n = size(M)[2]
    L = rec_perm(n,t)
    L != Int64[] || throw(ArgumentError("M must have a non-zero number of columns and k might be a positive integer less or equal to the number of columns of M"))
    Mat = Vector{typeof(M[1,1])}[]
    for j in 1:(length(L))
        l = L[j]
	cat = hcat([M[:,i] for i in l])
	Col = minors(cat,t)
	push!(Mat,Col)
    end
    return matrix(Mat)
end

function ext_power_rpz(rpz::Vector{AbstractAlgebra.Generic.MatSpaceElem{nf_elem}},t::Int64)
    return [ext_power(M,t) for M in rpz]
end

function basis_ext_power(B::Vector{AbstractAlgebra.Generic.MPoly{nf_elem}},k::Int64)
    l = length(B)
    L = rec_perm(l,k)
    return Vector{typeof(B[1])}[[B[i] for i in lis] for lis in L]
end

function base_to_columns(base::Vector{AbstractAlgebra.Generic.MPoly{nf_elem}},(dict,B)::Tuple{Dict{AbstractAlgebra.Generic.MPoly{nf_elem}, Int64}, Vector{AbstractAlgebra.Generic.MPoly{nf_elem}}})
    columns = zeros(base_ring(base[1]),length(B), length(base))
    for i=1:length(base)
        columns[dict[base[i]],i] = base_ring(base[1])(1)
    end
    return matrix(columns)
end

function change_basis(w, basis::Vector{Vector{AbstractAlgebra.Generic.MPoly{nf_elem}}}, (dict,B)::Tuple{Dict{AbstractAlgebra.Generic.MPoly{nf_elem}, Int64}, Vector{AbstractAlgebra.Generic.MPoly{nf_elem}}})
    length(w) == length(basis) || throw(ArgumentError("The coordinates w do not correspond to basis"))
    gene = [[w[i],basis[i]] for i =1:length(w) if w[i] != parent(w[i])(0)]
    return [[g[1], base_to_columns(g[2],(dict,B))] for g in gene]
end

function coord_in_homo_poly(w::AbstractAlgebra.Generic.MatSpaceElem{nf_elem}, R::AbstractAlgebra.Generic.MPolyRing{nf_elem}, d::Int64)
    dict, B = homog_basis(R,d)
    length(B) == size(w)[1] || throw(ArgumentError("w must have as many rows as the number of generators of R_{(d)}"))
    return [sum([w[:,j][i]*B[i] for i=1:(size(w)[1])]) for j =1:(size(w)[2])] 
end

function is_smooth(I::T) where T <:MPolyIdeal
    v = [f for f in gens(I)]
    R = base_ring(I)
    x = gens(R)
    D = jacobi_matrix(v)
    J = ideal(R, minors(D, length(v)))
    rad = radical(I+J)
    return rad == ideal(R,x) || rad == ideal(R,[R(1)]) 
end

function decompose_vec(w::Vector{Vector{SetElem}}, basis::Vector{Vector{AbstractAlgebra.Generic.MPoly{nf_elem}}}, (dict,B)::Tuple{Dict{AbstractAlgebra.Generic.MPoly{nf_elem}, Int64}, Vector{AbstractAlgebra.Generic.MPoly{nf_elem}}})
    R  =parent(B[1])
    d =degrees(B[1])[1]
    m,n = size(w[1][2])
    F  =parent(w[1][1])
    Mat = matrix(zeros(F,binomial(m,n+1),m))
    for i=1:m
	v = matrix(zeros(F,m,1))
	v[i,1] = 1
	col = matrix(zeros(F,binomial(m,n+1),1))
        for j=1:length(w)
           col += w[j][1]*matrix(minors(hcat(change_base_ring(F,w[j][2]),v),n+1))
	end
        Mat[:,i] = col
    end
    if rank(Mat) != m-n
	return "w is not decomposable"
    else
        K = kernel(Mat)[2]
	kern = [K[:,j] for j=1:(size(K)[2])]
	return [coord_in_homo_poly(k,R,d) for k in kern]
    end
end

function sm_grass_comp(v::AbstractAlgebra.Generic.MatSpaceElem{nf_elem}, basis::Vector{Vector{AbstractAlgebra.Generic.MPoly{nf_elem}}}, (dict,B)::Tuple{Dict{AbstractAlgebra.Generic.MPoly{nf_elem}, Int64}, Vector{AbstractAlgebra.Generic.MPoly{nf_elem}}}, smooth::Bool=true)
    R = parent(B[1])
    w = change_basis(v,basis,(dict,B))
    dec  = decompose_vec(w,basis, (dict,B))
    if dec != "w is not decomposable"
        I = ideal(R,[dec[i][1] for i=1:length(dec)])
        if (smooth == true && is_smooth(I)) || (smooth == false)
            return I
	else
	    return "Empty"
	end
    else
	return "Empty"
    end
end

function sm_snf(V::Vector{AbstractAlgebra.Generic.MatSpaceElem{nf_elem}}, basis::Vector{Vector{AbstractAlgebra.Generic.MPoly{nf_elem}}}, (dict,B)::Tuple{Dict{AbstractAlgebra.Generic.MPoly{nf_elem}, Int64}, Vector{AbstractAlgebra.Generic.MPoly{nf_elem}}}, smooth::Bool=true)
    length(V)==2 || throw(ArgumentError("V has to be composed of exactly 2 vectors"))
    V[1] != V[2] || throw(ArgumentError("The components of V has to be distinct"))
    v1,v2 = V
    w1 = change_basis(v1,basis,(dict,B))
    w2 = change_basis(v2,basis,(dict,B))
    F = parent(w1[1][1])
    dec1 = decompose_vec(w1,basis,(dict,B))
    dec2 = decompose_vec(w2,basis,(dict,B))
    R = parent(B[1])
    if dec1 != "w is not decomposable"
        I = ideal(R,[dec1[i][1] for i=1:length(dec1)])
        if (smooth == true && is_smooth(I)) || (smooth == false)
            return I
	end
    elseif dec2 != "w is not decomposable"
        I = ideal(R,[dec2[i][1] for i=1:length(dec2)])
        if (smooth == true && is_smooth(I)) || (smooth == false)
            return I
	end
    end
    ww1 = sum([w1[j][1]*hcat(change_base_ring(F,w1[j][2])) for j=1:length(w1)])
    ww2 = sum([w2[j][1]*hcat(change_base_ring(F,w2[j][2])) for j=1:length(w2)])
    L,y = PolynomialRing(F,"y")
    w = change_base_ring(L,ww1) + y*change_base_ring(L,ww2)
    m,n = size(w)
    Mat = matrix(zeros(L,binomial(m,n+1),m))
    for i=1:m
        v = matrix(zeros(L,m,1))
        v[i,1] = 1
        col = matrix(minors(hcat(w,v),n+1))
        Mat[:,i] = col
    end
    A = snf(Mat)
    c = A[m-n+1,m-n+1]
    if c == y || c == L(1) || c == L(0)
	return "Empty"
    elseif degree(c) >1
	while evaluate(c,0) == 0
	    c = divrem(c,y)[1]
        end
	pot = typeof(c)[]

	p = [r for r in roots(c,F) if r!=0]
	for r in p
            dec = decompose_vec(v1+r*v2, basis,(dict,B))
            JJ = ideal(R,[dec[i][1] for i=1:length(dec)])
            if (smooth == true && is_smooth(JJ)) || (smooth == false)
                push!(pot,JJ)
	    end
	    if length(pot) == 0	
		return "Empty"
	    else
		return pot
	    end
	end
    else
	r = roots(c,F)[1]
	dec = decompose_vec(v1+r*v2, basis,(dict,B))
	II = ideal(R,[dec[i][1] for i=1:length(dec)])
        if (smooth == true && is_smooth(II)) || (smooth == false)
            return II
        else
	    return "Empty"
	end
    end
end
    

function inv_space(rpz::Vector{AbstractAlgebra.Generic.MatSpaceElem{nf_elem}}, chi::Vector{AbstractAlgebra.Generic.MatSpaceElem{nf_elem}} , basis::Vector{Vector{AbstractAlgebra.Generic.MPoly{nf_elem}}}, (dict,B)::Tuple{Dict{AbstractAlgebra.Generic.MPoly{nf_elem}, Int64}, Vector{AbstractAlgebra.Generic.MPoly{nf_elem}}}, smooth::Bool=true)
    VS = VectorSpace(parent(rpz[1][1,1]), size(rpz[1])[1])
    v = eigenspace(transpose(rpz[1]),trace(chi[1]))
    V,f = sub(VS, [VS(w) for w in v])
    for i = 2:(length(chi))
        vv = eigenspace(transpose(rpz[i]), trace(chi[i]))
        VV,  = sub(VS, [VS(w) for w in vv])
	V,ff = intersect(V,VV)
	f = compose(ff,f)
    end
    if length(gens(V)) == 0
        return "Empty"
    elseif length(gens(V)) == 1
        gen = f(gens(V)[1])
	vect = gen.v
	return sm_grass_comp(vect, basis, (dict,B),smooth)
    elseif length(gens(V)) == 2
	gen = [f(gens(V)[1]).v,f(gens(V)[2]).v]
	return sm_snf(gen,basis,(dict,B),smooth)
    else
	return [f(gens(V)[i]).v for i=1:length(gens(V))]
    end
end

function homo_ideal_in_coord(I::T) where T <:MPolyIdeal
    g = gens(I)
    R = base_ring(I)
    F = base_ring(R)
    d = sum(degrees(collect(terms(g[1]))[1]))
    dict, B = homog_basis(R,d)
    v = zeros(F,length(B),length(g))
    for i=1:(length(g))
	Coll = collect(terms(g[i]))
	vf = zeros(F,length(B),1)
	for c in Coll
    	    vf[dict[collect(monomials(c))[1]]] = collect(coeffs(c))[1]
	end
    v[:,i] = vf
    end
    return (v,B)
end

function is_invariant_by_rep(homorpz::Vector{AbstractAlgebra.Generic.MatSpaceElem{nf_elem}},I::T) where T <:MPolyIdeal
    rpz = homorpz
    G = gens(I)
    R = parent(G[1])
    d = sum(degrees(collect(terms(G[1]))[1]))
    F = base_ring(R)
    dict,B = homog_basis(R,d)
    length(B) == size(rpz[1])[1] || throw(ArgumentError("Rpz might be a representation by matrices on the space of homogeneous polynomial in which the generators of I leave"))
    Coord = homo_ideal_in_coord(I)[1]
    L,y = PolynomialRing(F,"y" => (1:(size(Coord)[2]+1)))
    for M in rpz
	for j=1:size(Coord)[2]
	    act = change_base_ring(L,M*matrix(Coord[:,j]))
	    v = y[end]*act-sum([y[i]*change_base_ring(L,matrix(Coord[:,i])) for i=1:(size(Coord)[2])])
	    II = ideal(L,[v[i,:][1] for i=1:(size(v)[1])])
	    J = radical(II)
	    if J == ideal(L,y) || J == ideal(L,L(1))
	        return false
	    end
        end
    end
    return true	
end

function is_symplectic(prpz::Vector{AbstractAlgebra.Generic.MatSpaceElem{nf_elem}},homorpz::Vector{AbstractAlgebra.Generic.MatSpaceElem{nf_elem}},I::T) where T <:MPolyIdeal
    rpz = homorpz
    G = gens(I)
    R  = parent(G[1])
    d = sum(degrees(collect(terms(G[1]))[1]))
    F = base_ring(R)
    dict,B = homog_basis(R,d)
    Coord = homo_ideal_in_coord(I)[1]
    L,y = PolynomialRing(F,"y" => (1:(size(Coord)[2]+1)))
    for i=1:length(rpz)
	PM = prpz[i]
	M = rpz[i]
      	MM = matrix(zeros(F,size(Coord)[2],size(Coord)[2]))
	VV = VectorSpace(F,length(B))
	Var,f = sub(VV, [VV(Coord[:,i]) for i=1:size(MM)[2]])
	Pas = hcat([transpose(preimage(f,VV(transpose(matrix(Coord[:,j])))).v) for j=1:size(MM)[2]])
	for j=1:size(MM)[2]
	    MM[:,j] = inv(Pas)*transpose(preimage(f, VV(transpose(M*matrix(Coord[:,j])))).v)
	end
	l = F(det(PM))*F(inv(det(MM)))
	if l != F(1)
	    return false
	end
    end
    return true
end

function invs(Id::Tuple{Int64,Int64},nvars::Int64, degree::Int64, dim::Int64)
    o,b,d,t = Id[1], Id[2], degree, dim
    (lpfr,char),(F,ch,ch_gap,ct) = lift_proj_faith_rpz(o,b, nvars)
    println("The linear representations of a SchurCover(G) of dimension $nvars reducing to a projective faithful representation of G have been computed. There are $(length(lpfr)) of them.")
    R,x = PolynomialRing(F,"x"=>(1:nvars))
    homorpz, homo_char_gap  = homo_poly_rpz(lpfr,d, (char,ct))
    println("The induced representations on I_{($d)} have been computed")
    dict, B = homog_basis(R,d)
    basis = basis_ext_power(B,t)
    ext_char_gap = GG.AntiSymmetricParts(ct, homo_char_gap,t)
    L_rep = length(homorpz)
    INVS = []
    for i=1:L_rep
	chara = ext_char_gap[i]
	rep = ext_power_rpz(homorpz[i],t)	
	println("The $t-exterior power of the $i-representation has been computed")
	inv_spaces = []
	CH = [ch[j] for j=1:(length(ch)) if GG.ScalarProduct(chara, ch_gap[j]) !=0]
	for chi in CH
	    inv = inv_space(rep, chi, basis,(dict,B))
	    if inv != "Empty"
	        push!(inv_spaces, inv)
	    end
	end
	if length(inv_spaces)>0
	    push!(INVS,[inv_spaces,i])
	    println("For the representation $i, there are $(length(inv_spaces)) potential invariant subspace(s) as wanted")
	else
	    println("For the representation $i there are no invariant subspaces as wanted")
	end
    end
    return (INVS, lpfr, homorpz, homo_char_gap, GG.Irr(ct))
end

function matrix_ext_powers(B::Vector{AbstractAlgebra.Generic.MPoly{nf_elem}},k::Int64, l::Int64)
    length(B) == k+l || throw(ArgumentError("l should be equal to length(B)-k"))
    basis = basis_ext_power(B,k)
    basis2 = basis_ext_power(B,l)
    F = base_ring(B[1])
    Mat = matrix(zeros(F, length(basis2), length(basis)))
    for j=1:length(basis)
	bt = basis[j]
	i = Int(1)
	while isempty(intersect(bt, basis2[i])) == false
	    i +=1
        end
	b = vcat(bt,basis2[i])
	perma = Int64[]
	for poly in b
	    index=1
	    while poly != B[index]
		index +=1
	    end
	    push!(perma,index)
	end
	PP = Perm(perma)
	Mat[i,j] = sign(PP)
    end
    return Mat
end

function reduction_sparse_mat(M)
    M = vcat([M[i,:] for i =1:size(M)[1] if M[i,:] != matrix(zeros(parent(M[1,1]),1,size(M)[2]))])
    M = hcat([M[:,j] for j =1:size(M)[2] if M[:,j] != matrix(zeros(parent(M[1,1]),size(M)[1],1))])
    rowM = [M[1,:]]
    for i=2:size(M)[1]
       rowint = M[i,:]
       bool = true
       for roww in rowM
           if rowint == roww || rowint == -roww
               bool = false
           end
       end
       if bool == true
           push!(rowM,rowint)
       end
    end
    M = vcat(rowM)
    colM = [M[:,1]]
    for j=2:size(M)[2]
       colint = M[:,j]
       bool = true
       for coll in colM
           if colint == coll || colint == -coll
               bool = false
           end
       end
       if bool == true
           push!(colM,colint)
       end
    end
    return hcat(colM)
end


function sparse_matrix_fact(M) 
    M = reduction_sparse_mat(M)
    values = typeof(M[1,1])[]
    indrow = Int64[]
    indcol = Int64[]
    for i=1:size(M)[1]
	for j=1:size(M)[2]
	    if M[i,j] != 0
		push!(values,M[i,j])
		push!(indrow,i)
		push!(indcol,j)
	    end
	end
    end
    return (values, indrow, indcol)
end

function distinct(L)
    L2 = [L[1]]
    for l in L
	if (l in L2) == false 
	    push!(L2,l)
	end
    end
    return L2 == L
end

function approx_ideal_minors_sparse_matrix(M,k)
    val,row,col = sparse_matrix_fact(M)
    println("The matrix has been reduced. It it of size ($(maximum(row)), $(maximum(col))) and has $(length(val)) non-zero entries")
    L = parent(val[1])
    k <= length(val) || return(typeof(val[1])[])
    it = maximum(row)
    I = ideal(L,L(0))
    for i=it:-1:1
	CO =  coelev(row,k,i,i)
	indices = []
	for index in CO
	    if distinct(col[index])
		push!(indices,index)
	    end
	end
	q,r = divrem(length(indices),10000)
        JJ = []
        for index in indices[1:r]
	    ROW = row[index]
	    COL = sort(col[index])
	    minor = det(M[ROW,COL])
	    push!(JJ,minor)
	end
	if length(JJ) >0
	    I = radical(I+ideal(L,JJ))
            if dim(quo(L,I)[1]) <=1
                return (I,dim(quo(L,I)[1]))
	    end
        end
	for j in r:10000:(length(indices)-10000)
	    JJ = []
            for index in indices[j+1:j+10000]
                ROW = row[index]
                COL = sort(col[index])
                minor = det(M[ROW,COL])
                push!(JJ,minor)
            end
	    if length(JJ) >0
	        I = radical(I+ideal(L,JJ))
	        if dim(quo(L,I)[1]) <=1
	            return (I,dim(quo(L,I)[1]))
		end
	    end
	end
    end
    return (I,dim(quo(L,I)[1]))
end

	

function matrix_multivec_star(V,(dict,B),k)
    base_ring(B[1]) == parent(V[1][1]) ||throw(ArgumentError("V and B have to be defined over the same field"))
    R = parent(B[1])
    F = base_ring(R)
    l = length(B)-k
    Basis = basis_ext_power(B,k)
    Basis2 = basis_ext_power(B,l)
    L,y = PolynomialRing(F,"y"=>(1:length(V)))
    w = sum([y[i]*change_base_ring(L,V[i]) for i=1:length(y)])
    Mat = matrix_ext_powers(B,k,l)
    wstar = change_basis(Mat*transpose(w),Basis2,(dict,B))
    m,n = size(wstar[1][2])
    M = matrix(zeros(L,binomial(m,n+1),m))
    for i=1:m
        v = matrix(zeros(L,m,1))
        v[i,1] = 1
        col = matrix(zeros(L,binomial(m,n+1),1))
        for j=1:length(wstar)
           col += wstar[j][1]*matrix(minors(hcat(change_base_ring(L,wstar[j][2]),v),n+1))
        end
        M[:,i] = col
    end
    return M
end

function comp_dec_comps(V,(dict,B),k)
    M = matrix_multivec_star(V,(dict,B),k)
    println("The matrix of f* has been computed")
    return approx_ideal_minors_sparse_matrix(M,k+1)
end

function cart_prod(L::Vector{Int64},Cart::Vector{Vector{Int64}}=[Int64[]])
    minimum(L) > 0 || throw(ArgumentError("L has to be a list of positive integers"))
    Cart2 = Vector{Int64}[]
    for cart in Cart
	for i=1:L[1]
	    cart_bis = deepcopy(cart)
	    push!(Cart2, push!(cart_bis,i))
	end
    end
    if length(L) == 1
	return Cart2
    else
        return cart_prod( L[2:end], Cart2)
    end
end

function all_ideal(L)
    bool = true
    for V in L
	if typeof(V)<:AbstractAlgebra.Ideal{AbstractAlgebra.Generic.MPoly{nf_elem}}
	    continue
	else
	    bool = false
	end
    end
    return bool
end
    
function sm_cart_ideal(inv_spaces::Vector{Any})
    L = [length(D) for D in inv_spaces]
    Cart = cart_prod(L)
    pot = []
    for cart in Cart
	V = [inv_spaces[i][cart[i]] for i=1:length(inv_spaces)]
	if all_ideal(V)
	    I = sum(V)
	    if is_smooth(I)
		push!(pot,radical(I))
	    end
	else
	    push!(pot,V)
	end
    end
    return(pot)
end


function invs_gen(Id::Tuple{Int64,Int64},nvars::Int64, degree::T, dim::T) where T <:Union{Int64, Vector{Int64}}
    typeof(degree) != Int64 || return invs(Id,nvars,degree,dim)
    length(degree) == length(dim) || throw(ArgumentError("$(degree) and $(dim) should have the same length."))
    o,b,D,K = Id[1], Id[2], degree, dim
    (lpfr,char),(F,ch,ch_gap,ct) = lift_proj_faith_rpz2(o,b, nvars)
    println("The linear representations of a SchurCover(G) of dimension $nvars reducing to a projective faithful representation of G have been computed. There are $(length(lpfr)) of them.")
    R,x = PolynomialRing(F,"x"=>(1:nvars))
    HRPZ  = [homo_poly_rpz(lpfr,d, (char,ct)) for d in D]
    println("The induced representations on the I_{(d)}'s have been computed")
    HBASIS = [homog_basis(R,d) for d in D]
    EXTBASIS = [basis_ext_power(HBASIS[i][2],K[i]) for i=1:length(K)]
    EXTCHARGAP = [GG.AntiSymmetricParts(ct, HRPZ[i][2],K[i]) for i=1:length(K)]
    INVS = []
    for i=1:length(lpfr)
	CHAR = [EXTCHARGAP[j][i] for j=1:length(EXTCHARGAP)]
	EXTPOWERRPZ = [ext_power_rpz(HRPZ[j][1][i],K[j]) for j=1:length(HRPZ)]
	println("The induced action on the exterior powers by the $i-representation have been computed")
	inv_spaces = []
	for j=1:length(D)
	    chara = CHAR[j]
	    rep = EXTPOWERRPZ[j]
	    inv_inter = []
	    CH = [ch[j] for j=1:(length(ch)) if GG.ScalarProduct(chara, ch_gap[j]) !=0]
	    for chi in CH
                inv = inv_space(rep, chi, EXTBASIS[j],HBASIS[j], false)
                if inv != "Empty"
                    push!(inv_inter, inv)
                end
            end
	    if length(inv_inter)>0 
		push!(inv_spaces,inv_inter)
	    end
	end
        if length(inv_spaces) == length(D)
	    pot = sm_cart_ideal(inv_spaces)
	    if length(pot) > 0
                push!(INVS,[pot,i])
                println("For the representation $i, there are potential invariant subspaces as wanted")
            else
                println("For the representation $i there are no invariant subspaces as wanted")
	    end
        end
    end
    return (INVS, lpfr, [HRPZ[j][1] for j=1:length(HRPZ)], [HRPZ[j][2] for j=1:length(HRPZ)], GG.Irr(ct))
end
