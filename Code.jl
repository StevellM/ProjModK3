GG = GAP.Globals
GG.LoadPackage(GAP.julia_to_gap("repsn"))

# An extra macro for the input checks 

macro req(args...)
  @assert length(args) == 2
  quote
    if !($(esc(args[1])))
      throw(ArgumentError($(esc(args[2]))))
    end
  end
end

##############################################################################
#                                                                            
# Extra conversion(s)
#                                                                            
##############################################################################

# A conversion to transform elements of cyclotomic fields from GAP to Oscar

function _convert_gap_to_julia(w_gap,F::AnticNumberField,z::nf_elem,n::Int64)
  L = GAP.gap_to_julia(GG.CoeffsCyc(w_gap,n))   
  w = sum([F(L[l]*z^(l-1)) for l=1:length(L) if L[l] !=0], init = F(0))
  return w
end

##############################################################################
#
# Combinatoric
#
##############################################################################

# An internal gathering the respective dimensions of different representations 
# of the same kind.

function _dimrep(rep::Vector{MatrixGroup})
  return Int64[degree(rep[i]) for i=1:(length(rep))]
end

# An internal recursive function for the elev method

function _rec(A::Vector{Vector{Int64}},L::Vector{Int64},k::Int64)
  Ind_inter = typeof(A[1])[]
  bool = false
  for t in A
    L_inter = Int64[L[t[l]] for l=1:length(t)]
    if sum(L_inter) == k
      push!(Ind_inter,t)
    else
      for l = (t[end]):(length(L))
        if sum(L_inter) + L[l] <= k
          U = deepcopy(t)
          bool = true
          push!(U,l)
          push!(Ind_inter, U)
        end
      end
    end
  end
  bool == false ? (return Ind_inter) : (return _rec(Ind_inter, L, k))
end

"""
    elev(L::Vector{Int64}, k::Int64) -> Vector{Vector{Int64}}

Given a sorted list of integers `L` and an integer `k`, return all the set of
indices for which the corresponding elements in `L` sum up to `k`. Such sets of
indices are ordered increasingly (not strictly) and the output is ordered in
the lexicographic order from the left.
"""
function elev(L::Vector{Int64}, k::Int64)
  @req L == sort(L) "L has to be a sorted list of integers"
  Ind = Vector{Int64}[[i] for i = 1:(length(L))]
  return _rec(Ind,L,k)
end

# An internal recursive function for the coelev method

function _corec(A::Vector{Vector{Int64}},L::Vector{Int64},k::Int64)
  Ind_inter = typeof(A[1])[]
  bool = false
  for t in A
    L_inter = L[t]
    if length(L_inter) == k
      push!(Ind_inter,t)
    else
      for l=(t[end]):(length(L))
        if L[l] > maximum(L[t])
          U = deepcopy(t)
          bool = true
          push!(U,l)
          push!(Ind_inter, U)
        end
      end
    end
  end
  bool == false ? (return Ind_inter) : (return _corec(Ind_inter, L, k))
end

"""
    coelev(L::Vector{Int64}, k::Int64, minb = false, maxb = true) -> Vector{Vector{Int64}}

Given a sorted list of integers `L` and an integer `k`, return all the set of indices
of length `k` such that the corresponding elements in `L` form a sequence of strictly
increasing integers.

If `minb` or/and `maxb` are specified, the first index `i` of any set of indices
in the output will satisfy `minb <= L[i] <= maxb`. If not specified, `minb = minimum(L)`
and `maxb = maximum(L)`.
"""
function coelev(L::Vector{Int64},k::Int64, minb = false, maxb = false)
  @req L == sort(L) "L has to be a sorted list of integers"
  k > length(L) && return Int64[]
  minb = minb == false ? minimum(L) : max(minb, minimum(L))
  maxb = maxb == false ? maximum(L) : min(maxb, maximum(L))
  Ind = Vector{Int64}[[i] for i=1:length(L) if L[i] in minb:maxb]
  return _corec(Ind,L,k)
end

# An internal recursive function for computing exterior powers 

function _rec_perm(n::Int64,k::Int64)
  if n==0 || k>n || k <= 0
    return Int64[]
  elseif k == 1
    return [[i] for i=1:n]
  elseif k == n
    return [[i for i=1:n]]
  else
    L = Vector{Int64}[]
    for j =k:n
      list1 = _rec_perm(j-1,k-1)
      for l in list1
        push!(l,j)
        push!(L,l)
      end
    end
    return L
  end
end

##############################################################################
#
# Projectively suitable representations
#
##############################################################################

# An internal function computing the quotient of a group by `G` its subgroup of 
# complex multiple of the identity.

function _quo_proj(G::GAP.GapObj)
  e = GG.Exponent(G)
  Elem = GG.Elements(GG.Center(G))
  mult_id = GAP.julia_to_gap([], recursive=true)
  for elem in Elem
    if GG.IsDiagonalMat(elem) && GG.Size(GG.Eigenvalues(GG.CyclotomicField(e),elem)) == 1
      GG.Add(multid,elem)
    end
  end
  return GG.FactorGroup(G,GG.Group(mult_id))
end

"""
    proj_suit_rep(o::Int64, n::Int64, dim::Int64)
              -> Vector{Vector{MatElem{nf_elem}}, Vector{GAP.GapObj}, 
                 Vector{Vector{MatElem{nf_elem}}, Vector{GAP.GapObj}

Given a small group `G` of GAP index `[o,n]`, return representatives of all classes of
complex projectively suitable representations of a Schur cover `E` of `G` of dimension `dim`.

- The first output is the set of representatives given in Oscar matrix form for a minimal set
  of generators `H` of `E`;
- The second output corresponds to the characters of these representations, given as GAP objects;
- The third output is the set of linear characters for `E` given in Oscar matrix form for `H`;
- The last output is the set of linear characters for `E` given as GAP objects.
"""
function proj_suit_rep(o::Int64, n::Int64, dim::Int64)
  G_gap = GG.SmallGroup(o,n)
  f = GG.EpimorphismSchurCover(G_gap)
  f = GG.InverseGeneralMapping(GG.IsomorphismPermGroup(GG.Source(f)))*f
  G_cover = GG.Source(f)
  e = GG.Exponent(G_cover)
  F,z = cyclotomic_field(Int(e))
  H_cover = GG.GeneratorsOfGroup(G_cover)
  Rep = MatrixGroup[]
  lin_oscar = Vector{MatElem{nf_elem}}[]
  ct = GG.CharacterTable(G_cover)
  Irr = GG.Irr(ct)
  lin_gap = [Irr[i] for i=1:(GG.Size(Irr)) if Irr[i][1] == 1]
  for irr in Irr
    if irr[1] <= dim
      rep = GG.IrreducibleAffordingRepresentation(irr)
      Mat_cover = [GG.Image(rep,h) for h in H_cover]
      Mat = MatElem{nf_elem}[]
      for u =1:(length(Mat_cover))
        M_cover = Mat_cover[u]
        k = length(M_cover)
        M = [_convert_gap_to_julia(M_cover[i,j],F,z,Int(e)) for i=1:k, j =1:k]
        push!(Mat, matrix(F,M))
      end
      Mat = [m for m in Mat]
      GM = matrix_group(Mat)
      push!(Rep,GM)
      if degree(GM) == 1
        push!(lin_oscar, Mat)
      end
    end
  end
  L = _dimrep(Rep)
  El = elev(L,dim)
  char_gap = GAP.GapObj[]
  psr = Vector{MatElem{nf_elem}}[]
  for l in El
    Mat = [matrix(g) for g in gens(Rep[l[end]])]
    for i=length(l)-1:-1:1
      Mat = [block_diagonal_matrix([Mat[j], matrix(gens(Rep[l[i]])[j])]) for j=1:length(Mat)]
    end
    chara = GG.Character(G_cover, sum(Irr[l]))
    Facto = GG.FactorGroup(G_cover, GG.CenterOfCharacter(chara))
    !((GG.Size(Facto) == GG.Size(G_gap)) && (GG.IdGroup(Facto) == GG.IdGroup(G_gap))) ? continue : nothing
    bool = true
    if any(lin -> lin*chara in char_gap, lin_gap)
      bool = false
    end
    for Mat_inter in psr
      G_inter = GG.Group(GAP.julia_to_gap(Mat_inter, recursive=true))
      Mat_gap = GAP.julia_to_gap(Mat, recursive=true)
      it2 = count(mat -> mat in G_inter, Mat_gap)       
      it2 == length(Mat) ? bool = false : nothing
    end
    if bool == true 
      push!(psr, Mat)
      push!(char_gap, chara)
    end
  end
  return (psr, char_gap, lin_oscar, lin_gap)
end

##############################################################################
#
# Induced representations
#
##############################################################################

# An internal for computing dual representations in matrix form from those in `Rep`.

function _dual_rep(Rep::Vector{Vector{T}}) where T <: MatElem
  return [transpose.(inv.(rep)) for rep in Rep]
end

"""
    homog_basis(R::MPolyRing{nf_elem}, d::Int64}) -> Vector{MPolyElem{nf_elem}}

Given a multivariate polynomial `R` with the standard grading, return a 
basis of the `d`-homogeneous part of `R`, i.e. all the monomials of homogeneous
degree `d`. The output is ordered in the lexicographic order from the left for the indices
of the variables of `R` involved.
"""
function homog_basis(R::T,d::Int64) where T <: MPolyRing
  n = nvars(R)
  L = Int64[1 for i =1:n]
  E = elev(L,d)
  G = gens(R)
  B = typeof(G[1])[prod(G[e]) for e in E]
  return B
end

# An internal to return at which index appears an element `f` in a basis `B`.

function _index(B::Vector{T}, f::T) where T
  @assert f in B
  return findfirst(b -> b == f, B)
end

# An internal to transform a set of polynomials whose coordinates in a basis
# of the corresponding polynomial algebra `R` are the columns of the given matrix `M`.

function _mat_to_poly(M::MatElem{T}, R::MPolyRing{T}) where T <: RingElem
  @assert nrows(M) == nvars(R) 
  G = gens(R)
  return typeof(G[1])[(change_base_ring(R,transpose(M)[i,:])*matrix(G))[1] for i=1:(size(M)[2])]
end

# An internal that compute the action of a group on an `d`-homogeneous part of
# a polynomial algebra `R` from a matrix form `M` of the action on the variables of `R`.

function _action_poly_ring(M::MatElem{T},R::MPolyRing{T},d::Int64) where T <: RingElem
  @assert nrows(M) == nvars(R) 
  B = homog_basis(R,d)
  v = _mat_to_poly(M,R)
  MM = zeros(base_ring(M), length(B), length(B))
  for i =1:(length(B))
    W = evaluate(B[i],v)
    C = collect(terms(W))
    for c in C
      MM[_index(B,collect(monomials(c))[1]),i] = collect(coeffs(c))[1]
    end
  end
  return matrix(MM)
end

"""
   homo`_`poly`_`rep(Rep:Vector{Vector{T}}, d::Int64, (char`_`gap, ct)::Tuple{Vector{S}, S})
                 where T <: MatElem, S <: GAP.GapObj
                    -> Vector{Vector{T}}, Vector{S}

Given a set `Rep` of linear representations of a group `G` on a finite dimensional complex 
vector space `V`, return the induced representations on the `d` homogeneous part of the dual
of `V` seen as a polynomial algebra.

- The first output is the set of induced representations given in Oscar matrix form;
- The second output is the set of the corresponding characters given as GAP objects
  computed from the input `char_gap`, the characters of the original representations,
  and `ct` the character table of `G`.
"""
function homo_poly_rep(Rep::Vector{Vector{T}}, d::Int64, (char_gap ,ct)::Tuple{Vector{GAP.GapObj},GAP.GapObj}) where T <: MatElem
  rep_homo = Vector{T}[]
  _rep_dual = _dual_rep(Rep)
  _char_dual_gap = GG.ComplexConjugate(GAP.julia_to_gap(char_gap))
  R,x = PolynomialRing(base_ring(Rep[1][1]), "x"=>(1:ncols(Rep[1][1]))) 
  rep_homo = [[_action_poly_ring(m,R,d) for m in rep] for rep in _rep_dual]
  char_homo_gap = GG.SymmetricParts(ct, _char_dual_gap,d)
  return (rep_homo, char_homo_gap)
end

"""
   ext_power(M::MatElem{T}, t::Int64) where T -> MatElem{T}

Return the `t`-exterior power of `M`.
"""
function ext_power(M::MatElem{T}, t::Int64) where T <: RingElem
  n = ncols(M)
  L = _rec_perm(n,t)
  @req L != Int64[] "We must have 0 < t <= ncols(M)"
  return matrix([minors(M[:,J],t) for J in L])
end

"""
    ext_power_rep(rep::Vector{T}, t::Int64) where T <: MatElem{nf_elem}
                             -> Vector{T}

Given a representation of a group on a finite dimensional complex vector space `V`,
return the induced representation on the `t`-exterior power of `V` given in
matrix form.
"""
function ext_power_rep(rep::Vector{T}, t::Int64) where T <: MatElem
  return [ext_power(M,t) for M in rep]
end

##############################################################################
#
# some checks functions
#
##############################################################################

"""
   is`_`smooth(I::T) where T <: MPolyIdeal -> Bool

Given an homogeneous ideal `I`, return `true` if `V(I)` is smooth, `false` else.
"""
function is_smooth(I::T) where T <:MPolyIdeal
  v = [f for f in gens(I)]
  R = base_ring(I)
  x = gens(R)
  D = jacobi_matrix(v)
  J = ideal(R, minors(D, length(v)))
  rad = radical(I+J)
  return rad == ideal(R,x) || rad == ideal(R,[R(1)])
end

# An internal to transform an homogeneous ideal into a matrix whose columns are the coordinates
# of homogenoues generators of the same degree of `I` in an appropriate basis

function _homo_ideal_in_coord(I::T) where T <:MPolyIdeal
  g = gens(I)
  R = base_ring(I)
  F = base_ring(R)
  d = sum(degrees(collect(terms(g[1]))[1]))
  @req all(gg -> sum(degrees(collect(terms(gg))[1])) == d, g) "The generators of `I` must be of the same homogeneous degree"
  B = homog_basis(R,d)
  v = zeros(F,length(B),length(g))
  for i=1:(length(g))
    Coll = collect(terms(g[i]))
    vf = zeros(F, length(B), 1)
    for c in Coll
      vf[_index(B, collect(monomials(c))[1])] = collect(coeffs(c))[1]
    end
    v[:,i] = vf
  end
  return (v,B)
end

# An internal to check if an ideal is invariant under a group action given by `rep_homo`.
# The generators of `I` has to be of the same degree

function _is_invariant_by_rep(rep_homo::Vector{S}, I::T) where {S,T}
  G = gens(I)
  R = parent(G[1])
  F = base_ring(R)
  Coord,_ = _homo_ideal_in_coord(I)
  L,y = PolynomialRing(F,"y" => (1:(ncols(Coord)+1)))
  for M in rep_homo
    for j=1:ncols(Coord)
      act = change_base_ring(L,M*matrix(Coord[:,j]))
      v = y[end]*act-sum([y[i]*change_base_ring(L,matrix(Coord[:,i])) for i=1:ncols(Coord)])
      II = ideal(L,[v[i,:][1] for i=1:nrows(v)])
      J = radical(II)
      J == ideal(L,y) || J == ideal(L,L(1)) ? (return false) : continue
    end
  end
  return true
end

# An internal to check if the action `rep` of a group on `V(I)` is symplectic.

function _is_symplectic_action(rep::Vector, rep_homo::Vector, I) 
  G = gens(I)
  R  = parent(G[1])
  F = base_ring(R)
  Coord, B = _homo_ideal_in_coord(I)
  L,y = PolynomialRing(F,"y" => (1:(ncols(Coord)+1)))
  for i=1:length(rep)
    PM = rep[i]
    M = rep_homo[i]
    MM = matrix(zeros(F,ncols(Coord),ncols(Coord)))
    VV = VectorSpace(F,length(B))
    Var,f = sub(VV, [VV(Coord[:,i]) for i=1:ncols(MM)])
    Pas = hcat([transpose((f\VV(transpose(matrix(Coord[:,j])))).v) for j=1:ncols(MM)])
    for j=1:ncols(MM)
      MM[:,j] = inv(Pas)*transpose((f\VV(transpose(M*matrix(Coord[:,j])))).v)
    end
    l = F(det(PM))*F(inv(det(MM)))
    l != F(1) ? (return false) : continue
  end
  return true
end


##############################################################################
#
# Intersection with Grassmannians
#
##############################################################################

"""
   basis`_`ext`_`power(B::Vector{T}, k::Int64) where T -> Vector{Vector{T}}

Given a basis `B` of a vector space `V`, return a basis of the `t`-exterior power of
`V` as a set of lists. Each list is ordered in strictly increasing order of the 
indices of the corresponding elements in `B`. The output is ordered in the lexicographic
order from the right in the indices of the corresponding elements in `B`
"""
function basis_ext_power(B::Vector{T}, t::Int64) where T
  l = length(B)
  L = _rec_perm(l,t)
  return Vector{T}[B[lis] for lis in L]
end

# An internal to transform a vector representing a basis element `base` of an exterior power
# of a vector space into a matrix whose columns are the coordinates of each elements
# of the vector in a basis `B` of the corresponding vector space.

function _base_to_columns(base::Vector{T}, B::Vector{T}) where T 
  columns = zeros(base_ring(base[1]),length(B), length(base))
  for i=1:length(base)
    columns[_index(B,base[i]),i] = base_ring(base[1])(1)
  end
  return matrix(columns)
end

# An internal that given an element `w` of the `t`-exterior power of a vector space 
# expressed by its coordinates in a basis `basis` of this exterior power, returns it in the
# form of a set of pairs consisting of the coefficients and the corresponding element of 
# the basis (given as a matrix as in `_base_to_columns`) read from the coordinates `w`.

function _change_basis(w, basis::Vector{Vector{T}}) where T 
  @assert length(w) == length(basis) 
  gene = [(w[i],basis[i]) for i =1:length(w) if w[i] != parent(w[i])(0)]
  return gene
end

# An internal to change an homogeneous polynomial of `R` of degree `d`given in 
# coordinates `w` into its polynomial form.

function _coord_in_homo_poly(w::MatElem{T}, R::MPolyRing{T}, d::Int64) where T <: RingElem
  B = homog_basis(R,d)
  @assert length(B) == size(w)[1]
  return sum([w[:,1][i]*B[i] for i=1:(size(w)[1])])
end

# An internal to check if two pure tensors define the same element up to
# reordering.

function _same_base(v::Vector{T}, w::Vector{T}) where T
  @assert length(v) == length(w)
  l = count(vv -> vv in w, v)
  return l == length(v)
end

# An internal that, given two elements representing the same pure tensors, return
# the sign of the permutation of components from one to another.

function _div(v::Vector{T}, w::Vector{T}) where T
  @assert _same_base(v,w)
  return sign(perm([findfirst(vv -> vv == ww, v) for ww in w]))
end

# An internal to check whether or not a pure tensor is a basis tensor. If yes, it
# returns the given basis tensor and the sign of the permutation from one to another.

function _in_basis(v::Vector{T}, basis::Vector{Vector{T}}) where T
  @assert length(v) == length(basis[1])
  i = findfirst(w -> _same_base(v,w),basis)
  i == nothing ? (return false) : (return basis[i], _div(v,basis[i]))
end

# An internal that computeis the sum of two tensors in the same tensor space.

function _sum_tensors(v::Vector{T}, w::Vector{T}) where T
  wbis = deepcopy(w)
  for vv in v
    i = findfirst(ww -> vv[2] == ww[2],w)
    if i == nothing
      push!(wbis, vv)
    else
      wbis[i][1] += vv[1]
    end
  end
  return wbis
end

# An internal that changes the coefficient ring of the coefficients of a tensor, if 
# this change is possible.

function _change_coeff_ring(w::Vector{T}, L) where T
  return [[L(ww[1]), ww[2]] for ww in w]
end

# An internal to rescale the coefficients of a tensor by a same element.

function _rescale(w::Vector{T}, r) where T
  @assert parent(w[1][1]) == parent(r)
  return [[r*ww[1],ww[2]] for ww in w]
end

"""
   is_pure(w::Vector{Vector{SetElem}}, basis::Vector{Vector{T}}, B::Vector{T})
           where T <: MPolyElem
                        -> Tuple{Bool, Vector{T}}

Given an element `w` of an exterior power of an homogeneous part of a polynomial algebra
given as a set of pairs consisting of a coefficient and an element of `basis` in matrix form, 
return whether it defines a pure tensor or not.

If it is, it returns `(true,dec)` where `dec` is a vector of polynomials whose wedge product
is the completely decomposed form of `w`.
If not, it returns `(false, w)`
"""
function is_pure(w, basis::Vector{Vector{T}}) where T <: MPolyElem
  R = parent(basis[1][1])
  d = degrees(basis[1][1])[1]
  B = homog_basis(R,d)
  basis2 = basis_ext_power(B, length(basis[1])+1)
  m, n = length(B), length(basis[1])
  F  = parent(w[1][1])
  Mat = matrix(zeros(F,length(basis2),length(B)))
  for i=1:length(B)
    col = zeros(F,length(basis2),1)
    v = B[i]
    for ww in w
      if v in ww[2]
        continue
      end
      vv, mult = _in_basis(vcat(v, ww[2]), basis2)
      col[_index(basis2,vv)] = ww[1]*mult
      Mat[:,i] = col
    end
  end
  if Oscar.rank(Mat) != m-n
    return (false, w)
  else
    K = kernel(Mat)[2]
    kern = [K[:,j] for j=1:(size(K)[2])]
    return (true, [_coord_in_homo_poly(k,R,d) for k in kern])
  end
end

# An internal to compute the intersection of the projectivisation of a 1-dimensional subvector
# space `W` of the `t`-exterior power of another space `V` with the Grassmannian `Gr(t,V)`. The
# output is false for empty intersection, otherwise it gives the completely decomposed form 
# `dec` of the generator of `W` and the ideal `I` generated by the elements fo the pure tensor.

function _grass_comp(v::MatElem{S}, basis::Vector{Vector{T}}, smooth::Bool=true) where T <: MPolyElem{S} where S
  R = parent(basis[1][1])
  w = _change_basis(v, basis)
  bool, dec  = is_pure(w, basis)
  if bool
    I = ideal(R,[dec[i] for i=1:length(dec)])
    if (smooth == true && is_smooth(I)) || (smooth == false)
      return [(dec, I)]
    else
      return false
    end
  else
    return false
  end
end

# An internal to compute the intersection of the projectivisation of a 2-dimensional subvector
# space `W` of the `t`-exterior power of another space `V` with the Grassmannian `Gr(t,V)`. The
# output is false for empty intersection, otherwise it returns a vector of pairs consisting of
# the completely decomposed form `dec` of an elementt of `W` and the ideal `I` generated by
# the elements of the corresponding pure tensor.

function _grass_comp_snf(V::Vector{T}, basis::Vector{Vector{S}}, smooth::Bool=true) where {T, S}
  @req (length(V)==2 && V[1] != V[2]) "V has to be composed of exactly 2 vectors"
  R = parent(basis[1][1])
  d = degrees(basis[1][1])[1]
  B = homog_basis(R,d)
  basis2 = basis_ext_power(B, length(basis[1])+1)
  m, n = length(B), length(basis[1])
  v1,v2 = V
  w1 = _change_basis(v1,basis)
  w2 = _change_basis(v2,basis)
  F = parent(w1[1][1])
  bool1, _ = is_pure(w1,basis)
  bool2, _ = is_pure(w2,basis)
  L,y = PolynomialRing(F,"y")
  if !bool2
    w = _sum_tensors(_change_coeff_ring(ww1, L), _rescale(_change_coeff_ring(ww2,L),y))
  else
    w = _sum_tensors(_change_coeff_ring(ww2, L), _rescale(_change_coeff_ring(ww1,L),y))
  end
  Mat = matrix(zeros(F,length(basis2),length(B)))
  for i=1:length(B)
    col = zeros(F,length(basis2),1)
    v = B[i]
    for ww in w
      if v in ww[2]
        continue
      end
      vv, mult = _in_basis(vcat(v, ww[2]), basis2)
      col[_index(basis2,vv)] = ww[1]*mult
      Mat[:,i] = col
    end
  end
  A = snf(Mat)
  c = A[m-n+1,m-n+1]
  if c == y || c == L(1) || c == L(0)
    return false
  elseif degree(c) >1
    while evaluate(c,0) == 0
      c = divexact(c,y)
    end
    pot = []
    p = roots(c,F) 
    for r in p
      bool, dec = !bool2 ? is_pure(_change_basis(v1+r*v2,basis), basis) : is_pure(_change_basis(r*v1+v2,basis), basis)
      @assert bool
      I = ideal(R,[dec[i] for i=1:length(dec)])
      if (smooth == true && is_smooth(JJ)) || (smooth == false)
        push!(pot,(dec, I))
      end
    end
    if length(pot) == 0	
      return false
    else
      return pot
    end
  else
    r = roots(c,F)[1]
    bool, dec = !bool2 ? is_pure(_change_basis(v1+r*v2,basis), basis) : is_pure(_change_basis(r*v1+v2,basis), basis)
    @assert bool	
    I = ideal(R,[dec[i] for i=1:length(dec)])
    if (smooth == true && is_smooth(II)) || (smooth == false)
      return [(dec, I)]
    else
      return false
    end
  end
end
    
# An internal function that returns the intersection of an isotypic component of weight 1 of
# the `t`-exterior power `W` of the `d`-homogeneous part `V` of a polynomial algebra with
# the Grassmannian `Gr(t,V). `W` is seen as a group algebra via `rep`. The input 'smooth' is
# to allow only the elements in the intersection generating an ideal defining a smooth variety.

function _inv_space(rep, chi , basis, smooth::Bool=true) 
  VS = VectorSpace(base_ring(rep[1]), ncols(rep[1]))
  v = eigenspace(transpose(rep[1]), trace(chi[1]))
  V,f = sub(VS, [VS(w) for w in v])
  for i = 2:(length(chi))
    vv = eigenspace(transpose(rep[i]), trace(chi[i]))
    VV,  = sub(VS, VS.(vv))
    V, ff = intersect(V,VV)
    f = compose(ff,f)
  end
  if length(gens(V)) == 0
    return false
  elseif length(gens(V)) == 1
    gen = f(gens(V)[1])
    vect = gen.v
    return _grass_comp(vect, basis, smooth)
  elseif length(gens(V)) == 2
    gen = [f(gens(V)[1]).v,f(gens(V)[2]).v]
    return _grass_comp_snf(gen,basis, smooth)
  else
    return [([f(gens(V)[i]).v for i=1:length(gens(V))],false)]
  end
end

##############################################################################
#
# Invariant homogeneous ideals under group actions
#
##############################################################################

"""
    invariant`_`ideal`_`same`_`degree(Id::Tuple{Int64, Int64}, nvar::Int64, degree::Int64, 
				dim::Int64; smooth::Bool = true, symplectic::Bool = false, 
				stopfirst::Bool = false)
                                                -> Vector{Vector{MPolyIdeal}, Vector{MatElem}}

Given a small group `G` of GAP ID `Id`, return all the homogeneous ideals generated by `dim` 
polynomials in `nvar` variables and of the same degree `degree`. The output consists of a 
vector of pairs `([I_1, dots, I_k], rep)` where the `I_i`'s are ideals invariant under the 
action of `G` given by `rep`.

If `smooth = true`, then only the ideals defining a smooth variety are returned.
If `symplectic = true`, then only the ideal defining a variety on which `G` acts symplectically
are returned.
If `stopfirst = true`, then the function returns the first vector tuple `(I,rep)` satisfying the
inputs.
"""
function invariant_ideal_same_degree(Id::Tuple{Int64,Int64}, nvar::Int64, degree::Int64, dim::Int64; smooth::Bool = true, symplectic::Bool = false, stopfirst = false)
  o,b,d,t = Id[1], Id[2], degree, dim
  (psr, char_gap, lin_oscar, lin_gap) = proj_suit_rep(o,b, nvar)
  F = base_ring(psr[1][1])
  ct = GG.CharacterTable(GG.UnderlyingGroup(char_gap[1]))
  R,x = PolynomialRing(F,"x"=>(1:nvar))
  rep_homo, char_homo_gap  = homo_poly_rep(psr,d, (char_gap,ct))
  B = homog_basis(R,d)
  basis = basis_ext_power(B,t)
  char_ext_gap = t == 1 ? char_homo_gap : GG.AntiSymmetricParts(ct, char_homo_gap,t)
  L_rep = length(psr)
  println(L_rep)
  result = []
  for i=1:L_rep
    chara = char_ext_gap[i]
    result2 = []
    rep = t == 1 ? rep_homo[i] : ext_power_rep(rep_homo[i],t)	
    nice_char = [lin_oscar[j] for j=1:(length(lin_oscar)) if GG.ScalarProduct(chara, lin_gap[j]) !=0]
    for chi in nice_char
      pot = _inv_space(rep, chi, basis, smooth)
      if pot != false
        V, I = [pott[1] for pott in pot], [pott[2] for pott in pot]
        result_int = symplectic ? union([II for II in I if II != false && _is_symplectic_action(psr[i], rep_homo[i], II)],[V[i] for i=1:length(V) if I[i] == false]) : union([II for II in I if II != false],[V[i] for i=1:length(V) if I[i] == false])
        all(v -> v isa MPolyIdeal, result_int) ? (stopfirst ? (return (result_int[1], psr[i])) : result2 = union(result2, result_int)) : (result2 = union(result2, result_int)) 
      end
    end
    length(result2) >0 ? push!(result, (result2, psr[i])) : nothing	  
  end
  return result
end


#######################################################################################
#
# In progress: decomposition of intersection with the Grassmannian varieties of 
# dimension greater than 2.
#
#######################################################################################

# An internal to compute a matrix of an isomprhism from the `t`-exterior power of a 
# `n`-dimensional vector space to the `(n-t)`-exterior power of its dual.

function _matrix_ext_powers(B::Vector{T},k::Int64, l::Int64) where T <: MPolyElem{nf_elem}
  @req length(B) == k+l "l should be equal to length(B)-k"
  basis = basis_ext_power(B,k)
  basis2 = basis_ext_power(B,l)
  F = base_ring(B[1])
  Mat = matrix(zeros(F, length(basis2), length(basis)))
  for j=1:length(basis)
    bt = basis[j]
    i = findfirst(i -> isempty(intersect(bt, basis2[i])), 1:length(basis2))
    b = vcat(bt,basis2[i])
    perma = Int64[_index(B,poly) for poly in b]
    PP = Perm(perma)
    Mat[i,j] = sign(PP)
  end
  return Mat
end

# An internal to reduce a polynomial sparse matrix by deleting all zero rows and 
# columns, and deleting rows and columns appearing several times.

function _reduction_sparse_mat(M::T) where T <: MatElem{S} where S <: MPolyElem
  @assert !iszero(M)
  M = vcat([M[i,:] for i =1:nrows(M) if !iszero(M[i,:])])
  M = hcat([M[:,j] for j =1:ncols(M) if !iszero(M[:,j])])
  rowM = [M[1,:]]
  for i=2:nrows(M)
    rowint = M[i,:]
    bool = !any(roww -> (rowint == roww || rowint == -roww), rowM)
    bool == true ? push!(rowM, rowint) : continue
  end
  M = vcat(rowM)
  colM = [M[:,1]]
  for j=2:ncols(M)
    colint = M[:,j]
    bool = !any(coll -> (colint == coll || colint == -coll),  colM)
    bool == true ? push!(colM, colint) : continue
  end
  return hcat(colM)
end

# An internal to store sparse matrices into 3 lists: a list of non-zero values, and
# the other lists that keep track of the indices of the rows and columns in which each
# value lies.

function _sparse_matrix_fact(M::T) where T <: MatElem{S} where S <: MPolyElem 
  @assert !iszero(M)
  M = _reduction_sparse_mat(M)
  values = [M[i,j] for j=1:ncols(M), i=1:nrows(M) if !iszero(M[i,j])]
  indrow = [i for j=1:ncols(M), i=1:nrows(M) if !iszero(M[i,j])]
  indcol = [j for j=1:ncols(M), i=1:nrows(M) if !iszero(M[i,j])]
  return (values, indrow, indcol)
end

# An internal that given indices `i,j` returns the value in the sparse matrix,
# at the `i`th row and `j`th column.

function _value(M, i,j)
  val,row,col = M
  k = findfirst(k -> row[k] == i && col[k] == j, 1:length(val))
  k == nothing ? (return parent(val[1])(0)) : (return val[k])
end

# An internal to refactorise a sparse matrix (deleting the zero entries
# in its factorised form).

function _refact(Mfact)
  val, row, col = Mfact
  valbis, rowbis, colbis = typeof(val[1])[], typeof(row[1])[], typeof(col[1])[]
  for i=1:length(val)
    if !iszero(val[i])
      push!(valbis,val[i])
      push!(rowbis, row[i])
      push!(colbis, col[i])
    end
  end
  return (valbis, rowbis, colbis)
end

# An internal that checks is all the elements of a list are distinct.

function _distinct(L)
  L2 = [L[1]]
  for l in L
    !(l in L2) ? (push!(L2,l)) : continue 
  end
  return L2 == L
end

# An internal to compute, step-by-step the ideal generated by the minors of a certain size of
# a sparse matrix. The step can be chosen, 10000 by default, and the depth of the wanted
# ideal can be bounded by dim_min and dim_max, in order to reduce the computations.

function _approx_ideal_minors_sparse_matrix(M::T, k::Int64; step::Int64 = 10000, dim_min::Int64 = 0, dim_max = inf) where T <: MatElem{S} where S <: MPolyElem
  val, row, col = _sparse_matrix_fact(M)
  @assert k <= length(val)
  L = parent(val[1])
  @assert L isa MPolyRing
  dim_min = max(dim_min, 0)
  dim_max = min(dim_max, length(gens(L)))
  @assert dim_min <= dim_max
  it = maximum(row)
  I = ideal(L,L(0))
  for i=it:-1:1
    CO =  coelev(row,k,i,i)
    indices = [index for index in CO if _distinct(col[index])]
    q,r = divrem(length(indices), step)
    JJ = [det(M[row[index], sort(col[index])]) for index in indices[1:r]]
    I = length(JJ) > 0 ? radical(I+ideal(L,JJ)) : I
    dima = dim(quo(L,I)[1])
    dima <= dim_max ? (dima == dim_max ? (return [prime[2] for prime in primary_decomposition(I) if dim_min <= dim(quo(L,prime[2]))[1] <= dim_max]) : (return false)) : nothing
    for j in r:step:(length(indices)-step)
      JJ = [det(M[row[index], sort(col[index])]) for index in indices[j+1:j+step]]
      I = length(JJ) > 0 ? radical(I+ideal(L,JJ)) : I
      dima = dim(quo(L,I)[1])
      dima <= dim_max ? (dima == dim_max ? (return [prime[2] for prime in primary_decomposition(I) if dim_min <= dim(quo(L,prime[2]))[1] <= dim_max]) : (return false)) : nothing
    end
  end
  return [prime[2] for prime in primary_decomposition(I) if dim_min <= dim(quo(L,prime[2]))[1] <= dim_max]
end

# An internal still under development to improve the previous function without
# having to compute minors.

function _ideal_degeneracy(Mfact, k, it = 1)
  val, row, col = Mfact
  L = parent(val[1])
  y = gens(L)
  if it > length(y)
    return [ideal(L, L(1))]
  end
  iszero(val) ? (return [ideal(L,L(1))]) : (Mfact = _refact(Mfact))
  val, row, col = Mfact
  elem1 = deepcopy(y)
  elem1[it] = L(0)
  if k == 1
    if length(val) == 0
      return [ideal(L, L(1))]
    else
      return [p[2] for p in primary_decomposition(ideal(L, val))]
    end
  end
  index1 = findfirst(p -> total_degree(evaluate(p, elem1)) == -1, val)
  p, i, j = val[index], row[index], col[index]
  for k=1:length(val)
    if (row[k] == i) && (col[k] != j)
      for l=1:length(val)
        if col[l] == col[k]
	  val[l] = val[l]*p - val[k]*_value(Mfact, row[l], j)
	end
      end
    end
  end
  val2, row2, col2 = typeof(val[1])[], [], []
  for k=1:length(val)
    if (row[k] != i) && (col[k] != j)
      push!(val2, val[k])
      roww = row[k] < i ? row[k] : row[k]-1
      push!(row2,roww)
      coll = col[k] < j ? col[k] : col[k]-1
      push!(col2, coll)
    end
  end
  L2 = isempty(val2) ? [ideal(L,L(1))] : _ideal_degeneracy((val2, row2,col2), k-1, it+1)
  val3 = [evaluate(pp, elem1) for pp in val]
  L3 = _ideal_degeneracy((val3,row,col), k, it+1)
  L2 = [I for I in L2 if I != ideal(L, L(1))]
  L3 = [I for I in L3 if I != ideal(L,L(1))]
  return union(L2,L3)
end

# An internal to compute the matrix of the linear map from which we read the pure tensors 
# from the degeneracy locus at which the rank doesn't exceed a certain rank.

function _matrix_multivec_star(V, B, k::Int64)
  @assert base_ring(B[1]) == parent(V[1][1])
  R = parent(B[1])
  F = base_ring(R)
  l = length(B)-k
  Basis = basis_ext_power(B,k)
  Basis2 = basis_ext_power(B,l)
  Basis3 = basis_ext_power(B,l+1)
  L,y = PolynomialRing(F,"y"=>(1:length(V)))
  w = sum([y[i]*change_base_ring(L,V[i]) for i=1:length(V)])
  Mat = _matrix_ext_powers(B,k,l)
  wstar = _change_basis(Mat*transpose(w), Basis2)
  Mat = matrix(zeros(L,length(Basis3),length(B)))
  for i=1:length(B)
    col = zeros(L,length(Basis3),1)
    v = B[i]
    for ww in wstar
      if v in ww[2]
        continue
      end
      vv, mult = _in_basis(vcat(ww[2],v), Basis3)
      col[_index(Basis3,vv)] = ww[1]*mult
      Mat[:,i] = col
    end
  end
  return Mat
end

# An internal still under development and improvement to compute intersection with 
# Grassmannian varieties in dimension bigger than 2.

function _grass_comp_big_degree(v, basis; step = 10000, dim_min = 0, dim_max = inf)
  R = parent(basis[1][1])
  d = degrees(basis[1][1])[1]
  B = homog_basis(R,d)
  k = length(basis[1])
  M = _matrix_multivec_star(v, B, k)
  return _approx_ideal_minors_sparse_matrix(M,k+1, step = step, dim_min = dim_min, dim_max = dim_max)
end

