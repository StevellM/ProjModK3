GG = GAP.Globals
GG.LoadPackage(GAP.julia_to_gap("repsn"))
using Markdown

### An extra macro for the input checks 

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
# Helpers
#                                                                            
##############################################################################

### Extra converter

"""
  A conversion to transform elements of cyclotomic fields from GAP to Oscar
"""
function _convert_gap_to_julia(w_gap,F::AnticNumberField,z::nf_elem,n::Int64)
  L = GAP.gap_to_julia(GG.CoeffsCyc(w_gap,n))   
  w = sum([F(L[l]*z^(l-1)) for l=1:length(L) if L[l] !=0], init = F(0))
  return w
end

### Lists operations

"""
  Given a sorted list of integers, return the list of distinct integers in
  the last, and a second list giving the number of occurence of each value.
"""
function content(L::Vector{Int64})
  @assert issorted(L)
  Lu = unique(L)
  cont = Int64[]
  for i in Lu
    numb = count(j -> j == i, L)
    push!(cont, numb)
  end
  return Lu, cont
end

content(a::Int64) = content([a])

"""
  An internal to return at which index appears an element `f` in a basis `B`.
"""
function _index(B::Vector{T}, f::T) where T
  @req f in B "f not in B"
  return findfirst(b -> b == f, B)
end

"""
  Return the list of elements in a list `A` which satisfies a function `f`.
"""
function keep(f, A)
  lis = [i for i=1:length(A) if f(A[i])]
  return A[lis]
end

"""
  An internal that checks is all the elements of a list are distinct.
"""
function _distinct(L)
  L2 = [L[1]]
  for l in L
    !(l in L2) ? (push!(L2,l)) : continue 
  end
  return L2 == L
end

##############################################################################
#
# Combinatoric
#
##############################################################################

### Elevators

"""
  An internal recursive function for the elev method
"""

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
  @req issorted(L) "L has to be a sorted list of integers"
  Ind = Vector{Int64}[[i] for i = 1:(length(L))]
  return _rec(Ind,L,k)
end

### For exterior powers

"""
  Use to construct all all tuples of `k` distinct among `1, ...,n` for exterior
  powers.
"""
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

###############################################################
#
#  Tool to construct all possible character of a certain degree
#
###############################################################

### Get list information 

"""
  Given a sorted list of integers `L` and an integer `d`, return the number of
  distinct possible sums of elements in `L` to `d`, the type of this sums, and
  the cumulative numbers of type of sums
"""
function _number_sums(L::Vector{Int64}, d::Int64)
  Lu, numb = content(L)
  El = elev(Lu, d)
  sums = [Lu[el] for el in El]
  len = 0
  cumul = Int64[0]
  sumsum = []
  for sum in sums
    if length(sum) == 1
      for i in [i for i in 1:length(L) if L[i] == sum[1]]
        len += 1
        push!(cumul, len)
        push!(sumsum, (i, sum))
      end
    else
      it = 0
      LL = copy(L)
      while sum[1] in LL
        j = _index(LL, sum[1])
        LLu, numbLL = content(LL)
        Lu2, numb2 = content(sum[2:end])
        len += prod([binomial(numbLL[_index(LLu, Lu2[i])]+numb2[i]-1,numb2[i]) for i=1:length(Lu2)])
        LL = LL[j+1:end]
        it += j
        push!(cumul, len)
        push!(sumsum, (it, sum))
      end
    end
  end
  return len, cumul, sumsum
end

### "Elevations" for big lists

mutable struct ElevCtx
  L::Vector{Int64}
  d::Int64
  length::Int64
  cumul_length::Vector{Int64}
  sums::Vector{Tuple{Int64, Vector{Int64}}}

  function ElevCtx(L::Vector{Int64}, d::Int64)
    z = new(L, d)
    len, cumul, sumsum = _number_sums(L, d)
    z.length = len
    z.cumul_length = cumul
    z.sums = sumsum
    return z
  end
end

len(EC::ElevCtx) = EC.length
cumulated_lengths(EC::ElevCtx) = EC.cumul_length
base_list(EC::ElevCtx) = EC.L
degree(EC::ElevCtx) = EC.d
possible_sums(EC::ElevCtx) = EC.sums

function _rec_get_index(EC2::ElevCtx, i::Int64, sumtype::Vector{Int64})
  @assert 0 < i <= len(EC2)
  cumul2 = cumulated_lengths(EC2)
  sumsum2 = possible_sums(EC2)
  j = findfirst(j -> cumul2[j+1] >= i > cumul2[j] && sumsum2[j][2] == sumtype, 1:length(cumul2)-1)
  indexL2, sumtype2 = sumsum2[j]
  if length(sumtype2) == 1
    return [indexL2]
  end
  d = degree(EC2)
  L2 = base_list(EC2)
  el2 = [indexL2]
  EC3 = ElevCtx(L2[indexL2:end], d-L2[indexL2])
  i2 = -cumul2[j]
  i2 += sum([cumul2[k+1]-cumul2[k] for k =1:j-1 if sumsum2[k][1] == indexL2])
  suite = [indexL2 - 1 + i for i = _rec_get_index(EC3, i+i2, sumtype2[2:end])]
  el2 = vcat(el2, suite)
  return el2
end

function Base.getindex(EC::ElevCtx, i::Int64)
  @assert 0 < i <= len(EC) 
  cumul = cumulated_lengths(EC)
  j = findfirst(j -> cumul[j+1] >= i > cumul[j], 1:length(cumul)-1)
  sumsum = possible_sums(EC)
  indexL, sumtype = sumsum[j]
  if length(sumtype) == 1
    return [indexL]
  end
  d = degree(EC)
  L = base_list(EC)
  el = [indexL]
  EC2 = ElevCtx(L[indexL:end], d-L[indexL])
  i2 = -cumul[j]
  i2 += sum([cumul[k+1]-cumul[k] for k =1:j-1 if sumsum[k][1] == indexL])
  suite = [indexL - 1 + i for i = _rec_get_index(EC2, i+i2, sumtype[2:end])]
  el = vcat(el, suite)
  return el
end

Base.lastindex(EC::ElevCtx) = len(EC)

function Base.iterate(EC::ElevCtx, i::Int64 = 1)
  if i > len(EC)
    return nothing
  end
  return EC[i], i+1
end

##############################################################################
#
# Projective representations
#
##############################################################################


### Associated structures

@attributes mutable struct RepRing{S, T, U, V} 
  field::S
  group::T
  gens::U
  ct::V
  irr

  function RepRing(E::T) where {T <: Oscar.GapObj}
    e = GG.Exponent(E)
    F, _ = cyclotomic_field(e)
    ct = GG.CharacterTable(E)
    Irr = GG.Irr(ct)
    H = GG.GeneratorsOfGroup(E)
    RR = new{typeof(F), T, typeof(H), typeof(ct)}(F, E, H, ct, Irr)
    return RR
  end
end

splitting_field(RR::RepRing) = RR.field

underlying_group(RR::RepRing) = RR.group

generators_of_group(RR::RepRing) = RR.gens

character_table(RR::RepRing) = RR.ct

irreducible_characters(RR::RepRing) = RR.irr

polynomial_algebra(RR::RepRing) = get_attribute(RR, :poly_ring)

@attributes mutable struct LinRep{S, T, U, V, W} 
  rep_ring::RepRing{S, T, U, V}
  mats::Vector{MatElem}
  char_gap::W

  function LinRep(RR::RepRing{S,T,U, V}, MR::Vector{ <: MatElem}, CG::W) where {S, T, U, V, W}
    z = new{S, T, U, V, W}()
    z.rep_ring = RR
    z.mats = MR
    z.char_gap = CG
    return z
  end
end

representation_ring(LR::LinRep) = LR.rep_ring

matrix_representation(LR::LinRep) = LR.mats

char_gap(LR::LinRep) = LR.char_gap

dim(LR::LinRep) = LR.char_gap[1]

@attributes mutable struct ProjRep{S, T, U, V, W} 
  LR::LinRep{S, T, U, V, W}
  G::T

  function ProjRep(LR::LinRep{S, T, U, V, W}, G::T) where {S, T, U, V, W}
    z = new{S, T, U, V, W}()
    z.LR = LR
    z.G = G
    return z
  end
end

lift(PR::ProjRep) = PR.LR

underlying_group(PR::ProjRep) = PR.G

representation_ring(PR::ProjRep) = representation_ring(PR.LR)

matrix_representation(PR::ProjRep) = matrix_representation(PR.LR)

char_gap(PR::ProjRep) = char_gap(PR.LR)

dim(PR::ProjRep) = dim(PR.LR)

function Base.show(io::IO, ::MIME"text/plain", RR::RepRing)
  println(io, "Representation ring of")
  println(io, "$(RR.group)")
  println(io, "over")
  print(io, "$(RR.field)")
end

function Base.show(io::IO, RR::RepRing)
  print(io, "Representation ring of finite group over a field of characteristic 0")
end

function Base.show(io::IO, ::MIME"text/plain", LR::LinRep)
  println(io, "Linear $(dim(LR))-dimensional representation of")
  println(io, "$(LR.rep_ring.group)")
  println(io, "over")
  println(io, "$(LR.rep_ring.field)")
  println(io, "with matrix representation")
  print(io, "$(LR.mats)")
end 

function Base.show(io::IO, LR::LinRep)
  print(io, "Linear representation of finite group of dimension $(dim(LR))")
end

function Base.show(io::IO, ::MIME"text/plain", PR::ProjRep)
  println(io, "Linear lift of a $(dim(PR))-dimensional projective representation of")
  println(io, "$(PR.G)")
  println(io, "over")
  println(io, "$(PR.LR.rep_ring.field)")
  println(io, "with matrix representation")
  print(io, "$(PR.LR.mats)")
end

function Base.show(io::IO, PR::ProjRep)
    print(io, "Linear lift of a projective representation of finite group of dimension $(dim(PR.LR))")
end


### Identification of matrix representations

"""
  An internal function computing the quotient of a finite matrix group `G` by 
  its subgroup of complex multiple of the identity.
"""
function _quo_proj(G::GAP.GapObj)
  e = GG.Exponent(G)
  Elem = GG.Elements(GG.Centre(G))
  mult_id = GAP.julia_to_gap([], recursive=true)
  for elem in Elem
    if GG.IsDiagonalMat(elem) && GG.Size(GG.Eigenvalues(GG.CyclotomicField(e),elem)) == 1
      GG.Add(mult_id,elem)
    end
  end
  return GG.FactorGroup(G,GG.Group(mult_id))
end

"""
  An internal function computing the GAP matrix group associated to the matrix
  form of a representation
"""
function _rep_to_gap_group(rep::Vector{T}) where T <: MatElem
  rep_gap = GAP.julia_to_gap(rep, recursive = true)
  return GG.Group(rep_gap)
end

"""
  An internal function which returns, if it exists, the GAP id of the matrix group
  generated by `rep` modulo the multiple of the identity
"""
function _id_group_rep(rep::Vector{T}) where T <: MatElem
  G_gap = _rep_to_gap_group(rep)
  if !GG.IsFinite(G_gap)
    return "Possibly infinite group"
  end
  G_gap = _quo_proj(G_gap)
  if !GG.IdGroupsAvailable(GG.Size(G_gap))
    return "Group of order $(GG.Size(G_gap))"
  else
    return GG.IdGroup(G_gap)
  end
end

"""
  An internal functions checking whether the matrix form `rep` of a representation
  defines a projectively faitful representation of `GG.SmallGroup(o,n)`.
"""
function _is_good_pfr(rep::Vector{T}, (o,n)::Tuple{Integer, Integer}) where T <: MatElem
  G_gap = _rep_to_gap_group(rep)
  if !GG.IsFinite(G_gap)
    return false
  end
  G_gap = _quo_proj(G_gap)
  GG.Size(G_gap) != o ? (return false) : (return GAP.gap_to_julia(GG.IdGroup(G_gap)) == [o,n])
end

### Projectively faithful representations

"""
  An internal function which checks whether a small group `G_gap` admits
  faitful projective representations of dimension `dim`. If yes, it returns the
  necessary tools to create the projectively faithful representations of a Schur
  cover associated to those faithful projective representations
"""
function _has_pfr(G_gap::GAP.GapObj, dim::Int64)
  f = GG.EpimorphismSchurCover(G_gap)
  H = GG.Source(f)
  n, p = ispower(GG.Size(H))
  if isprime(p)
    G_cover = GG.Image(GG.EpimorphismPGroup(H, p))
  else
    G_cover = GG.Image(GG.IsomorphismPermGroup(H))
  end
  RR = RepRing(G_cover)
  ct = character_table(RR)
  Irr = irreducible_characters(RR)
  Irr = keep(irr -> irr[1] <= dim, Irr)
  L = [irr[1] for irr in Irr]
  ps = sortperm(L)
  L, Irr = L[ps], Irr[ps]
  RR.irr = Irr
  lin_gap = [Irr[i] for i=1:length(Irr) if Irr[i][1] == 1]
  set_attribute!(RR, :lin_gap, lin_gap)
  set_attribute!(RR, :poly_ring, PolynomialRing(RR.field, "x" => 1:dim, cached = false)[1])
  keep_index = Int64[]
  sum_index = Vector{Int64}[]
  char_gap = GAP.GapObj[]
  local El::ElevCtx
  El = ElevCtx(L, dim)
  @info "Classify $(len(El)) many projective representations."
  for l in El
    chi = sum(Irr[l])
    if any(lin -> lin*chi in char_gap, lin_gap)
      continue
    end
    Facto = GG.FactorGroup(G_cover, GG.CenterOfCharacter(chi))
    if !((GG.Size(Facto) == GG.Size(G_gap)) && (GG.IdGroup(Facto) == GG.IdGroup(G_gap)))
      continue
    end
    push!(char_gap, chi)
    keep_index = union(keep_index, l)
    push!(sum_index, l)
  end
  bool = length(keep_index) > 0
  return bool, RR, keep_index, sum_index
end

"""
    projectively_faithful_representations(o::Int64, n::Int64, dim::Int64)
                      -> Vector{Vector{MatElem{nf_elem}}, Vector{GAP.GapObj}, 
                         Vector{Vector{MatElem{nf_elem}}, Vector{GAP.GapObj}

Given a small group `G` of GAP index `[o,n]`, return representatives of all classes of
complex projectively faithful representations of a Schur cover `E` of `G` of dimension `dim`.
"""
function projectively_faithful_representations(o::Int64, n::Int64, dim::Int64)
  G_gap = GG.SmallGroup(o,n)
  bool, RR, keep_index, sum_index = _has_pfr(G_gap, dim)
  if bool == false
    return ProjRep[]
  end
  @info "Construct $(length(sum_index)) many projectively faithful representations."
  F = splitting_field(RR)
  e = get_attribute(F, :cyclo)
  z = gen(F)
  H_cover = generators_of_group(RR)
  ct = character_table(RR)
  Irr = irreducible_characters(RR)
  G_cover = underlying_group(RR)
  Rep = Vector{MatElem{nf_elem}}[]
  lin_gap = get_attribute(RR, :lin_gap)
  lin_oscar = Vector{MatElem{nf_elem}}[]
  for lin in lin_gap
    rep = GG.IrreducibleAffordingRepresentation(lin)
    Mat_cover = [GG.Image(rep,h) for h in H_cover]
    Mat = MatElem{nf_elem}[]
    for u =1:(length(Mat_cover))
      M_cover = Mat_cover[u]
      k = length(M_cover)
      M = [_convert_gap_to_julia(M_cover[i,j],F,z,Int(e)) for i=1:k, j =1:k]
      push!(Mat, matrix(F,M))
    end
    Mat = [m for m in Mat]
    push!(lin_oscar, Mat)
  end
  set_attribute!(RR, :lin_oscar, lin_oscar) 
  for index in keep_index
    irr = Irr[index]
    j = findfirst(j -> irr == lin_gap[j], 1:length(lin_gap))
    if j === nothing
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
    else
      Mat = lin_oscar[j]
    end
    push!(Rep, Mat)
  end
  pfr = ProjRep[]
  for l in sum_index
    chara = sum(Irr[l])
    @assert chara[1] == dim
    Mat = Rep[_index( keep_index, l[end])]
    for i=length(l)-1:-1:1
      Mat = [block_diagonal_matrix([Mat[j], Rep[_index(keep_index, l[i])][j]]) for j=1:length(Mat)]
    end
    MG = matrix_group(Mat)
    bool = true
    for pr in pfr
      Mat_inter = matrix_representation(pr)
      G_inter = matrix_group(Mat_inter)
      MG == G_inter ? bool = false : nothing
    end
    if bool == true
      lr = LinRep(RR, Mat, chara)
      pr = ProjRep(lr, G_gap)
      push!(pfr, pr)
    end
  end
  return pfr
end

### Projective representations 

"""
  An internal function which checks whether a small group `G_gap` admits projective
  representations of dimension `dim` with kernel of dimension at most `index_max`.
  If yes, it returns the tools necessary to compute the linear representations
  of a Schur cover corresponding to those projective representations
"""
function _has_pr(G_gap::GAP.GapObj, dim::Int64; index_max::IntExt = inf)
  f = GG.EpimorphismSchurCover(G_gap)
  H = GG.Source(f)
  n, p = ispower(GG.Size(H))
  if isprime(p)
    G_cover = GG.Image(GG.EpimorphismPGroup(H, p))
  else
    G_cover = GG.Image(GG.IsomorphismPermGroup(H))
  end
  RR = RepRing(G_cover)
  ct = character_table(RR)
  Irr = irreducible_characters(RR)
  Irr = keep(irr -> irr[1] <= dim, Irr)
  L = [irr[1] for irr in Irr]
  ps = sortperm(L)
  L, Irr = L[ps], Irr[ps]
  RR.irr = Irr
  lin_gap = [Irr[i] for i=1:length(Irr) if Irr[i][1] == 1]
  set_attribute!(RR, :lin_gap, lin_gap)
  set_attribute!(RR, :poly_ring, PolynomialRing(RR.field, "x" => 1:dim, cached = false)[1])
  keep_index = Int64[]
  sum_index = Vector{Int64}[]
  char_gap = GAP.GapObj[]
  local El::ElevCtx
  El = ElevCtx(L, dim)
  @info "Classify $(len(El)) many projective representations."
  for l in El
    chi = GG.Character(G_cover, sum(Irr[l]))
    @assert chi[1] == dim
    keep = true
    Facto = GG.FactorGroup(G_cover, GG.CenterOfCharacter(chi))
    idx, r = divrem(GG.Size(G_gap), GG.Size(Facto))
    if (r == 0 && idx <= index_max)
      if idx == 1
        if GG.IdGroup(Facto) != GG.IdGroup(G_gap)
          keep = false
        end
      end
      if any(lin -> lin*chi in char_gap, lin_gap)
        keep = false
      end
    else
      keep = false
    end
    if keep == true
      push!(char_gap, chi)
      keep_index = union(keep_index, l)
      push!(sum_index, l)
    end
  end
  bool = length(keep_index) > 0
  return bool, RR, keep_index, sum_index
end

"""
  Return projective representations of a group, given as linear representations
  of a Schur cover, for which the kernel as maximal index `index_max` in the 
  group
"""
function projective_representations(o::Int64, n::Int64, dim::Int64; index_max::IntExt = inf)
  @req (o >= index_max || index_max == inf) "index_max must be smaller than the order of the group"
  index_max = min(o, index_max)
  if (index_max == 1)
    return projectively_faithful_representations(o, n, dim)
  end
  G_gap = GG.SmallGroup(o,n)
  bool, RR, keep_index, sum_index = _has_pr(G_gap, dim, index_max = index_max)
  if bool == false
    return ProjRep[]
  end
  @info "Construct $(length(sum_index)) many projective representations."
  F = splitting_field(RR)
  e = get_attribute(F, :cyclo)
  z = gen(F)
  H_cover = generators_of_group(RR)
  ct = character_table(RR)
  Irr = irreducible_characters(RR)
  G_cover = underlying_group(RR)
  Rep = Vector{MatElem{nf_elem}}[]
  lin_gap = get_attribute(RR, :lin_gap)
  lin_oscar = Vector{MatElem{nf_elem}}[]
  for lin in lin_gap
    rep = GG.IrreducibleAffordingRepresentation(lin)
    Mat_cover = [GG.Image(rep,h) for h in H_cover]
    Mat = MatElem{nf_elem}[]
    for u =1:(length(Mat_cover))
      M_cover = Mat_cover[u]
      k = length(M_cover)
      M = [_convert_gap_to_julia(M_cover[i,j],F,z,Int(e)) for i=1:k, j =1:k]
      push!(Mat, matrix(F,M))
    end
    Mat = [m for m in Mat]
    push!(lin_oscar, Mat)
  end
  set_attribute!(RR, :lin_oscar, lin_oscar)
  for index in keep_index
    irr = Irr[index]
    j = findfirst(j -> irr == lin_gap[j], 1:length(lin_gap))
    if j === nothing
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
    else
      Mat = lin_oscar[j]
    end
    push!(Rep, Mat)
  end
  pfr = ProjRep[]
  for l in sum_index
    chara = sum(Irr[l])
    @assert chara[1] == dim
    Mat = Rep[_index( keep_index, l[end])]
    for i=length(l)-1:-1:1
      Mat = [block_diagonal_matrix([Mat[j], Rep[_index(keep_index, l[i])][j]]) for j=1:length(Mat)]
    end
    bool = true
    for pr in pfr
      Mat_inter = matrix_representation(pr)
      G_inter = matrix_group(Mat_inter)
      it2 = count(mat -> mat in G_inter, Mat)       
      it2 == length(Mat) ? bool = false : nothing
    end
    if bool == true
      lr = LinRep(RR, Mat, chara)
      pr = ProjRep(lr, G_gap)
      push!(pfr, pr)
    end
  end
  return pfr
end

##############################################################################
#
# Polynomial algebra tools
#
##############################################################################

### Basis for homogeneous components

"""
    homog_basis(R::MPolyRing{nf_elem}, d::Int64}) -> Vector{MPolyElem{nf_elem}}

Given a multivariate polynomial ring `R` with the standard grading, return a 
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

### Functions for conversion between abstract homogeneous polynomials and their coordinates
### to the chosen bases

"""
  An internal to transform a set of polynomials whose coordinates in a basis
  of the corresponding polynomial algebra `R` are the columns of the given matrix `M`.
"""
function _mat_to_poly(M::MatElem{T}, R::MPolyRing{T}) where T <: RingElem
  @assert nrows(M) == nvars(R) 
  G = gens(R)
  return typeof(G[1])[(change_base_ring(R,transpose(M)[i,:])*matrix(G))[1] for i=1:(size(M)[2])]
end

"""
  An internal to change a homogeneous polynomials into a vector whose entries are the 
  coefficients of `P` in the canonical basis of the corresponding homogeneous component
"""
function _homo_poly_in_coord(P::T) where T 
  R = parent(P)
  F = base_ring(R)
  d = total_degree(P)
  B = homog_basis(R,d)
  v = zeros(F,length(B), 1)
  Coll = collect(terms(P))
  for c in Coll
    v[_index(B, collect(monomials(c))[1])] = collect(coeffs(c))[1]
  end
  return matrix(v)
end

"""
  An internal to change an homogeneous polynomial of `R` of degree `d` given in 
  coordinates `w` into its polynomial form.
"""
function _coord_in_homo_poly(w::MatElem{T}, R::MPolyRing, d::Int64) where T <: RingElem
  B = homog_basis(R,d)
  @assert length(B) == size(w)[1]
  return sum([w[:,1][i]*B[i] for i=1:(size(w)[1])])
end

"""
  An internal to transform an homogeneous ideal into a matrix whose columns are the coordinates
  of homogenoues generators of the same degree of `I` in an appropriate basis
"""
function _homo_ideal_in_coord(I::T) where T <:MPolyIdeal
  g = gens(I)
  R = base_ring(I)
  F = base_ring(R)
  d = total_degree(g[1])
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

##############################################################################
#
# About tensors of homogeneous polynomials
#
##############################################################################

### Basis of exterior power

"""
   basis`_`exterior`_`power(B::Vector{T}, k::Int64) where T -> Vector{Vector{T}}

Given a basis `B` of a vector space `V`, return a basis of the `t`-exterior power of
`V` as a set of lists. Each list is ordered in strictly increasing order of the 
indices of the corresponding elements in `B`. The output is ordered in the lexicographic
order from the right in the indices of the corresponding elements in `B`
"""
function basis_exterior_power(B::Vector{T}, t::Int64) where T
  l = length(B)
  L = _rec_perm(l,t)
  return Vector{T}[B[lis] for lis in L]
end

### Operations on pure tensors

"""
  An internal to check if two pure tensors define the same element up to
  reordering.
"""
function _same_base(v::Vector{T}, w::Vector{T}) where T
  @assert length(v) == length(w)
  l = count(vv -> vv in w, v)
  return l == length(v)
end

"""
  An internal that, given two elements representing the same pure tensors, return
  the sign of the permutation of components from one to another.
"""
function _div(v::Vector{T}, w::Vector{T}) where T
  @assert _same_base(v,w)
  return sign(perm([findfirst(vv -> vv == ww, v) for ww in w]))
end

"""
  An internal to check whether or not a pure tensor is a basis tensor. If yes, it
  returns the given basis tensor and the sign of the permutation from one to another.
"""
function _in_basis(v::Vector{T}, basis::Vector{Vector{T}}) where T
  @assert length(v) == length(basis[1])
  i = findfirst(w -> _same_base(v,w),basis)
  i == nothing ? (return false) : (return basis[i], _div(v,basis[i]))
end

"""
  An internal that given an element `w` of the `t`-exterior power of a vector space 
  expressed by its coordinates in a basis `basis` of this exterior power, returns it in the
  form of a set of pairs consisting of the coefficients and the corresponding element of 
  the basis (given as a matrix as in `_base_to_columns`) read from the coordinates `w`.
"""
function _change_basis(w, basis::Vector{Vector{T}}) where T 
  @assert length(w) == length(basis) 
  gene = [(w[i],basis[i]) for i =1:length(w) if w[i] != parent(w[i])(0)]
  return gene
end

### wedge product of polynomials

"""
   wedge_product(F::Vector{T}) where T <: MPolyElem 
                                 -> Vector{Tuple{nf_elem}, Vector{MPolyElem}}
                                 
Given a list of homogeneous polynomials `F` of the same polynomial algebra and of the same
total degree, return their wedge product as an abstract tensor, seen as a list of tuples
of coefficients and the respective elements of the basis of the exterior power.
"""
function wedge_product(F::Vector{T}) where T <: MPolyElem
  if length(F) == 1
    f = F[1]
    R = parent(f)
    d = total_degree(f)
    B = homog_basis(R,d)
    basis = basis_exterior_power(B, 1)
    list_mon, list_coeff = collect(monomials(f)), collect(Oscar.coefficients(f))
    part= [(list_coeff[i], [list_mon[i]]) for i=1:length(list_mon)]
    return part
  end
  f = popfirst!(F)
  wp = wedge_product(copy(F))
  R = parent(f)
  d = total_degree(f)
  B = homog_basis(R,d)
  basis = basis_exterior_power(B, length(F)+1)
  list_mon, list_coeff = collect(monomials(f)), collect(Oscar.coefficients(f))
  part = [(list_coeff[i], list_mon[i]) for i=1:length(list_mon)]
  coeffs2 = zeros(base_ring(R), length(basis))
  for l in part
    for w in wp
      if l[2] in w[2]
        continue
      end
      w_co = copy(w[2])
      lw_co = pushfirst!(w_co, l[2])
      ba, mult = _in_basis(lw_co, basis)
      coeffs2[_index(basis, ba)] += mult*w[1]*l[1]
    end
  end
  return _change_basis(coeffs2, basis)
end  

### Operations on arbitrary tensors

"""
  An internal that computes the sum of two tensors in the same tensor space.
"""
function _sum_tensors(v::Vector{T}, w::Vector{T}) where T
  wbis = copy(w)
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

"""
  An internal that changes the coefficient ring of the coefficients of a tensor, if 
  this change is possible.
"""
function _change_coeff_ring(w::Vector{T}, L) where T
  return [[L(ww[1]), ww[2]] for ww in w]
end

"""
  An internal to rescale the coefficients of a tensor by a same element.
"""
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
  d = total_degree(basis[1][1])
  B = homog_basis(R,d)
  basis2 = basis_exterior_power(B, length(basis[1])+1)
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

### Manipulation of tensors by their coordinates to the basis of the exterior power

"""
  An internal to transform a vector representing a basis element `base` of an exterior power
  of a vector space into a matrix whose columns are the coordinates of each elements
  of the vector in a basis `B` of the corresponding vector space.
"""
function _base_to_columns(base::Vector{T}, B::Vector{T}) where T 
  columns = zeros(base_ring(base[1]),length(B), length(base))
  for i=1:length(base)
    columns[_index(B,base[i]),i] = base_ring(base[1])(1)
  end
  return matrix(columns)
end

### Helper for intersection with Grassmannian

"""
  An internal to compute a matrix of an isomorphism from the `t`-exterior power of a 
  `n`-dimensional homogeneous component of a polynomial algebra to the `(n-t)`-exterior 
  power of its dual.
"""
function _matrix_ext_powers(B::Vector{T},k::Int64, l::Int64) where T <: MPolyElem{nf_elem}
  @req length(B) == k+l "l should be equal to length(B)-k"
  basis = basis_exterior_power(B,k)
  basis2 = basis_exterior_power(B,l)
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

"""
  An internal to compute the matrix of the linear map from which we read the pure tensors 
  from the degeneracy locus at which the rank doesn't exceed a certain bound
"""
function _matrix_multivec_star(V, B, k::Int64)
  @assert base_ring(B[1]) == parent(V[1][1])
  R = parent(B[1])
  F = base_ring(R)
  l = length(B)-k
  Basis = basis_exterior_power(B,k)
  Basis2 = basis_exterior_power(B,l)
  Basis3 = basis_exterior_power(B,l+1)
  L,y = PolynomialRing(F,"y"=>(1:length(V)))
  w = sum([y[i]*map_entries(L, V[i]) for i=1:length(V)])
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

##############################################################################
#
# Induced representations
#
##############################################################################

### Helper to compute induced representations on different vector spaces

function _induced_representation(prep::ProjRep, M::Vector{T}, chara::GAP.GapObj) where T <: MatElem
  lr = LinRep(representation_ring(prep), M, chara)
  return ProjRep(lr, underlying_group(prep))
end

### Induced representations on homogeneous component of polynomial algebra

"""
  An internal for computing dual representations in matrix form from those in `Rep`.
"""
function _dual_representation(prep::ProjRep)
  Rep = matrix_representation(prep)
  char = char_gap(prep)
  Rep_dual = [transpose(inv(rep)) for rep in Rep]
  char_dual = GG.ComplexConjugate(GAP.julia_to_gap([char], recursive = true))[1]
  return _induced_representation(prep, Rep_dual, char_dual)
end

"""
  An internal that compute the action of a group on an `d`-homogeneous part of
  a polynomial algebra `R` from a matrix form `M` of the action on the variables of `R`.
"""
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

_homo_poly_action(m, R, d) = _action_poly_ring(transpose(inv(m)), R, d)
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
function homo_poly_rep(prep::ProjRep, d::Int64)
  prep_dual = _dual_representation(prep)
  ct = character_table(representation_ring(prep))
  R = polynomial_algebra(representation_ring(prep))
  if R === nothing
    R, _ = PolynomialRing(splitting_field(representation_ring(prep)), "x" => 1:dim(prep), cached = false)
  end
  Rep_homo = [_action_poly_ring(m,R,d) for m in matrix_representation(prep_dual)]
  char_homo = GG.SymmetricParts(ct, GAP.julia_to_gap([char_gap(prep_dual)], recursive = true),d)[1]
  prep_homo = _induced_representation(prep_dual, Rep_homo, char_homo)
  set_attribute!(prep, :prep_homo, prep_homo)
  set_attribute!(prep_homo, :degree_homo, d)
  return prep_homo
end

### Induced representation on exterior power of homogeneous component of polynomials
### algebra

"""
    ext__homo_poly_rep(Rep::Vector{T}, R::MPolyring, d::Int64, t::Int64) 
                                               where T <: MatElem{nf_elem}
                                                                -> Vector{T}

Given a representation of a group on a the `d` homogeneous part of `R`,
return the induced representation on the `t`-exterior power of `R_d` given in
matrix form.
"""
function ext_homo_poly_rep(prep_homo::ProjRep, t::Int64)
  @req 1 <= t <= dim(prep_homo) "t must be contain between 1 and the dimension $(dim(prep_homo)) of prep"
  d = get_attribute(prep_homo, :degree_homo)
  @assert d !== nothing
  R = polynomial_algebra(representation_ring(prep_homo))
  B = homog_basis(R,d)
  basis = basis_exterior_power(B,t)
  chara = char_gap(prep_homo)
  ct = character_table(representation_ring(prep_homo))
  Rep_homo = matrix_representation(prep_homo)
  prep_ext = typeof(Rep_homo[1])[]
  for M in Rep_homo
    M_ext = zeros(base_ring(M), length(basis), length(basis))
    for i =1:length(basis)
      b = basis[i]
      bb = [_coord_in_homo_poly(M*_homo_poly_in_coord(bbb), R, d) for bbb in b]
      wp = wedge_product(bb)
      for bbb in wp
        M_ext[_index(basis, bbb[2]), i] += bbb[1]
      end
    end
    push!(prep_ext, matrix(M_ext))
  end
  chara_ext = GG.AntiSymmetricParts(ct, GAP.julia_to_gap([chara], recursive=true), t)[1]
  return _induced_representation(prep_homo, prep_ext, chara_ext)
end

##############################################################################
#
# Fitting ideals (with authorization)
#
##############################################################################

"""
  An internal based on a code of Matthias Zach (TU Kaiserslautern) for computation
  of fitting ideals. Here it is used to look for the ideal of coordinates of pure
  tensors (computed from the denegeracy locus for the rank of a sparse matrix) and
  the smoothness test.
"""
function _ideal_degeneracy(X, Mfact, k)
  one(localized_ring(OO(X))) in localized_modulus(OO(X)) ? (return [X.OO.R.base_ring]) : nothing
  
  Mfact = _refact(Mfact)
  val, row, col = Mfact

  if k == 1
    if length(val) == 0  
      return [X]
    else
      Y = subscheme(X, ideal(X.OO.R, val))
      one(localized_ring(OO(X))) in localized_modulus(OO(X)) ? (return [Y.OO.R.base_ring]) : (return [Y])
    end
  end
  
  if length(val) == 0
    return [X]
  end
  
  d = maximum(total_degree.(val))
  (i, j) = (1, 1)

  for l=1:length(val)
    val[l] = numerator(reduce(X.OO.W(val[l]), groebner_basis(localized_modulus(OO(X)))))
    if total_degree(val[l]) <= d && !iszero(val[l])
      d = total_degree(val[l])
      (i, j) = (row[l], col[l])
    end
  end
  
  v = _value(Mfact, i, j)

  if iszero(val)
    return [X]
  end
  
  val2, row2, col2 = typeof(val[1])[], [], []
  for l in union(1:(i-1), (i+1):maximum(row))
    for m=1:maximum(col)
      vall = _value(Mfact, l, m)*v - _value(Mfact, i, m)*_value(Mfact, l, j)
      if !iszero(vall)
        push!(val2, vall)
	l < i ?	push!(row2, l) : push!(row2, l-1)
	m < j ? push!(col2, m) : push!(col2, m-1)
      end
    end
  end
    
  Mfact = (val, row, col)
  Mfact2 = (val2, row2, col2)

  Y = subscheme(X, v)
  U = hypersurface_complement(X, v)

  ID = _ideal_degeneracy(Y, Mfact, k)
  _ID2 = _ideal_degeneracy(U, Mfact2, k-1)
  ID2 = [closure(V, X) for V in _ID2 if V != X.OO.R.base_ring]

  ID = [V for V in ID if V != X.OO.R.base_ring && (radical(V.OO.I) != ideal(V.OO.R, gens(V.OO.R)) && radical(V.OO.I) != ideal(V.OO.R, V.OO.R(1)))]
  ID2 = [V for V in ID2 if V != X.OO.R.base_ring && (radical(V.OO.I) != ideal(V.OO.R, gens(V.OO.R)) && radical(V.OO.I) != ideal(V.OO.R, V.OO.R(1)))]
  return union(ID,ID2)
end

##############################################################################
#
# some checks functions
#
##############################################################################

### Smoothness test

"""
   is`_`smooth(I::T) where T <: MPolyIdeal -> Bool

Given an homogeneous ideal `I`, return `true` if `V(I)` is smooth, `false` else.
"""
function is_smooth(I::T) where T <:MPolyIdeal
  v = [f for f in gens(I)]
  R = base_ring(I)
  L = quo(R,I)[1]
  X = Spec(L)
  x = gens(R)
  D = jacobi_matrix(v)
  Dfact = _sparse_matrix_fact(D)
  k = length(x) - Oscar.dim(L)
  ID = _ideal_degeneracy(X, Dfact, k)
  length(ID) == 0 ? (return true) : nothing
  for Y in ID
    bool = true
    for y in x
      U = hypersurface_complement(Y, y)
      bool = one(U.OO.W) in localized_modulus(OO(U)) ? bool : false
    end
    bool == false ? (return bool) : nothing
  end
  return true
end

### Invariance test

"""
  An internal to check if an ideal is invariant under a group action given by `rep_homo`.
  The generators of `I` has to be of the same degree
"""
function _is_invariant_by_rep(prep::ProjRep, I::T) where {S,T}
  R = base_ring(I)
  @req R == polynomial_algebra(representation_ring(prep)) "polynomial algebra must coincide"
  d = total_degree(gens(I)[1])
  prep_homo = get_attribute(prep, :prep_homo)
  if prep_homo !== nothing
    d0 = get_attribute(prep_homo, :degree_homo)
  end
  if (prep_homo === nothing || d != d0)
    prep_homo = homo_poly_rep(prep, d)
  end
  F = base_ring(R)
  Coord,_ = _homo_ideal_in_coord(I)
  L,y = PolynomialRing(F,"y" => (1:(ncols(Coord)+1)), cached = false)
  Rep_homo = matrix_representation(prep_homo)
  for M in Rep_homo
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

### About (non)-symplectic actions

"""
  An internal to check if the action `rep` of a group on `V(I)` is symplectic.
"""
function _is_symplectic_action(prep::ProjRep, I) 
  R = base_ring(I)
  @req R == polynomial_algebra(representation_ring(prep)) "polynomial algebra must coincide"
  d = total_degree(gens(I)[1])
  prep_homo = get_attribute(prep, :prep_homo)
  if prep_homo !== nothing
    d0 = get_attribute(prep_homo, :degree_homo)
  end
  if (prep_homo === nothing || d != d0)
    prep_homo = homo_poly_rep(prep, R, d)
  end
  F = base_ring(R)
  Coord, B = _homo_ideal_in_coord(I)
  L,y = PolynomialRing(F,"y" => (1:(ncols(Coord)+1)), cached = false)
  Rep = matrix_representation(prep)
  Rep_homo = matrix_representation(prep_homo)
  for i=1:length(Rep_homo)
    PM = Rep[i]
    M = Rep_homo[i]
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

"""
  An internak to check whether the action `rep` of a group on `V(I)` is purely 
  non-symplectic.
"""
function _is_purely_non_symplectic_action(prep::ProjRep, I)
  R = base_ring(I)
  @req R == polynomial_algebra(representation_ring(prep)) "polynomial algebra must coincide"
  d = total_degree(gens(I)[1])
  F = base_ring(R)
  Coord, B = _homo_ideal_in_coord(I)
  L,y = PolynomialRing(F,"y" => (1:(ncols(Coord)+1)), cached = false)
  Rep = matrix_representation(prep)
  MG = matrix_group(Rep)
  H = conjugacy_classes(MG)
  for h in H
    m = representative(h)
    if m == one(MG)
      continue
    end
    PM = matrix(m)
    M = _homo_poly_action(PM, R, d) 
    MM = matrix(zeros(F,ncols(Coord),ncols(Coord)))
    VV = VectorSpace(F,length(B))
    Var,f = sub(VV, [VV(Coord[:,i]) for i=1:ncols(MM)])
    Pas = hcat([transpose((f\VV(transpose(matrix(Coord[:,j])))).v) for j=1:ncols(MM)])
    for j=1:ncols(MM)
      MM[:,j] = inv(Pas)*transpose((f\VV(transpose(M*matrix(Coord[:,j])))).v)
    end
    l = F(det(PM))*F(inv(det(MM)))
    l == F(1) ? (return false) : continue
  end
  return true
end

"""
  Given `rep` acting on `V(I)`, return the id of the group generated by the
  elements of `rep` acting symplectically on `V(I)`.
"""
function _id_symplectic_subgroup(prep::ProjRep, I; with::Bool = false)
  R = base_ring(I)
  @req R == polynomial_algebra(representation_ring(prep)) "polynomial algebra must coincide"
  d = total_degree(gens(I)[1])
  F = base_ring(R)
  Coord, B = _homo_ideal_in_coord(I)
  L,y = PolynomialRing(F,"y" => (1:(ncols(Coord)+1)), cached = false)
  Rep = matrix_representation(prep)
  MG = matrix_group(Rep)
  H = conjugacy_classes(MG)
  coll = elem_type(MG)[]
  for h in H
    m = representative(h)
    PM = matrix(m)
    M = _homo_poly_action(PM, R, d) 
    MM = matrix(zeros(F,ncols(Coord),ncols(Coord)))
    VV = VectorSpace(F,length(B))
    Var,f = sub(VV, [VV(Coord[:,i]) for i=1:ncols(MM)])
    Pas = hcat([transpose((f\VV(transpose(matrix(Coord[:,j])))).v) for j=1:ncols(MM)])
    for j=1:ncols(MM)
      MM[:,j] = inv(Pas)*transpose((f\VV(transpose(M*matrix(Coord[:,j])))).v)
    end
    l = F(det(PM))*F(inv(det(MM)))
    l == F(1) ? append!(coll, elements(h)) : continue
  end
  if with == true
    MG2 = subgroup(MG, coll)[1]
    Q, p = quo(MG, MG2)
    gQ = gens(Q)
    gMG2 = [p\q for q in gQ]
    return _id_group_rep(matrix.(coll)), matrix.(gMG2)
  else 
    return _id_group_rep(matrix.(coll)), typeof(Rep[1])[]
  end
end

######################################################################
#
#  Sparse matrices
#
######################################################################

"""
  An internal to reduce a polynomial sparse matrix by deleting all zero rows and 
  columns, and deleting rows and columns appearing several times.
"""
function _reduction_sparse_mat(M::T) where T 
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

"""
  An internal to store sparse matrices into 3 lists: a list of non-zero values, and
  the other lists that keep track of the indices of the rows and columns in which each
  value lies.
"""
function _sparse_matrix_fact(M::T) where T  
  @assert !iszero(M)
  M = _reduction_sparse_mat(M)
  values = [M[i,j] for j=1:ncols(M), i=1:nrows(M) if !iszero(M[i,j])]
  indrow = [i for j=1:ncols(M), i=1:nrows(M) if !iszero(M[i,j])]
  indcol = [j for j=1:ncols(M), i=1:nrows(M) if !iszero(M[i,j])]
  return (values, indrow, indcol)
end

"""
  An internal that given indices `i,j` returns the value in the sparse matrix,
  at the `i`th row and `j`th column.
"""
function _value(M, i,j)
  val,row,col = M
  k = findfirst(k -> row[k] == i && col[k] == j, 1:length(val))
  k == nothing ? (return parent(val[1])(0)) : (return val[k])
end

"""
  An internal to refactorise a sparse matrix (deleting the zero entries
  in its factorised form).
"""
function _refact(Mfact)
  val, row, col = Mfact
  if length(val) == 0
    return [],[],[]
  end
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

######################################################################
#
#  Intersections with Grassmannians
#
######################################################################

### Dimension 1: check purity of a basis tensor

"""
  An internal to compute the intersection of the projectivisation of a 1-dimensional subvector
  space `W` of the `t`-exterior power of another space `V` with the Grassmannian `Gr(t,V)`. The
  output is false for empty intersection, otherwise it gives the completely decomposed form 
  `dec` of the generator of `W` and the ideal `I` generated by the elements fo the pure tensor.
"""
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

### Dimension 2: put one coefficient to 1 and use snf to check which values are allowed for 
### the second coordinate

"""
  An internal to compute the intersection of the projectivisation of a 2-dimensional subvector
  space `W` of the `t`-exterior power of another space `V` with the Grassmannian `Gr(t,V)`. The
  output is false for empty intersection, otherwise it returns a vector of pairs consisting of
  the completely decomposed form `dec` of an elementt of `W` and the ideal `I` generated by
  the elements of the corresponding pure tensor. If the pure tensors form a family, then the
  elements of the basis in coordinates are returned back, to be used in
  '_grass_comp_big_degree'.
"""
function _grass_comp_snf(V::Vector{T}, basis::Vector{Vector{S}}, smooth::Bool=true) where {T, S}
  @req (length(V)==2 && V[1] != V[2]) "V has to be composed of exactly 2 vectors"
  R = parent(basis[1][1])
  d = degrees(basis[1][1])[1]
  B = homog_basis(R,d)
  basis2 = basis_exterior_power(B, length(basis[1])+1)
  m, n = length(B), length(basis[1])
  v1,v2 = V
  w1 = _change_basis(v1,basis)
  w2 = _change_basis(v2,basis)
  F = parent(w1[1][1])
  bool1, dec1 = is_pure(w1,basis)
  bool2, dec2 = is_pure(w2,basis)
  L,y = PolynomialRing(F,"y", cached = false)
  if !bool2
    w = _sum_tensors(_change_coeff_ring(w1, L), _rescale(_change_coeff_ring(w2,L),y))
  else
    w = _sum_tensors(_change_coeff_ring(w2, L), _rescale(_change_coeff_ring(w1,L),y))
  end
  Mat = matrix(zeros(L,length(basis2),length(B)))
  for i=1:length(B)
    col = zeros(L,length(basis2),1)
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
  if c == L(1) 
    return false
  elseif c == y
    if !bool2
      I = ideal(parent(dec1[1]),[dec1[i] for i=1:length(dec1)])
      if (smooth && is_smooth(I)) || !smooth
        return [(dec, I)]
      else 
        return false
     end
    else
      I = ideal(parent(dec2[1]),[dec2[i] for i=1:length(dec2)])
      if (smooth && is_smooth(I)) || !smooth
        return [(dec, I)]
      else  
        return false        
      end
    end
  elseif c == L(0)
    return  [(V, false)]
  elseif Oscar.degree(c) >1
    while evaluate(c,0) == 0
      c = divexact(c,y)
    end
    pot = []
    p = roots(c,F) 
    for r in p
      bool, dec = !bool2 ? is_pure(_change_basis(v1+r*v2,basis), basis) : is_pure(_change_basis(r*v1+v2,basis), basis)
      @assert bool
      I = ideal(R,[dec[i] for i=1:length(dec)])
      if (smooth == true && is_smooth(I)) || (smooth == false)
        push!(pot,(dec, I))
      end
    end
    if length(pot) == 0	
      return false
    else
      return pot
    end
  else
    r = evaluate(c, 0)
    bool, dec = !bool2 ? is_pure(_change_basis(v1-r*v2,basis), basis) : is_pure(_change_basis(r*v1-v2,basis), basis)
    @assert bool	
    I = ideal(R,[dec[i] for i=1:length(dec)])
    if (smooth == true && is_smooth(I)) || (smooth == false)
      return [(dec, I)]
    else
      return false
    end
  end
end
    
### Dimension >= 2

"""
  An internal to compute intersection with Grassmannian varieties in dimension bigger than 
  2. For now, it returns the ideals parametrising the coordinates of pure tensors. It 
  still need the user to construct the (family.ies of) pure tensors 'by hand'
"""
function _grass_comp_big_degree(V, basis)
  R = parent(basis[1][1])
  d = total_degree(basis[1][1])
  B = homog_basis(R,d)
  k = length(basis[1])
  M = _matrix_multivec_star(V, B, k)
  Mfact = _sparse_matrix_fact(M)
  X = Spec(parent(Mfact[1][1]))
  ID = _ideal_degeneracy(X, Mfact, k+1)
  return modulus.(OO.(ID))
end

##############################################################################
#
# Invariant homogeneous ideals under group actions
#
##############################################################################

### Computations of homotypic components in exterior power

"""
  An internal function that returns the intersection of an isotypic component of weight 1 of
  the `t`-exterior power `W` of the `d`-homogeneous part `V` of a polynomial algebra with
  the Grassmannian `Gr(t,V). `W` is seen as a group algebra via `rep`. The input 'smooth' is
  to allow only the elements in the intersection generating an ideal defining a smooth variety.
"""
function _inv_space(prep_homo::ProjRep, chi::Vector, t::Int64, smooth::Bool=true)
  R = polynomial_algebra(representation_ring(prep_homo))
  d = get_attribute(prep_homo, :degree_homo)
  basis = basis_exterior_power(homog_basis(R,d), t)
  prep_ext = t ==1 ? prep_homo : ext_homo_poly_rep(prep_homo, t)
  rep = matrix_representation(prep_ext)
  rep = [rep[i]-chi[i][1]*identity_matrix(base_ring(R), ncols(rep[1])) for i=1:length(rep)]
  rep = reduce(vcat, rep)
  srep = sparse_matrix(rep)
  dim, V = right_kernel(srep)
  if dim == 0
    return false
  end
  V = [transpose(V[:,i]) for i=1:ncols(V)]
  if t == 1
    w = _change_basis(sum(V), basis)
    _, dec = is_pure(w, basis)
    I = ideal(parent(dec[1]),[dec[i] for i=1:length(dec)])
    if (smooth && is_smooth(I)) || !smooth
      return [(dec, I)]
    else 
      return false
    end
  end
  if dim == 1
    return _grass_comp(V[1], basis, smooth)
  elseif dim == 2
    return _grass_comp_snf(V,basis, smooth)
  else
    return [(V,false)]
  end
end

"""
    invariant`_`ideal`_`same`_`degree(Id::Tuple{Int64, Int64}, nvar::Int64, degree::Int64, 
				dim::Int64; smooth::Bool = true, symplectic::Bool = false, 
				stopfirst::Bool = false)

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
function invariant_ideal_same_degree(Id::Tuple{Int64,Int64}, nvar::Int64, degree::Int64, dim::Int64; smooth::Bool = true, symplectic::Bool = false, purely_non_symplectic::Bool = false, stopfirst = false)
  @req !(symplectic && purely_non_symplectic) "Action cannot be symplectic AND purely non-symplectic"
  o,b,d,t = Id[1], Id[2], degree, dim
  pfr = projectively_faithful_representations(o,b, nvar)
  if isempty(pfr)
    return Any[]
  end
  RR = representation_ring(pfr[1])
  ct = character_table(RR)
  lin_oscar = get_attribute(RR, :lin_oscar)
  lin_gap = get_attribute(RR, :lin_gap)
  R = polynomial_algebra(RR)
  L_rep = length(pfr)
  result = []
  for i=1:L_rep
    prep = pfr[i]
    prep_homo = homo_poly_rep(prep, d)
    chara = t == 1 ? char_gap(prep_homo) : GG.AntiSymmetricParts(ct, GAP.julia_to_gap([char_gap(prep_homo)], recursive = true), t)[1]
    result2 = []	
    nice_char = [lin_oscar[j] for j=1:(length(lin_oscar)) if GG.ScalarProduct(ct, chara, lin_gap[j]) !=0]
    for chi in nice_char
      pot = _inv_space(prep_homo, chi, t, smooth)
      if pot != false
        V, I = [pott[1] for pott in pot], [pott[2] for pott in pot]
        if symplectic 
	  _result_int = [II for II in I if II != false && _is_symplectic_action(prep, II)]
	elseif purely_non_symplectic
	  _result_int = [II for II in I if II != false && _is_purely_non_symplectic_action(prep, II)]
	else
	  _result_int = [II for II in I if II != false]
	end
	result_int = union(_result_int, [V[i] for i=1:length(V) if I[i] == false])
        if all(v -> v isa MPolyIdeal, result_int) 
	  stopfirst ? (return (result_int[1], prep)) : result2 = union(result2, result_int)
        else
          result2 = union(result2, result_int)
        end
      end
      GC.gc()
    end
    length(result2) >0 ? push!(result, (result2, prep)) : nothing	  
  end
  return result
end

function invariant_ideal_same_degree(preps::Vector{ProjRep}, d::Int64, t::Int64; smooth::Bool = true, symplectic::Bool = false, stopfirst = false, purely_non_symplectic::Bool = false)
  @req !(symplectic && purely_non_symplectic) "Action cannot be symplectic AND purely non-symplectic"
  RR = representation_ring(preps[1])
  ct = character_table(RR)
  lin_oscar = get_attribute(RR, :lin_oscar)
  lin_gap = get_attribute(RR, :lin_gap)
  R = polynomial_algebra(RR)
  L_rep = length(preps)
  result = []
  for i=1:L_rep
    prep = preps[1]
    prep_homo = homo_poly_rep(prep, d)
    chara = t == 1 ? char_gap(prep_homo) : GG.AntiSymmetricParts(ct, GAP.julia_to_gap([char_gap(prep_homo)], recursive = true), t)[1]
    result2 = []
    nice_char = [lin_oscar[j] for j=1:(length(lin_oscar)) if GG.ScalarProduct(chara, lin_gap[j]) !=0]
    for chi in nice_char
      pot = _inv_space(prep_homo, chi, t, smooth)
      if pot != false
        V, I = [pott[1] for pott in pot], [pott[2] for pott in pot]
        if symplectic
          _result_int = [II for II in I if II != false && _is_symplectic_action(prep,  II)]
        elseif purely_non_symplectic
          _result_int = [II for II in I if II != false && _is_purely_non_symplectic_action(prep, II)]
        else
	  _result_int = [II for II in I if II != false]
	end
        result_int = union(_result_int, [V[i] for i=1:length(V) if I[i] == false])
        if all(v -> v isa MPolyIdeal, result_int)
          stopfirst ? (return (result_int[1], prep)) : result2 = union(result2, result_int)
        else
          result2 = union(result2, result_int)
        end
      end
    end
    length(result2) >0 ? push!(result, (result2, prep)) : nothing
  end
  return result
end

function invariant_ideal_same_degree(prep::ProjRep, d::Int64, t::Int64; smooth::Bool = true, symplectic::Bool = false, purely_non_symplectic::Bool = false, stopfirst = false)
  @req !(symplectic && purely_non_symplectic) "Action cannot be symplectic AND purely non-symplectic"
  RR = representation_ring(prep)
  ct = character_table(RR)
  lin_oscar = get_attribute(RR, :lin_oscar)
  lin_gap = get_attribute(RR, :lin_gap)
  R = polynomial_algebra(RR)
  prep_homo = homo_poly_rep(prep, d)
  chara = t == 1 ? char_gap(prep_homo) : GG.AntiSymmetricParts(ct, GAP.julia_to_gap([char_gap(prep_homo)], recursive = true), t)[1]
  result = []
  nice_char = [lin_oscar[j] for j=1:(length(lin_oscar)) if GG.ScalarProduct(chara, lin_gap[j]) !=0]
  for chi in nice_char
    pot = _inv_space(prep_homo, chi, t, smooth)
    if pot != false
      V, I = [pott[1] for pott in pot], [pott[2] for pott in pot]
      if symplectic
        _result_int = [II for II in I if II != false && _is_symplectic_action(prep, II)]
      elseif purely_non_symplectic
        _result_int = [II for II in I if II != false && _is_purely_non_symplectic_action(prep,II)]
      else
        _result_int = [II for II in I if II != false]
      end
      result_int = union(_result_int, [V[i] for i=1:length(V) if I[i] == false])
      if all(v -> v isa MPolyIdeal, result_int)
        stopfirst ? (return (result_int[1], prep)) : result = union(result, result_int)
      else
        result = union(result, result_int)
      end
    end
  end
  return result
end


