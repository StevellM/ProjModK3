includet("/home/user/Desktop/projmodk3/Code.jl")
include("/home/user/Desktop/K3Groups/K3SurfaceAutGrp.jl")

function _gather_K3(rk::Int64, d::Int64)
  vals = keep(n -> euler_phi(n) <= 20 && n != 60, 2:66)
  gat = K3SurfaceAutGrp[]
  for pure in [true, false]
    if !pure
      vals2 = keep(n -> euler_phi(n) <= 12, vals)
    else 
      vals2 = vals
    end
    for n in vals2
      A = load(K3SurfaceAutGrp, n, pure)
      for a in A
        L = invariant_lattice(a)
        if rank(L) == rk && gram_matrix(L)[1,1] == d
          push!(gat, a)
        end
      end
    end
  end
  return gat
end

function _wce(a::nf_elem)
  F = parent(a)
  bool, e = Hecke.iscyclotomic_type(F)
  @assert bool 
  d = denominator(a)
  if d == 1
    co = numerator.(coefficients(a))
    str = co[1] == 0 ? "" : "$(co[1])"
  else
    co = numerator.(coefficients(d*a))
    str = co[1] == 0 ? "" : "1//$d*($(co[1])"
  end
  for i =2:length(co)
    if i == 2
      if abs(co[i]) == 1
        if co[i] > 0
          str *= str == "" ? ("z_$e") : (" + z_$e")
        else
          str *= str == "" ? ("-z_$e") : (" - z_$e")
        end
      elseif co[i] != 0
        if co[i] > 0
          str *= str == "" ? ("$(co[i])*z_$e") : (" + $(co[i])*z_$e")
        else
          str *= str == "" ? ("$(co[i])*z_$e") : (" - $(abs(co[i]))*z_$e")
        end
      end
    else
      if abs(co[i]) == 1
        if co[i] > 0
          str *= str == "" ? ("z_$e^$(i-1)") : (" + z_$e^$(i-1)")
        else
          str *= str == "" ? ("-z_$e^$(i-1)") : (" - z_$e^$(i-1)")
        end
      elseif co[i] != 0
        if co[i] > 0
          str *= str == "" ? ("$(co[i])*z_$e^$(i-1)") : (" + $(co[i])*z_$e^$(i-1)")
        else
          str *= str == "" ? ("$(co[i])*z_$e^$(i-1)") : (" - $(abs(co[i]))*z_$e^$(i-1)")
        end
      end
    end
  end
  return str
end
 
function _iis(I::MPolyIdeal)
  R = base_ring(I)
  F = base_ring(R)
  d = total_degree(gens(I)[1])
  B = homog_basis(R,d)
  bool, e = Hecke.iscyclotomic_type(F)
  @assert bool
  co = _homo_ideal_in_coord(I)[1]
  gene = gens(I)
  str = "("
  for j=1:ncols(co)
    v = co[:,j]
    str2 = ""
    for i=1:length(v)
      if v[i] == F(1) 
        str2 *= str2 == "" ? ("$(B[i])") : (" + $(B[i])")
      elseif v[i] == -F(1)
        str2 *= str2 == "" ? ("-$(B[i])") : (" - $(B[i])")
      elseif count(vv -> vv != 0, coefficients(v[i])) == 1
        if keep(vv -> vv!= 0, coefficients(v[i]))[1] > 0
          str2 *= str2 == "" ? (_wce(v[i]) * "*$(B[i])") : (" + " * _wce(v[i]) * "*$(B[i])")
        else 
          str2 *= str2 == "" ? (_wce(v[i]) * "*$(B[i])") : (" - " * _wce(v[i]) * "*$(B[i])")
        end
      elseif v[i] != 0
        str2 *= str2 == "" ? ("(" * _wce(v[i]) * ")*$B([i])") : (" + (" * _wce(v[i]) *")*$(B[i])")
      end
    end
    str *= j == ncols(co) ? (str2) : (str2*", ")
  end
  str *= ")"
  return str
end
    
function _mis(M)
  n, m = size(M)
  str = "["
  for i=1:n
    for j=1:m
      if M[i,j] == 0
        str *= j == 1 ? ("0") : (" 0")
      else
        str *= j == 1 ? (_wce(M[i,j])) : (" " * _wce(M[i,j]))
      end
      if j == m
        if i != n
          str *= "; "
        end
      end
    end
  end
  str *= "]"
  return str
end

function _ris(invs)
  II, rep = invs
  str = "'invariant ideals' : [ "
  for i =1:length(II)
    I = II[i]
    if i == 1
      str *= (_iis(I))
    else
      str *= (", " * _iis(I))
    end
    if i == length(II)
      str *= " ],"
    end
  end
  str *= " 'action' : [ "
  for i = 1:length(rep)
    M = rep[i]
    if i == 1
      str *= (_mis(M))
    else
      str *= (", " * _mis(M))
    end
    if i == length(rep)
      str*= " ]"
    end
  end
  return str
end

function _sk3(a::K3SurfaceAutGrp)
  id = small_group_identification(a.group)
  ids = small_group_identification(a.symplectic_subgroup)
  pure = ids == (1,1)
  INVS = invariant_ideal_same_degree(id, 4, 4, 1, smooth = true, purely_non_symplectic = pure)
  if length(INVS) == 0
    return "[$(a.name), [$(id[1]), $(id[2])], [$(ids[1]), $(ids[2])], 4, 4, 1, hyperelliptic?]"
  end
  F = parent(INVS[1][2][1][1,1])
  e = get_attribute(F, :cyclo)
  str = "[$(a.name), [$(id[1]), $(id[2])], [$(ids[1]), $(ids[2])], 4, 4, 1, $e, ["
  for i = 1:length(INVS)
    invs = INVS[i]
    II = keep(I -> _id_symplectic_subgroup(invs[2], I)[1] == GAP.julia_to_gap(ids), invs[1])
    rep = invs[2]
    if length(II) != 0
      str2 = _ris((II, rep)) 
      str *= str[end] == '[' ? " " * str2 : (" ], [ " * str2)
    end
    if i == length(INVS) && str[end] != '['
      str *= (" ] ]")
    end
  end
  if str[end] == '['
    return "[$(a.name), [$(id[1]), $(id[2])], [$(ids[1]), $(ids[2])], 4, 4, 1, hyperelliptic?]"
  else
    return str
  end
end

function _write_result()
  gat = _gather_K3(1,4)
  forbidden_names = String["70.2.1.11", "70.2.1.12", "80.4.0.1", "81.2.1.3", "74.4.0.1", "76.2.1.3", "77.6.0.1"]
  gat = keep(a -> !(a.name in forbidden_names), gat)
  f = open("rk1_deg4.txt", "w")
  local str::String
  for a in gat
    str = _sk3(a)
    write(f, str)
    write(f, "\n")
  end
  close(f)
end

