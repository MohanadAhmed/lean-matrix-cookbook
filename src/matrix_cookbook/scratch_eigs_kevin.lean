import linear_algebra.matrix.spectrum
import linear_algebra.eigenspace
import linear_algebra.charpoly.basic
import linear_algebra.matrix.charpoly.coeff
import linear_algebra.charpoly.to_matrix

variables {n: Type*}[fintype n][decidable_eq n][nonempty n]
variables {R: Type*}[field R]

open matrix polynomial
open linear_map module.End  
open_locale classical
open_locale matrix big_operators

variable Z: matrix n n R

#check linear_map.charpoly (matrix.to_lin' Z)

noncomputable def eigs (A: matrix n n R): multiset R := 
  -- let bA := pi.basis_fun R n in
  polynomial.roots (linear_map.charpoly (matrix.to_lin' A))

lemma eig_if_eigenvalue (A: matrix n n R) (μ: R) :
  μ ∈ eigs A →  module.End.has_eigenvalue (matrix.to_lin' A) μ := 
begin
  rw [eigs,has_eigenvalue_iff_is_root],
  rw mem_roots',
  intro heig,

  cases heig with hp_nz hcp,
  rw to_lin', 
end

lemma eigenvalue_if_eig (A: matrix n n R) (μ: R) :
  -- let bA := pi.basis_fun R n in
  module.End.has_eigenvalue (matrix.to_lin' A) μ → μ ∈ eigs A := 
begin
  -- intro bA,
  rw [eigs,has_eigenvalue_iff_is_root],
  rw mem_roots',
  intro heig,
  split, 
  by_contra, 
  
  
  replace h := congr_arg nat_degree h, rw nat_degree_zero at h,
  
  
  have And := charpoly_nat_degree_eq_dim A,

  rw ← dvd_iff_is_root at *,
  have hmc := minpoly_dvd_charpoly (matrix.to_lin' A),
  -- exact dvd_trans heig hmc,
  sorry,
end

lemma eig_iff_eigenvalue (A: matrix n n R) (μ: R) :
  μ ∈ eigs A ↔  module.End.has_eigenvalue (matrix.to_lin' A) μ := 
begin
sorry,
end

lemma is_root_minpoly_iff_is_root_charpoly (A: matrix n n R) (μ: R) :
  is_root (matrix.charpoly A) μ ↔ is_root (minpoly R A) μ :=
begin
  split,
  intro h,
  rw is_root.def at *,
end