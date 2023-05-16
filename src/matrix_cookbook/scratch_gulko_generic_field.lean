import linear_algebra.matrix.spectrum
import linear_algebra.eigenspace
import linear_algebra.charpoly.basic
import linear_algebra.matrix.charpoly.coeff
import linear_algebra.charpoly.to_matrix
import linear_algebra.matrix.charpoly.minpoly
import linear_algebra.matrix.to_linear_equiv
import ring_theory.polynomial_algebra
import ring_theory.integral_closure

variables {n: Type*}[fintype n][decidable_eq n][nonempty n]
variables {R: Type*}[field R][is_alg_closed R][is_domain R]

open matrix polynomial
open linear_map module.End  
open_locale matrix big_operators

lemma root_charpoly_of_eig (A: matrix n n R)(μ: R):
  has_eigenvalue (matrix.to_lin' A) μ → A.charpoly.is_root μ:=
begin
  intro heig,
  have va := has_eigenvalue.exists_has_eigenvector heig, 
  have xa : (∃ (v : n → R) (H : v ≠ 0), (μ • 1 - A).mul_vec v = 0), {
    cases va with v hv, use v, cases hv with hv hnz, split, exact hnz,
    rw mem_eigenspace_iff at hv, 
    rw to_lin'_apply at hv, 
    symmetry' at hv,
    rw ← sub_eq_zero at hv, 
    rw sub_mul_vec, rw smul_mul_vec_assoc, rw one_mul_vec, exact hv,
  },
  have ya := matrix.exists_mul_vec_eq_zero_iff.1 xa,

  rw matrix.charpoly, 
  rw is_root, 
  rw eval_det,
  rw mat_poly_equiv_charmatrix,
  rw eval_sub, rw eval_C, rw eval_X, rw coe_scalar,

  rw ← ya,
end

lemma eig_of_root_charpoly (A: matrix n n R)(μ: R):
   A.charpoly.is_root μ → has_eigenvalue (matrix.to_lin' A) μ :=
begin

  rw matrix.charpoly, 
  rw is_root,
  rw eval_det,
  rw mat_poly_equiv_charmatrix,
  rw eval_sub, rw eval_C, rw eval_X, rw coe_scalar, dsimp,

  intro h,
  have h := matrix.exists_mul_vec_eq_zero_iff.2 h, 
  rcases h with ⟨v, hv_nz, hv⟩,
  rw sub_mul_vec at hv, rw smul_mul_vec_assoc at hv, rw one_mul_vec at hv,
  rw sub_eq_zero at hv,  symmetry' at hv,
  rw [has_eigenvalue, submodule.ne_bot_iff], 
   use v, rw mem_eigenspace_iff, 
  rw to_lin'_apply, split, assumption',
end

lemma root_charpoly_iff_eig (A: matrix n n R)(μ: R) :
   A.charpoly.is_root μ ↔ has_eigenvalue (matrix.to_lin' A) μ := 
begin
  split,
  apply eig_of_root_charpoly,
  apply root_charpoly_of_eig,
end

lemma root_charpoly_iff_root_minpoly (A: matrix n n R)(μ: R) :
  (minpoly R (matrix.to_lin' A)).is_root μ ↔ A.charpoly.is_root μ := 
begin
  split,

  intro h, rw root_charpoly_iff_eig, 
  apply has_eigenvalue_iff_is_root.2 h,
  
  rw root_charpoly_iff_eig, intro h,
  apply has_eigenvalue_iff_is_root.1 h,
end
