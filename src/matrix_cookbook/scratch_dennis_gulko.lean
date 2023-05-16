import linear_algebra.matrix.spectrum
import linear_algebra.eigenspace
import linear_algebra.charpoly.basic
import linear_algebra.matrix.charpoly.coeff
import linear_algebra.charpoly.to_matrix
import linear_algebra.matrix.charpoly.minpoly
import data.complex.basic
import analysis.complex.polynomial

variables {n: Type*}[fintype n][decidable_eq n][nonempty n]
variables {R: Type*}[field R][is_alg_closed R]

open matrix polynomial
open linear_map module.End  
open_locale matrix big_operators

theorem mhnd_aeval_apply_of_has_eigenvector (f : module.End ℂ (n → ℂ))
  (p : polynomial ℂ) (μ : ℂ) (x : n → ℂ) (h : f.has_eigenvector μ x) :
  aeval f p x = (p.eval μ) • x :=
begin
  apply p.induction_on,
  { intro a, simp [module.algebra_map_End_apply] },
  { intros p q hp hq, simp [hp, hq, add_smul] },
  { intros n a hna,
    rw [mul_comm, pow_succ, mul_assoc, alg_hom.map_mul, linear_map.mul_apply, mul_comm, hna],
    simp only [mem_eigenspace_iff.1 h.1, smul_smul, aeval_X, eval_mul, eval_C, eval_pow, eval_X,
      linear_map.map_smulₛₗ, ring_hom.id_apply, mul_comm] }
end

lemma root_of_minploy_root_of_charpoly (A: matrix n n ℂ)(μ: ℂ):
  (minpoly ℂ (matrix.to_lin' A)).is_root μ → A.charpoly.is_root μ :=
begin
  intro h_mp_root,
  
  have h_eig_lmap := has_eigenvalue_of_is_root h_mp_root,
  cases (has_eigenvalue.exists_has_eigenvector h_eig_lmap) with v h_eigv,
  set p := A.charpoly,
  set f := matrix.to_lin' A,
  let h_aeval := mhnd_aeval_apply_of_has_eigenvector f p μ v h_eigv,
  -- let h_aeval := @module.End.aeval_apply_of_has_eigenvector 
  -- ℂ _ f p μ v h_eigv,

  -- have h_aeval : ⇑(⇑(polynomial.aeval f) p) v = polynomial.eval μ p • v, {

  -- } ,

end



-- lemma poly_eval_eig_mat_aeval_eig 
--   (A: matrix n n ℂ)(μ: ℂ)(p: polynomial ℂ) 
--   (heig: has_eigenvalue (matrix.to_lin' A) μ):
--      has_eigenvalue (matrix.to_lin' ((polynomial.aeval A) p)) μ := 
-- begin
--   cases (has_eigenvalue.exists_has_eigenvector heig) with v hv,
--   -- replace hv := has_eigenvector.apply_eq_smul hv,
--   -- rw matrix.to_lin'_apply at hv,
--   have za := module.End.aeval_apply_of_has_eigenvector hv,
-- end