import linear_algebra.matrix.spectrum
import linear_algebra.eigenspace
import linear_algebra.charpoly.basic
import linear_algebra.matrix.charpoly.coeff
import linear_algebra.matrix.charpoly.minpoly
import linear_algebra.charpoly.to_matrix
import data.complex.basic
import analysis.complex.polynomial

variables {n: Type*}[fintype n][decidable_eq n][nonempty n]

open matrix polynomial
open linear_map module.End  
open_locale matrix big_operators

noncomputable def eigs (A: matrix n n ℂ): multiset ℂ := 
  polynomial.roots (matrix.charpoly A)

lemma det_eq_prod_eigs (A: matrix n n ℂ): 
  A.det = (eigs A).prod :=
begin
  rw eigs,
  by_cases hn: nonempty n, {
    rw det_eq_sign_charpoly_coeff,
    have hdeg := charpoly_nat_degree_eq_dim A,
    rw ← hdeg,
    rw polynomial.prod_roots_eq_coeff_zero_of_monic_of_split,
    rw ← mul_assoc, rw ← pow_two,
    rw ← pow_mul, 
    have hstupid: -1 ≠ (1:ℂ), { norm_num,},
    have hs2 : even(A.charpoly.nat_degree*2), 
      {simp only [even.mul_left, even_two],},

    rw (neg_one_pow_eq_one_iff_even hstupid).2 hs2, rw one_mul,
    apply matrix.charpoly_monic,
    apply complex.is_alg_closed.splits,
  },{
    rw not_nonempty_iff at hn,
    rw matrix.charpoly, 
    repeat {rw det_eq_one_of_card_eq_zero (fintype.card_eq_zero_iff.2 hn)},
    rw polynomial.roots_one,
    simp only [multiset.empty_eq_zero, multiset.prod_zero],
  }
end

lemma trace_eq_sum_eigs (A: matrix n n ℂ) : A.trace = (eigs A).sum := --sorry
begin
  rw eigs,
  by_cases hn: (nonempty n), {  
    apply_fun (has_neg.neg),
    rw ← polynomial.sum_roots_eq_next_coeff_of_monic_of_split ,
    rw trace_eq_neg_charpoly_coeff, rw next_coeff,
    rw neg_neg, rw charpoly_nat_degree_eq_dim, 
    have fn: 0 < fintype.card n, by apply (fintype.card_pos),    
    have fne := ne_of_lt fn, 
    symmetry' at fne, rw ne.def at fne,
    split_ifs, refl,
    apply matrix.charpoly_monic,
    apply complex.is_alg_closed.splits,
    rintros a x hax, rwa neg_inj at hax,
  }, {
    rw not_nonempty_iff at hn,
    rw matrix.trace, 
    rw fintype.sum_empty _, rotate, exact hn,
    rw matrix.charpoly, 
    rw det_eq_one_of_card_eq_zero (fintype.card_eq_zero_iff.2 hn),
    rw polynomial.roots_one,
    simp only [multiset.empty_eq_zero, multiset.sum_zero],
  },
end

lemma is_root_minpoly_iff_is_root_charpoly (A: matrix n n ℂ) (μ: ℂ) :
  is_root (matrix.charpoly A) μ ↔ is_root (minpoly ℂ A) μ :=
begin
  split,
  intro h,
  let mp := minpoly ℂ A,

  sorry,
  intro h,
  apply is_root.dvd h,
  exact matrix.minpoly_dvd_charpoly A,
end

lemma eig_if_eigenvalue (A: matrix n n ℂ) (μ: ℂ) :
  μ ∈ eigs A →  module.End.has_eigenvalue (matrix.to_lin' A) μ := 
begin
  rw [eigs,has_eigenvalue_iff_is_root],
  rw mem_roots',
  intro heig,

  cases heig with hp_nz hcp,
  rw to_lin', 
  sorry,
end

lemma eigenvalue_if_eig (A: matrix n n ℂ) (μ: ℂ) :
  -- let bA := pi.basis_fun ℂ n in
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
  sorry,sorry,
end

lemma eig_iff_eigenvalue (A: matrix n n ℂ) (μ: ℂ) :
  μ ∈ eigs A ↔  module.End.has_eigenvalue (matrix.to_lin' A) μ := 
begin
  split, exact eig_if_eigenvalue A μ, exact eigenvalue_if_eig A μ,
end

-- lemma eigs_are_eigenvalues (A: matrix n n ℂ) (μ : ℂ):
--   let eigenvaluesA := (eigenvalues.fintype (matrix.to_lin' A)).elems in
--   μ ∈ eigs A ↔  
--     μ ∈ ↑(((eigenvalues.fintype (matrix.to_lin' A)).elems).image)  := 
-- begin

-- end