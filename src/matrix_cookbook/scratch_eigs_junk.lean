import linear_algebra.matrix.spectrum
import linear_algebra.eigenspace
import data.complex.basic
import linear_algebra.matrix.charpoly.coeff

variables {n: Type*}[fintype n][decidable_eq n][nonempty n]

open matrix polynomial
open module.End
open_locale classical
open_locale matrix big_operators

noncomputable def eig_multiplicity (A: matrix n n ℂ) (μ: ℂ) : ℕ := 
  polynomial.root_multiplicity μ (matrix.charpoly A)

lemma exists_multiset_eigs {A : matrix n n ℂ}  (hp : A ≠ 0) :
  ∃ s : multiset ℂ, (s.card : with_bot ℕ) ≤ fintype.card n ∧ ∀ μ, s.count μ = eig_multiplicity A μ
  :=
begin
  unfold eig_multiplicity,
  have p_nz : matrix.charpoly A ≠ 0, { 
    by_contra, replace h := congr_arg nat_degree h, simp only [nat_degree_zero] at h, 
    have p_deg := matrix.charpoly_nat_degree_eq_dim A, rw p_deg at h,
    have hn: fintype.card n ≠ 0, {exact fintype.card_ne_zero,},
    exact hn h,
  },
  have Adeg := matrix.charpoly_degree_eq_dim A,
  let zeta := exists_multiset_roots p_nz,
  rw ← Adeg,
  exact zeta,
end

noncomputable def eigs (A: matrix n n ℂ): multiset ℂ := 
  if h : A = 0  then ∅ 
  else classical.some (exists_multiset_eigs h)

lemma eig_is_eigenvalue (A: matrix n n ℂ) (μ: ℂ) :
  μ ∈ eigs A ↔  module.End.has_eigenvalue (matrix.to_lin' A) μ := sorry

lemma eigs_are_eigenvalues (A: matrix n n ℂ) : ∀(μ : ℂ),
  let eigenvaluesA := (eigenvalues.fintype (matrix.to_lin' A)).elems in
  μ ∈ eigenvaluesA ↔ μ ∈ eigs A  := sorry 

/-Useful Lemmas -/
lemma det_eq_prod_eigs (A: matrix n n ℂ): A.det = (eigs A).prod := sorry
lemma trace_eq_sum_eigs (A: matrix n n ℂ) {hn: nonempty n}: A.trace = (eigs A).sum := --sorry
begin
  by_cases hAz: A = 0, rw hAz, rw trace_zero, rw eigs, 
  simp only [multiset.empty_eq_zero, dif_pos, multiset.sum_zero],

  -- A ≠ 0 Case
  rw trace_eq_neg_charpoly_coeff A,
  -- have: 
end


-- noncomputable def eigsZ := (eigenvalues.fintype (matrix.to_lin' Z)).elems
-- #check eigsZ Z

/-
-- lemma trace_nonhermitian_eq_sum_eigenvalues
--   {A: matrix n n ℂ} {hn: nonempty n}:
--   let fA := matrix.to_lin' A, eigsnm := fA.eigenvalues in
--     trace A = ∑(i: n), module.End.eigenvalues :=
-- begin
--   -- rw trace_eq_neg_charpoly_coeff,
--   -- rw matrix.charpoly_coeff_eq_prod_coeff_of_le,
  
  
--   -- let bA := pi.basis_fun ℂ n,
--   -- let fA := matrix.to_lin bA bA A,

--   -- have h1 := linear_map.to_matrix_to_lin bA bA A, 
  
  
--   -- have h2 := congr_arg matrix.trace h1,
--   -- rw ← linear_map.trace_eq_matrix_trace ℂ bA (fA) at h2,

--   have g1 : A.trace = A.trace, by refl,
--   nth_rewrite 1 ←  matrix.trace_linear_map_apply n ℂ ℂ at g1,

--   rw  algebra.coe_linear_map at g1,
--   -- set tA := trace_linear_map n ℂ ℂ,
--   -- have g2 := g1.symm,
--   -- rw ←  sub_eq_zero at g2,
  
--   sorry,
-- end
  
--   -- have h1 := linear_map.to_matrix'_to_lin' A,
--   -- replace h1 := congr_arg matrix.trace h1,
--   -- rw ← h1,
--   -- rw ← linear_map.to_matrix_eq_to_matrix' ,
--   -- rw ← linear_map.trace_eq_matrix_trace,
  
--   -- have b := matrix.std_basis ℂ n n, 
--   -- have h2 := linear_map.trace_eq_matrix_trace,

--   -- rw trace_eq_neg_charpoly_coeff A,
--   -- rw matrix.charpoly_coeff_eq_prod_coeff_of_le, dsimp,

--   -- rw is_hermitian.eigenvalues, dsimp,
--   -- rw is_hermitian.eigenvalues₀,
--   -- conv_rhs{
--   --   apply_congr, skip,
--   --   rw matrix.is_hermitian.eigenvalues_eq hA x,
--   -- }

  

--   -- unfold linear_map.to_matrix', dsimp,

--   -- have h2 := trace_eq_sum_roots,
--   -- rw linear_map.to_matrix'_apply,
-- --   -- polynomial.sum_roots_eq_next_coeff_of_monic_of_split
-- --   -- complex.is_alg_closed

-- --   -- trace_eq_sum_roots 
-- --   -- linear_map.trace_eq_matrix_trace 
-- --   have h1: trace_eq_sum_roots,
-- --   sorry,
-/