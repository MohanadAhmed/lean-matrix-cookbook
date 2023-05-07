import data.complex.basic
import data.complex.exponential
import data.matrix.basic
import data.matrix.notation
import linear_algebra.matrix.circulant
import analysis.special_functions.pow
import analysis.special_functions.complex.log
import analysis.special_functions.trigonometric.basic

open matrix
open_locale matrix big_operators complex_conjugate
open equiv equiv.perm finset
open_locale real matrix big_operators
open matrix
open equiv equiv.perm finset
open complex

-- Forward DFT Matrix
noncomputable def Wₙ {N: ℕ}: matrix (fin N) (fin N) ℂ :=
λ k n, complex.exp(2 * π * I * k * n / N)

-- Inverse DFT Matrix
noncomputable def iWₙ {N: ℕ} : matrix (fin N) (fin N) ℂ :=
λ k n, complex.exp(- 2 * π * I * k * n / N)

lemma W_N_mul_iW_N {N: ℕ} {hN: N ≠ 0} : 
(Wₙ) ⬝ (iWₙ) = (N)•(1: matrix (fin N) (fin N) ℂ) := 
begin
  sorry,
end

noncomputable def dft {N: ℕ} (x: (fin N) → ℂ) : (fin N → ℂ) := 
λ (k: fin N), ∑ (n : fin N), (Wₙ k n) * (x n)

-- lemma circ_dft_relation {N: ℕ} (t: (fin N) → ℂ) :
--   matrix.circulant t = iWₙ ⬝ (diagonal(dft t)) ⬝ Wₙ := 
-- begin
--   funext i j,
--   rw circulant_apply,
--   -- rw mul_mul_apply,
--   -- rw dot_product,
--   rw mul_apply',
--   rw dot_product,
--   simp only [mul_diagonal],
--   rw dft,
--   -- rw finset.sum_apply,
--   simp only,
--   conv_rhs {
--     apply_congr, skip, 
--     rw mul_comm, rw ← mul_assoc,
    
--   },
--   -- rw Wₙ, rw iWₙ, simp only [coe_coe, neg_mul],
--   -- rw mul_mul_apply',
-- end

example {N: ℕ} :
  ∑(i:  (range N)) (λ i, 1) = N := begin

end

-- lemma circ_dft_relation {N: ℕ} (t: (fin N) → ℂ) :
--   matrix.circulant t = iWₙ ⬝ (diagonal(dft t)) ⬝ Wₙ := 
-- begin
--   -- induction N,
--   -- simp only [eq_iff_true_of_subsingleton],
--   apply_fun (matrix.mul Wₙ),
--   rw ← matrix.mul_assoc,
--   rw ← matrix.mul_assoc,
--   rw W_N_mul_iW_N,
--    simp only [nat.smul_one_eq_coe],
--    funext i k, 
--    rw matrix.mul_apply,
--    conv_lhs {
--       apply_congr,
--    },
--    rw mul_mul_apply,
   
--    rw dot_product,
   

--   -- apply_fun (matrix.mul _ iWₙ),
-- end

-- lemma circ_dft_relation {N: ℕ} (t: (fin N) → ℂ) :
--   matrix.circulant t = iWₙ ⬝ (diagonal (matrix.mul_vec Wₙ t)) ⬝ Wₙ := 
-- begin
--   funext k n,
--   rw mul_apply',
--   rw circulant_apply,
  
--   rw Wₙ, rw iWₙ, 
--   -- simp only [neg_mul, coe_coe, mul_diagonal],
  
--   rw dot_product_comm,
--   squeeze_simp,
-- end