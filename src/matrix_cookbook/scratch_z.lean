import data.complex.basic
import data.complex.exponential
import data.matrix.basic
import analysis.special_functions.trigonometric.basic
import linear_algebra.matrix.hermitian

open matrix
open complex
open_locale matrix big_operators complex_conjugate real

-- eq_403 : Twiddle Factors
noncomputable def Wkn {N: ℕ} (k n: fin N) : ℂ :=  
exp(2 * π * I * k * n / N)

-- Forward DFT Matrix
noncomputable def W_N {N: ℕ}: matrix (fin N) (fin N) ℂ :=
of $ λ k n, Wkn k n

-- Inverse Twiddle Factors
noncomputable def iWkn {N: ℕ} (k n: fin N) : ℂ :=  
exp(- 2 * π * I * k * n / N)

-- Inverse DFT Matrix
noncomputable def iW_N {N: ℕ} : matrix (fin N) (fin N) ℂ :=
of $ λ k n, iWkn k n

lemma W_N_symmetric {N: ℕ} :
  (W_N: matrix (fin N) (fin N) ℂ) = (W_Nᵀ) := 
begin
  sorry,
end

lemma W_N_mul_iW_N {N: ℕ} {hN: N ≠ 0} : 
(W_N) ⬝ (iW_N) = 
  (N)•(1: matrix (fin N) (fin N) ℂ) := 
begin
  sorry,
end


lemma eq_408 {N: ℕ} {hN: N ≠ 0} : 
  -- let η : ℂ := (1/↑N),
(W_N : matrix (fin N) (fin N) ℂ)⁻¹ = 
  (N:ℂ)⁻¹ • (W_Nᵀ)ᴴ :=
-- Seems star means hermitian and not just conjugate
begin
have hW : (iW_N: matrix (fin N) (fin N) ℂ) = W_Nᴴ, by {
  sorry,
},
-- have : (↑N:ℂ)⁻¹ * (↑N:ℂ) = 1, by {
--   set η:ℂ := ↑N,
--   rw mul_comm, rw mul_inv_cancel,
--   change η with ↑N, rw nat.cast_ne_zero, exact hN,
-- },
rw ← W_N_symmetric,
rw inv_eq_right_inv,
rw ← hW,
rw matrix.mul_smul,
rw W_N_mul_iW_N, 

funext k n,
rw pi.smul_apply,
rw pi.smul_apply,
rw pi.smul_apply,
rw pi.smul_apply,
by_cases hkn: (k=n), rw hkn, 
rw one_apply_eq,
simp only [nat.smul_one_eq_coe, algebra.id.smul_eq_mul],
rw mul_comm,rw mul_inv_cancel, rw nat.cast_ne_zero, exact hN,
rw one_apply_ne,
rw smul_zero,
rw smul_zero, exact hkn, exact hN,
end

