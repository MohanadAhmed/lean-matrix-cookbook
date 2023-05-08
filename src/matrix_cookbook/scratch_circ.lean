import data.complex.basic
import data.complex.exponential
import data.matrix.basic
import data.fin.basic
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
(Wₙ) ⬝ (iWₙ) = (1: matrix (fin N) (fin N) ℂ) := 
begin
  sorry,
end

lemma iW_N_mul_W_N {N: ℕ} {hN: ne_zero N} : 
 (iWₙ)⬝(Wₙ) = (↑N:ℂ)•(1: matrix (fin N) (fin N) ℂ) := 
begin
  sorry,
end

noncomputable def dft {N: ℕ} (x: (fin N) → ℂ) : (fin N → ℂ) := 
λ (k: fin N), ∑ (n : fin N), (Wₙ k n) * (x n)

lemma circ_dft_relation {N: ℕ} (t: (fin N) → ℂ) :
  matrix.circulant t = iWₙ ⬝ (diagonal(dft t)) ⬝ Wₙ := 
begin
  funext i j,
  rw circulant_apply,
  -- rw mul_mul_apply,
  -- rw dot_product,
  rw mul_apply',
  rw dot_product,
  simp only [mul_diagonal],
  rw dft,
  -- rw finset.sum_apply,
  simp only,
  conv_rhs {
    apply_congr, skip, 
    rw mul_comm, rw ← mul_assoc, 
  },

  have xa: 
  ∑ (x n : fin N), Wₙ x j * iWₙ i x * (Wₙ x n * t n)
   = ∑ (x : fin N), Wₙ x j * iWₙ i x * ∑ (n : fin N), Wₙ x n * t n, {
    conv_lhs {
      apply_congr, skip,
    },
    -- rw sum_const
  },
  -- rw Wₙ, rw iWₙ, simp only [coe_coe, neg_mul],
  -- rw mul_mul_apply',
end

-- example {N: ℕ} (f: ℕ → ℝ) (a: ℝ):
--   ∑ (i: ℕ) in range N, (a * (f i)) = 
--     a * ∑ (i: ℕ) in range N, (f i):= begin
--     rw finset.sum_fn,
-- end
-- example {N: ℕ} :
--   ∑ (i: ℕ) in range N, (1) = N := begin
-- simp only [sum_const, 
--   card_range, 
--   algebra.id.smul_eq_mul, 
--   mul_one],
-- end

example {N: ℕ} :
  ∑ (i j: ℕ) in range N, (1) = N*N := begin
  simp only [sum_const, card_range, algebra.id.smul_eq_mul, mul_one],
end

lemma twiddle_comm {N: ℕ}(k n: fin N) :
  Wₙ k n = Wₙ n k := begin
  rw Wₙ, simp only, ring_nf,
end

lemma twiddle_sum {N: ℕ}(k m n: fin N) :
  Wₙ k m * Wₙ k n  = Wₙ k (m + n) := begin
sorry,
end



lemma W_N_symmetric {N: ℕ} :
  (Wₙ: matrix (fin N) (fin N) ℂ) = (Wₙᵀ) := 
begin
  rw [transpose, Wₙ],
  funext k n, simp only [coe_coe, of_apply], ring_nf,
end

def revN {N: ℕ}:(fin N → fin N) := λ n: (fin N), (-n)
def revN_equiv {N: ℕ} {hN: ne_zero N} : (fin N) ≃ (fin N) := 
{ 
  to_fun := revN,
  inv_fun := revN,
  left_inv := by {intros x, rw revN, dsimp, rw neg_neg x,},
  right_inv := by {intros x, rw revN, dsimp, rw neg_neg x,},
}

def shiftk {N: ℕ}{hN: ne_zero N} (k: fin N):(fin N → fin N) 
  := λ n: (fin N), (n + k)
-- def unshiftk {N: ℕ}{hN: ne_zero N} (k: fin N):(fin N → fin N) 
--   := λ n: (fin N), (n - k)
def sev_ne_zero: ne_zero 7 :=  by {rw ne_zero_iff, norm_num,}

#eval @shiftk 7 (sev_ne_zero) 3 1
def shiftk_equiv {N: ℕ} {hN: ne_zero N} (k: fin N) : (fin N) ≃ (fin N) :=
{
  to_fun := @shiftk N hN (-k),
  inv_fun := @shiftk N hN (k),
  left_inv := by {
    intro x, rw shiftk, rw shiftk, dsimp, ring,
  },
  right_inv := by {
    intro x, rw shiftk, rw shiftk, dsimp, ring,
  },
}

lemma circ_dft_relation_2 {N: ℕ} {hN: ne_zero N} (t: (fin N) → ℂ) :
  matrix.circulant t = iWₙ ⬝ (diagonal(dft t)) ⬝ Wₙ := 
begin
  apply_fun (matrix.mul Wₙ),
  rw ← matrix.mul_assoc,
  rw ← matrix.mul_assoc,
  rw W_N_mul_iW_N,

  -- rw matrix.mul_assoc,
  -- simp only [nat.smul_one_eq_coe], 
  sorry {
  funext j k,
  rw mul_mul_apply,
  rw dot_product_mul_vec, simp only,
  rw ← W_N_symmetric, rw matrix.mul_apply,
  conv_lhs {
    apply_congr, skip,
    rw circulant_apply,
  },
  rw dot_product,
  
  conv_rhs {
    apply_congr, skip,
     
    rw vec_mul_diagonal,
    -- rw pi.smul_apply,
    -- rw pi.smul_apply,
    rw matrix.one_apply,
    rw ite_mul, rw ite_mul,
    rw zero_mul,
    rw zero_mul, rw one_mul,
    rw mul_comm,
  },
  rw sum_ite,
  simp only [sum_const_zero, add_zero],
  rw filter_eq,
  simp only [mem_univ, if_true, sum_singleton],
  rw dft, simp only,
  rw twiddle_comm,
  rw mul_sum,
  conv_rhs {
    apply_congr, skip,
    rw ← mul_assoc,
    rw twiddle_sum,
  },
  -- rw Wₙ,simp only, dsimp,
  rw ← equiv.sum_comp (@shiftk_equiv N hN (-k)),
  rw shiftk_equiv, dsimp,  
  rw shiftk, simp only [neg_neg, add_sub_cancel],
  conv_lhs {
    apply_congr, skip, rw add_comm,
  }, 
  },
  rw ne_zero_iff at hN, exact hN,
  -- extract_goal,
    rintros x a h,
  replace hinj := congr_arg (iWₙ).mul h,
  rw ← matrix.mul_assoc at hinj,
  rw ← matrix.mul_assoc at hinj,
  rw iW_N_mul_W_N at hinj,
  rw matrix.smul_mul at hinj,
  rw matrix.smul_mul at hinj,
  rw matrix.one_mul at hinj,
  rw matrix.one_mul at hinj,
  
  funext k n,
  have hz := (matrix.ext_iff.2 hinj) k n,
  repeat {rw pi.smul_apply at hz},
  have hNz : (N:ℂ) ≠ 0, {
    rw nat.cast_ne_zero, exact ne_zero_iff.1 hN,
  },
  rw ← sub_eq_zero at hz,
  rw ← smul_sub at hz,
  rw smul_eq_zero_iff_eq' hNz at hz,
  rwa sub_eq_zero at hz,
  exact hN,
end

#print instances monoid








-- example (N: ℕ) (hN: N = 5) (f: (fin 5) → ℝ) (a: fin 5) (ha: a = 2) :
-- ∑ (i : fin 5), f i = 
--   ∑ (j : fin 5), (f (j - a)) := 
-- begin
  
--   rw fin.sum_univ_five,
--   rw fin.sum_univ_five, 
--   rw ha, ring_nf,
-- end

example (N: ℕ) (hN: ne_zero N) (f: (fin N) → ℝ) (a: fin N) :
∑ (i : fin N), f i = 
  ∑ (j : fin N), (f (j - a)) := 
begin
  -- conv_rhs {
  --   rw finset.equiv.sum_comp_finset (@shiftk_equiv N hN a),
  -- } ,
  
  -- -- erw (@shiftk_equiv N hN a).sum_comp_finset f _, 
  -- rw shiftk_equiv, dsimp,  
  -- rw shiftk, dsimp,
  -- conv_lhs {
  --   apply_congr, skip, rw ← sub_eq_add_neg,
  -- },
  -- rw shiftk_equiv, dsimp, rw shiftk,
  -- extract_goal,

  rw ← equiv.sum_comp (@shiftk_equiv N hN a),
  rw shiftk_equiv, dsimp,  
  rw shiftk, dsimp,
  conv_lhs {
    apply_congr, skip, rw ← sub_eq_add_neg,
  },
end

-- def x : fin 5 := 3
-- #check (x + 2)
-- #eval (x + 2) 


-- #check revN_equiv

-- #eval (@revN_equiv 9).to_fun 0
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

-- #check λ x:(fin 3) , (3 - x)