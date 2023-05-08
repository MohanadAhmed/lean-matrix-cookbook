import data.complex.basic
import data.complex.exponential
import analysis.special_functions.trigonometric.basic
import analysis.special_functions.complex.log

open_locale real matrix big_operators
open matrix
open equiv equiv.perm finset
open complex

-- eq_403 : Twiddle Factors
noncomputable def Wkn {N: ℕ} (k n: fin N) : ℂ :=  
exp(2 * π * I * k * n / N)

-- Forward DFT Matrix
noncomputable def W_N {N: ℕ}: matrix (fin N) (fin N) ℂ :=
of $ λ k n, Wkn k n

lemma twiddle_sum {N: ℕ}{hN: ne_zero N}(k m n: fin N) :
  W_N k m * W_N k n  = W_N k (m + n) := begin
  rw W_N, dsimp, 
  repeat {rw Wkn},
  have hNz: (↑N:ℂ) ≠ 0, {
    rw nat.cast_ne_zero, rwa ne_zero_iff at hN, 
  },

  rw ← exp_add, 
  rw exp_eq_exp_iff_exists_int,
  let a:ℤ := ((↑m + ↑n)/N),
  let w:ℤ := k*a,
  -- let w:ℤ,
  use w, 
  
  rw ← add_div, rw ← mul_add (2 * ↑π * I * ↑k),
  set α := (2 * ↑π * I),
  rw mul_comm _ α, 
  rw mul_assoc, rw mul_div_assoc,
  rw mul_assoc α _ _, rw mul_div_assoc α,
  rw ←  mul_add α,
  rw mul_right_inj' two_pi_I_ne_zero,
  rw div_eq_iff hNz, rw add_mul, 
  rw div_mul_cancel _ hNz ,
  change w with k*a,
  rw int.cast_mul, simp only [coe_coe, int.cast_coe_nat],
  rw ← coe_coe,
  rw mul_assoc,
  rw ← mul_add (↑k:ℂ),
  by_cases hk: (↑k:ℂ) ≠ 0, {
    -- rw mul_eq_mul_left_iff, left,
    rw mul_right_inj' hk,
    norm_cast, rw fin.coe_add,
    change a with ((↑m + ↑n)/N),
    simp only [coe_coe, int.cast_coe_nat], norm_cast,
    rw nat.mod_add_div' (↑m + ↑n) N,
  }, {
    simp only [not_not] at hk,
    rw hk, rw zero_mul, rw zero_mul,
  },
end

#print instances left_distrib_class
#print instances ring