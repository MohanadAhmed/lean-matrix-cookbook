import data.complex.basic
import data.complex.exponential
import data.real.basic
import analysis.special_functions.pow
import analysis.special_functions.trigonometric.basic



open_locale real matrix big_operators
open matrix
open equiv equiv.perm finset
open complex

lemma cexp_pow {a b: ℝ} {ha: a ≠ 0}:
  exp(a*I)^(↑b:ℂ) = exp(a*b*I) := 
begin
  rw cpow_def,
  split_ifs, sorry,
  sorry,
  rw log_exp, ring_nf,
  rw mul_I_im, simp only [of_real_re], sorry,
  rw mul_I_im, simp only [of_real_re],
end

example {N : ℝ} {hE : 2 < N} :
  -π < (-2 * ↑π * I / ↑N).im :=
begin
  rw mul_assoc, rw exp_of_real_mul_I_im,
end

example {N : ℝ} {hE : 2 < N} :
  ((-2) * ↑π * I / ↑N).im ≤ π :=
begin
  admit,
end

lemma complex_exp_neg_one {N: ℝ} {hE: 2 < N} : 
  exp ( (-2 * π * I / ↑N) : ℂ)  ^ ((↑N:ℂ) / 2) = -1 := 
begin
  set α := exp(- 2 * π * I / N),
  have hα : α ≠ 0, by {apply exp_ne_zero,}, 
  rw (cpow_def_of_ne_zero hα (N/2: ℂ)),
  rw log_exp, sorry,
  
  sorry,
  /-
  example {N : ℝ}
    {hE : 2 < N} :
    let α : ℂ := exp ((-2) * ↑π * I / ↑N)
    in α ≠ 0 → ((-2) * ↑π * I / ↑N).im ≤ π :=
  begin
    intros α hα,
    admit,
  end
  
  
  -/
  
  extract_goal,

end