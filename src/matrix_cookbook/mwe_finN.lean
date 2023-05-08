import data.complex.basic
import data.matrix.basic
import data.fin.basic
import data.matrix.notation


open matrix
open_locale matrix big_operators complex_conjugate
open equiv equiv.perm finset
open_locale matrix big_operators
open equiv equiv.perm finset
open complex

#print instances has_involutive_neg
#print instances has_one

lemma neg_neg_rev {N:ℕ} {hN: ne_zero N} (x: fin N) : - (-x) = x :=
begin
  rw @neg_neg (fin N) _ _,
end

lemma neg_neg_7 {N:ℕ} (x: fin 7): - (-x) = x :=
begin
  rw neg_neg x,
  --This one works!!
end

#print neg_neg_7

#check finset(fin 5)

example {N : ℕ}
  {hN : ne_zero N}
  {x a : matrix (fin N) (fin N) ℂ}
  (hinj : (↑N:ℂ) • x = (↑N:ℂ) • a) :
  x = a :=
begin
  funext k n,
  -- set X := (↑N:ℤ) • x,
  -- set A := (↑N:ℤ) • a,
  have hz := (matrix.ext_iff.2 hinj) k n,
  -- change X with (↑N:ℤ) • x at hz,
  -- change A with (↑N:ℤ) • a at hz,
  repeat {rw pi.smul_apply at hz},
  have hNz : (N:ℂ) ≠ 0, {
    rw nat.cast_ne_zero, exact ne_zero_iff.1 hN,
  },
  rw ← sub_eq_zero at hz,
  rw ← smul_sub at hz,
  rw smul_eq_zero_iff_eq' hNz at hz,
  rwa sub_eq_zero at hz,
end


