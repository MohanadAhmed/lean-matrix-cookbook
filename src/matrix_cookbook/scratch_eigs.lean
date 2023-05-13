import data.complex.basic
import data.matrix.basic
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.pos_def
import linear_algebra.eigenspace

/- What we want to do is bring the eigenvalues/eigenvectors
definitons under control.! Make as many available results about
eigenvalues/eigenvectors formalized or in close range to
formalization.
-/

/-
  The first one we want to do is show that an n × n complex matrix
  has exactly n eigenvalues (with multiplicities).
-/

variables {n: Type*} [fintype n] [decidable_eq n] 
variable (Z: matrix n n ℂ)

open matrix
open_locale matrix big_operators

def eigs := λ (x: matrix n n ℂ), 
  module.End.eigenvalues (matrix.to_lin' x)

def mhas_eigenvector (A: matrix n n ℂ) (μ : ℂ) (x : n → ℂ) : Prop :=
  A.mul_vec x = μ•x ∧ x ≠ 0

def mhas_eigenvalue (A: matrix n n ℂ) (a : ℂ) : Prop :=
  ∃ (x: n → ℂ), mhas_eigenvector A a x

def eigenvalues (A: matrix n n ℂ) : Type* := {μ : ℂ // mhas_eigenvalue A μ}

lemma has_eigenvalue_of_has_eigenvector (A: matrix n n ℂ) {μ : ℂ} {x : n → ℂ} 
  (h : mhas_eigenvector A μ x) :
  mhas_eigenvalue A μ := sorry

lemma has_eigenvalue.exists_has_eigenvector {A: matrix n n ℂ} {μ : ℂ} 
  (hμ : mhas_eigenvalue A μ) :
  ∃ v, mhas_eigenvector A μ v := sorry

lemma equivalence_eigs.has_eigenvector (A: matrix n n ℂ) (μ : ℂ) (x : n → ℂ):
  mhas_eigenvector A μ x ↔ module.End.has_eigenvector (matrix.to_lin' A) μ x :=
begin
  unfold mhas_eigenvector,
  split;{
    intros heig, 
    rw module.End.has_eigenvector at *,
    rw module.End.mem_eigenspace_iff at *, 
    rw matrix.to_lin'_apply at *, assumption',
  },
end

lemma equivalence_eigs.has_eigenvalue (A: matrix n n ℂ) (μ : ℂ) : 
  mhas_eigenvalue A μ ↔ module.End.has_eigenvalue (matrix.to_lin' A) μ :=
begin
  split,{
    intros heig,
    rw mhas_eigenvalue at *,
    cases heig with x hx,
    rw mhas_eigenvector at *,
    rw module.End.has_eigenvalue,
    rw submodule.ne_bot_iff, use x,
    rw module.End.mem_eigenspace_iff at *,
    rw matrix.to_lin'_apply at *, assumption',
  }, {
    intros heig,
    rw mhas_eigenvalue at *,
    rw module.End.has_eigenvalue at *,
    rw submodule.ne_bot_iff at *,
    cases heig with x hx, cases hx with he hNz,
    use x,
    rw module.End.mem_eigenspace_iff at *,
    rw mhas_eigenvector at *,
    rw matrix.to_lin'_apply at *,
    split,
    assumption',
  },
end

#check module.End.eigenvalues.fintype (matrix.to_lin' Z)

noncomputable def eigs_fin (A: matrix n n ℂ) := 
  module.End.eigenvalues.fintype (matrix.to_lin' A)

#check eigs_fin

-- lemma equivalence_eigs.eigenvalues (A: matrix n n ℂ) :
--   (module.End.eigenvalues.fintype (matrix.to_lin' A)) =
--   fintype (eigenvalues A) 
-- begin

-- end


/-
# Useful References
- https://people.math.wisc.edu/~ellenberg/Math204Lects/Week10.pdf
-/