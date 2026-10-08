import OAI.NumberTheory.DirichletL.Hecke.Dirichlet

/-!
# Boundary-independent transfer from the actual Hecke family

This uses the pinned OpenAI source's exact Eisenstein base-change identity.
The Hecke nonvanishing statement is an explicit hypothesis. The boundary can
be any nonnegative real number; this file supplies no improved Hecke estimate.
-/

namespace RH.Transport.PhysicalAnalytic

noncomputable section
open scoped Classical
open OAI.SevenEighths
open HeckeFamily

theorem dirichlet_of_hecke_at_boundary {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ (η : Character) (s : ℂ), B < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → LFunction η s ≠ 0)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : B < s.re) (hexc : ¬ (χ = 1 ∧ s = 1)) :
    χ.LFunction s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hexc) hge
  have hs1 : s ≠ 1 := by intro h; simp [h] at hge
  have hs0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    exact (not_lt_of_ge hB) hs
  have hh := hH (HeckeDirichlet.character χ) s hs (Or.inl hs1)
  rw [HeckeDirichlet.LFunction_eq_dirichlet_product χ hs0 hs1] at hh
  exact (mul_ne_zero_iff.mp hh).1

theorem zeta_of_hecke_at_boundary {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ (η : Character) (s : ℂ), B < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → LFunction η s ≠ 0)
    (s : ℂ) (hs : B < s.re) : riemannZeta s ≠ 0 := by
  by_cases h1 : s = 1
  · simpa [h1] using riemannZeta_one_ne_zero
  have hh := dirichlet_of_hecke_at_boundary hB hH
    (1 : DirichletCharacter ℂ 1) s hs (by simp [h1])
  simpa only [DirichletCharacter.LFunction_modOne_eq] using hh

end
end RH.Transport.PhysicalAnalytic
