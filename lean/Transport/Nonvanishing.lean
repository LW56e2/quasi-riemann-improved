import Transport.CommonProbe
import Transport.OriginalBaseline

/-! Improved nonvanishing using only the pinned OpenAI theorem and the
independent transport proved in this library. -/

namespace RH.Transport
noncomputable section
open OAI.SevenEighths

theorem improved_hecke_boundary :
    HeckeZeroSupremum.beta≤(4374785349/5000000000 : ℝ) := by
  rw [←TunedCandidate.boundary_value]
  exact improved_hecke_boundary_of_original original_hecke_boundary

theorem hecke_nonvanishing (χ : HeckeFamily.Character) (s : ℂ)
    (hs : (4374785349/5000000000 : ℝ)<s.re)
    (hpole : s≠1 ∨ χ.residue≠1) : HeckeFamily.LFunction χ s≠0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ (improved_hecke_boundary.trans_lt hs) hpole

theorem dirichlet_nonvanishing {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : (4374785349/5000000000 : ℝ)<s.re)
    (hpole : ¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
  PhysicalAnalytic.dirichlet_of_hecke_at_boundary (by norm_num)
    hecke_nonvanishing χ s hs hpole

theorem zeta_nonvanishing (s : ℂ)
    (hs : (4374785349/5000000000 : ℝ)<s.re) : riemannZeta s≠0 :=
  PhysicalAnalytic.zeta_of_hecke_at_boundary (by norm_num)
    hecke_nonvanishing s hs

end
end RH.Transport
