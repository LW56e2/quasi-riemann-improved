import Transport.TunedCandidate
import Transport.TunedEndpoint
import Transport.Certificate

/-!
# Joined two-parameter certificate

This module connects the current candidate's definitions to the exact endpoint
certificate and extends that exponent inequality to the buffered row interval.
It does not construct an estimate for an actual Hecke probe.
-/

namespace RH.Transport.TunedCertificate
noncomputable section

theorem candidate_matches_endpoint :
    TunedCandidate.p = TunedEndpoint.perturbation ∧
    TunedCandidate.b = TunedEndpoint.b ∧
    TunedCandidate.B = TunedEndpoint.boundary ∧
    TunedCandidate.ell = TunedEndpoint.ell ∧
    TunedCandidate.ly = TunedEndpoint.ly ∧
    TunedCandidate.h = TunedEndpoint.h ∧
    TunedCandidate.cushion = TunedEndpoint.saving := by
  norm_num [TunedCandidate.p, TunedCandidate.b, TunedCandidate.B,
    TunedCandidate.boundaryAt, TunedCandidate.ell, Geometry.ell,
    TunedCandidate.ly, TunedCandidate.lyAt, TunedCandidate.h, TunedCandidate.hAt,
    TunedCandidate.cushion, TunedEndpoint.perturbation, TunedEndpoint.b,
    TunedEndpoint.boundary, TunedEndpoint.ell, TunedEndpoint.ly, TunedEndpoint.h,
    TunedEndpoint.saving]

def highExponent (d δ x : ℝ) : ℝ :=
  (1 + δ) / 2 - TunedCandidate.B + TunedCandidate.h * (17 / 50 - 1 / 6) -
    ((1 + δ) / 2) * TunedCandidate.ly - TunedCandidate.ell / 2 +
    δ * x * TunedCandidate.ell + d * Certificate.rowSlope δ x

theorem high_exponent_endpoint (d δ x : ℝ) :
    highExponent d δ x = TunedEndpoint.endpointExponent δ x +
      (d - TunedCandidate.h) * Certificate.rowSlope δ x := by
  obtain ⟨_, _, hB, hell, hly, hh, _⟩ := candidate_matches_endpoint
  unfold highExponent TunedEndpoint.endpointExponent Certificate.rowSlope
  rw [hB, hell, hly, hh]
  simp only [TunedEndpoint.adaptiveCount]
  ring

/-- Bound on the entire buffered row interval for the tuned exponent. -/
theorem buffered_high_bound {d δ x : ℝ}
    (hd : d ≤ TunedCandidate.h + TunedCandidate.zeta)
    (hdlo : (1 / 50 : ℝ) ≤ δ) (hdhi : δ ≤ 3 / 4)
    (hxlo : 0 ≤ x) (hxhi : x ≤ 1 / 2) :
    highExponent d δ x ≤ -(3 / 4000000000000 : ℝ) := by
  have he := TunedEndpoint.adaptive_endpoint_bound hdlo hdhi hxlo hxhi
  obtain ⟨hs0, hs2⟩ := Certificate.row_slope_bounds hdlo hdhi hxlo hxhi
  have hm := mul_le_mul_of_nonneg_right
    (show d - TunedCandidate.h ≤ TunedCandidate.zeta by linarith) hs0
  have hz := mul_le_mul_of_nonneg_left hs2 TunedCandidate.zeta_pos.le
  rw [high_exponent_endpoint]
  norm_num [TunedCandidate.zeta] at hm hz
  linarith

end
end RH.Transport.TunedCertificate
