import Transport.PhysicalHigh.RowCount
import Transport.TunedCertificate
import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorSourceCount

/-! Accounting used to turn the actual arithmetic class estimates into a
tuned nonfloor saving. The source count is used with Δ=0 throughout. -/

namespace RH.Transport.PhysicalHigh
noncomputable section
open OAI OAI.SevenEighths
open ProbeHighRowFamily

def profileExponent (a e : ℝ) : ℝ :=
  TunedCandidate.lx * (4 / 25) + a + 16 * e - 33 / 50 -
    TunedCandidate.ly * (a + 6 * e)

def arithmeticExponent (N : ℕ) (a v d R q e eps loss mesh overhead : ℝ) : ℝ :=
  overhead + d * R + v * (a - 1 / 2 + 12 * e + eps * (N + 8) - 17 / 50) +
    loss - (4 / 25) * TunedCandidate.ell + q * TunedCandidate.ell +
    mesh * TunedCandidate.ell

theorem tuned_physical_scale_identity (Z a e : ℝ) (hZ : 0 < Z) :
    (Z ^ TunedCandidate.lx) ^ (4 / 25 : ℝ) * Z ^ (a + 16 * e - 33 / 50) *
      (Z ^ TunedCandidate.ly) ^ (-a - 6 * e) = Z ^ profileExponent a e := by
  rw [← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le,
    ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  unfold profileExponent
  ring

theorem adaptiveRowExponent_zero {a q ε εm slot ν : ℝ} (ha : a ≤ 7 / 8) :
    adaptiveRowExponent (2 * a - 1) q 0 ε εm slot ν =
      RH.Transport.Endpoint.adaptiveCount (2 * a - 1) (q / (2 * a - 1)) +
        (159 * ε + εm + slot + 7 * ν) := by
  have hd : 2 * a - 1 ≤ (5 / 6 : ℝ) := by linarith
  simp only [adaptiveRowExponent, if_pos hd, balanced_count_eq, zero_div, add_zero]
  ring

theorem tuned_accounting (N : ℕ) (a q v d countLoss e eps loss mesh overhead : ℝ)
    (ha : (1 / 2 : ℝ) < a) :
    profileExponent a e + arithmeticExponent N a v d
      (RH.Transport.Endpoint.adaptiveCount (2 * a - 1) (q / (2 * a - 1)) + countLoss)
      q e eps loss mesh overhead =
    TunedCandidate.signal TunedCandidate.B +
      TunedCertificate.highExponent v (2 * a - 1) (q / (2 * a - 1)) +
      (d - v) * RH.Transport.Endpoint.adaptiveCount (2 * a - 1) (q / (2 * a - 1)) +
      d * countLoss + e * (16 - 6 * TunedCandidate.ly) + 12 * v * e +
      v * eps * (N + 8) + loss + mesh * TunedCandidate.ell + overhead := by
  have hd : 2 * a - 1 ≠ 0 := by linarith
  have hq : (2 * a - 1) * (q / (2 * a - 1)) = q := mul_div_cancel₀ q hd
  unfold profileExponent arithmeticExponent TunedCertificate.highExponent
    Certificate.rowSlope
  rw [hq]
  unfold TunedCandidate.signal TunedCandidate.signalAt
    TunedCandidate.h TunedCandidate.hAt TunedCandidate.ly TunedCandidate.lyAt
    TunedCandidate.lx TunedCandidate.lxAt
  ring

theorem tuned_mixed_saving (N : ℕ) (a q v d countLoss μ e eps loss mesh overhead saving : ℝ)
    (ha : (51 / 100 : ℝ) < a) (ha' : a ≤ 7 / 8)
    (hq : 0 ≤ q) (hq' : q ≤ (2 * a - 1) / 2)
    (hv : v ≤ TunedCandidate.h + TunedCandidate.zeta) (hd : d ≤ 1)
    (hμ : 0 ≤ μ) (hdv : d - v ≤ μ) (hcount : 0 ≤ countLoss)
    (he : 0 ≤ e) (heps : 0 ≤ eps)
    (hbudget : countLoss + μ + 26 * e + eps * (N + 8) + loss +
      mesh * TunedCandidate.ell + overhead + saving ≤ (3 / 4000000000000 : ℝ)) :
    profileExponent a e + arithmeticExponent N a v d
      (RH.Transport.Endpoint.adaptiveCount (2 * a - 1) (q / (2 * a - 1)) + countLoss)
      q e eps loss mesh overhead ≤ TunedCandidate.signal TunedCandidate.B - saving := by
  have hδ : 0 < 2 * a - 1 := by linarith
  have hlo : (1 / 50 : ℝ) ≤ 2 * a - 1 := by linarith
  have hhi : 2 * a - 1 ≤ (3 / 4 : ℝ) := by linarith
  have hx : 0 ≤ q / (2 * a - 1) := div_nonneg hq hδ.le
  have hx' : q / (2 * a - 1) ≤ (1 / 2 : ℝ) :=
    (div_le_iff₀ hδ).mpr (by linarith)
  have hend := TunedCertificate.buffered_high_bound hv hlo hhi hx hx'
  obtain ⟨hRlo, hRhi⟩ := Certificate.adaptive_count_bounds hlo hhi hx hx'
  have hR0 : 0 ≤ RH.Transport.Endpoint.adaptiveCount (2 * a - 1) (q / (2 * a - 1)) := by
    linarith
  have hdiff1 := mul_le_mul_of_nonneg_right hdv hR0
  have hdiff2 := mul_le_mul_of_nonneg_left hRhi hμ
  have hdiff : (d - v) * RH.Transport.Endpoint.adaptiveCount (2 * a - 1) (q / (2 * a - 1)) ≤ μ := by
    linarith
  have hcount' := mul_le_mul_of_nonneg_right hd hcount
  have hv1 : v ≤ 1 := hv.trans TunedCandidate.buffered_upper_scale_lt_one.le
  have hly : (1 / 3 : ℝ) ≤ TunedCandidate.ly := by
    norm_num [TunedCandidate.ly, TunedCandidate.lyAt, TunedCandidate.ell,
      Geometry.ell, TunedCandidate.p, TunedCandidate.b]
  have hprofile := mul_le_mul_of_nonneg_left
    (show 16 - 6 * TunedCandidate.ly ≤ (14 : ℝ) by linarith) he
  have hve := mul_le_mul_of_nonneg_right hv1 he
  have hveps := mul_le_mul_of_nonneg_right hv1
    (show 0 ≤ eps * (N + 8) by positivity)
  rw [tuned_accounting N a q v d countLoss e eps loss mesh overhead (by linarith)]
  nlinarith only [hend, hdiff, hcount', hprofile, hve, hveps, hbudget]

end
end RH.Transport.PhysicalHigh
