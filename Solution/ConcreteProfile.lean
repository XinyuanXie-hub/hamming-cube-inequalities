import Solution.LogProfile
import Solution.CubicProfile
import Solution.AlternativeProfile
import Solution.PolynomialQRQ
import Solution.PolynomialQRR
import Solution.LRSymmetry
import Solution.CertificateAssembly
import Solution.LRFinal

namespace HammingCubeConcrete
open HammingCubeCertificateAssembly

noncomputable def B : ℝ → ℝ := assembled HammingCubeLog.L AlternativeProfile.Q AlternativeProfile.R

lemma max_bound_to_certificate {a b c d : ℝ}
    (h : 2*c ≤ max (Real.sqrt (d^2+b^2)) (d+(Real.sqrt 2-1)*b)+a) :
    0 ≤ max (twoPointOne a b c d) (twoPointTwo a b c d) := by
  have hh : 2*c-a ≤ max (Real.sqrt (d^2+b^2)) (d+(Real.sqrt 2-1)*b) := by linarith
  rcases le_max_iff.mp hh with hleft | hright
  · apply (le_max_left _ _).trans'
    dsimp [twoPointOne]
    linarith
  · apply (le_max_right _ _).trans'
    dsimp [twoPointTwo]
    linarith

/-- Exact certificates for all branch combinations. -/
theorem certificate :
    Certificates HammingCubeLog.L AlternativeProfile.Q AlternativeProfile.R where
  L_zero := HammingCubeLog.L_zero
  Q_zero := HammingCubeAnalytic.Q_zero
  R_one := AlternativeProfile.R_one
  L_half := HammingCubeLog.L_half
  Q_half := HammingCubeAnalytic.Q_half
  R_half := AlternativeProfile.R_half
  L_nonneg := fun t ht => HammingCubeLog.L_nonneg ht.1
  Q_nonneg := fun t ht => HammingCubeAnalytic.Q_nonneg t ht.1 ht.2
  R_nonneg := fun t ht => AlternativeProfile.R_nonneg t ht.1 ht.2
  L_two_point := fun x y hx hxy hy => HammingCubeLog.L_two_point hx hxy hy
  Q_two_point := HammingCubeAnalytic.Q_two_point
  R_two_point := AlternativeProfile.R_two_point
  L_le_Q := fun t ht => HammingCubeLog.L_le_Q ht.1 ht.2
  LRQ := fun x y hx hy hm =>
    max_bound_to_certificate (HammingCubeLRFinal.LRQ_bound x y hx hy hm)
  LRR := fun x y hx hy hm =>
    max_bound_to_certificate (HammingCubeLRFinal.LRR_bound x y hx hy hm)
  QRQ := by
    intro x y hx hy hm
    have hy' : y ∈ Set.Icc (1/2) (3/4) := ⟨hy.1,by linarith [hx.1]⟩
    exact HammingCubePolynomial.QRQ_two_point x y hx hy'
  QRR := by
    intro x y hx hy hm
    exact PolynomialQRR.QRR_two_point x y hx.1 hx.2 hy.1 hy.2 (by linarith)
  LR_symmetry := PolynomialLRSym.LR_symmetry
  QR_symmetry := fun x hx => AlternativeProfile.QR_symmetry x hx.1 hx.2

theorem B_zero : B 0 = 0 := assembled_zero certificate

theorem B_one : B 1 = 0 := assembled_one certificate

theorem B_nonneg (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ B x :=
  assembled_nonneg certificate x ⟨hx,hx1⟩

theorem B_ge_L (x : ℝ) (hx : x ≤ 1/2) : HammingCubeLog.L x ≤ B x :=
  assembled_ge_L x hx

theorem B_symmetry (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    4*x*(1-x) ≤ B x+B (1-x) :=
  assembled_symmetry certificate x ⟨hx,hx1⟩

theorem B_two_point (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    0 ≤ max
      (Real.sqrt ((y-x)^2+B y^2)+B x-2*B ((x+y)/2))
      (y-x+(Real.sqrt 2-1)*B y+B x-2*B ((x+y)/2)) :=
  assembled_two_point certificate x y hx hxy hy

theorem B_log_lower (x : ℝ) (hxhalf : x ≤ 1/2) :
    x*Real.sqrt (Real.logb 2 (1/x)) ≤ B x := B_ge_L x hxhalf

end HammingCubeConcrete

