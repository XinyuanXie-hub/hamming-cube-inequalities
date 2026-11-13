import Mathlib

namespace HammingCubeAnalytic

noncomputable def Q (x : ℝ) : ℝ :=
  (2 / 3 : ℝ) * x * (1 - x) *
    (4 * Real.sqrt 2 - 3 + 4 * (3 - 2 * Real.sqrt 2) * x)

theorem Q_zero : Q 0 = 0 := by norm_num [Q]
theorem Q_half : Q (1 / 2) = 1 / 2 := by unfold Q; ring

theorem Q_nonneg (x : ℝ) (hx : 0 ≤ x) (hh : x ≤ 1 / 2) : 0 ≤ Q x := by
  have hlo : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hhi : Real.sqrt 2 ≤ (3 / 2 : ℝ) := Real.sqrt_le_iff.mpr (by norm_num)
  have hbase : 0 ≤ 4 * Real.sqrt 2 - 3 := by linarith
  have hcoef : 0 ≤ 3 - 2 * Real.sqrt 2 := by linarith
  have hfactor : 0 ≤ 1 - x := by linarith
  unfold Q
  positivity

/-- Pure polynomial branch of the two-point inequality. -/
theorem Q_two_point_squared (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ 1 / 2) :
    0 ≤ (y - x) ^ 2 + Q y ^ 2 - (2 * Q ((x + y) / 2) - Q x) ^ 2 := by
  let t := Real.sqrt (2 : ℝ)
  let a := 2 * x
  let b := 2 * (y - x)
  let c := 1 - 2 * y
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have htlo : (7 / 5 : ℝ) ≤ t := by nlinarith
  have hthi : t ≤ (10 / 7 : ℝ) := by nlinarith
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have h0 : 0 ≤ (3 - 2 * t : ℝ) := by linarith
  have h1 : 0 ≤ (8 - 16 * t / 3 : ℝ) := by linarith
  have h2 : 0 ≤ (35 / 4 - 6 * t : ℝ) := by linarith
  have h3 : 0 ≤ (65 / 3 - 14 * t : ℝ) := by linarith
  have h4 : 0 ≤ (7 / 3 : ℝ) := by linarith
  have h5 : 0 ≤ (10 - 7 * t : ℝ) := by linarith
  have h6 : 0 ≤ (131 / 6 - 14 * t : ℝ) := by linarith
  have h7 : 0 ≤ (12 * t - 12 : ℝ) := by linarith
  have h8 : 0 ≤ (64 * t / 3 - 82 / 3 : ℝ) := by linarith
  have h9 : 0 ≤ (17 * t / 3 - 22 / 3 : ℝ) := by linarith
  have h10 : 0 ≤ (22 * t - 343 / 12 : ℝ) := by linarith
  have h11 : 0 ≤ (64 * t / 3 - 82 / 3 : ℝ) := by linarith
  have heq : (y - x) ^ 2 + Q y ^ 2 - (2 * Q ((x + y) / 2) - Q x) ^ 2 =
    (y - x) ^ 2 * (
      (3 - 2 * t) * (a ^ 3 * b) +
      (8 - 16 * t / 3) * (a ^ 3 * c) +
      (35 / 4 - 6 * t) * (a ^ 2 * b ^ 2) +
      (65 / 3 - 14 * t) * (a ^ 2 * b * c) +
      (7 / 3) * (a ^ 2 * c ^ 2) +
      (10 - 7 * t) * (a * b ^ 3) +
      (131 / 6 - 14 * t) * (a * b ^ 2 * c) +
      (12 * t - 12) * (a * b * c ^ 2) +
      (64 * t / 3 - 82 / 3) * (a * c ^ 3) +
      (17 * t / 3 - 22 / 3) * (b ^ 3 * c) +
      (22 * t - 343 / 12) * (b ^ 2 * c ^ 2) +
      (64 * t / 3 - 82 / 3) * (b * c ^ 3) + c ^ 4) := by
    dsimp [Q, a, b, c, t]
    ring_nf
    norm_num [Real.sq_sqrt]
    ring
  rw [heq]
  positivity


theorem Q_two_point (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ 1 / 2) :
    2 * Q ((x + y) / 2) ≤ Real.sqrt ((y - x)^2 + Q y ^ 2) + Q x := by
  have h := Q_two_point_squared x y hx hxy hy
  have hs := Real.le_sqrt_of_sq_le (show (2 * Q ((x + y) / 2) - Q x)^2 ≤
      (y - x)^2 + Q y ^ 2 by linarith)
  linarith

end HammingCubeAnalytic
